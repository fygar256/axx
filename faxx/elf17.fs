\ elf17.fs -- ELF オブジェクトの書き出し (8): 名前表、配置、ファイル

decimal

create secname-off MAXSEC cells allot
create dbgpname-s 3 cells allot

: shs-add ( a u -- off ) shs @ bb-len -rot shs @ put-cstr ;
: dbg-prog-name ( i -- a u ) dup 0= if drop s" .debug_abbrev" exit then 1 = if s" .debug_info" else s" .debug_line" then ;
: dbg-rela-tgt ( kind -- a u ) 0= if s" .debug_info" else s" .debug_line" then ;

: wr-shstr ( -- )
  bb-new shs !  0 shs @ sb-c
  ncs @ 0 ?do i cs-name shs-add i cells secname-off + ! loop
  nrela @ 0 ?do rela-prefix rso i cells + @ 1- cs-name sconcat shs-add i cells rname-off + ! loop
  s" .symtab" shs-add sh-symtab-name !
  s" .strtab" shs-add sh-strtab-name !
  s" .shstrtab" shs-add sh-shstr-name !
  ndbgp @ 0 ?do i dbg-prog-name shs-add i cells dpname-off + ! loop
  ndbgr @ 0 ?do rela-prefix i cells drkind + @ dbg-rela-tgt sconcat shs-add i cells drname-off + ! loop
  ngr @ 0 ?do i cells gr-na + @ i cells gr-nu + @ shs-add i cells gname-off + ! loop
  ncs @ G @ + 65280 >= need-xidx !
  cfi-cur @ if s"  error - .cfi_startproc without .cfi_endproc." diag-e then
  cfi-head @ 0<> has-eh !
  has-eh @ if
    s" .eh_frame" shs-add sh-eh-name !
    rela-prefix s" .eh_frame" sconcat shs-add sh-ehr-name !
  then
  need-xidx @ if s" .symtab_shndx" shs-add sh-xidx-name ! then ;

\ ELF32 の r_info に収まらない型・シンボル番号の警告
: wr-elf32-warn ( -- )
  w-64 @ mt-rinfo-u @ or if exit then
  1 om-new { wt }  false { wsym }
  nrela @ 0 ?do
    rso i cells + @ { sidx }
    xr-n @ 0 ?do
      i xr@ { e }
      e @ sidx = if
        e 5 cells + @ { rt }
        rt 255 > if
          rt n>s wt om-find 0= if
            rt n>s wt om-put drop
            mb-reset s"  warning - relocation type " mb+ rt mb-n s"  does not fit the 8-bit type field of an ELF32 r_info; it is written as " mb+ rt 255 and mb-n s" ." mb+ mb-get diag-w
          then
        then
        wsym 0= if
          e 3 cells + @ e 4 cells + @ symidx om-find ?dup if @ 16777215 > else false then if
            true to wsym
            s"  warning - more than 16777215 symbols: the symbol index does not fit the 24-bit field of an ELF32 r_info." diag-w
          then
        then
      then
    loop
  loop
  wt om-free ;

: wr-rela-data ( -- )
  nrela @ 0 ?do
    rso i cells + @ { sidx }
    bb-new { b }
    xr-n @ 0 ?do
      i xr@ { e }
      e @ sidx = if
        e 3 cells + @ e 4 cells + @ dup if symidx om-find ?dup if @ else 0 then else 2drop 0 then { sym }
        mt-rela? if e 2 cells + @ sym e 5 cells + @ e 6 cells + b pack-rela
        else e 2 cells + @ sym e 5 cells + @ b pack-rel then
      then
    loop
    b i cells rdata + !
  loop ;

: wr-eh ( -- )
  0 eh-data-sb !  0 eh-rdata-sb !
  has-eh @ 0= if exit then
  build-eh-frame
  eh-sb @ eh-data-sb !
  bb-new eh-rdata-sb !
  er-n @ 0 ?do
    mt-rela? if er-at i cells + @ er-si i cells + @ er-rt i cells + @ er-ad i cells + @ qn eh-rdata-sb @ pack-rela
    else er-at i cells + @ er-si i cells + @ er-rt i cells + @ eh-rdata-sb @ pack-rel then
  loop ;

: wr-group-data ( -- )
  ngr @ 0 ?do
    bb-new { b }
    i cells gr-fl + @ b put32
    i cells gr-nm + @ { nm }
    i 256 * cells gr-mem + { mp }
    nm 0 ?do mp i cells + @ G @ + b put32 loop
    nm 0 ?do
      mp i cells + @ { k }
      nrela @ 0 ?do rso i cells + @ k = if ncs @ 1+ i + G @ + b put32 then loop
    loop
    b i cells gdata + !
    i cells gr-sa + @ i cells gr-su + @ symidx om-find ?dup if @ else
      i cells gr-sa + @ i cells gr-su + @ cs-find dup 0>= if 1+ else
        drop
        mb-reset s"  warning - .elfgroup: signature symbol '" mb+ i cells gr-sa + @ i cells gr-su + @ mb+ s" ' of group '" mb+
        i cells gr-na + @ i cells gr-nu + @ mb+ s" ' is not in the symbol table." mb+ mb-get diag-w
        0
      then
    then
    i cells ginfo + !
  loop ;

\ ---- 配置 ----
variable L-symtab-off  variable L-strtab-off  variable L-shstr-off  variable L-base-idx
variable L-total  variable L-shstrndx  variable L-symtab-shidx  variable L-strtab-shidx
variable L-eh-off  variable L-ehr-off  variable L-eh-shidx  variable L-xidx-off  variable L-xidx-shidx
variable L-shdr-off
variable L-eh-fl variable L-eh-ty variable L-eh-al variable L-eh-es

: nobits? ( i -- f ) cells cs-ty + @ 8 = ;
: len-of ( sb|0 -- n ) ?dup if bb-len else 0 then ;

: wr-layout ( -- )
  ehdr-size @ { off }
  ncs @ 0 ?do
    i cs-align dup 0= if drop 1 then 16 max { al }
    off al align-up2 to off
    off i cells soff + !
    i nobits? 0= if off i cells cs-sz + @ + to off then
  loop
  nrela @ 0 ?do
    off 8 align-up2 to off  off i cells roff + !
    off i cells rdata + @ bb-len + to off
  loop
  off 8 align-up2 L-symtab-off !
  L-symtab-off @ sy-sb @ bb-len + to off
  off L-strtab-off !  off st-sb @ bb-len + to off
  off L-shstr-off !  off shs @ bb-len + to off
  ncs @ nrela @ + 3 + G @ + L-base-idx !
  ndbgp @ 0 ?do off i cells dpoff + !  off i cells dpsb + @ bb-len + to off loop
  ndbgr @ 0 ?do off 8 align-up2 to off  off i cells droff + !  off i cells drsb + @ bb-len + to off loop
  ndbgp @ ndbgr @ + { ndbg }
  1 ncs @ + nrela @ + 3 + ndbg + G @ + L-total !
  ncs @ nrela @ + 3 + G @ + L-shstrndx !
  ncs @ nrela @ + 1+ G @ + L-symtab-shidx !
  ncs @ nrela @ + 2 + G @ + L-strtab-shidx !
  ngr @ 0 ?do off 4 align-up2 to off  off i cells goff + !  off i cells gdata + @ bb-len + to off loop
  s" .eh_frame" section-attrs
  sa-fl @ L-eh-fl !  sa-ty @ L-eh-ty !  sa-al @ L-eh-al !  sa-es @ L-eh-es !
  L-eh-al @ 0< if
    d-cfi? @ d-cfi-pad @ 0<> and if d-cfi-pad @ else w-64 @ if 8 else 4 then then L-eh-al !
  then
  0 L-eh-off !  0 L-ehr-off !  0 L-eh-shidx !
  has-eh @ if
    off L-eh-al @ 1 max align-up2 to off  off L-eh-off !  off eh-data-sb @ bb-len + to off
    off 8 align-up2 to off  off L-ehr-off !  off eh-rdata-sb @ bb-len + to off
    L-total @ L-eh-shidx !  2 L-total +!
  then
  0 L-xidx-off !  0 L-xidx-shidx !
  need-xidx @ if
    off 4 align-up2 to off  off L-xidx-off !  off xidx-sb @ bb-len + to off
    L-total @ L-xidx-shidx !  1 L-total +!
  then
  off 8 align-up2 L-shdr-off ! ;

\ .elflink の値 (セクション名か数)
: hexdig? ( c -- f ) lc dup digc? swap dup 97 >= swap 102 <= and or ;
: shidx-of ( ta tu sa su what-a what-u -- n ) { ta tu sa su wa wu }
  ta tu strip-st to tu to ta
  tu 0= if 0 exit then
  true { dig } tu 0 ?do ta i + c@ digc? 0= if false to dig then loop
  dig if ta tu parse-int0 drop exit then
  ta tu s" 0x" starts-ci? tu 2 > and if
    true { hx } tu 2 ?do ta i + c@ hexdig? 0= if false to hx then loop
    hx if ta tu parse-int0 drop exit then
  then
  ta tu slower { tl tlu }
  ncs @ 0 ?do i cs-name tl tlu str=ci if i 1+ G @ + unloop exit then loop
  nrela @ 0 ?do
    rela-prefix rso i cells + @ 1- cs-name sconcat tl tlu str=ci if ncs @ 1+ i + G @ + unloop exit then
  loop
  tl tlu s" .symtab" str=cs if L-symtab-shidx @ exit then
  tl tlu s" .strtab" str=cs if L-strtab-shidx @ exit then
  tl tlu s" .shstrtab" str=cs if L-shstrndx @ exit then
  ndbgp @ 0 ?do i dbg-prog-name tl tlu str=ci if L-base-idx @ 1+ i + unloop exit then loop
  mb-reset s"  warning - .elflink: " mb+ wa wu mb+ s"  of '" mb+ sa su mb+ s" ': no section named '" mb+ ta tu mb+ s" '; written as 0." mb+ mb-get diag-w
  0 ;

\ ---- ファイルへ ----
: out-sb ( sb out -- ) { sb out } sb sb$ out put-bytes ;

: wr-emit-body ( out -- ) { out }
  1 elf-machine @ L-shdr-off @
  L-total @ 65280 >= if 0 else L-total @ then
  L-shstrndx @ 65280 >= if 65535 else L-shstrndx @ then
  out pack-ehdr
  ncs @ 0 ?do
    i cells soff + @ out pad-to
    i nobits? 0= if i cells cs-data + @ out out-sb then
  loop
  nrela @ 0 ?do i cells roff + @ out pad-to  i cells rdata + @ out out-sb loop
  L-symtab-off @ out pad-to  sy-sb @ out out-sb  st-sb @ out out-sb  shs @ out out-sb
  ndbgp @ 0 ?do i cells dpoff + @ out pad-to  i cells dpsb + @ out out-sb loop
  ndbgr @ 0 ?do i cells droff + @ out pad-to  i cells drsb + @ out out-sb loop
  ngr @ 0 ?do i cells goff + @ out pad-to  i cells gdata + @ out out-sb loop
  has-eh @ if
    L-eh-off @ out pad-to  eh-data-sb @ out out-sb
    L-ehr-off @ out pad-to  eh-rdata-sb @ out out-sb
  then
  need-xidx @ if L-xidx-off @ out pad-to  xidx-sb @ out out-sb then
  L-shdr-off @ out pad-to ;

: rela-shtype ( -- n ) mt-rela? if 4 else 9 then ;
: rel-entsize ( -- n ) mt-rela? if w-64 @ if 24 else 12 then else w-64 @ if 16 else 8 then then ;
: word-align ( -- n ) w-64 @ if 8 else 4 then ;

: wr-shdrs ( out -- ) { out }
  0 0 0 0 0
  L-total @ 65280 >= if L-total @ else 0 then
  L-shstrndx @ 65280 >= if L-shstrndx @ else 0 then
  0 0 0 out pack-shdr
  ngr @ 0 ?do
    i cells gname-off + @ 17 0 0 i cells goff + @ i cells gdata + @ bb-len
    L-symtab-shidx @ i cells ginfo + @ 4 4 out pack-shdr
  loop
  ncs @ 0 ?do
    i cs-name { na nu }
    na nu slower d-link om-find ?dup if { dl } dl dstr@ dl 2 cells + dstr@ else s" " s" " then { lka lku ia iu }
    i cells secname-off + @  i cells cs-ty + @  i cells cs-fl + @  0  i cells soff + @  i cells cs-sz + @
    lka lku na nu s" sh_link" shidx-of
    ia iu na nu s" sh_info" shidx-of
    i cs-align  i cells cs-es + @  out pack-shdr
  loop
  nrela @ 0 ?do
    i cells rname-off + @  rela-shtype
    64 rso i cells + @ cells grp-member + @ if 512 or then
    0  i cells roff + @  i cells rdata + @ bb-len
    L-symtab-shidx @  rso i cells + @ G @ +  word-align  rel-entsize  out pack-shdr
  loop
  sh-symtab-name @ 2 0 0 L-symtab-off @ sy-sb @ bb-len
  L-strtab-shidx @ sy-first-global @ word-align  w-64 @ if 24 else 16 then  out pack-shdr
  sh-strtab-name @ 3 0 0 L-strtab-off @ st-sb @ bb-len 0 0 1 0 out pack-shdr
  sh-shstr-name @ 3 0 0 L-shstr-off @ shs @ bb-len 0 0 1 0 out pack-shdr
  ndbgp @ 0 ?do
    i cells dpname-off + @ 1 0 0 i cells dpoff + @ i cells dpsb + @ bb-len 0 0 1 0 out pack-shdr
  loop
  ndbgr @ 0 ?do
    i cells drname-off + @ rela-shtype 64 0 i cells droff + @ i cells drsb + @ bb-len
    L-symtab-shidx @  i cells drkind + @ 0= if 2 else 3 then L-base-idx @ +  word-align rel-entsize out pack-shdr
  loop
  has-eh @ if
    sh-eh-name @ L-eh-ty @ L-eh-fl @ 0 L-eh-off @ eh-data-sb @ bb-len 0 0 L-eh-al @ L-eh-es @ out pack-shdr
    sh-ehr-name @ rela-shtype 64 0 L-ehr-off @ eh-rdata-sb @ bb-len L-symtab-shidx @ L-eh-shidx @ word-align rel-entsize out pack-shdr
  then
  need-xidx @ if
    sh-xidx-name @ 18 0 0 L-xidx-off @ xidx-sb @ bb-len L-symtab-shidx @ 0 4 4 out pack-shdr
  then ;

: wr-xidx ( -- )
  0 xidx-sb !
  need-xidx @ 0= if exit then
  bb-new xidx-sb !
  sx-n @ 0 ?do sx-base @ i cells + @ 4294967295 and xidx-sb @ put32 loop ;

: wr-message ( -- )
  mb-reset s" elf: wrote " mb+ o-obj-a @ o-obj-u @ mb+ s"  (" mb+ ncs @ mb-n s"  section(s), " mb+ nrela @ mb-n s"  " mb+
  mt-rela? if s" rela" else s" rel" then mb+ s"  section(s), " mb+ sy-n @ mb-n s"  symbol(s)" mb+
  ndbgp @ if s" , " mb+ ndbgp @ mb-n s"  debug section(s)" mb+ then
  s" )" mb+ mb-get etype ecr ;

: write-elf-obj-impl ( -- )
  o-obj-u @ 0= if exit then
  wr-prelude
  bts @ e-bts !  bts @ mask-q e-mask q!
  build-csecs 0= if exit then
  build-relocs
  rel-patch-all
  wr-rela-order
  build-groups
  wr-dwarf
  wr-shstr
  build-symtab
  wr-elf32-warn
  wr-rela-data
  wr-eh
  wr-xidx
  wr-group-data
  wr-layout
  bb-new { out }
  out wr-emit-body
  out wr-shdrs
  o-obj-a @ o-obj-u @ w/o create-file if
    drop
    mb-reset s"  error - cannot create ELF output file '" mb+ o-obj-a @ o-obj-u @ mb+ s" ': [Errno 2] No such file or directory: '" mb+
    o-obj-a @ o-obj-u @ mb+ s" '" mb+ mb-get diag-e exit
  then
  { fid }
  out sb$ fid write-file throw
  fid close-file throw
  wr-message ;
' write-elf-obj-impl is write-elf-obj
