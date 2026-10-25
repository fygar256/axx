\ elf14.fs -- ELF オブジェクトの書き出し (5): r_info、DWARF (-g)

decimal

\ ---- r_info ----
: elf-r-info ( sym rt -- v ) { sym rt }
  mt-rinfo-u @ if
    s" .elfrinfo" mt-rinfo-a @ mt-rinfo-u @ sym qn rt qn elf-call-func 0= if 0 then
    w-64 @ 0= if 4294967295 and then
    exit
  then
  w-64 @ if sym 32 lshift rt 4294967295 and or
  else sym 16777215 and 8 lshift rt 255 and or then ;

\ addend を int64 / int32 に丸める
: clamp-addend ( q -- n ) { q }
  w-64 @ if 63 else 31 then { bits }
  q1 bits qshl q1 q- { mx }  mx qneg q1 q- { mn }
  q mx q> if mx q>n exit then
  q mn q< if mn q>n exit then
  q q>n ;

\ リロケーション項目 1 つ (sec 抜き) を sb へ
: pack-rela ( off sym rt addend-q sb -- ) { off sym rt aq sb }
  sym rt elf-r-info { info }
  w-64 @ if off sb put64 info sb put64 aq clamp-addend sb put64
  else off sb put32 info sb put32 aq clamp-addend sb put32 then ;
: pack-rel ( off sym rt sb -- ) { off sym rt sb }
  sym rt elf-r-info { info }
  w-64 @ if off sb put64 info sb put64 else off sb put32 info sb put32 then ;

\ ---- DWARF ----
variable dw-abs  variable dw-asz
variable dw-sb-abbrev  variable dw-sb-info  variable dw-sb-line
variable dwi-n  variable dwl-n
variable dwi-at variable dwi-si variable dwi-rt variable dwi-ad     \ 項目の配列 (heap)
variable dwl-at variable dwl-si variable dwl-rt variable dwl-ad
variable dw-ok

: dwr-init ( -- )
  labels om-count 16 + dup cells allocate throw dwi-at !
  dup cells allocate throw dwi-si !  dup cells allocate throw dwi-rt !  cells allocate throw dwi-ad !
  0 dwi-n !
  1024 cells allocate throw dwl-at !  1024 cells allocate throw dwl-si !
  1024 cells allocate throw dwl-rt !  1024 cells allocate throw dwl-ad !
  0 dwl-n ! ;
: dwi-add ( at si rt ad -- ) { at si rt ad }
  at dwi-at @ dwi-n @ cells + !  si dwi-si @ dwi-n @ cells + !
  rt dwi-rt @ dwi-n @ cells + !  ad dwi-ad @ dwi-n @ cells + !  1 dwi-n +! ;
: dwl-add ( at si rt ad -- ) { at si rt ad }
  dwl-n @ 1024 >= if exit then
  at dwl-at @ dwl-n @ cells + !  si dwl-si @ dwl-n @ cells + !
  rt dwl-rt @ dwl-n @ cells + !  ad dwl-ad @ dwl-n @ cells + !  1 dwl-n +! ;

: put-addr ( v sb -- ) dw-asz @ swap put ;

: dw-addr>sec ( ba sa su -- sidx off true | false ) { ba sa su }
  ba e-bpw @ / { wpc }
  su 0> if
    sa su cs-find { ix }
    ix 0>= if sa su wpc addr>woff if e-bpw @ * ix 1+ swap true exit then then
  then
  ncs @ 0 ?do
    i cs-name wpc addr>woff if e-bpw @ * i 1+ swap true unloop exit then
  loop
  false ;

: dw-check ( -- ok )
  mach-table
  mt-dwarf@ 0= if
    mb-reset s"  warning - DWARF debug info (-g) needs an absolute relocation type for machine " mb+ elf-machine @ mb-n
    s" ; declare it with .elfdwarf. Skipping debug sections." mb+ mb-get diag-w false exit
  then
  mt-dwarf@ dw-abs !
  w-64 @ if 8 else 4 then dw-asz !
  dw-abs @ mt-bytes@ dw-asz @ <> if
    dw-asz @ 8 = if s" abs64" else s" abs32" then mt-named om-find ?dup if @ else 0 then { alt }
    alt 0<> if alt mt-bytes@ dw-asz @ = else false then
    if alt dw-abs !
    else
      mb-reset s"  warning - DWARF debug info (-g) needs a " mb+ dw-asz @ mb-n s" -byte absolute relocation, which " mb+ mt-name mb+
      s"  does not have; skipping debug sections." mb+ mb-get diag-w false exit
    then
  then
  true ;

: dw-abbrev ( labels? -- ) { lab? }
  bb-new dw-sb-abbrev !
  dw-sb-abbrev @ { a }
  1 a uleb  17 a uleb  lab? if 1 else 0 then a put8
  37 a uleb 8 a uleb   19 a uleb 5 a uleb   3 a uleb 8 a uleb   27 a uleb 8 a uleb
  17 a uleb 1 a uleb   18 a uleb 7 a uleb   16 a uleb 23 a uleb
  0 a uleb 0 a uleb
  2 a uleb 10 a uleb 0 a put8
  3 a uleb 8 a uleb  17 a uleb 1 a uleb
  0 a uleb 0 a uleb
  0 a uleb ;

create cwd14 4096 allot
: get-cwd ( -- a u ) cwd14 4096 get-dir intern ;

variable dw-nlab  variable dwlab-base
: dwlab@ ( i -- addr ) 4 * cells dwlab-base @ + ;     \ name-a name-u sidx off

: dw-collect-labels ( -- )
  0 dw-nlab !
  labels om-count 1+ 4 * cells allocate throw dwlab-base !
  labels sort-om { la ln }
  ln 0 ?do
    la i cells + @ { ix }
    ix labels om-val { sl }
    sl lab-equ? sl lab-imported? or 0= if
      sl q>n e-bpw @ * sl 4 cells + s@ dw-addr>sec if
        { sidx off }
        dw-nlab @ dwlab@ { e }
        ix labels om-key e cell+ ! e !
        sidx e 2 cells + !  off e 3 cells + !
        1 dw-nlab +!
      then
    then
  loop
  la free throw ;

: lm-fname ( i -- a u ) lm@ { e } e 3 cells + @ e 4 cells + @ dup 0= if 2drop s" (source)" then ;

variable dw-prim-idx  variable dw-prim-size
: dw-build-info ( -- )
  bb-new { die }
  1 die uleb
  s" axx general assembler (DWARF4)" die put-cstr
  32769 die put16
  0 lm-fname die put-cstr
  get-cwd die put-cstr
  dw-prim-idx @ if die bb-len dw-prim-idx @ dw-abs @ 0 dwi-add then
  0 die put-addr
  dw-prim-size @ die put64
  0 die put32
  dw-nlab @ 0 ?do
    i dwlab@ { e }
    2 die uleb
    e @ e cell+ @ die put-cstr
    die bb-len e 2 cells + @ dw-abs @ e 3 cells + @ dwi-add
    mt-rela? if 0 else e 3 cells + @ then die put-addr
  loop
  dw-nlab @ if 0 die uleb then
  bb-new { ib }
  4 ib put16  0 ib put32  dw-asz @ ib put8  die sb$ ib put-bytes
  bb-new dw-sb-info !
  ib bb-len dw-sb-info @ put32  ib sb$ dw-sb-info @ put-bytes
  dwi-n @ 0 ?do dwi-at @ i cells + dup @ 11 + swap ! loop ;

\ 行表
variable dw-nfiles
create dw-fa 4096 cells allot  create dw-fu 4096 cells allot
: dw-file-idx ( a u -- idx ) { a u }
  dw-nfiles @ 0 ?do i cells dw-fa + @ i cells dw-fu + @ a u str=cs if i 1+ unloop exit then loop
  dw-nfiles @ 4096 >= if 1 exit then
  a u intern dw-nfiles @ cells dw-fu + ! dw-nfiles @ cells dw-fa + !
  1 dw-nfiles +!  dw-nfiles @ ;

262144 cells lazy dw-rows  variable dw-nrows
: dw-woff ( name-a name-u wpc -- n ) addr>woff 0= if 0 then ;

: dw-line-sec ( s -- ) { s }                              \ s = セクション番号 (1 始まり)
  0 dw-nrows !
  lm-n @ 0 ?do
    i lm@ dup @ swap cell+ @ cs-find 1+ s = if
      dw-nrows @ 262144 < if i dw-nrows @ cells dw-rows + !  1 dw-nrows +! then
    then
  loop
  dw-nrows @ 0= if exit then
  dw-nrows @ 1 > if
    dw-nrows @ 1 do
      dw-rows i cells + @ { x }  x lm@ 2 cells + @ { xw }  i { j }
      begin j 0> if dw-rows j 1- cells + @ lm@ 2 cells + @ xw > else false then while
        dw-rows j 1- cells + @ dw-rows j cells + !  j 1- to j
      repeat
      x dw-rows j cells + !
    loop
  then ;

variable dw-hlen
: dw-build-line ( -- )
  0 dw-nfiles !
  lm-n @ 0 ?do i lm-fname dw-file-idx drop loop
  bb-new { h }
  1 h put8 1 h put8 1 h put8  251 h put8  14 h put8  13 h put8
  0 h put8 1 h put8 1 h put8 1 h put8 1 h put8 0 h put8 0 h put8 0 h put8 1 h put8 0 h put8 0 h put8 1 h put8
  0 h put8
  dw-nfiles @ 0 ?do i cells dw-fa + @ i cells dw-fu + @ h put-cstr  0 h uleb 0 h uleb 0 h uleb loop
  0 h put8
  h bb-len dw-hlen !
  bb-new { prog }
  10 h bb-len + { pbase }
  ncs @ 1+ 1 ?do
    i dw-line-sec
    dw-nrows @ if
      i 1- cs-name { sa su }
      dw-rows @ lm@ 2 cells + @ { w0 }
      sa su w0 dw-woff e-bpw @ * { first }
      0 prog put8  1 dw-asz @ + prog uleb  2 prog put8
      pbase prog bb-len + i dw-abs @ first dwl-add
      mt-rela? if 0 else first then prog put-addr
      first { curo }  1 { curl }  1 { curf }
      dw-nrows @ 0 ?do
        dw-rows i cells + @ lm@ { e }
        e 2 cells + @ { wpc }
        sa su wpc dw-woff e-bpw @ * { bo }
        dw-rows i cells + @ lm-fname dw-file-idx { fi }
        fi curf <> if 4 prog put8 fi prog uleb fi to curf then
        e 5 cells + @ { ln }
        ln curl <> if 3 prog put8 ln curl - prog sleb ln to curl then
        bo curo > if 2 prog put8 bo curo - prog uleb bo to curo then
        1 prog put8
      loop
      i 1- cells cs-sz + @ { endo }
      endo curo > if 2 prog put8 endo curo - prog uleb then
      0 prog put8  1 prog uleb  1 prog put8
    then
  loop
  bb-new { lb }
  4 lb put16  h bb-len lb put32  h sb$ lb put-bytes  prog sb$ lb put-bytes
  bb-new dw-sb-line !
  lb bb-len dw-sb-line @ put32  lb sb$ dw-sb-line @ put-bytes ;
