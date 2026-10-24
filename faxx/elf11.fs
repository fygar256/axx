\ elf11.fs -- ELF オブジェクトの書き出し (2): セクションの組み立て、リロケーション項目

decimal

: build-csecs ( -- ok )
  bts @ 7 + 8 / 1 max e-bpw !
  0 ncs !
  pc @ 0 max { endw }
  sections om-count 0= if
    omax @ endw max
  else
    0 sections om-used 0 ?do
      i sections om-live? if
        i sections om-key { na nu }
        na nu sec-nranges 0 ?do na nu i sec-range@ nip + loop
      then
    loop
  then { totw }
  totw e-bpw @ * 1073741824 > if
    mb-reset s"  error - output size " mb+ totw e-bpw @ * mb-n s"  bytes exceeds maximum 1073741824. Check for incorrect .ORG or address values." mb+ mb-get diag-ef
    false exit
  then
  sections om-count 0= if
    s" .text" section-attrs
    bb-new { sb }
    0 totw sb extract-words
    s" .text" intern cs-nu ! cs-na !
    0 cs-bs !  sb cs-data !  sb bb-len cs-sz !
    sa-fl @ cs-fl !  sa-ty @ cs-ty !  sa-al @ cs-al !  sa-es @ cs-es !
    1 ncs !
    true exit
  then
  sections om-used 0 ?do
    i sections om-live? if
      ncs @ MAXSEC >= if leave then
      i sections om-key { na nu }
      na nu section-attrs
      bb-new { sb }
      na nu sec-nranges 0= if 0 else na nu 0 sec-range@ drop then { w0 }
      na nu sec-nranges 0 ?do na nu i sec-range@ sb extract-words loop
      ncs @ { k }
      na k cells cs-na + !  nu k cells cs-nu + !
      na nu sec-nranges 0= if i sections om-val @ else w0 then e-bpw @ * k cells cs-bs + !
      sb k cells cs-data + !  sb bb-len k cells cs-sz + !
      sa-fl @ k cells cs-fl + !  sa-ty @ k cells cs-ty + !  sa-al @ k cells cs-al + !  sa-es @ k cells cs-es + !
      1 ncs +!
    then
  loop
  true ;

\ ---- リロケーション項目 (rela_entries) ----
\ 項目: [0]=sidx(1 始まり) [2]=off [3]=name-a [4]=name-u [5]=rt [6..9]=addend [10]=nb [11]=fm
variable xr-n  variable xr-cap  variable xr-base
: xr-init ( -- ) 256 xr-cap ! xr-cap @ RLSZ * allocate throw xr-base ! 0 xr-n ! ;
xr-init
: xr@ ( i -- addr ) RLSZ * xr-base @ + ;
: xr-add ( sidx off na nu rt addend nb fm -- ) { sidx off na nu rt ad nb fm }
  xr-n @ xr-cap @ >= if xr-cap @ 2* xr-cap ! xr-base @ xr-cap @ RLSZ * resize throw xr-base ! then
  xr-n @ xr@ { e }
  sidx e !  0 e cell+ !  off e 2 cells + !
  na e 3 cells + !  nu e 4 cells + !
  rt e 5 cells + !  ad e 6 cells + q!  nb e 10 cells + !  fm e 11 cells + !
  1 xr-n +! ;

: build-relocs ( -- )
  0 xr-n !
  mach-table
  rl-n @ 0 ?do
    i rl@ { r }
    r @ r cell+ @ cs-find { si }
    si 0>= if
      si 1+ r 2 cells + @ r 3 cells + @ r 4 cells + @ r 5 cells + @ r 6 cells + r 10 cells + @ r 11 cells + @ xr-add
      r 5 cells + @ rtk mt-extra om-find ?dup if
        @ { l }
        l ml-n 0 ?do
          l i ml-crt { crt }  l i ml-sym { cs }
          si 1+ r 2 cells + @ cs if r 3 cells + @ r 4 cells + @ else 0 0 then crt q0 r 10 cells + @ 0 xr-add
        loop
      then
    else
      report? if
        mb-reset s"  error - relocation references unknown section '" mb+ r @ r cell+ @ mb+ s" '; dropped from output." mb+ mb-get diag-e
      then
    then
  loop ;

\ そのセクションに項目があるか
: sec-has-relocs? ( sidx -- f ) { sidx }
  xr-n @ 0 ?do i xr@ @ sidx = if true unloop exit then loop false ;
