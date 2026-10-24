\ elf15.fs -- ELF オブジェクトの書き出し (6): REL (加数を欄へ書き戻す)

decimal

1 om-new constant rp-written
: sec-base ( sidx -- a ) 1- cells cs-data + @ sb$ drop ;
: sec-len ( sidx -- n ) 1- cells cs-sz + @ ;

\ 欄の位置のバイト列をワード (bpw バイト) として読む / 書く
: rp-word@ ( a -- u ) { a }
  0 e-bpw @ 0 ?do
    endian-big @ 0= if a i + c@ i 8 * lshift else a i + c@ e-bpw @ 1- i - 8 * lshift then or
  loop ;
: rp-word! ( u a -- ) { u a }
  e-bpw @ 0 ?do
    endian-big @ 0= if u i 8 * rshift 255 and else u e-bpw @ 1- i - 8 * rshift 255 and then a i + c!
  loop ;

: rp-iv-read ( a nw -- q ) { a nw }
  q0 { iv }
  nw 0 ?do
    a i e-bpw @ * + rp-word@ qun e-mask qand
    endian-big @ 0= if i e-bts @ * else nw 1- i - e-bts @ * then qshl iv qor to iv
  loop
  iv ;
: rp-iv-write ( q a nw -- ) { iv a nw }
  nw 0 ?do
    iv endian-big @ 0= if i e-bts @ * else nw 1- i - e-bts @ * then qsar e-mask qand q>n a i e-bpw @ * + rp-word!
  loop ;

: rel-patch-one ( e -- ) { e }
  e @ { sidx }
  e 2 cells + @ { off }
  e 6 cells + { aq }
  e 10 cells + @ { nb }
  e 11 cells + @ { fm }
  e 5 cells + @ { rt }
  sidx n>s s" :" sconcat off n>s sconcat { ka ku }
  ka ku rp-written om-find if exit then
  ka ku rp-written om-put drop
  rt field-load { fd? }
  fd? fm 0<> and if fm g-fm ! then
  rt rtk mt-encode om-find ?dup if
    dstr@ { fa fu }
    nb e-bpw @ / 1 max { nw }
    off 0>= off nw e-bpw @ * + sidx sec-len <= and 0= if exit then
    sidx sec-base off + { a }
    a nw rp-iv-read { iv }
    s" .elfencode" fa fu iv aq elf-call-func 0= if exit then
    qn a nw rp-iv-write
    exit
  then
  fd? if
    nb e-bpw @ / 1 max { nw }
    off 0>= off nw e-bpw @ * + sidx sec-len <= and 0= if exit then
    sidx sec-base off + { a }
    a nw rp-iv-read { iv }
    iv g-fm @ qun qnot qand
    g-fm @ aq g-fsh @ qsar field-deposit qun qor
    a nw rp-iv-write
    exit
  then
  off 0>= off nb + sidx sec-len <= and 0= if exit then
  sidx sec-base off + { a }
  nb 0 ?do
    aq endian-big @ 0= if i 8 * else nb 1- i - 8 * then qsar q>n 255 and a i + c!
  loop ;

: rel-patch-all ( -- )
  mt-rela? if exit then
  rp-written om-clear
  mach-table
  xr-n @ 0 ?do i xr@ rel-patch-one loop ;
