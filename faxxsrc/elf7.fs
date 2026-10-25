\ elf7.fs -- リロケーションの記録 (lineassemble の ELF ブロックの前半: 道具)

decimal

\ ---- 記録 ----
12 cells constant RLSZ
variable rl-base  variable rl-n  variable rl-cap
: rl-init ( -- ) 256 rl-cap !  rl-cap @ RLSZ * allocate throw rl-base !  0 rl-n ! ;
[undefined] cc-forth [if] rl-init [then]
: rl-reset ( -- ) 0 rl-n ! ;
: rl@ ( i -- addr ) RLSZ * rl-base @ + ;
\ 0=sec-a 1=sec-u 2=off 3=name-a 4=name-u 5=rtype 6..9=addend(q) 10=nbytes 11=fmask
: rel-add ( sa su off na nu rt addend nb fm -- ) { sa su off na nu rt ad nb fm }
  rl-n @ rl-cap @ >= if
    rl-cap @ 2* rl-cap !
    rl-base @ rl-cap @ RLSZ * resize throw rl-base !
  then
  rl-n @ rl@ { e }
  sa su intern e cell+ ! e !
  off e 2 cells + !
  na nu intern e 4 cells + ! e 3 cells + !
  rt e 5 cells + !
  ad e 6 cells + q!
  nb e 10 cells + !  fm e 11 cells + !
  1 rl-n +! ;
: rel-add-n ( sa su off na nu rt addend nb fm -- ) { sa su off na nu rt ad nb fm }
  sa su off na nu rt ad qn nb fm rel-add ;

\ ---- アンカー ----
variable an-n
create an-off 4096 cells allot
create an-sa 4096 cells allot  create an-su 4096 cells allot
create an-na 4096 cells allot  create an-nu 4096 cells allot
: an-reset ( -- ) 0 an-n ! ;
: anchor-at ( sa su off -- na nu ) { sa su off }
  an-n @ 0 ?do
    i cells an-off + @ off = if
      i cells an-sa + @ i cells an-su + @ sa su str=cs if
        i cells an-na + @ i cells an-nu + @ unloop exit
      then
    then
  loop
  an-n @ 4096 >= if s" .Lanchor" exit then
  mb-reset s" .Lanchor" mb+ an-n @ mb-n
  begin
    mb-get lab-find 0<> mb-get export-labels om-find 0<> or
  while 95 mb-c repeat
  mb-get intern { na nu }
  na an-n @ cells an-na + !  nu an-n @ cells an-nu + !
  sa su intern an-n @ cells an-su + ! an-n @ cells an-sa + !
  off an-n @ cells an-off + !
  1 an-n +!
  na nu ;

\ ---- 実表の問い合わせ ----
: reloc-data-pcrel ( nbytes -- rt|0 ) { nb }
  mach-table
  mt-named om-used 0 ?do
    i mt-named om-live? if
      i mt-named om-val @ { rt }
      rt mt-bytes@ 0 max nb = rt mt-pc? and if
        rt mt-field? if 2drop 2drop else rt unloop exit then
      then
    then
  loop 0 ;
: reloc-data-abs ( nbytes -- rt|0 ) { nb }
  mach-table
  mt-named om-used 0 ?do
    i mt-named om-live? if
      i mt-named om-val @ { rt }
      rt mt-bytes@ 0 max nb = rt mt-pc? 0= and if
        rt mt-field? if 2drop 2drop else rt unloop exit then
      then
    then
  loop
  nb mt-wg@ dup if dup mt-pc? if drop 0 then then ;
: reloc-same-width ( nbytes want-pcrel -- rt|0 ) { nb want }
  mach-table
  mt-named om-used 0 ?do
    i mt-named om-live? if
      i mt-named om-val @ { rt }
      rt mt-bytes@ 0 max nb = if
        rt mt-pc? 0<> want 0<> = if rt unloop exit then
      then
    then
  loop 0 ;

: elf-relaxing? ( -- f )
  d-relax @ 0>= if d-relax @ 0<> exit then
  d-diff om-count 0> d-diff-t om-count 0> or ;

\ ---- ビットの詰め込み (_field_deposit) ----
: field-deposit ( mask value -- out ) { mask v }
  0 { out }  0 { bit }  mask { m }
  begin m while
    m dup negate and { low }
    v bit qsar @ 1 and if out low or to out then
    bit 1+ to bit
    m low xor to m
  repeat
  out ;
: popcount ( u -- n ) 0 swap begin dup while dup 1 and rot + swap 1 rshift repeat drop ;

\ ---- 行の文脈 ----
variable e-bpw  variable e-bts  variable e-cw  variable e-epc  variable e-scale
variable e-sa  variable e-su
variable e-mask-q 4 cells allot
: e-mask ( -- q ) e-mask-q ;
variable e-nobj0
: mask-q ( bits -- q ) dup 0<= if drop q0 exit then dup 256 >= if drop q0 qnot exit then q1 swap qshl q1 q- ;

\ 欄のワード列を対象のバイト順で 1 つの整数にして符号を付ける (_field_raw)
: field-raw ( first nwords -- q ) { first nw }
  q0 { rv }
  nw 0 ?do
    first i + { wk }
    wk nobj @ < if
      wk obj-q e-mask qand
      endian-big @ 0= if i e-bts @ * else nw 1- i - e-bts @ * then qshl
      rv qor to rv
    then
  loop
  nw e-bts @ * { fb }
  fb 0> fb 256 < and if
    rv q1 fb 1- qshl q>= if rv q1 fb qshl q- to rv then
  then
  rv ;

: words-zero ( first n -- ) { first n }
  n 0 ?do first i + nobj @ < if q0 first i + obj-q q! then loop ;
\ 欄のマスクで該当ビットを消す: 型 mask をワードごとに切り分ける
: words-clear-mask ( first n mask -- ) { first n mask }
  n 0 ?do
    first i + nobj @ < if
      endian-big @ 0= if e-bts @ i * else e-bts @ n 1- i - * then { sh }
      mask sh 64 < if sh rshift else drop 0 then qun e-mask qand { clr }
      first i + obj-q clr qnot qand e-mask qand first i + obj-q q!
    then
  loop ;
