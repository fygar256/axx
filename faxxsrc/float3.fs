\ float3.fs -- 4 倍精度 (binary128) の式の評価 (axx.py の _F128Eval、caxx.c の f128_eval_text)
\
\ 値は [種類][符号][m][qe] の 4 セル。種類 0 有限 / 1 無限大 / 2 非数。
\ 有限の値は m * 2^qe (m = 0 は符号つきのゼロ)。演算のたびに 4 倍精度へ丸める。

decimal

variable ft-a  variable ft-u  variable ft-i
: ftch ( off -- c ) ft-i @ + dup ft-u @ < if ft-a @ + c@ else drop 0 then ;
: ftabs ( i -- c ) dup ft-u @ < if ft-a @ + c@ else drop 0 then ;
: xfail ( -- ) -4711 throw ;
: ft-skip ( -- ) begin 0 ftch dup 32 = swap 9 = or while 1 ft-i +! repeat ;
: fdig? ( c -- f ) dup 48 >= swap 57 <= and ;

: ev-new ( kind sign m qe -- ev ) 4 cells ar-alloc { kind sign m qe ev }
  kind ev !  sign ev cell+ !  m ev 2 cells + !  qe ev 3 cells + !  ev ;
: ev-kind ( ev -- k ) @ ;
: ev-sign ( ev -- s ) cell+ @ ;
: ev-m ( ev -- m ) 2 cells + @ ;
: ev-qe ( ev -- q ) 3 cells + @ ;
: ev-zero? ( ev -- f ) dup ev-kind 0= swap ev-m bn-zero? and ;
: ev-from-rr ( sign -- ev ) rr-inf @ if 1 swap 1 bn-new 0 ev-new
  else 0 swap rr-m @ rr-qe @ ev-new then ;
: ev-rat ( sign N D x2 -- ev ) { sign nn dd x2 } nn dd x2 round-rat sign ev-from-rr ;
: ev-zero ( sign -- ev ) 0 swap 1 bn-new 0 ev-new ;
: ev-inf ( sign -- ev ) 1 swap 1 bn-new 0 ev-new ;
: ev-nan ( -- ev ) 2 0 1 bn-new 0 ev-new ;
: ev-neg ( ev -- ev' ) { ev } ev ev-kind 2 = if ev exit then
  ev ev-kind ev ev-sign 0= ev ev-m ev ev-qe ev-new ;

\ 特別な値 (inf / nan) との演算
: ev-special ( a b op -- ev ) { a b op }
  a ev-kind 2 = b ev-kind 2 = or if ev-nan exit then
  op [char] - = if b ev-neg to b then
  op [char] + = op [char] - = or if
    a ev-kind 1 = b ev-kind 1 = and if
      a ev-sign b ev-sign = if a ev-sign ev-inf else ev-nan then exit
    then
    a ev-kind 1 = if a else b then exit
  then
  a ev-sign b ev-sign xor { sg }
  op [char] * = if
    a ev-kind 0= a ev-zero? and b ev-kind 0= b ev-zero? and or if ev-nan exit then
    sg ev-inf exit
  then
  a ev-kind 1 = b ev-kind 1 = and if ev-nan exit then
  a ev-kind 1 = if sg ev-inf else sg ev-zero then ;

: ev-addsub ( a b op -- ev ) { a b op }
  a ev-kind 0<> b ev-kind 0<> or if a b op ev-special exit then
  b ev-sign op [char] - = if 0= then { sb }          \ 引く側は符号を反転
  a ev-sign { sa }
  a ev-zero? b ev-zero? and if sa sb and ev-zero exit then
  a ev-zero? if 0 sb b ev-m b ev-qe ev-new exit then
  b ev-zero? if 0 sa a ev-m a ev-qe ev-new exit then
  a ev-qe b ev-qe min { qm }
  a ev-m a ev-qe qm - bn-shl { x }
  b ev-m b ev-qe qm - bn-shl { y }
  sa sb = if sa x y bn-add 1 bn-u qm ev-rat exit then
  x y bn-cmp dup 0= if drop 0 ev-zero exit then
  0> if sa x y bn-sub 1 bn-u qm ev-rat else sb y x bn-sub 1 bn-u qm ev-rat then ;

: ev-muldiv ( a b op -- ev ) { a b op }
  a ev-kind 0<> b ev-kind 0<> or if a b op ev-special exit then
  a ev-sign b ev-sign xor { sg }
  a ev-zero? if sg ev-zero exit then
  op [char] * = if
    b ev-zero? if sg ev-zero exit then
    sg a ev-m b ev-m bn-mul 1 bn-u a ev-qe b ev-qe + ev-rat exit
  then
  sg a ev-m b ev-m a ev-qe b ev-qe - ev-rat ;

\ ---- 数 ----
: dec-ev ( sign nn p -- ev ) { sign nn p }
  p 0>= if sign nn p bn-pow10 bn-mul 1 bn-u 0 ev-rat
  else sign nn p negate bn-pow10 0 ev-rat then ;
: dcount ( a u -- n ) { a u } 0 { n }
  begin n u < if a n + c@ fdig? else false then while n 1+ to n repeat n ;
: zcount ( a u -- n ) { a u } 0 { n }
  begin n u < if a n + c@ 48 = else false then while n 1+ to n repeat n ;
: ft-exp ( ba bu me -- ex ) { ba bu me } 0 0 { ep neg }
  me bu >= if 0 exit then
  ba me + c@ dup 101 <> swap 69 <> and if 0 exit then
  me 1+ to ep
  ep bu < if
    ba ep + c@ dup 43 = over 45 = or if 45 = to neg ep 1+ to ep else drop then
  then
  ba ep + bu ep - dcount { nd }
  nd 0= if 0 exit then
  ba ep + nd zcount { z }
  nd z - 9 > if 10000000000 else
    0 nd z ?do 10 * ba ep + i + c@ 48 - + loop
  then
  neg if negate then ;
: ft-e10 ( ba ipn fpa fpn -- e10 ) { ba ipn fpa fpn }
  ba ipn zcount { lz }
  ipn lz - dup 0> if exit then drop
  fpa fpn zcount negate ;
: ftnum ( -- ev )
  ft-i @ { st }
  begin 0 ftch dup fdig? swap 46 = or while 1 ft-i +! repeat
  0 ftch dup 101 = swap 69 = or if
    1 ft-i +!
    0 ftch dup 43 = swap 45 = or if 1 ft-i +! then
    begin 0 ftch fdig? while 1 ft-i +! repeat
  then
  ft-a @ st + { ba }  ft-i @ st - { bu }
  ba bu dcount { ipn }
  ipn bu < if ba ipn + c@ 46 = else false then { dot }
  ba ipn + dot 1 and + { fpa }
  fpa ba bu + fpa - dcount { fpn }
  fpa fpn + ba - { me }
  ipn fpn + 0= if 0 ev-zero exit then
  ba ipn zcount ipn = fpa fpn zcount fpn = and if 0 ev-zero exit then
  ba bu me ft-exp { ex }
  ba ipn fpa fpn ft-e10 { e10 }
  e10 ex + 4940 > if 0 ev-inf exit then
  e10 ex + -4970 < if 0 ev-zero exit then
  ipn fpn + 1+ ar-alloc { dg }
  ba dg ipn move  fpa dg ipn + fpn move
  dg ipn fpn + bn-dec { nn }
  ex fpn - { p }
  0 nn p dec-ev ;

defer ft-expr
: ft-factor ( -- ev )
  ft-skip
  0 ftch dup 40 = if
    drop 1 ft-i +! ft-expr ft-skip 0 ftch 41 = if 1 ft-i +! then exit
  then
  dup 45 = if drop 1 ft-i +! recurse ev-neg exit then
  dup 43 = if drop 1 ft-i +! recurse exit then
  dup fdig? over 46 = or if drop ftnum exit then
  drop xfail ;
: ft-step ( r c -- r' ) { r c } 1 ft-i +! ft-factor { r2 }
  c 47 = if r2 ev-zero? if xfail then then
  r r2 c ev-muldiv ;
: ft-term ( -- ev ) ft-factor
  begin ft-skip 0 ftch dup 42 = over 47 = or while ft-step repeat drop ;
: ft-estep ( r c -- r' ) { r c } 1 ft-i +! ft-term { r2 } r r2 c ev-addsub ;
: ft-expr1 ( -- ev ) ft-skip ft-term
  begin ft-skip 0 ftch dup 43 = over 45 = or while ft-estep repeat drop ;
bind ft-expr1 ft-expr

: f128-eval ( a u -- ev true | false )
  ft-u ! ft-a ! 0 ft-i !
  ['] ft-expr1 catch if false exit then
  ft-skip 0 ftch 0<> if drop false exit then
  dup ev-kind 0<> if drop false exit then
  true ;

: ev>q ( ev -- q ) { ev } q0 { r }
  ev ev-sign 63 lshift { sgb }
  ev ev-m bn-zero? if sgb r cell+ ! r exit then
  ev ev-m { m }
  m bn-bitlen 1- ev ev-qe + { ee }
  ee -16382 < { sub? }
  sub? if ev ev-qe 16494 + else ev ev-qe ee 112 - - then { d }
  d 0>= if m d bn-shl else m d negate bn-shr then { fr }
  sub? if 0 else ee 16383 + then { ef }
  fr 0 bn@ fr 1 bn@ 32 lshift or r !
  fr 2 bn@ fr 3 bn@ $ffff and 32 lshift or  ef 48 lshift or  sgb or r cell+ ! r ;
