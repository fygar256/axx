\ u256.fs -- 256 ビット整数 (2 の補数)。caxx.c の uint256_t と同じ規則。
\
\ 値は 4 セル (w0 が最下位) の領域へのアドレスで持ち回る。演算は新しい領域を
\ 一時領域の輪から取って結果を返すので、結果は次の 65536 回の演算のあいだだけ
\ 有効。表へしまうときは q! で写す。語の前置きは q (quad)。

decimal

4 cells constant QB
65536 constant NTMP
create tmp-pool NTMP QB * allot
variable tmp-i
: tmp ( -- a ) tmp-i @ 1+ NTMP 1- and dup tmp-i ! QB * tmp-pool + ;

: qw ( a i -- w ) cells + @ ;
: q0 ( -- a ) tmp dup QB erase ;
: qcopy ( a -- b ) tmp tuck QB move ;
: q! ( a dst -- ) QB move ;
: qn ( n -- a )                                  \ 符号付き 64bit から (符号拡張)
  tmp { r }  dup r !  0< if -1 else 0 then
  dup r cell+ !  dup r 2 cells + !  r 3 cells + !  r ;
: qun ( u -- a ) q0 tuck ! ;                       \ 符号なし 64bit から
: q1 ( -- a ) 1 qn ;
: q-neg? ( a -- f ) 3 cells + @ 0< ;
: q-zero? ( a -- f ) dup @ over cell+ @ or over 2 cells + @ or swap 3 cells + @ or 0= ;
: q= ( a b -- f ) { a b }
  a @ b @ =  a cell+ @ b cell+ @ = and
  a 2 cells + @ b 2 cells + @ = and  a 3 cells + @ b 3 cells + @ = and ;
: q< ( a b -- f ) { a b }                           \ 符号付き
  a q-neg? b q-neg? <> if a q-neg? exit then
  0 3 do
    a i qw b i qw 2dup <> if u< unloop exit then 2drop
  -1 +loop
  false ;
: q> ( a b -- f ) swap q< ;
: q<= ( a b -- f ) q> 0= ;
: q>= ( a b -- f ) q< 0= ;

: qnot ( a -- r ) { a } tmp { r }  4 0 do a i qw invert r i cells + ! loop r ;
: qand ( a b -- r ) { a b } tmp { r }  4 0 do a i qw b i qw and r i cells + ! loop r ;
: qor ( a b -- r ) { a b } tmp { r }  4 0 do a i qw b i qw or r i cells + ! loop r ;
: qxor ( a b -- r ) { a b } tmp { r }  4 0 do a i qw b i qw xor r i cells + ! loop r ;

: adc ( x y c -- s c' ) { x y c }
  x y + { s1 }
  s1 x u< 1 and { c1 }
  s1 c + { s2 }
  s2 s1 u< 1 and { c2 }
  s2 c1 c2 or ;
: q+ ( a b -- r ) { a b } tmp { r } 0 { c }
  4 0 do a i qw b i qw c adc to c r i cells + ! loop r ;
: qneg ( a -- r ) qnot q1 q+ ;
: q- ( a b -- r ) qneg q+ ;
: q* ( a b -- r ) { a b } q0 { r }
  4 0 do
    0 { c }
    4 i - 0 do
      a j qw b i qw um*
      r i j + cells + @ 0 d+  c 0 d+
      to c  r i j + cells + !
    loop
  loop r ;
: q*small+ ( x m d -- r ovf ) { x m d } tmp { r } d { c }
  4 0 do x i qw m um* c 0 d+ to c r i cells + ! loop
  r c 0<> ;

: qshl ( a n -- r ) { a n }
  n 0<= if a exit then
  n 256 >= if q0 exit then
  q0 { r }  n 64 / { ws }  n 64 mod { bs }
  4 0 do
    i ws + { d }
    d 4 < if
      a i qw bs lshift  r d cells + dup @ rot or swap !
      bs 0<> d 1+ 4 < and if
        a i qw 64 bs - rshift  r d 1+ cells + dup @ rot or swap !
      then
    then
  loop r ;
: q-fill ( a -- f ) q-neg? if -1 else 0 then ;
: qsar ( a n -- r ) { a n }
  n 0<= if a exit then
  a q-fill { fill }
  n 256 >= if fill qn exit then
  tmp { r }  n 64 / { ws }  n 64 mod { bs }
  0 3 do
    i ws + { src }
    src 4 < if a src qw else fill then { hi }
    src 1+ 4 < if a src 1+ qw else fill then { lo }
    bs 0<> if hi bs rshift lo 64 bs - lshift or else hi then
    r i cells + !
  -1 +loop
  r ;

\ 符号なし除算 (ビットごと)
: q-uge? ( a b -- f ) { a b }
  0 3 do a i qw b i qw 2dup <> if u> unloop exit then 2drop -1 +loop
  true ;
: qudiv ( a b -- q ) { a b }
  b q-zero? if q0 exit then
  q0 { q }  q0 { r }
  0 255 do
    r 1 qshl to r
    a i 64 / qw i 64 mod rshift 1 and  r @ or  r !
    r b q-uge? if
      r b q- to r
      1 i 64 mod lshift  q i 64 / cells + dup @ rot or swap !
    then
  -1 +loop
  q ;
: qdiv-prep ( a b -- ua ub sa sb ) { a b }
  a q-neg? { sa }  b q-neg? { sb }
  sa if a qneg else a then  sb if b qneg else b then  sa sb ;
: qdiv0 ( -- ) s" Division by zero" stderr write-file drop s\" \n" stderr write-file drop ;
: qfloordiv ( a b -- q ) { a b }
  b q-zero? if qdiv0 q0 exit then
  a b qdiv-prep { ua ub sa sb }
  ua ub qudiv { q }
  ua q ub q* q- { rem }
  sa sb <> if
    q qneg to q
    rem q-zero? 0= if q q1 q- to q then
  then
  q ;
: qtruncdiv ( a b -- q ) { a b }
  b q-zero? if qdiv0 q0 exit then
  a b qdiv-prep { ua ub sa sb }
  ua ub qudiv { q }
  sa sb <> if q qneg else q then ;
: qmod ( a b -- r ) { a b }
  b q-zero? if qdiv0 q0 exit then
  a b qfloordiv b q* a swap q- ;
: qpow ( base exp -- r ) { base ex }
  q1 { r }
  4 0 do
    ex i qw { word }
    word 0= if
      true  4 i 1+ ?do ex i qw if drop false then loop
      if r unloop exit then
    then
    64 0 do
      word 1 i lshift and if r base q* to r then
      j 3 = i 63 = and 0= if base base q* to base then
    loop
  loop r ;

: q>n ( a -- n ) @ ;
: q-nonneg-gt? ( a max -- f ) { a max }               \ 非負の a が max を超えるか
  a cell+ @ a 2 cells + @ or a 3 cells + @ or if true exit then
  a @ max u> ;
: bitlen ( u -- n ) 0 swap begin dup while 1 rshift swap 1+ swap repeat drop ;
: qnbit ( a -- n ) { a }
  a q-neg? if
    a qneg to a
    a q-neg? if 256 exit then
  then
  0 3 do
    a i qw ?dup if bitlen i 64 * + unloop exit then
  -1 +loop
  0 ;

128 constant SEXT-MAX
: qsext ( x bits -- r warn ) { x bits }
  bits q-neg? bits q-zero? or if q0 false exit then
  bits SEXT-MAX q-nonneg-gt? if q0 true exit then
  bits q>n { tv }
  q0 qnot tv qshl qnot { mask }
  x mask qand to x
  x tv 1- qsar q1 qand q-zero? 0= if
    x  q0 qnot tv qshl  qor to x
  then
  x false ;
: qbyte ( x index -- r neg ) { x ix }
  ix q-neg? if q0 true exit then
  ix 32 q-nonneg-gt? if 256 else ix q>n 8 * then { sh }
  x sh qsar false ;

\ 未定義の番兵 (2**255 - 1) と、それに由来する値
: qundef ( -- a ) q0 qnot { r } r 3 cells + dup @ 1 rshift swap ! r ;
: qundef? ( a -- f ) qundef q= ;
: qabs ( a -- r ) dup q-neg? if qneg then ;
: qundef-derived? ( a -- f )
  dup qundef? if drop true exit then
  qabs 3 cells + @ 0<> ;

\ ---- 10 進・16 進の文字列 ----
: qdivsmall ( a n -- q rem ) { a n } tmp { q } 0 { rem }
  0 3 do
    a i qw rem n um/mod  q i cells + !  to rem
  -1 +loop
  q rem ;
create qdbuf 160 allot
: q>dec ( a -- c-addr u ) { a }
  a q-neg? { neg }  neg if a qneg else a then { m }  160 { p }
  begin m q-zero? 0= while
    m 10 qdivsmall { rm } to m
    p 1- to p  rm 48 + qdbuf p + c!
  repeat
  p 160 = if p 1- to p 48 qdbuf p + c! then
  neg if p 1- to p 45 qdbuf p + c! then
  qdbuf p + 160 p - ;
: hexch ( n -- c ) dup 10 < if 48 + else 55 + then ;
: q>hex ( a upper? -- c-addr u ) { a up }              \ 符号つきの 16 進 (0x なし)
  a q-neg? { neg }  neg if a qneg to a then
  0 { n }  neg if 45 qdbuf c! 1 to n then
  0 { st }  n { n0 }
  0 63 do
    a i 16 / qw  i 16 mod 4 * rshift 15 and { nb }
    nb 0<> st or if
      true to st
      nb hexch up 0= if dup 65 >= if 32 + then then
      qdbuf n + c!  n 1+ to n
    then
  -1 +loop
  n n0 = if 48 qdbuf n + c! n 1+ to n then
  qdbuf n ;

: qshr ( a n -- r ) { a n }                        \ 論理右シフト
  n 0<= if a exit then
  n 256 >= if q0 exit then
  tmp { r }  n 64 / { ws }  n 64 mod { bs }
  4 0 do
    i ws + { src }
    src 4 < if a src qw else 0 then { lo }
    src 1+ 4 < if a src 1+ qw else 0 then { hi }
    bs 0<> if lo bs rshift hi 64 bs - lshift or else lo then
    r i cells + !
  loop r ;
