\ float2.fs -- 任意精度の自然数 (bn) と、2 進浮動小数への正しい丸め
\
\ bn は先頭に [個数][容量] の 2 セルを持ち、肢 (32 ビット) を下位から並べる。
\ 結果は領域 (arena) に取る。呼び出し側が ar-mark / ar-release で巻き戻す。
\ 繰り返しの中で局所変数を作ると積み上がるので、内側の繰り返しでは使わない。

decimal

$ffffffff constant M32

: bn-new ( cap -- a ) dup 2 + cells ar-alloc { cap a }
  a cap 2 + cells erase  cap a cell+ !  a ;
: bn-lp ( a i -- addr ) 2 + cells + ;
: bn@ ( a i -- u ) over @ over u> if bn-lp @ else 2drop 0 then ;
: bn-or! ( u addr -- ) dup @ rot or swap ! ;
: bn-trim ( a -- ) { a }
  begin a @ 0> if a a @ 1- bn-lp @ 0= else false then while -1 a +! repeat ;
: bn-zero? ( a -- f ) @ 0= ;
: bn-u ( u -- a ) 2 bn-new { u a }
  u M32 and a 0 bn-lp !  u 32 rshift a 1 bn-lp !  2 a !  a bn-trim a ;
: bn-copy ( a cap -- b ) { a cap } a @ cap max bn-new { r }
  a @ r !  a 2 cells + r 2 cells + a @ cells move  r ;
: bn-bitlen ( a -- n ) { a }
  a @ 0= if 0 exit then
  a @ 1- 32 *  a a @ 1- bn-lp @ bitlen + ;
: bn-bit ( a i -- b ) { a i } a i 32 / bn@ i 32 mod rshift 1 and ;
: bn-low? ( a nbits -- f ) { a nb }                \ 下位 nb ビットに 1 があるか
  nb 32 / { wn }  nb 32 mod { rb }
  wn 0 ?do a i bn@ 0<> if true unloop exit then loop
  rb 0> if a wn bn@  1 rb lshift 1- and 0<> else false then ;
: bn-shl ( a k -- b ) { a k }
  a @ 0= if 1 bn-new exit then
  k 32 / { ls }  k 32 mod { bs }
  a @ ls + 1+ bn-new { r }
  a @ 0 ?do
    a i bn@ bs lshift
    dup M32 and r i ls + bn-lp bn-or!
    32 rshift r i ls + 1+ bn-lp bn-or!
  loop
  a @ ls + 1+ r !  r bn-trim  r ;
: bn-shr ( a k -- b ) { a k }
  k 32 / { ls }  k 32 mod { bs }
  ls a @ >= if 1 bn-new exit then
  a @ ls - { m }
  m 1+ bn-new { r }
  m 0 ?do
    a i ls + bn@ bs rshift
    a i ls + 1+ bn@ 32 bs - lshift M32 and or
    r i bn-lp !
  loop
  m r !  r bn-trim  r ;
: bn-cmp ( a b -- -1|0|1 ) { a b }
  a @ b @ <> if a @ b @ u< if -1 else 1 then exit then
  a @ begin dup 0> while
    1-
    a over bn@ b 2 pick bn@ 2dup <> if u< if drop -1 else drop 1 then exit then
    2drop
  repeat drop 0 ;
: bn-add ( a b -- c ) { a b }
  a @ b @ max { n }
  n 1+ bn-new { r }
  0 n 0 ?do
    a i bn@ + b i bn@ +
    dup M32 and r i bn-lp !  32 rshift
  loop
  r n bn-lp !
  n 1+ r !  r bn-trim  r ;
: bn-sub! ( a b -- ) { a b }                       \ a -= b (a >= b)
  0 a @ 0 ?do
    a i bn@ b i bn@ - swap -
    dup M32 and a i bn-lp !  63 rshift
  loop drop
  a bn-trim ;
: bn-sub ( a b -- c ) { a b } a a @ bn-copy { c } c b bn-sub! c ;
: mul-row ( r a b ri -- ) { r a b ri } a ri bn@ { x }
  0 b @ 0 ?do
    r ri i + bn-lp @ +  x b i bn@ * +
    dup M32 and r ri i + bn-lp !  32 rshift
  loop
  r ri b @ + bn-lp ! ;
: bn-mul ( a b -- c ) { a b }
  a @ 0= b @ 0= or if 1 bn-new exit then
  a @ b @ + bn-new { r }
  a @ 0 ?do r a b i mul-row loop
  a @ b @ + r !  r bn-trim  r ;
: bn-mul1+ ( a m c -- ) { a m c }                  \ a = a*m + c (m c < 2^32、容量は呼び側が確保)
  c a @ 0 ?do
    a i bn-lp @ m * +
    dup M32 and a i bn-lp !  32 rshift
  loop
  dup 0<> if
    a @ a cell+ @ >= abort" bn overflow"
    a a @ bn-lp !  1 a +!
  else drop then ;
: bn-pow10 ( e -- a ) { e }
  e 9 / 2 + bn-new { r }  1 r 0 bn-lp !  1 r !
  e 9 / 0 ?do r 1000000000 0 bn-mul1+ loop
  1 e 9 mod 0 ?do 10 * loop { rest }
  rest 1 > if r rest 0 bn-mul1+ then
  r ;
: dch ( c -- v ) dup 97 >= if 87 - exit then dup 65 >= if 55 - exit then 48 - ;
: bn-digits ( a u base -- bn ) { da du base }       \ 基数 base の数字列から
  du 4 * 32 / 3 + bn-new { r }
  du 0 ?do r base da i + c@ dch bn-mul1+ loop r ;
: dec-chunk ( a n -- v ) 0 swap 0 ?do over i + c@ 48 - swap 10 * + loop nip ;
: bn-dec ( a u -- bn ) { da du }                    \ 10 進の数字列から (9 桁ずつ)
  du 9 / 3 + bn-new { r }
  du 9 / 0 ?do r 1000000000 da i 9 * + 9 dec-chunk bn-mul1+ loop
  du 9 mod { rm }
  rm 0> if r  1 rm 0 ?do 10 * loop  da du rm - + rm dec-chunk  bn-mul1+ then
  r ;
\ 256 ビットの q との行き来 (q は符号付き。bn は大きさ)
: q>bn ( q -- bn ) qabs { a } 9 bn-new { r }
  4 0 ?do
    a i qw dup M32 and r i 2 * bn-lp !  32 rshift r i 2 * 1+ bn-lp !
  loop
  8 r ! r bn-trim r ;
: bn>q ( bn -- q ) { a } q0 { r }                   \ 256 ビットを越える分は捨てる
  4 0 ?do a i 2 * bn@ a i 2 * 1+ bn@ 32 lshift or r i cells + ! loop r ;

\ ---- 正しい丸め: 正の有理数 N/D * 2^x2 を 精度 P 桁の 2 進浮動小数 m * 2^qe にする ----
variable rr-p  variable rr-qmin  variable rr-emax    \ 精度 / 量子の最小の指数 / 溢れの指数
variable rr-m  variable rr-qe  variable rr-inf
: rr-quad ( -- ) 113 rr-p !  -16494 rr-qmin !  16384 rr-emax ! ;
: rr-dbl ( -- ) 53 rr-p !  -1074 rr-qmin !  1024 rr-emax ! ;

: bn-divq ( n d -- q sticky ) { nn dd }              \ n/d < 2^119 のとき。商と余りの有無
  nn nn @ 1+ bn-copy { r }
  5 bn-new { qq }
  119 0 do
    r dd 118 i - bn-shl bn-cmp 0< 0= if
      r dd 118 i - bn-shl bn-sub!
      qq 118 i - 32 / 2 + cells + dup @ 1 118 i - 32 mod lshift or swap !
    then
  loop
  5 qq !  qq bn-trim
  qq r bn-zero? 0= ;

: round-rat ( N D x2 -- ) { nn dd x2 }
  false rr-inf !
  nn bn-zero? if 1 bn-new rr-m !  0 rr-qe ! exit then
  nn bn-bitlen dd bn-bitlen - { diff }
  117 diff - { k }
  k 0>= if nn k bn-shl dd else nn dd k negate bn-shl then bn-divq { q st }
  q bn-bitlen { ql }
  ql 1- x2 + k - { ee }
  ee rr-p @ 1- - rr-qmin @ max { qe }
  qe x2 k - - { r }
  q r bn-shr { m }
  q r 1- bn-bit { h }
  q r 1- bn-low? st or { rest }
  h if rest m 0 bn-bit 0<> or if m 1 bn-u bn-add to m then then
  m bn-bitlen rr-p @ > if m 1 bn-shr to m  qe 1+ to qe then
  m bn-bitlen qe + rr-emax @ > if true rr-inf ! then
  m rr-m !  qe rr-qe ! ;
