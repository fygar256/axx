\ float4.fs -- 倍精度の補助 (2 のべき・正しい丸め・%.17g)

decimal

create fb-buf 16 allot
: f2^ ( n -- ) ( F: -- r )                       \ -1022 <= n <= 1023
  1023 + 52 lshift fb-buf ! fb-buf f@ ;
: ldexp-m ( m qe -- ) ( F: -- r )                 \ m * 2^qe (m は 53 ビット以下)
  { m qe }
  m u>f
  qe -1022 < if -1022 f2^ f*  qe 1022 + f2^ f* else qe f2^ f* then ;
: f-signbit ( F: x -- ) ( -- f ) fb-buf f! fb-buf @ 63 rshift 0<> ;
: f-bits ( F: x -- ) ( -- u ) fb-buf f! fb-buf @ ;
: bits>f ( u -- ) ( F: -- r ) fb-buf ! fb-buf f@ ;
: f-inf ( sign -- ) ( F: -- r ) if $fff0000000000000 else $7ff0000000000000 then bits>f ;
: bn>u ( bn -- u ) dup 0 bn@ swap 1 bn@ 32 lshift or ;
: rr>dbl ( sign -- ) ( F: -- r )                   \ rr-m rr-qe から
  { sign }
  rr-inf @ if sign f-inf exit then
  rr-m @ bn>u rr-qe @ ldexp-m
  sign if fnegate then ;
: dbl-fin? ( F: x -- ) ( -- f ) f-bits 52 rshift $7ff and $7ff <> ;

\ ---- 10 進への変換 (正しい丸め) ----
\ n / d の整数部と、端数が半分以上かどうか
: ddig-calc ( n d -- floor h rest ) { nn dd }
  117 nn bn-bitlen dd bn-bitlen - - { k }
  k 2 < abort" ddig k"
  nn k bn-shl dd bn-divq { q st }
  q k bn-shr bn>u
  q k 1- bn-bit
  q k 1- bn-low? st or ;
create g17-dig 24 allot
variable g17-e10
variable g17-neg
10000000000000000 constant D16
100000000000000000 constant D17
: dig-try ( m e d10 -- floor h rest ) { m e d10 }
  d10 16 - { s }
  m bn-u e 0 max bn-shl s negate 0 max bn-pow10 bn-mul { nn }
  1 bn-u e negate 0 max bn-shl s 0 max bn-pow10 bn-mul { dd }
  nn dd ddig-calc ;
: dig-put ( fl -- ) 17 0 do dup 10 mod 48 + g17-dig 16 i - + c! 10 / loop drop ;
: g17-digits ( bits -- flag ) { bits }               \ 有限の非零の 17 桁を g17-dig へ。0 のときは false
  bits 63 rshift g17-neg !
  bits 52 rshift $7ff and { ex }
  bits $fffffffffffff and { fr }
  ex 0= if fr else fr $10000000000000 or then { m }
  ex 0= if -1074 else ex 1075 - then { e }
  m 0= if false exit then
  ar-mark { mk }
  m bitlen e + 1- 30103 * s>d 100000 fm/mod nip { d10 }
  begin
    m e d10 dig-try { fl h rest }
    fl D16 u< if d10 1- to d10 false else
    fl D17 u< 0= if d10 1+ to d10 false else
      h if rest fl 1 and 0<> or if fl 1+ to fl then then
      fl D17 = if D16 to fl d10 1+ to d10 then
      fl dig-put  d10 g17-e10 !  true
    then then
  until
  mk ar-release  true ;

create go-buf 80 allot  variable go-u
: go-reset ( -- ) 0 go-u ! ;
: go-c ( c -- ) go-buf go-u @ + c! 1 go-u +! ;
: go+ ( a u -- ) 0 ?do dup i + c@ go-c loop drop ;
: go-n ( n -- ) s>d <# #s #> go+ ;
: g17-text ( bits -- a u ) { bits }                 \ printf("%.17g") と同じ綴り
  go-reset
  bits 52 rshift $7ff and { ex }
  bits $fffffffffffff and { fr }
  bits 63 rshift 0<> { neg }
  neg if 45 go-c then
  ex $7ff = if fr 0= if s" inf" else s" nan" then go+ go-buf go-u @ exit then
  bits g17-digits 0= if 48 go-c go-buf go-u @ exit then
  17 { nd }
  begin nd 1 > if g17-dig nd 1- + c@ 48 = else false then while nd 1- to nd repeat
  g17-e10 @ { x }
  x -4 < x 17 >= or if
    g17-dig c@ go-c
    nd 1 > if 46 go-c g17-dig 1+ nd 1- go+ then
    101 go-c  x 0< if 45 go-c else 43 go-c then
    x abs dup 10 < if 48 go-c then go-n
  else x 0>= if
    x 1+ 0 ?do i nd < if g17-dig i + c@ else 48 then go-c loop
    nd x 1+ > if 46 go-c g17-dig x 1+ + nd x 1+ - go+ then
  else
    s" 0." go+  x negate 1- 0 ?do 48 go-c loop  g17-dig nd go+
  then then
  go-buf go-u @ ;
