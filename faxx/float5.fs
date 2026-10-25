\ float5.fs -- flt{} / dbl{} / qad{} の中身の式 (axx.py の _XevalParser、caxx.c の xeval_*)
\
\ 値は ( q flag ): flag が 0 なら 256 ビット符号付きの整数、-1 なら倍精度 (q の先頭セル)。
\ 失敗は throw し、xeval が捕まえる。

decimal

variable xs-a  variable xs-u  variable xs-i
defer x-label ( a u -- q )
: xch ( off -- c ) xs-i @ + dup xs-u @ < if xs-a @ + c@ else drop 0 then ;
: xeof? ( -- f ) xs-i @ xs-u @ >= ;
: xe-skip ( -- ) begin 0 xch dup 32 = swap 9 = or while 1 xs-i +! repeat ;
: xpeek? ( a u -- f ) { a u }
  xs-i @ u + xs-u @ > if false exit then
  true u 0 ?do a i + c@ i xch <> if drop false leave then loop ;
: cin? ( c a u -- f ) 0 ?do 2dup i + c@ = if 2drop true unloop exit then loop 2drop false ;
: x-digit? ( c -- f ) dup 48 >= swap 57 <= and ;
: x-alpha? ( c -- f ) { c } c 97 >= c 122 <= and c 65 >= c 90 <= and or ;

: xflt ( F: r -- ) ( -- q true ) dq dup qd-fin? 0= if xfail then true ;
: xv>f ( q flag -- ) ( F: -- r ) if qd else qi>f then ;

\ ---- 範囲つきの整数演算 ----
: q+ovf ( a b -- r ovf ) { a b } a b q+ { r }
  a q-neg? b q-neg? = a q-neg? r q-neg? <> and { o } r o ;
: q-ovf ( a b -- r ovf ) { a b } a b q- { r }
  a q-neg? b q-neg? <> a q-neg? r q-neg? <> and { o } r o ;
: q*ovf ( a b -- r ovf ) { a b }
  a q-neg? b q-neg? xor { neg }
  ar-mark { mk }
  a q>bn b q>bn bn-mul { p }
  p bn-bitlen { bl }
  neg bl 256 = and p 255 bn-low? 0= and { exact-min }
  bl 255 > exact-min 0= and { ovf }
  p bn>q neg if qneg then { r }
  mk ar-release
  r ovf ;
: q-min? ( q -- f ) { a } a q-neg? a qneg a q= and ;

\ ---- 倍精度の演算 ----
: fdec ( F: x -- ) ( -- m e )                      \ |x| = m * 2^e (有限)
  fabs f-bits { bits }
  bits 52 rshift $7ff and { ex }  bits $fffffffffffff and { fr }
  ex 0= if fr -1074 else fr $10000000000000 or ex 1075 - then ;
: fmod-ex ( F: x y -- r )                          \ C の fmod (符号は x)。y != 0
  fdec { my ey }
  fdup f-signbit { sg }
  fdec { mx ex }
  mx 0= if 0e sg if fnegate then exit then
  ex ey >= if
    mx my mod { r }
    ex ey - 0 ?do r 2* my mod to r loop
    r ey ldexp-m
  else
    ey ex - { sh }
    my bitlen sh + 53 > if mx else mx my sh lshift mod then
    ex ldexp-m
  then
  sg if fnegate then ;
\ CPython の float_div_mod
: fdivmod ( F: x y -- mod floordiv ) { f: x f: y }  0e 0e 0e { f: md f: dv f: fd }
  x y fmod-ex to md
  x md f- y f/ to dv
  md f0= 0= if
    y f0< md f0< <> if md y f+ to md  dv 1e f- to dv then
  else
    0e y f-signbit if fnegate then to md
  then
  dv f0= 0= if
    dv floor to fd
    dv fd f- 0.5e f> if fd 1e f+ to fd then
  else
    0e x y f/ f-signbit if fnegate then to fd
  then
  md fd ;
: xdiv-int ( a b -- ) ( F: -- r ) { a b }                  \ 整数どうしの真の商 (正しく丸める)
  ar-mark { mk }
  a q-neg? b q-neg? xor { sg }
  rr-dbl a q>bn b q>bn 0 round-rat sg rr>dbl
  mk ar-release ;
: x-fpow2 ( F: x y -- ) ( -- q flag ) { f: x f: y }
  x f0= y f0< and if xfail then
  x f0< y y floor f= 0= and if xfail then
  x y f** xflt ;
: shn ( b -- n ) { b }
  b cell+ @ b 2 cells + @ or b 3 cells + @ or 0<> b @ 256 u> or if 257 else b @ then ;
: x-pow ( a af b bf -- q flag ) { a af b bf }
  af 0= bf 0= and b q-neg? 0= and { bi }
  bi 0= if a af xv>f b bf xv>f x-fpow2 exit then
  a q1 q= a q0 q= or a -1 qn q= or { small }
  small 0= b 256 qn q> and if a af xv>f b bf xv>f x-fpow2 exit then
  small if
    a q0 q= if b q-zero? if q1 else q0 then false exit then
    a q1 q= if q1 false exit then
    b @ 1 and if -1 qn else q1 then false exit
  then
  q1 false { r ov }
  b @ 0 ?do r a q*ovf ov or to ov to r ov if leave then loop
  ov if a af xv>f b bf xv>f x-fpow2 exit then
  r false ;
: x-neg ( q flag -- q' flag' ) { a af }
  af if a qd fnegate dq true exit then
  a q-min? if a qi>f fnegate xflt exit then
  a qneg false ;
: x-not ( q flag -- q' flag' ) if xfail then qnot false ;

\ 演算子の番号: 1 << 2 >> 3 & 4 | 5 ^ 6 / 7 // 8 % 9 + 10 - 11 *
: x-zero? ( q flag -- f ) if qd 0e f= else q-zero? then ;
: x-arith ( a af b bf op -- q flag ) { a af b bf op }
  af 0= bf 0= and { bi }
  bi if
    op 9 = if a b q+ovf else op 10 = if a b q-ovf else a b q*ovf then then
    0= if false exit then drop
  then
  a af xv>f b bf xv>f
  op 9 = if f+ else op 10 = if f- else f* then then xflt ;
: x-binop ( a af b bf op -- q flag ) { a af b bf op }
  af 0= bf 0= and { bi }
  op 5 <= if
    bi 0= if xfail then
    op 3 = if a b qand false exit then
    op 4 = if a b qor false exit then
    op 5 = if a b qxor false exit then
    b q-neg? if xfail then
    op 2 = if a b shn 256 min qsar false exit then
    a q-zero? if q0 false exit then
    b shn { n }
    n 256 > if xfail then
    a n qshl { r }
    r n qsar a q= 0= if xfail then
    r false exit
  then
  op 6 = if
    b bf x-zero? if xfail then
    bi if a b xdiv-int xflt exit then
    a af xv>f b bf xv>f f/ xflt exit
  then
  op 7 = op 8 = or if
    b bf x-zero? if xfail then
    bi if
      op 8 = if a b qmod false exit then
      a q-min? b -1 qn q= and 0= if a b qfloordiv false exit then
    then
    a af xv>f b bf xv>f fdivmod
    op 7 = if fswap then fdrop xflt exit
  then
  a af b bf op x-arith ;

\ ---- 数 ----
: x-digitpart ( sa su -- a u ) { sa su }                   \ digit (_? digit)*。無ければ 0 0
  xs-u @ xs-i @ - 1+ ar-alloc { buf }  0 { n }
  0 xch sa su cin? 0= if 0 0 exit then
  begin
    0 xch sa su cin? if
      0 xch buf n + c!  n 1+ to n  1 xs-i +!  true
    else
      0 xch 95 = 1 xch sa su cin? and if
        1 xch buf n + c!  n 1+ to n  2 xs-i +!  true
      else false then
    then
  0= until
  buf n ;
: x-exp-val ( a u neg -- n ) { a u neg }
  a u zcount { z }
  u z - 9 > if 10000000000 else 0 u z ?do 10 * a i + c@ 48 - + loop then
  neg if negate then ;
: dec-double ( ia iu fa fu ex -- ) ( F: -- r ) { ia iu fa fu ex }   \ float("ip.fpEex") の正しい丸め
  ar-mark { mk }
  iu fu + 1+ ar-alloc { dg }
  ia dg iu move  fa dg iu + fu move
  dg iu fu + zcount { lz }
  iu fu + lz - 0= if 0e mk ar-release exit then
  iu fu + lz - ex + fu - { e10 }
  e10 400 > if 0 f-inf mk ar-release exit then
  e10 -400 < if 0e mk ar-release exit then
  dg iu fu + bn-dec { nn }
  rr-dbl 0 nn ex fu - dec-ev drop 0 rr>dbl
  mk ar-release ;
: x-intval ( a u base -- q flag ) { da du base }
  ar-mark { mk }
  da du base bn-digits { b }
  b bn-bitlen 255 <= if b bn>q false mk ar-release exit then
  rr-dbl b 1 bn-u 0 round-rat 0 rr>dbl
  mk ar-release xflt ;
: x-radix ( c -- base ) 32 or dup 120 = if drop 16 exit then dup 111 = if drop 8 exit then 98 = if 2 else 0 then ;
: x-num-tail ( -- ) xeof? 0= if 0 xch dup x-alpha? over x-digit? or swap 95 = or if xfail then then ;
: x-dec-number ( -- q flag )
  s" 0123456789" x-digitpart { ia iu }
  false { isf }  0 0 { fa fu }  0 0 false { ea eu eneg }
  xeof? 0= if 0 xch 46 = else false then if
    1 xs-i +!
    s" 0123456789" x-digitpart to fu to fa
    iu 0= fu 0= and if xfail then
    true to isf
  then
  xeof? 0= if 0 xch dup 101 = swap 69 = or else false then if
    1 xs-i +!
    xeof? 0= if 0 xch dup 43 = swap 45 = or else false then if
      0 xch 45 = to eneg  1 xs-i +!
    then
    s" 0123456789" x-digitpart to eu to ea
    eu 0= if xfail then
    true to isf
  then
  isf if
    ia iu fa fu eu 0> if ea eu eneg x-exp-val else 0 then dec-double xflt
  else
    iu 0> if ia c@ 48 = ia iu zcount iu <> and else false then if xfail then
    ia iu 10 x-intval
  then ;
: xe-number ( -- q flag )
  0 xch 48 = if 1 xch x-radix else 0 then { base }
  base 0<> xs-i @ 1+ xs-u @ < and if
    2 xs-i +!
    0 xch 95 = if 1 xs-i +! then
    base 16 = if s" 0123456789abcdefABCDEF" else base 8 = if s" 01234567" else s" 01" then then
    x-digitpart dup 0= if xfail then
    base x-intval
  else
    x-dec-number
  then
  x-num-tail ;

\ ---- 項・演算 ----
defer x-expr ( -- q flag )
defer xe-unary ( -- q flag )
: x-func ( a u -- bits width ) 2dup s" enfloat" compare 0= if 2drop 32 exit then
  2dup s" enflt" compare 0= if 2drop 32 exit then
  2dup s" endouble" compare 0= if 2drop 64 exit then
  s" endbl" compare 0= if 64 exit then
  xfail ;
: x-call ( a u -- q flag ) { na nu }
  na nu x-func { w }
  1 xs-i +!  x-expr xe-skip s" )" xpeek? 0= if xfail then 1 xs-i +!
  { a af }
  af if a qd dq-trunc else a then @ { bits }
  w 32 = if bits $ffffffff and fb-buf l! fb-buf sf@ else bits bits>f then
  xflt ;
: xe-primary ( -- q flag )
  xe-skip xeof? if xfail then
  0 xch { c }
  c 40 = if 1 xs-i +! x-expr xe-skip s" )" xpeek? 0= if xfail then 1 xs-i +! exit then
  c 58 = if
    1 xs-i +! xs-i @ { st }
    begin xeof? 0= if 0 xch lwc? else false then while 1 xs-i +! repeat
    xs-i @ st = if xfail then
    xs-a @ st + xs-i @ st - x-label false exit
  then
  c x-alpha? c 95 = or if
    xs-i @ { st }
    begin xeof? 0= if 0 xch dup x-alpha? over x-digit? or swap 95 = or else false then while 1 xs-i +! repeat
    xs-a @ st + xs-i @ st - { na nu }
    xe-skip
    s" (" xpeek? 0= if xfail then
    na nu x-call exit
  then
  c x-digit? c 46 = or if xe-number exit then
  xfail ;
: x-power ( -- q flag ) xe-primary xe-skip s" **" xpeek? if 2 xs-i +! xe-unary x-pow then ;

: xe-unary1 ( -- q flag )
  xe-skip
  xeof? if x-power exit then
  0 xch { c }
  c 43 = if 1 xs-i +! recurse exit then
  c 45 = if 1 xs-i +! recurse x-neg exit then
  c 126 = if 1 xs-i +! recurse x-not exit then
  x-power ;
' xe-unary1 is xe-unary

\ 演算子の読み取り: 水準ごとに現在位置 (空白は読み飛ばし済み) の演算子の番号と長さ
: x-opcode ( lvl -- code len )
  case
    0 of
      s" //" xpeek? if 7 2 exit then
      s" /" xpeek? if 6 1 exit then
      s" %" xpeek? if 8 1 exit then
      s" *" xpeek? if s" **" xpeek? 0= if 11 1 exit then then
      0 0 endof
    1 of s" +" xpeek? if 9 1 exit then s" -" xpeek? if 10 1 exit then 0 0 endof
    2 of s" <<" xpeek? if 1 2 exit then s" >>" xpeek? if 2 2 exit then 0 0 endof
    3 of s" &" xpeek? if 3 1 exit then 0 0 endof
    4 of s" ^" xpeek? if 5 1 exit then 0 0 endof
    5 of s" |" xpeek? if 4 1 exit then 0 0 endof
    0 0 rot
  endcase ;
: x-level ( xt lvl -- q flag ) { sub lvl }
  sub execute
  begin
    xe-skip lvl x-opcode { code len }
    code 0<>
  while
    len xs-i +!  sub execute code x-binop
  repeat ;
: x-term ( -- q flag ) ['] xe-unary 0 x-level ;
: xe-add ( -- q flag ) ['] x-term 1 x-level ;
: xe-shift ( -- q flag ) ['] xe-add 2 x-level ;
: xe-band ( -- q flag ) ['] xe-shift 3 x-level ;
: xe-bxor ( -- q flag ) ['] xe-band 4 x-level ;
: xe-bor ( -- q flag ) ['] xe-bxor 5 x-level ;
' xe-bor is x-expr

: xeval ( a u -- q flag true | false )
  xs-u ! xs-a ! 0 xs-i !
  fdepth { fd0 }
  ['] xe-bor catch
  begin fdepth fd0 > while fdrop repeat
  if false exit then
  xe-skip xeof? 0= if 2drop false exit then
  true ;
