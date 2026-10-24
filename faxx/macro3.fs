\ macro3.fs -- マクロ層: 組み込み関数、呼び出し、実行、補間、展開

decimal

\ ---- 組み込み関数 ----
variable bi-fa variable bi-fu variable bi-ln
: bi-err-head ( -- ) bi-fa @ bi-fu @ bi-ln @ mfail-pos ;
: bi-check ( n lo hi na nu -- ) { n lo hi na nu }
  n lo < n hi > or if
    bi-err-head na nu mb+ s" () takes " mb+ lo mb-n s" .." mb+ hi mb-n s"  argument(s), got " mb+ n mb-n mb+ mfail
  then ;
: arg@ ( args i -- v ) cells + @ ;

\ Python の int(s, base): ASCII のみ。ok: 0 成功 1 数でない 2 桁あふれ
: py-int ( a u base -- n rc ) { a u base }
  base 0<> if base 2 < base 36 > or if 0 1 exit then then
  u 0 ?do a i + c@ 128 >= if 0 1 unloop exit then loop
  begin u 0> if a c@ dup 32 = over 9 = or over 10 = or over 13 = or over 11 = or swap 12 = or else false then while a 1+ to a u 1- to u repeat
  begin u 0> if a u + 1- c@ dup 32 = over 9 = or over 10 = or over 13 = or over 11 = or swap 12 = or else false then while u 1- to u repeat
  false { neg }
  u 0> if a c@ 45 = if true to neg a 1+ to a u 1- to u else a c@ 43 = if a 1+ to a u 1- to u then then then
  base { b } false { prefixed }
  u 1 > if a c@ 48 = if
    a 1+ c@ lc { c }
    c 120 = b 0= b 16 = or and c 111 = b 0= b 8 = or and or c 98 = b 0= b 2 = or and or if
      c 120 = if 16 else c 111 = if 8 else 2 then then to b
      a 2 + to a u 2 - to u true to prefixed
    then
  then then
  false { zonly }
  b 0= if 10 to b a c@ 48 = u 0> and to zonly then
  0 0 false false { acc nd lastus ov }
  neg if $8000000000000000 else $7fffffffffffffff then { lim }
  prefixed u 0> and if a c@ 95 = if a 1+ to a u 1- to u true to lastus then then
  false { brk }
  begin u 0> brk 0= and while
    a c@ { c }
    c 95 = if
      lastus nd 0= or if 0 1 unloop exit then
      true to lastus
      a 1+ to a u 1- to u
    else
      c digc? if c 48 - else c alnc? c 128 < and if c lc 87 - else 0 -1 then then { d }
      d 0< if true to brk else
        d b >= if 0 1 unloop exit then
        zonly d 0<> and if 0 1 unloop exit then
        false to lastus  nd 1+ to nd
        ov 0= if
          lim d - 0 b um/mod nip acc swap u> if true to ov else acc b * d + to acc then
        then
        a 1+ to a u 1- to u
      then
    then
  repeat
  nd 0= lastus or if 0 1 exit then
  u 0> if 0 1 exit then
  ov if 0 2 exit then
  neg if acc negate else acc then 0 ;

sb-new constant bi-b
: bi-hex ( args n -- v ) { args n }
  n 1 2 s" hex" bi-check
  args 0 arg@ { v0 }  v0 mv-str? if bi-err-head s" hex() needs an integer" mb+ mfail then
  n 1 > if args 1 arg@ mv-str? if bi-err-head s" hex() width must be an integer" mb+ mfail then then
  v0 mv-n { v }  n 1 > if args 1 arg@ mv-n else 0 then { w }
  v 0< if v negate else v then base @ >r hex 0 <# #s #> r> base !
  { da du }
  bi-b sb-clear
  v 0< if 45 bi-b sb-c then
  w du > if w du - 0 ?do 48 bi-b sb-c loop then
  da du slower bi-b sb+
  bi-b sb$ mv-str ;

: bi-int ( args n -- v ) { args n }
  n 1 2 s" int" bi-check
  args 0 arg@ dup mv-str? 0= if exit then { v }
  n 1 > if args 1 arg@ mv-str? if bi-err-head s" int() base must be an integer" mb+ mfail then then
  n 1 > if args 1 arg@ mv-n else 0 then { base }
  v mv-s base py-int { r rc }
  rc 1 = if bi-err-head s" int(" mb+ v mv-s repr1 mb+ s" ) is not a number" mb+ mfail then
  rc 2 = if bi-err-head s" macro expression: integer overflow (64-bit) in int()" mb+ mfail then
  r mv-int ;

: bi-substr ( args n -- v ) { args n }
  n 2 3 s" substr" bi-check
  args 0 arg@ mv-text { ta tu }
  args 1 arg@ mv-str? if bi-err-head s" substr() index must be an integer" mb+ mfail then
  args 1 arg@ mv-n { st }
  st 0< if 0 to st then  st tu > if tu to st then
  n 2 > if args 2 arg@ mv-str? if bi-err-head s" substr() length must be an integer" mb+ mfail then then
  n 2 > if args 2 arg@ mv-n else tu st - then { cnt }
  cnt 0< if 0 to cnt then
  st cnt + tu > if tu st - to cnt then
  ta st + cnt mv-str ;

: bi-minmax ( args n want-min -- v ) { args n wm }
  args 0 arg@ { best }
  n 1 ?do
    args i arg@ { v }
    v best false m-order { lt }
    wm if lt else lt 0= v best m-equal 0= and then if v to best then
  loop best ;

: bi-label ( args n -- v ) { args n }
  n 1 1 s" label" bi-check
  args 0 arg@ mv-str? 0= if bi-err-head s" label() needs a string" mb+ mfail then
  args 0 arg@ mv-s asm-label { kind val }
  kind 0= if bi-err-head s" no such label or .equ: '" mb+ args 0 arg@ mv-s mb+ s" '" mb+ mfail then
  val mv-int ;

: m-builtin ( na nu args n -- v true | false ) { na nu args n }
  x-fa @ bi-fa ! x-fu @ bi-fu ! x-ln @ bi-ln !
  na nu s" len" str=cs if n 1 1 s" len" bi-check args 0 arg@ mv-text nip mv-int true exit then
  na nu s" str" str=cs if n 1 1 s" str" bi-check args 0 arg@ mv-text mv-str true exit then
  na nu s" hex" str=cs if args n bi-hex true exit then
  na nu s" int" str=cs if args n bi-int true exit then
  na nu s" upper" str=cs if n 1 1 s" upper" bi-check args 0 arg@ mv-text supper mv-str true exit then
  na nu s" lower" str=cs if n 1 1 s" lower" bi-check args 0 arg@ mv-text slower mv-str true exit then
  na nu s" substr" str=cs if args n bi-substr true exit then
  na nu s" abs" str=cs if
    n 1 1 s" abs" bi-check
    args 0 arg@ mv-str? if bi-err-head s" abs() needs an integer" mb+ mfail then
    args 0 arg@ mv-n { v }
    v $8000000000000000 = if bi-err-head s" macro expression: integer overflow (64-bit) in abs()" mb+ mfail then
    v abs mv-int true exit
  then
  na nu s" min" str=cs if n 1 64 s" min" bi-check args n true bi-minmax true exit then
  na nu s" max" str=cs if n 1 64 s" max" bi-check args n false bi-minmax true exit then
  na nu s" uid" str=cs if n 0 0 s" uid" bi-check mp.uid mp@ 1+ dup mp.uid mp! mv-int true exit then
  na nu s" label" str=cs if args n bi-label true exit then
  false ;

\ ---- 名前の解決 ----
: m-lookup-impl ( a u -- v ) { a u }
  a u scope-find ?dup if @ exit then
  a u func-find if
    x-fa @ x-fu @ x-ln @ mfail-pos s" macro '" mb+ a u mb+ s" ' used as a variable (call it as '" mb+ a u mb+ s" (...)')" mb+ mfail
  then
  a u asm-label { kind val }
  kind 0<> if val mv-int exit then
  x-fa @ x-fu @ x-ln @ mfail-pos s" undefined macro variable '" mb+ a u mb+ s" '" mb+ mfail 0 ;
' m-lookup-impl is m-lookup
: m-defined-impl ( a u -- f ) { a u }
  a u func-find if true exit then
  mp.scopen mp@ 0 ?do a u mp.scopes mp@ i cells + @ om-find if true unloop exit then loop
  a u asm-label nip 2 = ;
' m-defined-impl is m-defined?

defer m-loc-impl
: m-loc-counter-impl ( -- n )
  mp-pat? if
    x-fa @ x-fu @ x-ln @ mfail-pos s" '$'/'$$' is not available in pattern-file macros (there is no location counter before the source is assembled)" mb+ mfail
  then
  mp.keya mp@ mp.keyu mp@ { ka ku }
  ka 0= if 0 exit then
  ka ku mline-pcs-prev om-find 0= if 0 exit then
  { sl } sl @ { arr } sl cell+ @ { cnt }
  mp.outn mp@ { i }
  i 0>= i cnt < and if arr i cells + @ else 0 then ;
' m-loc-counter-impl is m-loc-counter

\ ---- 実行 ----
defer exec-block ( blk -- )
variable mx-ctl-dummy

: ctl@ ( -- n ) mp.ctl mp@ ;
: ctl! ( n -- ) mp.ctl mp! ;

: fn-name ( f -- a u ) s@ ;
: fn-np ( f -- n ) 2 cells + @ ;
: fn-pname ( f i -- a u ) 2 * cells swap 3 cells + @ + s@ ;
: fn-pdef ( f i -- a u ) 2 * cells swap 4 cells + @ + s@ ;
: fn-body ( f -- b ) 5 cells + @ ;
: fn-pos ( f -- fa fu ln ) dup 6 cells + @ over 7 cells + @ rot 8 cells + @ ;

: m-invoke ( f args n fa fu ln -- v ) { f args n fa fu ln }
  0 { nreq }
  f fn-np 0 ?do f i fn-pdef nip 0= if nreq 1+ to nreq then loop
  n f fn-np > n nreq < or if
    fa fu ln mfail-pos s" macro '" mb+ f fn-name mb+ s" ' takes " mb+ nreq mb-n s" .." mb+ f fn-np mb-n
    s"  argument(s), got " mb+ n mb-n mfail
  then
  mp.depth mp@ MACRO-MAX-DEPTH >= if
    fa fu ln mfail-pos s" macro recursion deeper than 200 while expanding '" mb+ f fn-name mb+ s" '" mb+ mfail
  then
  mp.scopen mp@ MAX-SCOPES >= if fa fu ln mfail-pos s" macro scope nesting too deep" mb+ mfail then
  scope-new { sc }
  sc mp.scopes mp@ mp.scopen mp@ cells + !  mp.scopen mp@ 1+ mp.scopen mp!
  f fn-np 0 ?do
    i n < if args i arg@ else f i fn-pdef fa fu ln m-eval then { v }
    f i fn-pname v scope-set
  loop
  mp.uid mp@ 1+ mp.uid mp!
  s" __id__" mp.uid mp@ mv-int scope-set
  s" __name__" f fn-name mv-str scope-set
  mp.depth mp@ 1+ mp.depth mp!
  f fn-body exec-block
  mp.depth mp@ 1- mp.depth mp!
  mp.scopen mp@ 1- mp.scopen mp!  sc om-free
  ctl@ 3 = if mp.retval mp@ 0 ctl! exit then
  ctl@ 0<> if
    0 ctl!
    fa fu ln mfail-pos s" '!break'/'!continue' outside a '!while' loop in macro '" mb+ f fn-name mb+ s" '" mb+ mfail
  then
  0 mv-int ;

: m-call-value-impl ( a u args n -- v ) { a u args n }
  x-noeval? if 0 mv-int exit then
  a u args n m-builtin if exit then
  a u func-find 0= if x-fa @ x-fu @ x-ln @ mfail-pos s" call to undefined macro '" mb+ a u mb+ s" '" mb+ mfail then
  mp.outn mp@ { mark }
  a u func-find args n x-fa @ x-fu @ x-ln @ m-invoke { v }
  mp.outn mp@ mark <> if
    mark OLSZ * mp.out mp@ + s@ strip-st { ea eu }
    mark mp.outn mp!
    x-fa @ x-fu @ x-ln @ mfail-pos s" macro '" mb+ a u mb+ s" ' emits source text (" mb+ ea eu repr1 mb+
    s" ) but was called from inside an expression, where there is nowhere to put it" mb+ mfail
  then
  v ;
' m-call-value-impl is m-call-value

\ ---- 書式 ----
variable f-fill  variable f-align  variable f-sign  variable f-hasfill  variable f-zco  variable f-alt
variable f-zero  variable f-width  variable f-group  variable f-hasprec  variable f-prec  variable f-type
: align? ( c -- f ) dup 60 = over 62 = or over 61 = or swap 94 = or ;
: fmt-parse ( a u -- ok ) { a u }
  32 f-fill ! 0 f-align ! 0 f-sign ! 0 f-hasfill ! 0 f-zco ! 0 f-alt ! 0 f-zero ! 0 f-width !
  0 f-group ! 0 f-hasprec ! 0 f-prec ! 0 f-type !
  0 { p }
  u 1 > if a 1+ c@ align? else false then if
    a c@ f-fill ! a 1+ c@ f-align ! 1 f-hasfill ! 2 to p
  else u 0> if a c@ align? else false then if a c@ f-align ! 1 to p then then
  p u < if a p + c@ dup 43 = over 45 = or swap 32 = or if a p + c@ f-sign ! p 1+ to p then then
  p u < if a p + c@ 122 = if 1 f-zco ! p 1+ to p then then
  p u < if a p + c@ 35 = if 1 f-alt ! p 1+ to p then then
  p u < if a p + c@ 48 = if 1 f-zero ! f-hasfill @ 0= if 48 f-fill ! then p 1+ to p then then
  begin p u < if a p + c@ digc? else false then while
    f-width @ 10 * a p + c@ 48 - + f-width !
    f-width @ 1000000 > if false exit then
    p 1+ to p
  repeat
  p u < if a p + c@ dup 44 = swap 95 = or if a p + c@ f-group ! p 1+ to p then then
  p u < if a p + c@ 46 = if
    p 1+ to p
    p u < if a p + c@ digc? 0= else true then if false exit then
    1 f-hasprec !
    begin p u < if a p + c@ digc? else false then while
      f-prec @ 10 * a p + c@ 48 - + f-prec !
      f-prec @ 1000000 > if false exit then
      p 1+ to p
    repeat
  then then
  p u < if
    a p + c@ { c }
    s" bcdeEfFgGnosxX%" c has-ch? 0= if false exit then
    c f-type ! p 1+ to p
  then
  p u = ;

: utf8-len ( a u -- n ) 0 -rot 0 ?do dup i + c@ $c0 and $80 <> if swap 1+ swap then loop drop ;
sb-new constant fp-b
: fmt-pad ( ha hu ba bu defalign -- a u ) { ha hu ba bu da }
  ha hu utf8-len ba bu utf8-len + { total }
  f-align @ ?dup 0= if da then { al }
  fp-b sb-clear
  total f-width @ >= if ha hu fp-b sb+ ba bu fp-b sb+ fp-b sb$ exit then
  f-width @ total - { pad }
  al 61 = if ha hu fp-b sb+ pad 0 ?do f-fill @ fp-b sb-c loop ba bu fp-b sb+ else
  al 60 = if ha hu fp-b sb+ ba bu fp-b sb+ pad 0 ?do f-fill @ fp-b sb-c loop else
  al 94 = if
    pad 2 / { left } pad left - { right }
    left 0 ?do f-fill @ fp-b sb-c loop ha hu fp-b sb+ ba bu fp-b sb+ right 0 ?do f-fill @ fp-b sb-c loop
  else pad 0 ?do f-fill @ fp-b sb-c loop ha hu fp-b sb+ ba bu fp-b sb+ then then then
  fp-b sb$ ;

sb-new constant fd-b
sb-new constant fg-b
: group-len ( n iv -- m ) { n iv } n n 1- iv / + ;
: fmt-int ( n -- a u ok ) { iv }
  f-type @ ?dup 0= if 100 then { type }
  type 101 = type 69 = or type 102 = or type 70 = or type 103 = or type 71 = or type 37 = or { isf }
  type 115 = if s" " false exit then
  isf if s" " false exit then
  f-hasprec @ f-zco @ or if s" " false exit then
  type 99 = if
    f-sign @ f-alt @ or f-group @ or if s" " false exit then
    iv 0< iv $10ffff > or if s" " false exit then
    iv 0= if s" " s" " 62 fmt-pad true exit then
    iv fd-b sb-clear
    { cp }
    cp 128 < if cp fd-b sb-c else
    cp 2048 < if $c0 cp 6 rshift or fd-b sb-c $80 cp $3f and or fd-b sb-c else
    cp 65536 < if $e0 cp 12 rshift or fd-b sb-c $80 cp 6 rshift $3f and or fd-b sb-c $80 cp $3f and or fd-b sb-c else
      $f0 cp 18 rshift or fd-b sb-c $80 cp 12 rshift $3f and or fd-b sb-c $80 cp 6 rshift $3f and or fd-b sb-c $80 cp $3f and or fd-b sb-c
    then then then
    s" " fd-b sb$ 62 fmt-pad true exit
  then
  f-group @ 44 = s" xXob" type has-ch? and if s" " false exit then
  f-group @ type 110 = and if s" " false exit then
  iv 0< { neg }
  neg if iv negate else iv then { uv }
  fd-b sb-clear  s" " { pa pu }
  type case
    100 of uv 0 <# #s #> endof
    110 of uv 0 <# #s #> endof
    120 of hex uv 0 <# #s #> decimal f-alt @ if s" 0x" to pu to pa then endof
    88 of hex uv 0 <# #s #> decimal f-alt @ if s" 0X" to pu to pa then endof
    111 of 8 base ! uv 0 <# #s #> decimal f-alt @ if s" 0o" to pu to pa then endof
    98 of 2 base ! uv 0 <# #s #> decimal f-alt @ if s" 0b" to pu to pa then endof
    drop s" " false exit
  endcase
  { da du }
  type 88 = if da du supper to du to da then
  type 120 = if da du slower to du to da then
  fg-b sb-clear
  neg if 45 fg-b sb-c else f-sign @ 43 = if 43 fg-b sb-c else f-sign @ 32 = if 32 fg-b sb-c then then then
  pa pu fg-b sb+
  fg-b sb$ sdup { ha hu }
  f-group @ 0= if
    ha hu da du f-zero @ f-align @ 0= and if 61 else 62 then fmt-pad true exit
  then
  s" xXob" type has-ch? if 4 else 3 then { step }
  du { want }
  f-align @ ?dup 0= if f-zero @ if 61 else 62 then then { eal }
  eal 61 = f-fill @ 48 = and if
    begin want step group-len f-width @ hu - < while want 1+ to want repeat
  then
  want 400 > if s" " false exit then
  fd-b sb-clear
  want du - 0 ?do 48 fd-b sb-c loop da du fd-b sb+
  fd-b sb$ { qa qu }
  fg-b sb-clear
  qu step mod { lead }  lead 0= if step to lead then
  qa lead fg-b sb+  lead { k }
  begin k qu < while
    f-group @ fg-b sb-c  qa k + step fg-b sb+  k step + to k
  repeat
  ha hu fg-b sb$ f-zero @ f-align @ 0= and if 61 else 62 then fmt-pad true ;

: fmt-str ( a u -- a' u' ok ) { a u }
  f-type @ if f-type @ 115 <> else false then if s" " false exit then
  f-sign @ f-alt @ or f-group @ or f-zco @ or if s" " false exit then
  f-align @ 61 = if s" " false exit then
  a u f-hasprec @ if
    a u utf8-len f-prec @ > if
      0 0 false { ofs seen fin }
      begin ofs u < fin 0= and while
        a ofs + c@ $c0 and $80 <> if seen f-prec @ = if true to fin else seen 1+ to seen then then
        fin 0= if ofs 1+ to ofs then
      repeat
      a ofs
    then
  then
  { ba bu }
  s" " ba bu 60 fmt-pad true ;

\ 補間
: m-format-value ( ba bu fa fu ln -- a u ) { ba bu fa fu ln }
  -1 { sp } 0 { q } 0 { par } 0 { k }
  begin k bu < sp 0< and while
    ba k + c@ { c }
    q 0<> if
      c 92 = if k 2 + to k else c q = if 0 to q then k 1+ to k then
    else
      c 34 = c 39 = or if c to q k 1+ to k else
      c 40 = c 91 = or if par 1+ to par k 1+ to k else
      c 41 = c 93 = or if par 1- to par k 1+ to k else
      c 58 = par 0= and if
        false { hasq } k 0 ?do ba i + c@ 63 = if true to hasq then loop
        hasq if k 1+ to k else k to sp then
      else k 1+ to k then then then then
    then
  repeat
  sp 0< if ba bu else ba sp then fa fu ln m-eval { v }
  sp 0< if v mv-text exit then
  ba sp 1+ + bu sp - 1- strip-st { sa su }
  su 0= if v mv-text exit then
  sa su fmt-parse 0= if
    fa fu ln mfail-pos s" bad format spec ':" mb+ sa su mb+ s" ' for value " mb+
    v mv-str? if v mv-s repr1 mb+ else v mv-n mb-n then mfail
  then
  v mv-str? if v mv-s fmt-str else v mv-n fmt-int then
  0= if
    2drop fa fu ln mfail-pos s" bad format spec ':" mb+ sa su mb+ s" ' for value " mb+
    v mv-str? if v mv-s repr1 mb+ else v mv-n mb-n then mfail
  then ;

sb-new constant ip-b
: m-interpolate ( ta tu fa fu ln -- a u ) { ta tu fa fu ln }
  ta tu s" !{" search nip nip 0= if ta tu exit then
  ip-b sb-clear
  0 { i }
  begin i tu < while
    ta i + c@ 92 = i 3 + tu <= and if ta i 1+ + 2 s" !{" str=cs else false then if
      s" !{" ip-b sb+ i 3 + to i
    else ta i + 2 s" !{" str=cs i 1+ tu < and 0= if
      ta i + c@ ip-b sb-c i 1+ to i
    else
      i 2 + { j } 1 { depth } 0 { q } false { fin }
      begin j tu < fin 0= and while
        ta j + c@ { c }
        q 0<> if
          c 92 = if j 2 + to j else c q = if 0 to q then j 1+ to j then
        else
          c 39 = if
            j 1+ { jj }
            begin jj tu < if ta jj + c@ dup 32 = swap 9 = or else false then while jj 1+ to jj repeat
            jj tu < if ta jj + c@ dup digc? swap 40 = or else false then 0= if 39 to q then
            j 1+ to j
          else c 34 = if 34 to q j 1+ to j else
          c 123 = if depth 1+ to depth j 1+ to j else
          c 125 = if depth 1- to depth depth 0= if true to fin else j 1+ to j then else j 1+ to j then then then then
        then
      repeat
      j tu >= if fa fu ln mfail-pos s" unterminated '!{' in line" mb+ mfail then
      ta i + 2 + j i 2 + - fa fu ln m-format-value ip-b sb+
      j 1+ to i
    then then
  repeat
  ip-b sb$ mm-str ;

\ ---- 実行 ----
: echo-write ( v -- ) mv-text etype ecr ;

: exec-if ( nd -- ) { nd }
  nd nd-pos { fa fu ln }
  nd 0 nf @ { na }  nd 1 nf @ { arms }
  na 0 ?do
    arms i 3 * cells + s@ fa fu ln m-eval mv-truth if
      arms i 3 * cells + 2 cells + @ exec-block unloop exit
    then
  loop
  nd 2 nf @ ?dup if exec-block then ;

: exec-while ( nd -- ) { nd }
  nd nd-pos { fa fu ln }
  0 { count }
  begin
    nd 0 nf s@ fa fu ln m-eval mv-truth ctl@ 0= and
  while
    count 1+ to count
    count MACRO-MAX-ITER > if fa fu ln mfail-pos s" '!while' ran more than 1000000 iterations; assuming it never terminates" mb+ mfail then
    nd 2 nf @ exec-block
    ctl@ 2 = if 0 ctl! then
    ctl@ 1 = if 0 ctl! exit then
    ctl@ 3 = if exit then
  repeat ;

: exec-def ( nd -- ) { nd }
  nd 0 nf @ { f }
  f fn-name func-find { prev }
  prev 0<> if
    prev fn-body blk-n 0> prev fn-pos { pfa pfu pln } f fn-pos { cfa cfu cln }
    pfa pfu cfa cfu str=cs pln cln = and 0= and if
      mb-reset nd nd-pos fmt-pos s" : macro '" mb+ f fn-name mb+ s" ' redefined (previous definition at " mb+
      prev fn-pos fmt-pos s" )" mb+ m-warn
    then
  then
  f fn-name mp @ mp.funcs + @ om-put f swap ! ;

\ 呼び出しの引数 `(a, b, ...)`
: m-parse-args ( ta tu fa fu ln -- args n ) { ta tu fa fu ln }
  ta tu strip-st { t n }
  n 0= if 0 0 exit then
  t c@ 59 = if 0 0 exit then
  t c@ 40 <> if fa fu ln mfail-pos s" macro call needs parentheses" mb+ mfail then
  x-a @ x-u @ x-i @ x-sup @ x-fa @ x-fu @ x-ln @ { sa su si ss sfa sfu sln }
  t x-a ! n x-u ! 0 x-i ! 0 x-sup ! fa x-fa ! fu x-fu ! ln x-ln !
  s" (" x-expect
  64 cells mm-alloc { args } 0 { na }
  x-peek 41 = if 1 x-i +! else
    begin
      x-ternary args na cells + !  na 1+ to na
      s" ," x-eat if true else s" )" x-expect false then 0=
    until
  then
  x-a @ x-i @ + x-u @ x-i @ - strip-st { ra ru }
  ru 0> if ra c@ 59 <> else false then if
    fa fu ln mfail-pos s" unexpected text after macro call: " mb+ ra ru repr1 mb+ mfail
  then
  sa x-a ! su x-u ! si x-i ! ss x-sup ! sfa x-fa ! sfu x-fu ! sln x-ln !
  args na ;

: exec-call ( nd -- ) { nd }
  nd nd-pos { fa fu ln }
  nd 0 nf s@ func-find { f }
  f 0= if fa fu ln mfail-pos s" call to undefined macro '" mb+ nd 0 nf s@ mb+ s" '" mb+ mfail then
  nd 2 nf s@ fa fu ln m-parse-args { args n }
  f args n fa fu ln m-invoke drop ;

defer m-do-include ( v fa fu ln -- )

: exec-node0 ( nd -- ) { nd }
  nd nd-pos { fa fu ln }
  nd @ case
    N-TEXT of nd 0 nf s@ fa fu ln m-interpolate fa fu ln out-add endof
    N-IF of nd exec-if endof
    N-WHILE of nd exec-while endof
    N-DEF of nd exec-def endof
    N-SET of nd 0 nf s@ nd 2 nf s@ fa fu ln m-eval assign-var endof
    N-LOCAL of nd 0 nf s@ nd 2 nf @ if nd 2 nf s@ fa fu ln m-eval else 0 mv-int then scope-set endof
    N-UNDEF of
      nd 0 nf s@ { na nu }
      na nu mp @ mp.funcs + @ om-del
      mp.scopen mp@ 0 ?do
        na nu mp.scopes mp@ mp.scopen mp@ 1- i - cells + @ om-find if
          na nu mp.scopes mp@ mp.scopen mp@ 1- i - cells + @ om-del leave
        then
      loop
    endof
    N-CALL of nd exec-call endof
    N-RETURN of nd 0 nf @ if nd 0 nf s@ fa fu ln m-eval else 0 mv-int then mp.retval mp! 3 ctl! endof
    N-BREAK of 1 ctl! endof
    N-CONT of 2 ctl! endof
    N-ERROR of fa fu ln mfail-pos nd 0 nf s@ fa fu ln m-eval mv-text mb+ mfail endof
    N-WARN of mb-reset fa fu ln fmt-pos s" : " mb+ nd 0 nf s@ fa fu ln m-eval mv-text mb+ m-warn endof
    N-ECHO of
      pass @ 1 <> if nd 0 nf s@ fa fu ln m-eval echo-write
      else nd 0 nf s@ fa fu ln m-eval drop then
    endof
    N-INCLUDE of nd 0 nf s@ fa fu ln m-eval fa fu ln m-do-include endof
  endcase ;

: exec-node ( nd -- ) depth 1- >r exec-node0 depth r> - if s" STACKLEAK " etype depth n>s etype ecr then ;
: exec-block-impl ( b -- ) { b }
  b blk-n 0 ?do
    b i blk-node exec-node
    ctl@ 0<> if leave then
  loop ;
' exec-block-impl is exec-block

