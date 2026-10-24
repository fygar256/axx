\ mini3.fs -- ミニ言語の評価器 (MiniInterp): 値、式、文

decimal

\ ---- 値の領域 (.call ごとに捨てる) ----
134217728 constant MIA-SIZE
MIA-SIZE allocate throw constant mia
variable mia-top
: mi-alloc ( n -- a ) 7 + -8 and mia-top @ over + MIA-SIZE > abort" mini memory full"
  mia-top @ mia + swap mia-top +! ;
: mi-str ( a u -- a' u ) { a u } u 1+ mi-alloc { d } a d u move 0 d u + c! d u ;

\ 値: 0 整数 [0][q 4 cells] / 1 文字列 [1][a][u] / 2 配列 [2][ptr][n][cap]
: mi-int ( q -- v ) 5 cells mi-alloc { v } 0 v ! v cell+ q! v ;
: mi-n ( n -- v ) qn mi-int ;
: mi-s ( a u -- v ) mi-str 3 cells mi-alloc { a u v } 1 v ! a v cell+ ! u v 2 cells + ! v ;
: mi-arr ( cap -- v ) { cap }
  4 cells mi-alloc { v }
  cap 4 max cells mi-alloc { p }
  2 v !  p v cell+ !  0 v 2 cells + !  cap 4 max v 3 cells + !  v ;
: v-type ( v -- t ) @ ;
: v-q ( v -- q ) cell+ ;
: v-str ( v -- a u ) cell+ s@ ;
: v-arr? ( v -- f ) @ 2 = ;
: v-str? ( v -- f ) @ 1 = ;
: ma-len ( v -- n ) 2 cells + @ ;
: ma-ref ( v i -- e ) cells swap cell+ @ + @ ;
: ma-set ( e v i -- ) cells swap cell+ @ + ! ;
: ma-push ( e v -- ) { e v }
  v 2 cells + @ v 3 cells + @ >= if
    v 3 cells + @ 2* { nc }
    nc cells mi-alloc { np }
    v cell+ @ np v 2 cells + @ cells move
    np v cell+ !  nc v 3 cells + !
  then
  e v cell+ @ v 2 cells + @ cells + !  1 v 2 cells + +! ;
: ma-copy ( v -- v' ) { v }
  v ma-len mi-arr { r }
  v ma-len 0 ?do v i ma-ref r ma-push loop r ;

-5102 constant X-MRT
variable rt-fa  variable rt-fu  variable rt-ln
: rt-head ( -- ) rt-fa @ rt-fu @ rt-ln @ mfail-pos ;
: rt-err ( a u -- ) rt-head mb+ mini-throw ;
: set-rt ( fa fu ln -- ) rt-ln ! rt-fu ! rt-fa ! ;

\ ---- 状態 ----
4000000 constant MAX-STEPS
128 constant MI-MAX-DEPTH
1048576 constant MAX-EMIT
1048576 constant MAX-ARRAY
variable steps
variable nframes
create fr-vars 130 cells allot
create fr-nl 130 cells allot
create fr-func 130 cells allot
QB MAX-EMIT * allocate throw constant mout
create mout-str 1 cells allot                 \ (未使用)
variable nout
1 om-new constant mini-suspects
1 om-new constant fallback-names
variable mini-ret                              \ 返り値 (0 なら値なし)
variable ctl-m                                 \ 0 なし 1 break 2 continue 3 return

: need-int ( v what-a what-u -- q ) { v wa wu }
  v v-arr? if wa wu rt-head mb+ s"  must be a number, not an array" mb+ mini-throw then
  v v-str? if wa wu rt-head mb+ s"  must be a number, not a string" mb+ mini-throw then
  v v-q ;
: is-zero? ( q -- f ) q-zero? ;
: need-elem ( v -- v' )
  dup v-arr? if drop rt-head s" an array element must be a number or a string, not an array" mb+ mini-throw then ;
: text-of ( v -- a u )                               \ + でつなぐ側の文字列
  dup v-str? if v-str exit then
  s" an operand" need-int q>dec ;

\ ---- 変数 ----
: top-frame ( -- n ) nframes @ 1- ;
: frame-for ( a u -- fr|-1 ) { a u }
  top-frame { t }
  a u t cells fr-nl + @ om-find 0= if t exit then
  t 0 ?do
    a u t 1- i - cells fr-vars + @ om-find if t 1- i - unloop exit then
  loop -1 ;

: core-eval ( a u -- v )                              \ 本体の式評価器でラベル・$$・#名前を読む
  { a u }
  a u 0 expr-mini { q pos }
  q qundef-derived? if q0 else q then mi-int ;
: core-name? ( a u -- f ) { a u }
  a u labels om-find if true exit then
  a u supper numsyms om-find if true exit then
  a u relax-prev om-find 0<> ;

: permissive? ( -- f )
  pass @ 2 <> pass @ 1 = relax-optimistic @ 0= and 0= and ;

: mini-get ( a u -- v ) { a u }
  a u frame-for { fr }
  fr 0< if rt-head s" '.nonlocal " mb+ a u mb+ s" ' found no enclosing definition of " mb+ a u repr1 mb+ mini-throw then
  a u fr cells fr-vars + @ om-find ?dup if @ exit then
  permissive? { perm }
  perm if a u mini-suspects om-find 0<> if false to perm then then
  a u core-name? perm or if
    perm a u core-name? 0= and if a u fallback-names om-put drop then
    a u core-eval exit
  then
  rt-head a u repr1 mb+ s"  is used before it is set" mb+ mini-throw 0 ;

: mini-set ( v a u -- ) { v a u }
  a u frame-for { fr }
  fr 0< if rt-head s" '.nonlocal " mb+ a u mb+ s" ' found no enclosing definition of " mb+ a u repr1 mb+ mini-throw then
  a u fr cells fr-vars + @ om-put v swap ! ;

\ 値の複製 (配列は写し、整数・文字列は共有)
: mi-copy ( v -- v' ) dup v-arr? if ma-copy then ;

defer mi-eval ( e -- v )
defer mi-call ( f args n -- ret|0 )

: mini-lookup ( a u -- f ) { a u }
  nframes @ 0> if top-frame cells fr-func + @ else 0 then { fn }
  begin fn 0<> while
    a u fn mf-children om-find ?dup if @ exit then
    fn mf-parent to fn
  repeat
  a u mfuncs om-find ?dup if @ exit then
  rt-head s" no function named " mb+ a u repr1 mb+ mini-throw 0 ;

\ ---- 文字列の道具 ----
sb-new constant mi-sb
: need-strlen ( n -- ) MAX-ARRAY > if rt-head s" string longer than the maximum length 1048576" mb+ mini-throw then ;
: mini-dec-s ( q -- v ) q>dec mi-s ;
: str-concat ( a b -- v )
  text-of 2>r text-of 2r> { aa au ba bu }
  au bu + need-strlen
  mi-sb sb-clear aa au mi-sb sb+ ba bu mi-sb sb+ mi-sb sb$ mi-s ;

\ ---- 二項演算 ----
: q-truth ( q -- f ) q-zero? 0= ;
: q-bool ( f -- v ) if q1 else q0 then mi-int ;

: op-text ( opid -- a u )
  case 1 of s" ||" endof 2 of s" &&" endof 3 of s" ==" endof 4 of s" !=" endof 5 of s" <=" endof 6 of s" >=" endof
    7 of s" <" endof 8 of s" >" endof 9 of s" |" endof 10 of s" ^" endof 11 of s" &" endof 12 of s" <<" endof
    13 of s" >>" endof 14 of s" +" endof 15 of s" -" endof 16 of s" *" endof 17 of s" /" endof 18 of s" %" endof
    19 of s" **" endof drop s" ?" 0 endcase ;

: int-binop ( opid a b -- v ) { opid a b }
  opid case
    14 of a b q+ endof
    15 of a b q- endof
    16 of a b q* endof
    17 of b q-zero? if rt-head s" division by zero" mb+ mini-throw then a b qtruncdiv endof
    18 of b q-zero? if rt-head s" division by zero" mb+ mini-throw then a a b qtruncdiv b q* q- endof
    19 of b q-neg? if rt-head s" negative exponent" mb+ mini-throw then a b qpow endof
    12 of b q-neg? b 256 qn q>= or if q0 else a b q>n qshl then endof
    13 of b q-neg? if q0 else b 256 qn q>= if a q-neg? if q0 qnot else q0 then else a b q>n qsar then then endof
    11 of a b qand endof
    9 of a b qor endof
    10 of a b qxor endof
    7 of a b q< if q1 else q0 then endof
    8 of a b q> if q1 else q0 then endof
    5 of a b q<= if q1 else q0 then endof
    6 of a b q>= if q1 else q0 then endof
    3 of a b q= if q1 else q0 then endof
    4 of a b q= if q0 else q1 then endof
    q0
  endcase
  mi-int ;

: str-repeat-v ( a b -- v ) { a b }
  a v-str? b v-str? and if rt-head s" a string can only be repeated by a number" mb+ mini-throw then
  a v-str? if a b else b a then { t n }
  n s" a repeat count" need-int q>n { cnt }
  cnt 0<= if s" " mi-s exit then
  t v-str { ta tu }
  tu cnt * need-strlen
  mi-sb sb-clear cnt 0 ?do ta tu mi-sb sb+ loop mi-sb sb$ mi-s ;

: str-binop ( opid a b -- v ) { opid a b }
  opid 14 = if a b str-concat exit then
  opid 16 = if a b str-repeat-v exit then
  opid 3 = opid 4 = or if
    a v-arr? b v-arr? or if rt-head s" an operand must be a number, not an array" mb+ mini-throw then
    a v-str? b v-str? and if a v-str b v-str str=cs else false then { eq }
    opid 3 = if eq else eq 0= then q-bool exit
  then
  opid 5 = opid 6 = or opid 7 = or opid 8 = or if
    a v-str? b v-str? and 0= if rt-head s" cannot order a string against a number" mb+ mini-throw then
    a v-str b v-str compare { c }
    opid 7 = if c 0< else opid 5 = if c 0<= else opid 8 = if c 0> else c 0>= then then then
    q-bool exit
  then
  rt-head s" an operand of '" mb+ opid op-text mb+ s" ' must be a number, not a string" mb+ mini-throw 0 ;

: binop ( e -- v ) { e }
  e 0 ef @ { opid }
  opid 2 = if
    e 1 ef @ mi-eval s" an operand" need-int q-truth 0= if q0 mi-int exit then
    e 2 ef @ mi-eval s" an operand" need-int q-truth q-bool exit
  then
  opid 1 = if
    e 1 ef @ mi-eval s" an operand" need-int q-truth if q1 mi-int exit then
    e 2 ef @ mi-eval s" an operand" need-int q-truth q-bool exit
  then
  e 1 ef @ mi-eval { a }  e 2 ef @ mi-eval { b }
  a v-str? b v-str? or if opid a b str-binop exit then
  opid a s" an operand" need-int  b s" an operand" need-int  int-binop ;

\ ---- `.int(文字列)` ----
: str-to-int ( v -- v' ) { v }
  v v-arr? if rt-head s" '.int' needs a number or a string" mb+ mini-throw then
  v v-str? 0= if v exit then
  v v-str strip-st { t n }
  false { neg } 10 { base }
  n 0> if t c@ 45 = if true to neg t 1+ to t n 1- to n else t c@ 43 = if t 1+ to t n 1- to n then then then
  n 1 > if t c@ 48 = if t 1+ c@ dup 120 = swap 88 = or if 16 to base t 2 + to t n 2 - to n
    else t 1+ c@ dup 98 = swap 66 = or if 2 to base t 2 + to t n 2 - to n then then then then
  n 0= if rt-head s" '.int' cannot read the string as a number" mb+ mini-throw then
  false { alld }  true to alld
  n 0 ?do t i + c@ 95 <> if false to alld then loop
  alld if rt-head s" '.int' cannot read the string as a number" mb+ mini-throw then
  q0 { r }
  n 0 ?do
    t i + c@ { c }
    c 95 = if else
      c digc? if c 48 - else c 128 < c alnc? and if c lc 87 - else -1 then then { d }
      d 0< d base >= or if rt-head s" '.int' cannot read the string as a number" mb+ mini-throw then
      r base 0 q*small+ drop to r  r d qn q+ to r
    then
  loop
  neg if r qneg else r then mi-int ;

\ ---- 添字・切り出し ----
: bound-of ( e dflt -- n ) { e dflt }
  e 0= if dflt exit then
  e mi-eval s" a slice bound" need-int q>n ;
: eval-index ( e -- v ) { e }
  e 0 ef @ mi-eval { base }
  base v-arr? base v-str? or 0= if rt-head s" only an array or a string can be indexed" mb+ mini-throw then
  e 1 ef @ mi-eval s" an index" need-int q>n { idx }
  base v-arr? if
    idx 0< idx base ma-len >= or if q0 mi-int exit then
    base idx ma-ref
  else
    base v-str { ba bu }
    idx 0< idx bu >= or if q0 mi-int exit then
    ba idx + c@ mi-n
  then ;
: eval-slice ( e -- v ) { e }
  e 0 ef @ mi-eval { base }
  base v-arr? base v-str? or 0= if rt-head s" only an array or a string can be sliced" mb+ mini-throw then
  base v-arr? if base ma-len else base v-str nip then { n }
  e 1 ef @ 0 bound-of { lo0 }
  e 2 ef @ n bound-of { hi0 }
  lo0 0 max n min { lo }
  hi0 lo max n min { hi }
  base v-arr? if
    hi lo - mi-arr { r }
    hi lo ?do base i ma-ref r ma-push loop r
  else base v-str drop lo + hi lo - mi-s then ;

: eval-un ( e -- v ) { e }
  e 0 ef @ { op }
  e 1 ef @ mi-eval s" an operand" need-int { q }
  op 45 = if q qneg mi-int exit then
  op 43 = if q mi-int exit then
  op 126 = if q qnot mi-int exit then
  q q-zero? q-bool ;

: eval-arr ( e -- v ) { e }
  e 0 ef @ { n }  e 1 ef @ { p }
  n mi-arr { r }
  n 0 ?do p i cells + @ mi-eval need-elem r ma-push loop r ;

: eval-args ( n p -- args ) { n p }
  n 1 max cells mi-alloc { a }
  n 0 ?do p i cells + @ mi-eval a i cells + ! loop a ;

: eval-call ( e -- v ) { e }
  e 0 ef s@ mini-lookup { f }
  e 2 ef @ e 3 ef @ eval-args { args }
  f args e 2 ef @ mi-call { r }
  r 0= if rt-head s" " mb+ e 0 ef s@ repr1 mb+ s"  returned no value; give it a '.return <expression>'" mb+ mini-throw then
  r ;

: mi-eval-impl ( e -- v ) { e }
  e @ case
    E-NUM of e 0 ef mi-int endof
    E-STR of e 0 ef s@ mi-s endof
    E-CORE of e 0 ef s@ core-eval endof
    E-VAR of e 0 ef s@ mini-get endof
    E-ARR of e eval-arr endof
    E-CALL of e eval-call endof
    E-LEN of
      e 0 ef @ mi-eval { v }
      v v-arr? v v-str? or 0= if rt-head s" '.len' needs an array or a string" mb+ mini-throw then
      v v-arr? if v ma-len else v v-str nip then mi-n
    endof
    E-TOSTR of
      e 0 ef @ mi-eval { v }
      v v-arr? if rt-head s" '.str' needs a number or a string" mb+ mini-throw then
      v v-str? if v else v v-q q>dec mi-s then
    endof
    E-CHR of
      e 0 ef @ mi-eval s" '.chr' argument" need-int q>n { c }
      c 0< c 255 > or if rt-head s" '.chr' needs a value from 0 to 255" mb+ mini-throw then
      1 mi-alloc { b } c b c!  b 1 mi-s
    endof
    E-TOINT of e 0 ef @ mi-eval str-to-int endof
    E-INDEX of e eval-index endof
    E-SLICE of e eval-slice endof
    E-UN of e eval-un endof
    E-BIN of e binop endof
    rt-head s" bad expression" mb+ mini-throw 0
  endcase ;
' mi-eval-impl is mi-eval

\ ---- 代入 ----
: slice-bound ( e -- n flag ) dup 0= if drop 0 false exit then mi-eval s" a slice bound" need-int q>n true ;
: slice-new-str ( cur val lo hi -- v ) { cur val lo hi }
  cur v-str { ca cu }
  mi-sb sb-clear  ca lo mi-sb sb+  val v-str mi-sb sb+  ca hi + cu hi - mi-sb sb+
  mi-sb sb-len need-strlen  mi-sb sb$ mi-s ;
: slice-new-arr ( cur val lo hi -- v ) { cur val lo hi }
  cur ma-len val ma-len + mi-arr { r }
  lo 0 ?do cur i ma-ref r ma-push loop
  val ma-len 0 ?do val i ma-ref r ma-push loop
  cur ma-len hi ?do cur i ma-ref r ma-push loop
  r ma-len MAX-ARRAY > if rt-head s" array longer than the maximum length 1048576" mb+ mini-throw then
  r ;
: store-slice ( val lo-e hi-e na nu -- ) { val lo-e hi-e na nu }
  lo-e slice-bound { lo-set } { lo0 }
  hi-e slice-bound { hi-set } { hi0 }
  na nu mini-get { cur }
  cur v-arr? cur v-str? or 0= if rt-head na nu repr1 mb+ s"  is not an array or a string" mb+ mini-throw then
  cur v-arr? if cur ma-len else cur v-str nip then { n }
  lo-set if lo0 0 max n min else 0 then { lo }
  hi-set if hi0 lo max n min else n then { hi }
  cur v-str? if
    val v-str? 0= if rt-head s" a string slice can only be given a string" mb+ mini-throw then
    cur val lo hi slice-new-str
  else
    val v-arr? 0= if rt-head s" an array slice can only be given an array" mb+ mini-throw then
    cur val lo hi slice-new-arr
  then
  na nu mini-set ;

: store-byte ( elem idx na nu -- ) { elem i na nu }
  na nu mini-get { arr }
  elem v-str? if elem v-str 1 = if elem v-str drop c@ else -1 then else elem v-q q>n then { b }
  b 0< b 255 > or if rt-head s" a byte of a string must be a value from 0 to 255 or a one-byte string" mb+ mini-throw then
  arr v-str { ca cu }
  mi-sb sb-clear
  ca cu mi-sb sb+
  i cu >= if i 1+ cu - 0 ?do 0 mi-sb sb-c loop then
  mi-sb sb$ { ba bu }
  b ba i + c!
  ba bu mi-s na nu mini-set ;

: store-index ( val idx-e na nu -- ) { val idx-e na nu }
  idx-e mi-eval s" an index" need-int { iq }
  iq q-neg? if rt-head s" negative index " mb+ iq q>dec mb+ s"  in assignment" mb+ mini-throw then
  iq q>n { i }
  i MAX-ARRAY >= if rt-head s" array index " mb+ i mb-n s"  exceeds the maximum length 1048576" mb+ mini-throw then
  val need-elem { elem }
  na nu mini-get { arr }
  arr v-str? if elem i na nu store-byte exit then
  arr v-arr? 0= if rt-head na nu repr1 mb+ s"  is not an array or a string" mb+ mini-throw then
  i arr ma-len >= if i 1+ arr ma-len - 0 ?do q0 mi-int arr ma-push loop then
  elem arr i ma-set ;

: mini-store ( val idx na nu -- ) { val idx na nu }
  idx 0= if val mi-copy na nu mini-set exit then
  idx @ E-SLICET = if val idx 0 ef @ idx 1 ef @ na nu store-slice exit then
  val idx na nu store-index ;

\ ---- 実行 ----
: mi-tick ( -- )
  1 steps +!
  steps @ MAX-STEPS > if
    pass @ 1 = relax-optimistic @ and if
      fallback-names om-used 0 ?do
        i fallback-names om-live? if i fallback-names om-key mini-suspects om-put drop then
      loop
    then
    rt-head s" mini language ran more than 4000000 statements; assuming a runaway loop" mb+ mini-throw
  then ;

: sn-set-pos ( s -- ) sn-pos set-rt ;
defer mi-exec ( s -- )
: mi-block ( b -- ) { b }
  b @ 0 ?do b i 1+ cells + @ mi-exec ctl-m @ 0<> if leave then loop ;

: emit-q ( q -- )
  nout @ MAX-EMIT >= if rt-head s" '.emit' produced more than 1048576 words" mb+ mini-throw then
  mout nout @ QB * + q!  1 nout +! ;
: emit-bytes ( a u -- ) 0 ?do dup i + c@ qn emit-q loop drop ;
: emit-value ( v -- ) { v }
  v v-arr? if
    v ma-len 0 ?do
      v i ma-ref { e }
      e v-str? if e v-str emit-bytes else e v-q emit-q then
    loop
  else v v-str? if v v-str emit-bytes else v v-q emit-q then then ;

: echo-str ( a u -- )                            \ NUL を \0 と書く
  { a u } u 0 ?do a i + c@ dup 0= if drop s" \0" mi-sb sb+ else mi-sb sb-c then loop ;
: echo-value ( v -- ) { v }
  v v-arr? if
    91 mi-sb sb-c
    v ma-len 0 ?do
      i if s" , " mi-sb sb+ then
      v i ma-ref { e }
      e v-str? if 34 mi-sb sb-c e v-str echo-str 34 mi-sb sb-c else e v-q q>dec mi-sb sb+ then
    loop
    93 mi-sb sb-c
  else v v-str? if v v-str echo-str else v v-q q>dec mi-sb sb+ then then ;

: mi-raise ( s -- ) { s }
  s 0 sf @ mi-eval { v }
  v v-arr? if rt-head s" '.raise' needs a number, not an array" mb+ mini-throw then
  v v-str? if rt-head s" '.raise' needs a number, not a string" mb+ mini-throw then
  report? size-mode @ 0= and if
    v v-q q>n { code }
    s" Line " etype line-no @ .en s"  Error code " etype code .en s"  " etype
    code 0>= if code err-text if etype then then
    s" : " etype ecr
    true had-error !
  then ;

: mi-echo ( s -- ) { s }
  mi-sb sb-clear
  s 0 sf @ { n }  s 1 sf @ { p }
  n 0 ?do
    i if 32 mi-sb sb-c then
    p i cells + @ mi-eval echo-value
  loop
  report? size-mode @ 0= and if mi-sb sb$ etype ecr then ;

: mi-call-impl ( f args n -- ret|0 ) { f args n }
  nframes @ MI-MAX-DEPTH >= if rt-head s" call nesting deeper than 128; assuming runaway recursion" mb+ mini-throw then
  n f mf-np <> if
    rt-head s" " mb+ f mf-name repr1 mb+ s"  takes " mb+ f mf-np mb-n s"  argument(s), got " mb+ n mb-n mini-throw
  then
  1 om-new { vars }  1 om-new { nl }
  n 0 ?do args i cells + @ mi-copy f i mf-pname vars om-put ! loop
  vars nframes @ cells fr-vars + !  nl nframes @ cells fr-nl + !  f nframes @ cells fr-func + !
  1 nframes +!
  0 mini-ret !  0 ctl-m !
  f mf-body ?dup if mi-block then
  ctl-m @ 3 = if mini-ret @ else 0 then
  0 ctl-m !
  -1 nframes +!
  vars om-free nl om-free ;
' mi-call-impl is mi-call

: mi-call-stmt ( s -- ) { s }
  s 0 sf s@ mini-lookup { f }
  s 2 sf @ s 3 sf @ eval-args { args }
  f args s 2 sf @ mi-call drop ;
: mi-callassign ( s -- ) { s }
  s 3 sf s@ mini-lookup { f }
  s 5 sf @ s 6 sf @ eval-args { args }
  f args s 5 sf @ mi-call { r }
  r 0= if rt-head s" " mb+ s 3 sf s@ repr1 mb+ s"  returned no value; give it a '.return <expression>'" mb+ mini-throw then
  r s 2 sf @ s 0 sf s@ mini-store ;
: mi-nonlocal ( s -- ) { s }
  s 0 sf @ 0 ?do
    s 1 sf @ i 2 * cells + s@ { na nu }
    na nu top-frame cells fr-vars + @ om-find if
      rt-head na nu repr1 mb+ s"  is already local; '.nonlocal' must come before it is set" mb+ mini-throw
    then
    na nu top-frame cells fr-nl + @ om-put drop
  loop ;

: mi-for-body ( s body-idx -- brk? ) { s bi }
  s bi sf @ mi-block
  ctl-m @ 2 = if 0 ctl-m ! false exit then
  ctl-m @ 1 = if 0 ctl-m ! true exit then
  ctl-m @ 3 = ;
