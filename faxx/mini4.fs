\ mini4.fs -- ミニ言語: 制御文、実行の入口、.call の引数 (ObjectGenerator.mini_call)

decimal

: mi-while ( s -- ) { s }
  begin
    s 0 sf @ mi-eval s" a condition" need-int q-truth
  while
    mi-tick
    s 1 mi-for-body if exit then
  repeat ;

: mi-if ( s -- ) { s }
  s 0 sf @ mi-eval s" a condition" need-int q-truth if s 1 sf @ mi-block else s 2 sf @ mi-block then ;

: for-bounds ( s -- start stop step ) { s }
  s 2 sf @ { n }  s 3 sf @ { p }
  3 cells mi-alloc { b }
  n 0 ?do p i cells + @ mi-eval s" a range bound" need-int q>n b i cells + ! loop
  n 1 = if 0 b @ 1 exit then
  n 2 = if b @ b cell+ @ 1 exit then
  b @ b cell+ @ b 2 cells + @ ;

: mi-for ( s -- ) { s }
  s for-bounds { start stop step }
  step 0= if rt-head s" range() step must not be zero" mb+ mini-throw then
  start { i }
  begin step 0> if i stop < else i stop > then while
    mi-tick
    i mi-n s 0 sf s@ mini-set
    s 4 mi-for-body if exit then
    i step + to i
  repeat ;

: mi-forin ( s -- ) { s }
  s 2 sf @ mi-eval { arr }
  arr v-arr? 0= if rt-head s" '.for " mb+ s 0 sf s@ mb+ s"  in' needs an array" mb+ mini-throw then
  arr ma-copy { cp }
  cp ma-len 0 ?do
    mi-tick
    cp i ma-ref mi-copy s 0 sf s@ mini-set
    s 3 mi-for-body if unloop exit then
  loop ;

: mi-exec-impl ( s -- ) { s }
  s sn-set-pos
  mi-tick
  s @ case
    S-ASSIGN of s 3 sf @ mi-eval s 2 sf @ s 0 sf s@ mini-store endof
    S-CALLASSIGN of s mi-callassign endof
    S-EMIT of s 0 sf @ 0 ?do s 1 sf @ i cells + @ mi-eval emit-value loop endof
    S-RAISE of s mi-raise endof
    S-ECHO of s mi-echo endof
    S-CALL of s mi-call-stmt endof
    S-BREAK of 1 ctl-m ! endof
    S-CONT of 2 ctl-m ! endof
    S-RETURN of s 0 sf @ ?dup if mi-eval else 0 then mini-ret ! 3 ctl-m ! endof
    S-NONLOCAL of s mi-nonlocal endof
    S-IF of s mi-if endof
    S-WHILE of s mi-while endof
    S-FOR of s mi-for endof
    S-FORIN of s mi-forin endof
    rt-head s" bad statement" mb+ mini-throw
  endcase ;
bind mi-exec-impl mi-exec

\ 関数を走らせる。返り値は mini-ret の写し (なければ 0)
: mini-run ( f args n -- ret|0 ) { f args n }
  0 nout !  0 steps !  0 nframes !  0 ctl-m !
  fallback-names om-clear
  f mf-file drop f mf-file nip f mf-line set-rt
  f args n mi-call ;

\ ---- .call の引数 ----
: skip-str ( a u k -- k' ) { a u k }                     \ "..." の次の位置
  k 1+ to k
  begin k u < while
    a k + c@ 92 = k 1+ u < and if k 2 + to k else
      a k + c@ 34 = if k 1+ exit then
      k 1+ to k
    then
  repeat k ;

: mini-diag ( -- ) size-mode @ 0= if mb-get diag-e then ;

\ 文字列引数: エスケープは \\ \" \n \t の 4 つ。成功なら v k'、失敗なら 0 -1
lazy-sb ma-sb
: arg-str ( a u k name-a name-u -- v k' ) { a u k na nu }
  ma-sb sb-clear
  k 1+ to k
  begin
    k u >= if
      mb-reset s"  error - '.call " mb+ na nu mb+ s" ': unterminated string in the argument list." mb+ mini-diag
      0 -1 exit
    then
    a k + c@ { c }
    c 34 = if ma-sb sb$ mi-s k 1+ exit then
    c 92 = if
      k 1+ u < if a k 1+ + c@ else 0 then mini-escape 0= if
        mb-reset s"  error - '.call " mb+ na nu mb+ s" ': unknown escape in a string in the argument list." mb+ mini-diag
        0 -1 exit
      then
      ma-sb sb-c  k 2 + to k
    else c ma-sb sb-c k 1+ to k then
    false
  until
  0 -1 ;

: match-close ( a u k -- j|-1 ) { a u k }
  0 { depth } k { j }
  begin j u < while
    a j + c@ { c }
    c 34 = if a u j skip-str to j else
    c 40 = c 91 = or if depth 1+ to depth j 1+ to j else
    c 41 = c 93 = or if
      depth 1- to depth
      depth 0= if j exit then
      j 1+ to j
    else j 1+ to j then then then
  repeat -1 ;

: sym-name-at ( a u k -- ka ku e true | false ) { a u k }
  k { j }
  begin j u < if a j + c@ corec? else false then while j 1+ to j repeat
  j k = if false exit then
  a u j skip-sp-from { e }
  e u < if a e + c@ 44 <> if false exit then then
  a k + j k - e true ;

: dotword-at? ( a u k wa wu -- f ) { a u k wa wu }         \ k から `.word` + 空白 + `(` か
  k wu + u > if false exit then
  a k + wu supper wa wu str=cs 0= if false exit then
  k wu + { j }
  j u < if a j + c@ corec? else false then if false exit then
  a u j skip-sp-from { e }
  e u < if a e + c@ 40 = else false then ;

: find-ch-from ( a u from c -- idx|-1 ) { a u from c }
  from u >= if -1 exit then
  a from + u from - c find-ch { n }
  from n + u >= if -1 else from n + then ;

\ .exp( 名前 ) / .islabel( 名前 ) の名前。off は a から見た `(` までの語の長さ (4 か 8)
: var-arg-name ( a u k off -- na nu e ok ) { a u k off }
  a u k off + skip-sp-from 1+ { st }
  a u st 41 find-ch-from { e }
  e 0< if 0 0 0 false exit then
  a st + e st - strip-st { na nu }
  nu 0= if 0 0 0 false exit then
  na nu var-name? 0= if 0 0 0 false exit then
  na nu e 1+ true ;

: captext-has-label? ( a u -- f ) { a u }
  0 { i }
  begin i u < while
    a i + c@ { c }
    c 34 = c 39 = or if
      i 1+ { j }
      begin j u < if a j + c@ c <> else false then while
        a j + c@ 92 = j 1+ u < and if j 1+ to j then j 1+ to j
      repeat
      j 1+ to i
    else c 36 = if
      i 1+ u < if a i 1+ + c@ dup 36 = swap 46 = or else false then if i 2 + to i else i 1+ to i then
    else c 35 = if
      i 1+ to i
      begin i u < if a i + c@ dup alnc? over 95 = or swap 46 = or else false then while i 1+ to i repeat
    else c digc? if
      begin i u < if a i + c@ dup alnc? over 95 = or swap 46 = or else false then while i 1+ to i repeat
    else c lwc? if
      i { j }
      begin j u < if a j + c@ lwc? else false then while j 1+ to j repeat
      a i + j i - 511 min { wa wu }
      j to i
      wa wu lab-find ?dup if
        { sl }
        sl lab-equ? 0= sl lab-rtype 0>= or if true exit then
      else
        wa wu supper numsyms om-find 0= if true exit then
      then
    else i 1+ to i
    then then then then then
  repeat false ;

defer mini-arg-one ( a u k name-a name-u in-array -- v k' )

: pat-var-text ( na nu -- a u ok )
  2dup slower varnames om-find 0= if 2drop 0 0 false exit then
  false vslot vtext true ;
: arg-exp ( a u k na nu -- v k' ) { a u k na nu }
  a u k 4 var-arg-name { vn vl e ok }
  ok 0= if mb-reset s"  error - '.call " mb+ na nu mb+ s" ': '.exp' needs '.exp(variable)'." mb+ mini-diag 0 -1 exit then
  vn vl slower varnames om-find 0= if
    mb-reset s"  error - '" mb+ vn vl mb+ s" ' is not a pattern variable; '.exp(" mb+ vn vl mb+ s" )' needs '" mb+ vn vl mb+ s" ' captured in the instruction field." mb+ mini-diag
    0 -1 exit
  then
  vn vl false vslot vtext mi-s e ;
: arg-islabel ( a u k na nu -- v k' ) { a u k na nu }
  a u k 8 var-arg-name { vn vl e ok }
  ok 0= if mb-reset s"  error - '.call " mb+ na nu mb+ s" ': '.islabel' needs '.islabel(variable)'." mb+ mini-diag 0 -1 exit then
  vn vl slower varnames om-find 0= if
    mb-reset s"  error - '" mb+ vn vl mb+ s" ' is not a pattern variable; '.islabel(" mb+ vn vl mb+ s" )' needs '" mb+ vn vl mb+ s" ' captured in the instruction field." mb+ mini-diag
    0 -1 exit
  then
  vn vl false vslot vtext captext-has-label? if 1 else 0 then mi-n e ;

: arg-arrsym ( ka ku na nu -- v|0 ) { ka ku na nu }
  ka ku asym-get { arr }
  arr arr-n mi-arr { r }
  arr arr-n 0 ?do
    arr i arr-item { it }
    it item-kind 1 = if
      it item-str { ia iu }
      ma-sb sb-clear 34 ma-sb sb-c ia iu ma-sb sb+ 34 ma-sb sb-c
      ma-sb sb$ sdup 0 na nu arg-str { sv k2 }
      sv 0= if 0 unloop exit then
      sv r ma-push
    else it item-q qundef-derived? if q0 else it item-q then mi-int r ma-push then
  loop r ;

: arg-array ( a u k na nu -- v k' ) { a u k na nu }
  a u k match-close { j }
  j 0< if
    mb-reset s"  error - '.call " mb+ na nu mb+ s" ': unbalanced '[' in the argument list." mb+ mini-diag 0 -1 exit
  then
  a j + c@ 93 <> if
    mb-reset s"  error - '.call " mb+ na nu mb+ s" ': unbalanced '[' in the argument list." mb+ mini-diag 0 -1 exit
  then
  a k 1+ + j k - 1- { ia iu }
  4 mi-arr { r }  0 { i }
  begin
    ia iu i skip-sp-from to i
    i iu <
  while
    ia i + c@ 44 = if i 1+ to i else
      ia iu i na nu true mini-arg-one { v i2 }
      v 0= if 0 -1 exit then
      v r ma-push  i2 to i
      ia iu i skip-sp-from to i
      i iu < if ia i + c@ 44 = if i 1+ to i else iu to i then then
    then
  repeat
  r j 1+ ;

: arg-one-impl ( a u k na nu in-array -- v k' ) { a u k na nu inarr }
  a k + c@ 91 = if
    inarr if mb-reset s"  error - '.call " mb+ na nu mb+ s" ': an array element cannot be an array." mb+ mini-diag 0 -1 exit then
    a u k na nu arg-array exit
  then
  a k + c@ 34 = if a u k na nu arg-str exit then
  a u k s" .EXP" dotword-at? if a u k na nu arg-exp exit then
  a u k s" .ISLABEL" dotword-at? if a u k na nu arg-islabel exit then
  a u k sym-name-at if
    { ka ku e }
    ka ku supper { ua uu }
    ua uu strsyms om-find if
      ua uu ssym-get drop { sa su }
      ma-sb sb-clear 34 ma-sb sb-c sa su ma-sb sb+ 34 ma-sb sb-c
      ma-sb sb$ sdup 0 na nu arg-str drop e exit
    then
    ua uu arrsyms om-find if
      inarr if mb-reset s"  error - '.call " mb+ na nu mb+ s" ': an array element cannot be an array." mb+ mini-diag 0 -1 exit then
      ua uu na nu arg-arrsym dup 0= if -1 else e then exit
    then
  then
  a u k expr-pat { q pos }
  q qundef-derived? if q0 else q then mi-int pos ;
bind arg-one-impl mini-arg-one

\ ---- .call の実行 ----
variable mc-k
: mi-call-args ( ta tu na nu -- args n ok ) { ta tu na nu }
  0 mia-top !
  64 cells mi-alloc { args }  0 0 { n ai }
  begin
    ta tu ai skip-sp-from to ai
    ai tu <
  while
    ta ai + c@ 44 = if ai 1+ to ai else
      ta tu ai na nu false mini-arg-one { v i2 }
      v 0= if args n false exit then
      n 64 < if v args n cells + ! n 1+ to n then
      i2 to ai
      ta tu ai skip-sp-from to ai
      ai tu < if ta ai + c@ 44 = if ai 1+ to ai else tu to ai then then
    then
  repeat
  args n true ;
: mi-call-finish ( ret n0 semi drp nk -- k' ) { ret n0 semi drp nk }
  nout @ 0 ?do mout i QB * + obj+ loop
  ret if
    ret v-arr? if
      ret ma-len 0 ?do
        ret i ma-ref { el }
        el v-str? if el v-str 0 ?do dup i + c@ obj-byte loop drop else el v-q obj+ then
      loop
    else ret v-str? if ret v-str 0 ?do dup i + c@ obj-byte loop drop else ret v-q obj+ then then
  then
  nobj @ n0 - { cnt }
  drp cnt 1 = semi and if n0 obj-q q-zero? else false then or if n0 nobj ! then
  nk ;
: mini-call-impl ( a u k semi drp -- k' ) { a u k semi drp }
  k 5 + to k
  a u k skip-sp-from to k
  k { j }
  begin j u < if a j + c@ corec? else false then while j 1+ to j repeat
  a k + j k - { na nu }
  a u j skip-sp-from to k
  na nu nip 0= k u >= or if 0 else a k + c@ 40 <> then if
    mb-reset s"  error - '.call' needs 'name(argument, ...)'." mb+ mini-diag u exit
  then
  a u k match-close { e }
  e 0< if
    mb-reset s"  error - '.call " mb+ na nu mb+ s" ': unbalanced parentheses." mb+ mini-diag u exit
  then
  a k 1+ + e k 1+ - { ta tu }
  e 1+ { nk }
  na nu mfuncs om-find ?dup 0= if
    mb-reset s"  error - '.call': no function named " mb+ na nu repr1 mb+ s"  (define it with '.func::" mb+ na nu mb+ s" :: ... .endfunc')." mb+ mini-diag nk exit
  then
  @ { fn }
  ta tu na nu mi-call-args { args n ok }
  ok 0= if nk exit then
  nobj @ { n0 }
  fn args n ['] mini-run catch dup X-MINI = if
    drop mb-reset s"  error - " mb+ merr-buf merr-u @ mb+ mini-diag nk exit
  then
  throw
  n0 semi drp nk mi-call-finish ;
bind mini-call-impl mini-call
