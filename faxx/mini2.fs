\ mini2.fs -- ミニ言語: 関数の表と文の構文木

decimal

\ ---- 関数 ----
14 cells constant FNSZ
: fnf ( f i -- addr ) cells + ;
: mf-name ( f -- a u ) s@ ;
: mf-np ( f -- n ) 2 fnf @ ;
: mf-pname ( f i -- a u ) 2* cells swap 3 fnf @ + s@ ;
: mf-parent ( f -- p ) 4 fnf @ ;
: mf-children ( f -- om ) 5 fnf @ ;
: mf-body ( f -- b|0 ) 10 fnf @ ;
: mf-file ( f -- a u ) 11 fnf 2@ swap ;
: mf-line ( f -- ln ) 13 fnf @ ;

1 om-new constant mfuncs                      \ 名前 -> func ptr (トップレベル)
create fstk 64 cells allot
variable fs-n

: mf-new ( na nu params-ptr np parent fa fu ln -- f ) { na nu pp np parent fa fu ln }
  FNSZ allocate throw { f } f FNSZ erase
  na nu pstr f s!  np f 2 fnf !  pp f 3 fnf !  parent f 4 fnf !
  1 om-new f 5 fnf !
  64 5 * cells allocate throw f 6 fnf !  0 f 7 fnf !  64 f 8 fnf !
  fa fu pstr f 11 fnf s! ln f 13 fnf !
  f ;
: mf-add-line ( a u fa fu ln f -- ) { a u fa fu ln f }
  f 7 fnf @ f 8 fnf @ >= if
    f 8 fnf @ 2* f 8 fnf !
    f 6 fnf @ f 8 fnf @ 5 * cells resize throw f 6 fnf !
  then
  f 6 fnf @ f 7 fnf @ 5 * cells + { e }
  a u pstr e s!  fa fu pstr e 2 cells + s!  ln e 4 cells + !
  1 f 7 fnf +! ;
: mf-line@ ( f i -- a u fa fu ln ) { f i }
  f 6 fnf @ i 5 * cells + { e }
  e s@ e 2 cells + s@ e 4 cells + @ ;

\ ---- `.func` のヘッダ ----
: hdr-ident-end ( a u i -- j ) { a u i }
  begin i u < if a i + c@ mini-name-char? else false then while i 1+ to i repeat i ;
: skip-sp-from ( a u i -- i' ) { a u i } begin i u < if a i + c@ dup 32 = swap 9 = or else false then while i 1+ to i repeat i ;
create fh-pn 32 2 * cells allot
variable fh-np  variable fh-name-a  variable fh-name-u  variable fh-err  variable fh-eu

: fh-add-param ( a u -- )
  strip-st dup 0= if 2drop exit then
  fh-np @ 32 >= if 2drop exit then
  pstr fh-np @ 2 * cells fh-pn + s!  1 fh-np +! ;
: fh-split-params ( a u -- )                  \ カンマで割って strip して空は飛ばす
  { a u } 0 { st }
  u 1+ 0 ?do
    i u = if true else a i + c@ 44 = then if a st + i st - fh-add-param  i 1+ to st then
  loop ;

create hf-a 8 cells allot  create hf-u 8 cells allot
variable hf-n
: hdr-fields ( a u -- )                          \ `::` で割る (欄は最大 8)
  { t n } 0 hf-n !  0 { hi }
  begin
    t n hi skip-sp-from to hi
    hi { st }
    begin hi n < if t hi + 2 s" ::" str=cs 0= else false then while hi 1+ to hi repeat
    hf-n @ 8 < if t st + hi st - rstrip-st hf-n @ cells hf-u + ! hf-n @ cells hf-a + ! 1 hf-n +! else 2drop then
    hi n < if hi 2 + to hi then
    n hi <=
  until ;

\ 名前・引数・エラーを fh-* に
: parse-old-header ( a u -- )
  hdr-fields
  hf-n @ 1 > if 1 cells hf-a + @ 1 cells hf-u + @ strip-st else s" " then pstr fh-name-u ! fh-name-a !
  hf-n @ 2 > if 2 cells hf-a + @ 2 cells hf-u + @ fh-split-params then ;

: parse-func-header ( a u -- ) strip-st { t n }
  0 fh-err !  0 fh-np !  0 fh-name-u !  0 fh-name-a !
  t n 1 hdr-ident-end { i0 }
  t n i0 skip-sp-from { ix }
  ix 1+ n < if t ix + 2 s" ::" str=cs else false then if t n parse-old-header exit then
  t n ix hdr-ident-end { j }
  t ix + j ix - pstr fh-name-u ! fh-name-a !
  t n j skip-sp-from { k }
  k n >= if exit then
  t k + c@ 40 <> if
    mb-reset s"  error - '.func': expected '(' or end of line after the name, got " mb+ t k + n k - repr1 mb+ mb-get pstr fh-eu ! fh-err ! exit
  then
  -1 { e } n 0 ?do t n 1- i - + c@ 41 = if n 1- i - to e leave then loop
  e k < if s"  error - '.func': missing closing ')' in the parameter list." pstr fh-eu ! fh-err ! exit then
  t e 1+ + n e 1+ - strip-st nip if
    mb-reset s"  error - '.func': trailing text after ')': " mb+ t e 1+ + n e 1+ - strip-st repr1 mb+ mb-get pstr fh-eu ! fh-err ! exit
  then
  t k 1+ + e k 1+ - fh-split-params ;

\ ---- 文の構文木 ----
12 cells constant SNSZ
1 constant S-ASSIGN  2 constant S-CALLASSIGN  3 constant S-EMIT  4 constant S-RAISE  5 constant S-ECHO
6 constant S-CALL  7 constant S-BREAK  8 constant S-CONT  9 constant S-RETURN  10 constant S-NONLOCAL
11 constant S-IF  12 constant S-WHILE  13 constant S-FOR  14 constant S-FORIN  15 constant S-ASSIGNSL
16 constant E-SLICET

variable mp-loop  variable mp-nest
variable mp-ln-tab  variable mp-ln-n                \ 構文解析中の関数の行
: sn-new ( kind fa fu ln -- s ) { kind fa fu ln }
  SNSZ allocate throw { s } s SNSZ erase
  kind s !  fa s cell+ !  fu s 2 cells + !  ln s 3 cells + !  s ;
: sf ( s i -- addr ) 4 + cells + ;
: sn-pos ( s -- fa fu ln ) dup cell+ @ over 2 cells + @ rot 3 cells + @ ;

create sbt 65536 cells allot
variable sbt-n
: sbt-mark ( -- m ) sbt-n @ ;
: sbt-push ( s -- ) sbt-n @ 65536 >= abort" mini block too large" sbt sbt-n @ cells + !  1 sbt-n +! ;
: sbt-finish ( m -- blk ) { m }
  sbt-n @ m - { n }
  n 1+ pcells { b }  n b !
  n 0 ?do sbt m i + cells + @ b i 1+ cells + ! loop
  m sbt-n !  b ;

: ml-text ( i -- a u ) 5 * cells mp-ln-tab @ + s@ ;
: ml-pos ( i -- fa fu ln ) 5 * cells mp-ln-tab @ + dup 2 cells + s@ rot 4 cells + @ ;
: ml-kw ( i -- ka ku ) ml-text dot-kw ;

: ender? ( i enders -- f )                           \ i 行目のキーワードが enders のどれか
  { i en }
  i ml-kw { ka ku }
  ka ku s" .ELIF" str=cs en 1 and 0<> and if true exit then
  ka ku s" .ELSE" str=cs en 2 and 0<> and if true exit then
  ka ku s" .ENDIF" str=cs en 4 and 0<> and if true exit then
  ka ku s" .NEXT" str=cs en 8 and 0<> and if true exit then
  ka ku s" .ENDWHILE" str=cs en 16 and 0<> and if true exit then
  false ;
: any-ender? ( ka ku -- f )
  2dup s" .ELIF" str=cs >r 2dup s" .ELSE" str=cs r> or >r 2dup s" .ENDIF" str=cs r> or >r
  2dup s" .NEXT" str=cs r> or >r s" .ENDWHILE" str=cs r> or ;

: mini-nest ( i -- ) 1 mp-nest +!
  mp-nest @ 1000 > if
    ml-pos mfail-pos s" '.if'/'.while'/'.for' blocks nest too deeply (more than 1000 levels)" mb+ mini-throw
  then drop ;

\ 行 i をトークンにする
: lex-line ( i -- ) dup ml-text rot ml-pos mini-lex ;

variable ts-fa variable ts-fu variable ts-ln
: set-pos ( fa fu ln -- ) { fa fu ln } fa ps-fa ! fu ps-fu ! ln ps-ln ! fa ts-fa ! fu ts-fu ! ln ts-ln ! ;

defer parse-mblock ( i enders -- blk i' )

\ 引数リスト `( e, e )` を読む: ( -- n ptr )  '(' は消費済みと別に呼び出し側
: xp-paren-list ( -- n ptr ) s" (" xp-expect-op xp-list { n p } s" )" xp-expect-op n p ;

: simple-return ( -- s ) ;

: make-sn ( kind -- s ) ts-fa @ ts-fu @ ts-ln @ sn-new ;

: ps-call-tail ( from -- na nu n ptr )               \ .call 名(引数...)
  xp-start
  xp-peek-kind 2 <> if ps-err-head s" '.call' needs a function name" mb+ mini-throw then
  xp-peek-s pstr { na nu } 1 xp-i +!
  s" (" xp-expect-op xp-list { n p } s" )" xp-expect-op
  xp-at-end? 0= if ps-err-head s" unexpected text after '.call'" mb+ mini-throw then
  na nu n p ;

: ps-dot-return ( -- s )
  S-RETURN make-sn { s }
  ntok @ 1 > if 1 xp-start xp-parse-all s 0 sf ! else 0 s 0 sf ! then s ;
: ps-dot-raise ( -- s )
  ntok @ 1 <= if ps-err-head s" '.raise' needs an error code" mb+ mini-throw then
  S-RAISE make-sn { s }  1 xp-start xp-parse-all s 0 sf !  s ;
: ps-dot-emit ( -- s )
  1 xp-start xp-paren-list { n p }
  xp-at-end? 0= if ps-err-head s" unexpected text after '.emit(...)'" mb+ mini-throw then
  n 0= if ps-err-head s" '.emit' needs at least one value" mb+ mini-throw then
  S-EMIT make-sn { s }  n s 0 sf !  p s 1 sf !  s ;
: ps-dot-echo ( -- s )
  1 xp-start xp-paren-list { n p }
  xp-at-end? 0= if ps-err-head s" unexpected text after '.echo(...)'" mb+ mini-throw then
  S-ECHO make-sn { s }  n s 0 sf !  p s 1 sf !  s ;
: ps-dot-break ( kw-a kw-u -- s ) { ka ku }
  ntok @ 1 <> if ps-err-head s" unexpected text after '" mb+ ka ku slower mb+ s" '" mb+ mini-throw then
  mp-loop @ 0<= if
    ps-err-head s" '" mb+ ka ku slower mb+ s" ' must be inside a '.while' or '.for' loop" mb+ mini-throw
  then
  ka ku s" .BREAK" str=cs if S-BREAK else S-CONT then make-sn ;
: ps-dot-call ( -- s )
  1 ps-call-tail { na nu n p }
  S-CALL make-sn { s }  na nu s 0 sf s!  n s 2 sf !  p s 3 sf !  s ;
: ps-dot-nonlocal ( -- s )
  32 2 * pcells { names } 0 { cnt } 1 { j }
  begin j ntok @ < while
    j tk-kind 2 <> if ps-err-head s" '.nonlocal' needs variable names" mb+ mini-throw then
    j tk-s pstr cnt 2 * cells names + s!  cnt 1+ to cnt  j 1+ to j
    j ntok @ < if
      j tk-kind 6 <> j tk-s s" ," str=cs 0= or if ps-err-head s" '.nonlocal' names must be separated by ','" mb+ mini-throw then
      j 1+ to j
    then
  repeat
  cnt 0= if ps-err-head s" '.nonlocal' needs variable names" mb+ mini-throw then
  S-NONLOCAL make-sn { s }  cnt s 0 sf !  names s 1 sf !  s ;

: ps-dot ( -- s ) 0 tk-s { va vu }
  va vu s" .RETURN" str=cs if ps-dot-return exit then
  va vu s" .RAISE" str=cs if ps-dot-raise exit then
  va vu s" .EMIT" str=cs if ps-dot-emit exit then
  va vu s" .ECHO" str=cs if ps-dot-echo exit then
  va vu s" .BREAK" str=cs va vu s" .CONTINUE" str=cs or if va vu ps-dot-break exit then
  va vu s" .CALL" str=cs if ps-dot-call exit then
  va vu s" .NONLOCAL" str=cs if ps-dot-nonlocal exit then
  ps-err-head s" unknown statement " mb+ va vu slower repr1 mb+ mini-throw 0 ;

\ 代入 `名前[添字] = 値` / `名前 = .call f(...)`
: ps-assign ( -- s ) 0 tk-s pstr { na nu }
  1 xp-start
  0 { idx }
  s" [" xp-at-op? if
    1 xp-i +!
    0 0 { lo hi }
    s" :" xp-at-op? 0= if xp-or to lo then
    s" :" xp-eat-op if
      s" ]" xp-at-op? 0= if xp-or to hi then
      E-SLICET en-new! { sl } lo sl 0 ef ! hi sl 1 ef ! sl to idx
    else lo to idx then
    s" ]" xp-expect-op
  then
  s" =" xp-expect-op
  xp-i @ { from }
  from ntok @ < if from tk-kind 3 = from tk-s s" .CALL" str=cs and else false then if
    from 1+ ps-call-tail { fa fu n p }
    S-CALLASSIGN make-sn { s }
    na nu s 0 sf s!  idx s 2 sf !  fa fu s 3 sf s!  n s 5 sf !  p s 6 sf !  s exit
  then
  xp-parse-all { val }
  S-ASSIGN make-sn { s }  na nu s 0 sf s!  idx s 2 sf !  val s 3 sf !  s ;

: ps-simple ( i -- s ) { i }
  i ml-pos set-pos
  i lex-line
  ntok @ 0= if ps-err-head s" empty statement" mb+ mini-throw then
  0 tk-kind 3 = if ps-dot exit then
  0 tk-kind 2 <> if ps-err-head s" statement must be a directive or an assignment" mb+ mini-throw then
  ps-assign ;

: mini-err ( i -- ) ml-pos mfail-pos ;

\ ---- .if ----
variable if-d
: ps-if-header ( i -- cond )                       \ .if / .elif の条件
  { i }
  i ml-pos set-pos
  i lex-line
  i mini-nest
  ntok @ 0= if true else ntok @ 1- tk-kind 3 <> ntok @ 1- tk-s s" .THEN" str=cs 0= or then if
    i mini-err i ml-kw slower mb+ s"  must end with '.then'" mb+ mini-throw
  then
  -1 ntok +!  1 xp-start xp-parse-all ;
: empty-block ( -- b ) 1 pcells { b } 0 b ! b ;
: ps-if-else ( ni fa fu ln -- else-b ni' ) { ni fa fu ln }
  ni ml-pos set-pos ni lex-line
  ntok @ 1 > if ni mini-err s" unexpected text after '.else'" mb+ mini-throw then
  ni 1+ 4 parse-mblock { eb ni2 }
  ni2 mp-ln-n @ >= if fa fu ln mfail-pos s" '.if' is never closed with '.endif'" mb+ mini-throw then
  eb ni2 ;
: ps-if-chain ( i -- node i' ) { i }
  i ml-pos { fa fu ln }
  i ps-if-header { cond }
  i 1+ 7 parse-mblock { then-b ni }
  ni mp-ln-n @ >= if fa fu ln mfail-pos s" '.if' is never closed with '.endif'" mb+ mini-throw then
  ni ml-kw { nka nku }
  empty-block { else-b }
  nka nku s" .ELIF" str=cs if
    ni recurse to ni { e2 }
    sbt-mark { m } e2 sbt-push m sbt-finish to else-b
  else nka nku s" .ELSE" str=cs if
    ni fa fu ln ps-if-else to ni to else-b
  then then
  -1 mp-nest +!
  S-IF fa fu ln sn-new { s }
  cond s 0 sf !  then-b s 1 sf !  else-b s 2 sf !  s ni ;

\ ---- .for のヘッダ ----
: ps-for-header ( i -- kind var-a var-u a b ) { i }
  i ml-pos set-pos  i lex-line
  ntok @ 4 < if 1 tk-kind 2 <> else true then if
    i mini-err s" '.for' needs 'variable in range(...)' or 'variable in array'" mb+ mini-throw
  then
  1 tk-s pstr { va vu }
  2 tk-kind 2 <> 2 tk-s s" in" str=cs 0= or if
    i mini-err s" '.for " mb+ va vu mb+ s" ' must be followed by 'in range(...)' or 'in array'" mb+ mini-throw
  then
  3 tk-kind 2 <> 3 tk-s s" range" str=cs 0= or ntok @ 5 < or if
    true
  else 4 tk-kind 6 <> 4 tk-s s" (" str=cs 0= or then if
    3 xp-start xp-parse-all { e }
    14 va vu e 0 exit                              \ forin: kind 14
  then
  4 xp-start
  s" (" xp-expect-op xp-list { n p } s" )" xp-expect-op
  xp-at-end? 0= if i mini-err s" unexpected text after 'range(...)'" mb+ mini-throw then
  n 1 < n 3 > or if i mini-err s" range() takes 1 to 3 arguments, got " mb+ n mb-n mini-throw then
  13 va vu n p ;
: ps-for ( i -- node i' ) { i }
  i ml-pos { fa fu ln }
  i mini-nest
  i ps-for-header { kind va vu a b }
  1 mp-loop +!
  i 1+ 8 parse-mblock { body ni }
  -1 mp-loop +!
  ni mp-ln-n @ >= if fa fu ln mfail-pos s" '.for' is never closed with '.next'" mb+ mini-throw then
  -1 mp-nest +!
  kind fa fu ln sn-new { s }
  va vu s 0 sf s!
  kind 13 = if a s 2 sf !  b s 3 sf !  body s 4 sf !  else a s 2 sf !  body s 3 sf ! then
  s ni ;
: ps-while ( i -- node i' ) { i }
  i ml-pos { fa fu ln }
  i mini-nest
  i ml-pos set-pos  i lex-line
  1 xp-start xp-parse-all { cond }
  1 mp-loop +!
  i 1+ 16 parse-mblock { body ni }
  -1 mp-loop +!
  ni mp-ln-n @ >= if fa fu ln mfail-pos s" '.while' is never closed with '.endwhile'" mb+ mini-throw then
  -1 mp-nest +!
  S-WHILE fa fu ln sn-new { s }  cond s 0 sf !  body s 1 sf !  s ni ;

: parse-mblock-impl ( i enders -- blk i' ) { i en }
  sbt-mark { m }
  begin i mp-ln-n @ < while
    i en ender? if m sbt-finish i exit then
    i ml-kw { ka ku }
    ka ku any-ender? if
      i mini-err s" '" mb+ ka ku slower mb+ s" ' without a matching opener" mb+ mini-throw
    then
    ka ku s" .IF" str=cs if i ps-if-chain 1+ to i sbt-push else
    ka ku s" .WHILE" str=cs if i ps-while 1+ to i sbt-push else
    ka ku s" .FOR" str=cs if i ps-for 1+ to i sbt-push else
      i ps-simple sbt-push i 1+ to i
    then then then
  repeat
  m sbt-finish i ;
' parse-mblock-impl is parse-mblock

\ ---- 関数の本体の構文解析 ----
: parse-func-body ( f -- ) { f }
  f 6 fnf @ mp-ln-tab !  f 7 fnf @ mp-ln-n !
  0 mp-loop !  0 mp-nest !  0 sbt-n !  0 ntok !
  0 0 parse-mblock { b ni }
  ni mp-ln-n @ < if
    ni ml-pos mfail-pos s" '" mb+ ni ml-text strip-st mb+ s" ' has no matching opener" mb+ mini-throw
  then
  b f 10 fnf ! ;

: mini-text-report ( -- ) mb-reset s"  error - " mb+ merr-buf merr-u @ mb+ mb-get diag-e ;
: walk-compile ( om -- ) { om }
  om om-used 0 ?do
    i om om-live? if
      i om om-val @ { f }
      f ['] parse-func-body catch dup X-MINI = if
        drop mini-text-report  empty-block f 10 fnf !
      else dup if throw else drop then then
      f mf-children recurse
    then
  loop ;
: compile-funcs ( -- ) mfuncs walk-compile ;

\ ---- パターンファイルの読み込みからの口 ----
: ident-name? ( a u -- f ) { a u }
  u 0= if false exit then
  u 0 ?do a i + c@ dup aln? swap 95 = or 0= if false unloop exit then loop true ;

: fs-push ( f -- ) fstk fs-n @ cells + !  1 fs-n +! ;
variable fr-fa variable fr-fu variable fr-ln
: dummy-func ( parent -- ) { parent }
  s" ?" 0 0 parent fr-fa @ fr-fu @ fr-ln @ mf-new fs-push ;
: fn-register-new ( parent -- ) { parent }
  fh-err @ if fh-err @ fh-eu @ diag-e parent dummy-func exit then
  fh-name-a @ fh-name-u @ ident-name? 0= if
    mb-reset s"  error - '.func' needs a name made of letters, digits and '_': " mb+ fh-name-a @ fh-name-u @ repr1 mb+ mb-get diag-e
    parent dummy-func exit
  then
  false { bad }
  fh-np @ 0 ?do
    bad 0= if
      i 2 * cells fh-pn + s@ ident-name? 0= if
        mb-reset s"  error - '.func " mb+ fh-name-a @ fh-name-u @ mb+ s" ': bad parameter name " mb+ i 2 * cells fh-pn + s@ repr1 mb+ mb-get diag-e
        true to bad
      then
    then
  loop
  bad if parent dummy-func exit then
  fh-np @ 2 * 1 max cells pcells { pp }  fh-pn pp fh-np @ 2 * cells move
  fh-name-a @ fh-name-u @ pp fh-np @ parent fr-fa @ fr-fu @ fr-ln @ mf-new { f }
  parent if parent mf-children else mfuncs then { tab }
  fh-name-a @ fh-name-u @ tab om-find if
    mb-reset s"  warning - function " mb+ fh-name-a @ fh-name-u @ repr1 mb+
    s"  is defined more than once; the later definition wins." mb+ mb-get diag-w
  then
  fh-name-a @ fh-name-u @ tab om-put f swap !
  f fs-push ;

: fs-top ( -- f ) fstk fs-n @ 1- cells + @ ;
: mini-open? ( ka ku -- f ) 2dup s" .IF" str=cs >r 2dup s" .FOR" str=cs r> or >r s" .WHILE" str=cs r> or ;
: mini-close? ( ka ku -- f ) 2dup s" .ENDIF" str=cs >r 2dup s" .NEXT" str=cs r> or >r s" .ENDWHILE" str=cs r> or ;

\ pat-line から: 関数の中、または `.func` の行
: func-handle-impl ( ra ru ka ku fa fu ln -- ) { ra ru ka ku fa fu ln }
  fa fr-fa ! fu fr-fu ! ln fr-ln !
  ka ku s" .FUNC" str=cs if
    ra ru parse-func-header
    fs-n @ 0> if fs-top else 0 then fn-register-new
    exit
  then
  fs-top { cur }
  ka ku s" .ENDFUNC" str=cs if
    cur 9 fnf @ 0<> if
      mb-reset s"  error - '.func " mb+ cur mf-name mb+ s" ': '.endfunc' while a block ('.if'/'.while'/'.for') is still open." mb+ mb-get diag-e
    then
    -1 fs-n +!  exit
  then
  ka ku mini-open? if 1 cur 9 fnf +! else
  ka ku mini-close? if
    -1 cur 9 fnf +!
    cur 9 fnf @ 0< if
      mb-reset s"  error - '.func::" mb+ cur mf-name mb+ s" ': " mb+ ka ku slower mb+ s"  without a matching block opener." mb+ mb-get diag-e
      0 cur 9 fnf !
    then
  then then
  ra ru strip-st nip if ra ru fa fu ln cur mf-add-line then ;
' func-handle-impl is func-handle
: mini-func-active? ( -- f ) fs-n @ 0<> ;
: mini-func-end-file ( fa fu -- )
  begin fs-n @ 0> while
    fs-top { f }
    2dup mb-reset s"  error - pattern file '" mb+ mb+ s" ' ends while function " mb+ f mf-name repr1 mb+
    s"  is still open (missing '.endfunc')." mb+ mb-get diag-e
    -1 fs-n +!
  repeat 2drop ;

' mini-func-active? is func-active?
' mini-func-end-file is func-end-file
: mini-func-reset ( -- ) mfuncs om-clear 0 fs-n ! ;
' mini-func-reset is pat-func-reset
' compile-funcs is pat-func-compile
