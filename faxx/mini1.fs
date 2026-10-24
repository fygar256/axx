\ mini1.fs -- ミニ言語 (.func): 字句、式の構文木、文の構文木

decimal

-5101 constant X-MINI
: mini-fail-pos ( fa fu ln -- ) mfail-pos ;
: mini-throw ( -- ) mb-get dup 8191 min merr-u ! merr-buf swap move X-MINI throw ;

\ ---- 永続の領域 ----
: pcells ( n -- a ) cells allocate throw ;
: pstr ( a u -- a' u ) hdup ;

\ ---- トークン ----
\ 種類: 0 end 1 num 2 name 3 dot 4 core 5 str 6 op
7 cells constant TKSZ
4096 constant MAXTOK
MAXTOK TKSZ * allocate throw constant toks
variable ntok
variable ps-fa  variable ps-fu  variable ps-ln              \ 診断に出す位置

: ps-err-head ( -- ) ps-fa @ ps-fu @ ps-ln @ mini-fail-pos ;
: tk ( i -- a ) TKSZ * toks + ;
: tk-kind ( i -- k ) tk @ ;
: tk-s ( i -- a u ) tk cell+ s@ ;
: tk-q ( i -- q ) tk 3 cells + ;
: tk-add ( kind a u -- ) { kind a u }
  ntok @ MAXTOK >= if ps-err-head s" line too long" mb+ mini-throw then
  ntok @ tk { t }
  kind t !  a u t cell+ s!  t 3 cells + QB erase
  1 ntok +! ;

: alpha? ( c -- f ) dup 65 91 within swap 97 123 within or ;
: aln? ( c -- f ) dup alpha? swap digc? or ;
: mini-name-char? ( c -- f ) dup aln? swap 95 = or ;

: mini-hexnum ( a u i -- q j ) { a u i }                    \ 0x...
  i 2 + { j } q0 { v }
  begin j u < if a j + c@ dup xdig? swap 95 = or else false then while
    a j + c@ 95 <> if v 16 0 q*small+ drop to v  v a j + c@ hexv qn q+ to v then
    j 1+ to j
  repeat
  j i 2 + = if ps-err-head s" malformed hex number" mb+ mini-throw then
  v j ;
: mini-binnum ( a u i -- q j ) { a u i }
  i 2 + { j } q0 { v }
  begin j u < if a j + c@ dup 48 = over 49 = or swap 95 = or else false then while
    a j + c@ 95 <> if v 2 0 q*small+ drop to v  v a j + c@ 48 - qn q+ to v then
    j 1+ to j
  repeat
  j i 2 + = if ps-err-head s" malformed binary number" mb+ mini-throw then
  v j ;
: mini-decnum ( a u i -- q j ) { a u i }
  i { j } q0 { v }
  begin j u < if a j + c@ dup digc? swap 95 = or else false then while
    a j + c@ 95 <> if v 10 0 q*small+ drop to v  v a j + c@ 48 - qn q+ to v then
    j 1+ to j
  repeat
  v j ;

sb-new constant ms-sb
: mini-escape ( c -- c' true | false )
  dup 92 = if drop 92 true exit then
  dup 34 = if drop 34 true exit then
  dup 110 = if drop 10 true exit then
  dup 116 = if drop 9 true exit then
  drop false ;
: mini-lex-str ( a u i -- bytes-a bytes-u j ) { a u i }
  ms-sb sb-clear
  i 1+ { j }
  begin
    j u >= if ps-err-head s" unterminated string" mb+ mini-throw then
    a j + c@ { ch }
    ch 34 = if j 1+ to j true else
    ch 92 = if
      j 1+ u >= if ps-err-head s" unterminated string" mb+ mini-throw then
      a j 1+ + c@ { e }
      e mini-escape 0= if ps-err-head s" unknown escape '\" mb+ e mb-c s" ' in a string" mb+ mini-throw then
      ms-sb sb-c  j 2 + to j false
    else ch ms-sb sb-c j 1+ to j false then then
  until
  ms-sb sb$ pstr j ;

: op2? ( a u i -- f ) { a u i }
  i 1+ u >= if false exit then
  a i + c@ { c1 }  a i 1+ + c@ { c2 }
  c1 42 = c2 42 = and c1 60 = c2 60 = and or c1 62 = c2 62 = and or
  c1 60 = c2 61 = and or c1 62 = c2 61 = and or c1 61 = c2 61 = and or
  c1 33 = c2 61 = and or c1 38 = c2 38 = and or c1 124 = c2 124 = and or ;
: op1? ( c -- f ) s" +-*/%&|^~<>!()[]:,=" rot has-ch? ;

: lex-num ( a u i -- i' ) { a u i }
  a i + c@ 48 = i 1+ u < and if
    a i 1+ + c@ dup 120 = swap 88 = or if a u i mini-hexnum { j } { q } 1 0 0 tk-add ntok @ 1- tk-q q swap q! j exit then
    a i 1+ + c@ dup 98 = swap 66 = or if a u i mini-binnum { j } { q } 1 0 0 tk-add ntok @ 1- tk-q q swap q! j exit then
  then
  a u i mini-decnum { j } { q } 1 0 0 tk-add ntok @ 1- tk-q q swap q! j ;
: lex-name ( a u i -- i' ) { a u i }
  i { st }
  begin i u < if a i + c@ mini-name-char? else false then while i 1+ to i repeat
  2 a st + i st - tk-add  i ;
: lex-dot ( a u i -- i' ) { a u i }
  i 1+ { j }
  begin j u < if a j + c@ mini-name-char? else false then while j 1+ to j repeat
  j i 1+ = if ps-err-head s" stray '.'" mb+ mini-throw then
  3 a i + j i - supper pstr tk-add  j ;
: lex-dollar ( a u i -- i' ) { a u i }
  i 1+ u < if a i 1+ + c@ dup 36 = swap 46 = or else false then if
    4 a i + 2 tk-add  i 2 + exit
  then
  ps-err-head s" '$' must be written '$$' (location counter) or '$.' (start of the next instruction)" mb+ mini-throw 0 ;
: lex-hash ( a u i -- i' ) { a u i }
  i 1+ { j }
  begin j u < if a j + c@ dup aln? over 95 = or over 46 = or swap 36 = or else false then while j 1+ to j repeat
  j i 1+ = if ps-err-head s" '#' needs a symbol name" mb+ mini-throw then
  4 a i + j i - tk-add  j ;
: lex-one ( a u i -- i' ) { a u i }
  a i + c@ { c }
  c 32 = c 9 = or if i 1+ exit then
  c digc? if a u i lex-num exit then
  c alpha? c 95 = or if a u i lex-name exit then
  c 46 = if a u i lex-dot exit then
  c 36 = if a u i lex-dollar exit then
  c 35 = if a u i lex-hash exit then
  c 34 = if a u i mini-lex-str { j } { ba bu } 5 ba bu tk-add j exit then
  a u i op2? if 6 a i + 2 tk-add  i 2 + exit then
  c op1? if 6 a i + 1 tk-add  i 1+ exit then
  ps-err-head s" unexpected character '" mb+ c mb-c s" '" mb+ mini-throw 0 ;
: mini-lex ( a u fa fu ln -- ) { a u fa fu ln }
  fa ps-fa ! fu ps-fu ! ln ps-ln !
  0 ntok !
  0 { i }
  begin i u < while a u i lex-one to i repeat ;

\ ---- 式の構文木 ----
6 cells constant ENSZ
1 constant E-NUM  2 constant E-STR  3 constant E-CORE 4 constant E-VAR  5 constant E-ARR  6 constant E-CALL
7 constant E-LEN  8 constant E-TOSTR 9 constant E-CHR 10 constant E-TOINT 11 constant E-INDEX 12 constant E-SLICE
13 constant E-UN  14 constant E-BIN

: en-new! ( kind -- e ) { k } ENSZ allocate throw { e } e ENSZ erase k e ! e ;
: ef ( e i -- addr ) 1+ cells + ;

variable xp-i  variable xp-depth
: xp-peek-kind ( -- k ) xp-i @ ntok @ < if xp-i @ tk-kind else 0 then ;
: xp-peek-s ( -- a u ) xp-i @ ntok @ < if xp-i @ tk-s else 0 0 then ;
: xp-at-end? ( -- f ) xp-i @ ntok @ >= ;
: xp-at-op? ( a u -- f ) xp-peek-kind 6 = if xp-peek-s 2swap str=cs else 2drop false then ;
: xp-eat-op ( a u -- f ) 2dup xp-at-op? if 2drop 1 xp-i +! true else 2drop false then ;
: tok-desc ( -- ) xp-peek-kind case
    0 of s" 'end of line'" mb+ endof
    1 of xp-i @ tk-q q>dec mb+ endof
    5 of 39 mb-c xp-peek-s mb+ 39 mb-c endof
    drop xp-peek-s repr1 mb+
  endcase ;
: xp-fail ( -- ) mini-throw ;
: xp-expect-op ( a u -- ) 2dup xp-eat-op if 2drop else
  ps-err-head s" expected " mb+ 2dup repr1 mb+ s" , found " mb+ tok-desc 2drop xp-fail then ;
: xp-enter ( -- ) 1 xp-depth +!  xp-depth @ 1000 > if ps-err-head s" expression nests too deeply (more than 1000 levels)" mb+ xp-fail then ;

defer xp-or

: xp-bin ( opid l r -- e ) { opid l r } E-BIN en-new! { e } opid e 0 ef ! l e 1 ef ! r e 2 ef ! e ;
: xp-un ( opc c -- e ) { opc c } E-UN en-new! { e } opc e 0 ef ! c e 1 ef ! e ;

: xp-list ( -- n ptr )                           \ カンマ区切りの式 (閉じ括弧の手前まで)
  64 pcells { arr } 0 { n }
  s" )" xp-at-op? 0= if
    xp-or arr n cells + !  n 1+ to n
    begin s" ," xp-eat-op while
      n 64 >= if ps-err-head s" too many arguments" mb+ xp-fail then
      xp-or arr n cells + !  n 1+ to n
    repeat
  then
  n arr ;

: xp-primary ( -- e ) xp-peek-kind { k }
  k 5 = if xp-peek-s E-STR en-new! { e } e 0 ef s! 1 xp-i +! e exit then
  k 4 = if xp-peek-s E-CORE en-new! { e } e 0 ef s! 1 xp-i +! e exit then
  k 1 = if E-NUM en-new! { e } xp-i @ tk-q e 0 ef q! 1 xp-i +! e exit then
  k 2 = if xp-peek-s E-VAR en-new! { e } e 0 ef s! 1 xp-i +! e exit then
  k 3 = if
    xp-peek-s { da du }
    da du s" .LEN" str=cs da du s" .STR" str=cs or da du s" .CHR" str=cs or da du s" .INT" str=cs or if
      da du s" .LEN" str=cs if E-LEN else da du s" .STR" str=cs if E-TOSTR else da du s" .CHR" str=cs if E-CHR else E-TOINT then then then
      { kind }
      1 xp-i +!  s" (" xp-expect-op xp-or { c } s" )" xp-expect-op
      kind en-new! { e } c e 0 ef ! e exit
    then
    da du s" .CALL" str=cs if
      1 xp-i +!
      xp-peek-kind 2 <> if ps-err-head s" '.call' needs a function name" mb+ xp-fail then
      xp-peek-s pstr { na nu } 1 xp-i +!
      s" (" xp-expect-op xp-list { n arr } s" )" xp-expect-op
      E-CALL en-new! { e } na nu e 0 ef s! n e 2 ef ! arr e 3 ef ! e exit
    then
    ps-err-head da du slower mb+ s"  cannot be used in an expression" mb+ xp-fail
  then
  k 6 = xp-peek-s s" (" str=cs and if 1 xp-i +! xp-or s" )" xp-expect-op exit then
  k 6 = xp-peek-s s" [" str=cs and if
    1 xp-i +!
    64 pcells { arr } 0 { n }
    s" ]" xp-at-op? 0= if
      xp-or arr n cells + !  n 1+ to n
      begin s" ," xp-eat-op while xp-or arr n cells + !  n 1+ to n repeat
    then
    s" ]" xp-expect-op
    E-ARR en-new! { e } n e 0 ef ! arr e 1 ef ! e exit
  then
  ps-err-head s" expected a value, found " mb+ tok-desc xp-fail 0 ;

: xp-postfix ( -- e ) xp-primary
  begin s" [" xp-at-op? while
    1 xp-i +!
    { base } 0 0 { lo hi }
    s" :" xp-at-op? 0= if xp-or to lo then
    s" :" xp-eat-op if
      s" ]" xp-at-op? 0= if xp-or to hi then
      s" ]" xp-expect-op
      E-SLICE en-new! { e } base e 0 ef ! lo e 1 ef ! hi e 2 ef ! e
    else
      s" ]" xp-expect-op
      lo 0= if ps-err-head s" empty subscript" mb+ xp-fail then
      E-INDEX en-new! { e } base e 0 ef ! lo e 1 ef ! e
    then
  repeat ;

defer xp-unary
: xp-power ( -- e ) xp-postfix
  s" **" xp-at-op? if 1 xp-i +! { l } 19 l xp-unary xp-bin then ;
: xp-unary-impl ( -- e )
  s" -" xp-at-op? s" +" xp-at-op? or s" ~" xp-at-op? or if
    xp-peek-s drop c@ { opc } 1 xp-i +!
    xp-enter xp-unary opc swap xp-un -1 xp-depth +! exit
  then
  xp-power ;
' xp-unary-impl is xp-unary
: xp-mul ( -- e ) xp-unary
  begin s" *" xp-at-op? s" /" xp-at-op? or s" %" xp-at-op? or while
    xp-peek-s drop c@ { c } 1 xp-i +!
    c 42 = if 16 else c 47 = if 17 else 18 then then
    swap xp-unary xp-bin
  repeat ;
: xp-add ( -- e ) xp-mul
  begin s" +" xp-at-op? s" -" xp-at-op? or while
    xp-peek-s drop c@ { c } 1 xp-i +!
    c 43 = if 14 else 15 then swap xp-mul xp-bin
  repeat ;
: xp-shift ( -- e ) xp-add
  begin s" <<" xp-at-op? s" >>" xp-at-op? or while
    xp-peek-s drop c@ { c } 1 xp-i +!
    c 60 = if 12 else 13 then swap xp-add xp-bin
  repeat ;
: xp-bitand ( -- e ) xp-shift
  begin s" &" xp-at-op? while 1 xp-i +! 11 swap xp-shift xp-bin repeat ;
: xp-bitxor ( -- e ) xp-bitand
  begin s" ^" xp-at-op? while 1 xp-i +! 10 swap xp-bitand xp-bin repeat ;
: xp-bitor ( -- e ) xp-bitxor
  begin s" |" xp-at-op? while 1 xp-i +! 9 swap xp-bitxor xp-bin repeat ;
: cmp-op? ( -- id|0 )
  s" ==" xp-at-op? if 3 exit then  s" !=" xp-at-op? if 4 exit then
  s" <=" xp-at-op? if 5 exit then  s" >=" xp-at-op? if 6 exit then
  s" <" xp-at-op? if 7 exit then   s" >" xp-at-op? if 8 exit then 0 ;
: xp-cmp ( -- e ) xp-bitor
  begin cmp-op? { id } id 0<> while
    1 xp-i +!  id swap xp-bitor xp-bin
  repeat ;
: xp-not ( -- e )
  s" !" xp-at-op? if 1 xp-i +! xp-enter recurse { c } 33 c xp-un -1 xp-depth +! exit then
  xp-cmp ;
: xp-and ( -- e ) xp-not
  begin s" &&" xp-at-op? while 1 xp-i +! 2 swap xp-not xp-bin repeat ;
: xp-or-impl ( -- e ) xp-enter xp-and
  begin s" ||" xp-at-op? while 1 xp-i +! 1 swap xp-and xp-bin repeat
  -1 xp-depth +! ;
' xp-or-impl is xp-or

: xp-start ( from -- ) xp-i ! 0 xp-depth ! ;
: xp-parse-all ( -- e )                         \ 式を 1 個。余りがあれば構文エラー
  xp-or xp-at-end? 0= if ps-err-head s" unexpected " mb+ tok-desc s"  in expression" mb+ xp-fail then ;
