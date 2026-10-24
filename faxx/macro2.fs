\ macro2.fs -- マクロ層の後半: 構文木、実行、補間、展開

decimal

\ ---- 出力行の表 ----
5 cells constant OLSZ
: out-add ( a u fa fu ln -- ) { a u fa fu ln }
  mp.outn mp@ MACRO-MAX-LINES >= if
    ln fa fu ln mfail-pos s" macro expansion produced more than 2000000 lines; assuming a runaway macro" mb+ mfail
  then
  mp.outn mp@ mp.outcap mp@ >= if
    mp.outcap mp@ 2* 1024 max dup mp.outcap mp!
    OLSZ * mp.out mp@ swap resize throw mp.out mp!
  then
  mp.outn mp@ OLSZ * mp.out mp@ + { e }
  a u hdup e s!  fa fu e 2 cells + s!  ln e 4 cells + !
  mp.outn mp@ 1+ mp.outn mp! ;

\ ---- 診断 ----
: m-warn ( -- )                              \ mb の文言を警告として 1 度だけ出す
  mb-get 2dup mp @ mp.reported + @ om-find if 2drop exit then
  2dup mp @ mp.reported + @ om-put drop
  mb-reset s"  warning - " mb+ mb+ mb-get diag-wf ;
: m-fail-report ( a u -- )
  2dup mp @ mp.reported + @ om-find 0= if
    2dup mp @ mp.reported + @ om-put drop
    mb-reset s"  error - " mb+ mb+ mb-get diag-ef
  else 2drop then
  1 mp.hadErr mp!  true had-error ! ;

\ ---- 文字クラス ----
: aan? ( c -- f ) dup 128 < swap dup alnc? swap 95 = or and ;
: lower-ascii ( a u -- a' u ) slower ;

\ ---- コメントの除去 ----
: strip-comment ( a u -- a' u' ) { a u } 0 0 { i q }
  begin i u < while
    a i + c@ { c }
    q 0<> if
      c 92 = if i 2 + to i else
        c q = if 0 to q then i 1+ to i
      then
    else
      c 34 = if 34 to q i 1+ to i else
      c 39 = if
        \ 後ろに ' があれば文字列
        false { found } u i 1+ ?do a i + c@ 39 = if true to found leave then loop
        found if 39 to q then i 1+ to i
      else
        mp-pat? if
          c 47 = i 1+ u < and if a i 1+ + c@ 42 = else false then if a i rstrip-st exit then
          i 1+ to i
        else
          c 59 = if a i rstrip-st exit then
          i 1+ to i
        then
      then then
    then
  repeat
  a u rstrip-st ;

: lstrip-st ( a u -- a' u' ) begin dup 0> if over c@ dup 32 = swap 9 = or else false then while 1 /string repeat ;
: strip-st ( a u -- a' u' ) lstrip-st rstrip-st ;

\ ---- 文 ----
\ 行頭の `!` 文のキーワードと残り。返り値は wa wu ra ru true | false
: statement-word ( a u -- wa wu ra ru true | false ) lstrip-st { t n }
  n 0= if false exit then
  t c@ 33 <> if false exit then
  n 1 > if t 1+ c@ 33 = if false exit then then
  1 { j }
  begin j n < if t j + c@ aan? else false then while j 1+ to j repeat
  j 1 = if false exit then
  t 1+ j 1- t j + n j - true ;

: kw? ( a u -- f ) slower
  2dup s" if" str=cs >r 2dup s" then" str=cs r> or >r 2dup s" else" str=cs r> or >r 2dup s" elif" str=cs r> or >r
  2dup s" while" str=cs r> or >r 2dup s" def" str=cs r> or >r 2dup s" return" str=cs r> or >r
  2dup s" set" str=cs r> or >r 2dup s" local" str=cs r> or >r 2dup s" break" str=cs r> or >r
  2dup s" continue" str=cs r> or >r 2dup s" error" str=cs r> or >r 2dup s" warning" str=cs r> or >r
  2dup s" echo" str=cs r> or >r 2dup s" include" str=cs r> or >r s" undef" str=cs r> or ;

: looks-like-call? ( ra ru -- f ) strip-st dup 0> if drop c@ 40 = else 2drop false then ;

\ ノード: [kind][fa][fu][ln][...]
: node-new ( kind n fa fu ln -- node ) { kind n fa fu ln }
  n 4 + cells mm-alloc { nd }
  kind nd !  fa nd cell+ !  fu nd 2 cells + !  ln nd 3 cells + !  nd ;
: nf ( nd i -- addr ) 4 + cells + ;
1 constant N-TEXT  2 constant N-IF  3 constant N-WHILE  4 constant N-DEF  5 constant N-SET
6 constant N-LOCAL 7 constant N-UNDEF 8 constant N-RETURN 9 constant N-BREAK 10 constant N-CONT
11 constant N-ERROR 12 constant N-WARN 13 constant N-ECHO 14 constant N-INCLUDE 15 constant N-CALL

: nd-pos ( nd -- fa fu ln ) dup cell+ @ over 2 cells + @ rot 3 cells + @ ;

\ ブロック: [n][node...]
: blk-new ( cap -- b ) 1+ cells mm-alloc { b } 0 b ! b ;
create blk-tmp 100000 cells allot       \ 構築中のノード (入れ子は再帰で別の領域に)

\ 関数の定義: [name-a name-u nparams params(a u)* defaults(a u)* body fa fu ln]
: fn-field ( f i -- addr ) cells + ;

\ 行の表 (読み込み)
variable pl-tab  variable pl-n

: pl-text ( i -- a u ) pl-tab @ swap tl@ ;
: pl-file ( i -- fa fu ) pl-tab @ swap tl-file ;
: pl-ln ( i -- ln ) pl-tab @ swap tl-ln ;
: pl-pos ( i -- fa fu ln ) dup pl-file rot pl-ln ;

: err-at ( fa fu ln -- ) mfail-pos ;
: mac-err-pos ( i -- ) pl-pos err-at ;

defer parse-block ( i depth -- blk i' )

: parse-header ( ta tu kw-a kw-u fa fu ln -- ba bu ) { ta tu ka ku fa fu ln }
  ta tu strip-st { t n }
  t ku 1+ + n ku 1+ - { b bn }
  b bn rstrip-st { b2 bn2 }
  bn2 0= if false else b2 bn2 + 1- c@ 123 = then 0= if
    fa fu ln err-at s" '!" mb+ ka ku mb+ s" ' header must end with '{'" mb+ mfail
  then
  b2 bn2 1- to bn2 to b2
  ka ku s" if" str=cs ka ku s" elif" str=cs or if
    b2 bn2 slower { la lu }
    -1 { k }
    lu 5 >= if lu 5 - 1+ 0 ?do la i + 5 s" !then" str=cs if i to k then loop then
    k 0< if fa fu ln err-at s" '!" mb+ ka ku mb+ s" ' needs '!then' before '{'" mb+ mfail then
    b2 k to bn2 to b2
  then
  b2 bn2 strip-st ;

: after-brace ( a u -- ra ru ) strip-comment strip-st 1 /string strip-st ;

: tail-check ( i -- ) { i }                         \ '}' のあとに何も無いこと
  i pl-text strip-comment strip-st 1 /string strip-st { ta tu }
  tu 0> if ta c@ 59 <> else false then if
    i pl-pos err-at s" unexpected text after '}': " mb+ ta tu repr1 mb+ mfail
  then ;

: parse-simple ( lw-a lw-u word-a word-u rest-a rest-u i -- node ) { la lu wa wu ra ru i }
  i pl-pos { fa fu ln }
  la lu s" set" str=cs if
    ra ru 61 find-ch { e }
    e ru >= if fa fu ln err-at s" '!set' needs 'name = expression'" mb+ mfail then
    N-SET 4 fa fu ln node-new { nd }
    ra e strip-st mm-str nd 0 nf s!
    ra e 1+ + ru e - 1- mm-str nd 2 nf s!
    nd exit
  then
  la lu s" local" str=cs if
    N-LOCAL 4 fa fu ln node-new { nd }
    ra ru 61 find-ch { e }
    e ru < if
      ra e strip-st mm-str nd 0 nf s!
      ra e 1+ + ru e - 1- mm-str nd 2 nf s!
    else
      ra ru strip-st mm-str nd 0 nf s!  0 0 nd 2 nf s!
    then
    nd exit
  then
  la lu s" undef" str=cs if N-UNDEF 2 fa fu ln node-new { nd } ra ru strip-st mm-str nd 0 nf s! nd exit then
  la lu s" return" str=cs if
    N-RETURN 2 fa fu ln node-new { nd }
    ra ru strip-st dup if mm-str else 2drop 0 0 then nd 0 nf s! nd exit
  then
  la lu s" break" str=cs if N-BREAK 0 fa fu ln node-new exit then
  la lu s" continue" str=cs if N-CONT 0 fa fu ln node-new exit then
  la lu s" error" str=cs if N-ERROR 2 fa fu ln node-new { nd } ra ru strip-st mm-str nd 0 nf s! nd exit then
  la lu s" warning" str=cs if N-WARN 2 fa fu ln node-new { nd } ra ru strip-st mm-str nd 0 nf s! nd exit then
  la lu s" echo" str=cs if N-ECHO 2 fa fu ln node-new { nd } ra ru strip-st mm-str nd 0 nf s! nd exit then
  la lu s" include" str=cs if N-INCLUDE 2 fa fu ln node-new { nd } ra ru strip-st mm-str nd 0 nf s! nd exit then
  N-CALL 4 fa fu ln node-new { nd }
  wa wu mm-str nd 0 nf s!  ra ru strip-st mm-str nd 2 nf s!  nd ;

\ ノード列の組み立て (一時領域を再帰ごとに切り出す)
variable bt-top
: bt-mark ( -- m ) bt-top @ ;
: bt-push ( nd -- ) bt-top @ 100000 >= abort" macro block too large" blk-tmp bt-top @ cells + !  1 bt-top +! ;
: bt-finish ( mark -- blk ) { m }
  bt-top @ m - { n }
  n blk-new { b }
  n b !  n 0 ?do blk-tmp m i + cells + @ b i 1+ cells + ! loop
  m bt-top !  b ;
: blk-n ( b -- n ) @ ;
: blk-node ( b i -- nd ) 1+ cells + @ ;

: ptail ( i -- ta tu ) pl-text strip-comment strip-st 1 /string strip-st ;

variable pi-i  variable pi-d  variable pi-n  variable pi-arms  variable pi-eb
variable pi-fa  variable pi-fu  variable pi-ln
variable pi-ca  variable pi-cu
variable pi-cfa variable pi-cfu variable pi-cln

: pi-finish ( -- node )
  N-IF 3 pi-fa @ pi-fu @ pi-ln @ node-new { nd }
  pi-n @ nd 0 nf !  pi-arms @ nd 1 nf !  pi-eb @ nd 2 nf !  nd ;
: pi-arm! ( body -- ) { body }
  pi-n @ 16 >= abort" too many elif arms"
  pi-arms @ pi-n @ 3 * cells + { a }
  pi-ca @ a !  pi-cu @ a cell+ !  body a 2 cells + !
  1 pi-n +! ;
: pi-elif ( ta tu -- )
  s" elif" pi-cfa @ pi-cfu @ pi-cln @ parse-header pi-cu ! pi-ca ! ;
: pi-else-block ( -- node done )
  pi-fa @ pi-fu @ pi-ln @ pi-n @ pi-arms @ pi-d @ pi-cfa @ pi-cfu @ pi-cln @ { sfa sfu sln sn sarms sd scfa scfu scln }
  pi-i @ 1+ pi-d @ 1+ parse-block pi-i ! { eb }
  sfa pi-fa ! sfu pi-fu ! sln pi-ln ! sn pi-n ! sarms pi-arms ! sd pi-d ! scfa pi-cfa ! scfu pi-cfu ! scln pi-cln !
  eb pi-eb !
  pi-i @ pl-n @ >= if pi-cfa @ pi-cfu @ pi-cln @ err-at s" '!else' block is never closed" mb+ mfail then
  pi-i @ ptail { tra tru }
  tru 0> if tra c@ 59 <> else false then if
    pi-i @ pl-pos err-at s" unexpected text after '}': " mb+ tra tru repr1 mb+ mfail
  then
  pi-finish ;
\ '}' の次を読む。完了なら node を返す
: pi-after ( -- node true | false )
  pi-i @ pl-pos pi-cln ! pi-cfu ! pi-cfa !
  pi-i @ ptail { ta tu }
  tu 0= if true else ta c@ 59 = then if pi-finish true exit then
  ta tu statement-word 0= if
    pi-cfa @ pi-cfu @ pi-cln @ err-at s" unexpected text after '}': " mb+ ta tu repr1 mb+ mfail
  then
  { wa wu ra ru }
  wa wu slower s" elif" str=cs if ta tu pi-elif false exit then
  wa wu slower s" else" str=cs 0= if
    pi-cfa @ pi-cfu @ pi-cln @ err-at s" unexpected '!" mb+ wa wu mb+ s" ' after '}'" mb+ mfail
  then
  ra ru strip-st { r rn }
  rn 3 >= if r 3 s" !if" str=cs else false then if
    r rn s" if" pi-cfa @ pi-cfu @ pi-cln @ parse-header pi-cu ! pi-ca !  false exit
  then
  rn 0= if false else r c@ 123 = then 0= if
    pi-cfa @ pi-cfu @ pi-cln @ err-at s" '!else' must be followed by '{'" mb+ mfail
  then
  pi-else-block true ;

: parse-if ( i depth -- node i' )
  pi-d ! pi-i !
  pi-i @ pl-pos pi-ln ! pi-fu ! pi-fa !
  pi-i @ pl-text strip-comment s" if" pi-fa @ pi-fu @ pi-ln @ parse-header pi-cu ! pi-ca !
  16 3 * cells mm-alloc pi-arms !  0 pi-n !  0 pi-eb !
  \ 入れ子の呼び出しで変数が壊れるので、必要な値は局所に退避して回す
  begin
    pi-fa @ pi-fu @ pi-ln @ pi-n @ pi-arms @ pi-d @ pi-ca @ pi-cu @ pi-eb @ { sfa sfu sln sn sarms sd sca scu seb }
    pi-i @ 1+ pi-d @ 1+ parse-block pi-i ! { body }
    sfa pi-fa ! sfu pi-fu ! sln pi-ln ! sn pi-n ! sarms pi-arms ! sd pi-d ! sca pi-ca ! scu pi-cu ! seb pi-eb !
    body pi-arm!
    pi-i @ pl-n @ >= if pi-fa @ pi-fu @ pi-ln @ err-at s" '!if' block is never closed with '}'" mb+ mfail then
    pi-after
  until
  pi-i @ 1+ ;

: parse-while ( i depth -- node i' ) { i depth }
  i pl-pos { fa fu ln }
  i pl-text strip-comment s" while" fa fu ln parse-header { ca cu }
  i 1+ depth 1+ parse-block to i { body }
  i pl-n @ >= if fa fu ln err-at s" '!while' block is never closed with '}'" mb+ mfail then
  i tail-check
  N-WHILE 3 fa fu ln node-new { nd }
  ca cu mm-str nd 0 nf s!  body nd 2 nf !
  nd i 1+ ;

: ident-start? ( c -- f ) dup 95 = swap dup 65 91 within swap 97 123 within or or ;
: name-ok? ( a u -- f ) { a u }
  u 0= if false exit then
  a c@ ident-start? 0= if false exit then
  u 0 ?do a i + c@ aan? 0= if false unloop exit then loop true ;
: builtin? ( a u -- f )
  2dup s" len" str=cs >r 2dup s" hex" str=cs r> or >r 2dup s" str" str=cs r> or >r
  2dup s" int" str=cs r> or >r 2dup s" upper" str=cs r> or >r 2dup s" lower" str=cs r> or >r
  2dup s" substr" str=cs r> or >r 2dup s" abs" str=cs r> or >r 2dup s" min" str=cs r> or >r
  2dup s" max" str=cs r> or >r 2dup s" uid" str=cs r> or >r s" label" str=cs r> or ;

variable pd-fa variable pd-fu variable pd-ln
variable pd-np  variable pd-pn  variable pd-pd
variable pd-na  variable pd-nu

: pd-header ( i -- pl plu ) { i }
  i pl-pos pd-ln ! pd-fu ! pd-fa !
  i pl-text strip-comment strip-st 4 /string strip-st { t n }
  t n rstrip-st { rt rn }
  rn 0= if false else rt rn + 1- c@ 123 = then 0= if
    pd-fa @ pd-fu @ pd-ln @ err-at s" '!def' header must end with '{'" mb+ mfail
  then
  rt rn 1- strip-st to n to t
  t n 40 find-ch { pp }
  pp n >= if pd-fa @ pd-fu @ pd-ln @ err-at s" '!def' needs 'name(p1, p2, ...)'" mb+ mfail then
  t n + 1- c@ 41 <> if pd-fa @ pd-fu @ pd-ln @ err-at s" '!def' needs 'name(p1, p2, ...)'" mb+ mfail then
  t pp strip-st pd-nu ! pd-na !
  pd-na @ pd-nu @ name-ok? 0= if
    pd-fa @ pd-fu @ pd-ln @ err-at s" bad macro name " mb+ pd-na @ pd-nu @ repr1 mb+ mfail
  then
  pd-na @ pd-nu @ kw? pd-na @ pd-nu @ builtin? or if
    pd-fa @ pd-fu @ pd-ln @ err-at s" '" mb+ pd-na @ pd-nu @ mb+ s" ' is a reserved macro name" mb+ mfail
  then
  t pp 1+ + n pp - 2 - strip-st ;

: pd-one-param ( pa pu -- )
  { pa pu }
  pa pu 61 find-ch { e }
  pd-np @ 32 >= abort" too many macro parameters"
  pd-np @ 2 * cells { off }
  e pu < if
    pa e strip-st mm-str pd-pn @ off + s!
    pa e 1+ + pu e - 1- strip-st mm-str pd-pd @ off + s!
  else
    pa pu strip-st mm-str pd-pn @ off + s!   0 0 pd-pd @ off + s!
  then
  pd-pn @ off + s@ { qa qu }
  qu 0= if false else qa c@ ident-start? then 0= if
    pd-fa @ pd-fu @ pd-ln @ err-at s" bad parameter name " mb+ qa qu repr1 mb+ s"  in '!def " mb+ pd-na @ pd-nu @ mb+ s" '" mb+ mfail
  then
  1 pd-np +! ;

: pd-params ( pl plu -- ) { pl plu }
  32 2 * cells mm-alloc pd-pn !  32 2 * cells mm-alloc pd-pd !  0 pd-np !
  plu 0= if exit then
  0 { st }
  plu 1+ 0 ?do
    i plu = if true else pl i + c@ 44 = then if
      pl st + i st - pd-one-param
      i 1+ to st
    then
  loop ;

: pd-check-defaults ( -- ) 0 0 { seen sn }
  pd-np @ 0 ?do
    pd-pd @ i 2 * cells + @ 0= if
      sn 0> if
        pd-fa @ pd-fu @ pd-ln @ err-at s" parameter '" mb+ pd-pn @ i 2 * cells + s@ mb+ s" ' without a default follows '" mb+ seen sn mb+ s" ' which has one" mb+ mfail
      then
    else pd-pn @ i 2 * cells + s@ to sn to seen then
  loop ;

: pd-make ( body -- node ) { body }
  9 cells mm-alloc { f }
  pd-na @ pd-nu @ f s!  pd-np @ f 2 cells + !  pd-pn @ f 3 cells + !  pd-pd @ f 4 cells + !  body f 5 cells + !
  pd-fa @ f 6 cells + !  pd-fu @ f 7 cells + !  pd-ln @ f 8 cells + !
  N-DEF 2 pd-fa @ pd-fu @ pd-ln @ node-new { nd }  f nd 0 nf !  nd ;

: parse-def ( i depth -- node i' ) { i depth }
  i pd-header pd-params pd-check-defaults
  pd-na @ pd-nu @ declare
  \ 入れ子のブロックが変数を壊すので退避
  pd-fa @ pd-fu @ pd-ln @ pd-np @ pd-pn @ pd-pd @ pd-na @ pd-nu @ { a1 a2 a3 a4 a5 a6 a7 a8 }
  i 1+ depth 1+ parse-block to i { body }
  a1 pd-fa ! a2 pd-fu ! a3 pd-ln ! a4 pd-np ! a5 pd-pn ! a6 pd-pd ! a7 pd-na ! a8 pd-nu !
  i pl-n @ >= if pd-fa @ pd-fu @ pd-ln @ err-at s" '!def " mb+ pd-na @ pd-nu @ mb+ s" ' block is never closed" mb+ mfail then
  i tail-check
  body pd-make i 1+ ;

: parse-block-impl ( i depth -- blk i' ) { i depth }
  bt-mark { m }
  begin i pl-n @ < while
    i pl-text { ta tu }
    ta tu strip-st { sa su }
    su 0> if sa c@ 125 = else false then depth 0> and if m bt-finish i exit then
    ta tu strip-comment statement-word if
      { wa wu ra ru }
      wa wu slower { la lu }
      la lu kw? 0=  wa wu func-find 0= and  wa wu declared? 0= and  ra ru looks-like-call? 0= and if
        N-TEXT 2 i pl-pos node-new { nd }  ta tu mm-str nd 0 nf s!  nd bt-push  i 1+ to i
      else
        la lu s" if" str=cs if i depth parse-if to i bt-push else
        la lu s" while" str=cs if i depth parse-while to i bt-push else
        la lu s" def" str=cs if i depth parse-def to i bt-push else
        la lu s" else" str=cs la lu s" elif" str=cs or la lu s" then" str=cs or if
          i mac-err-pos s" '!" mb+ wa wu mb+ s" ' without a matching '!if'" mb+ mfail
        else
          la lu wa wu ra ru i parse-simple bt-push  i 1+ to i
        then then then then
      then
    else
      N-TEXT 2 i pl-pos node-new { nd }  ta tu mm-str nd 0 nf s!  nd bt-push  i 1+ to i
    then
  repeat
  depth 0> if
    pl-n @ 1- 0 max { li }
    pl-n @ 0> if li pl-file li pl-ln else s" ?" 0 then mfail-pos
    s" unexpected end of file: a macro block opened with '{' is never closed" mb+ mfail
  then
  m bt-finish i ;
' parse-block-impl is parse-block
