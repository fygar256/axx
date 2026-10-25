\ obj3.fs -- テキストテンプレートの展開 ({{ }})

decimal

: txt-emit-expr ( ea eu kind sb -- ) { ea eu kind sb }
  undef-flag @ { sv }  false undef-flag !
  ea eu 0 expr-pat drop qcopy { v }
  undef-flag @ if true to sv then
  sv undef-flag !
  v qundef? if s" UNDEF" sb sb+ exit then
  kind 0 = if v 16 radix-str sb sb+ exit then
  kind 2 = if v 2 radix-str sb sb+ exit then
  kind 3 = if v txt-float sb sb+ exit then
  v 10 radix-str sb sb+ ;

: item-text ( it -- a u ) dup item-kind 1 = if item-str else item-q 10 radix-str then ;

: txt-name-text ( ka ku -- a u )                           \ {{名前}} (文字列か配列のとき)
  2dup ssym-get if 2swap 2drop exit then
  asym-get ?dup 0= if s" " exit then
  { arr } sb-new { b }
  arr arr-n 0 ?do i 0> if 44 b sb-c then arr i arr-item item-text b sb+ loop
  b sb$ sdup b sb-free ;

: txt-indexed-text ( na nu ia iu -- a u ) { na nu ia iu }
  na nu supper { ka ku }
  ka ku asym-get 0= if
    mb-reset s"  error - '" mb+ ka ku mb+ s" ' is not an array symbol; '" mb+ ka ku mb+
    s" [...]' needs '.setsym::" mb+ ka ku mb+ s" ::[...]'." mb+ mb-get diag-e s" " exit
  then
  ka ku ia iu arr-index-of 0= if drop s" " exit then
  ka ku asym-get swap arr-item item-text ;
: txt-index-text ( na nu ia iu -- a u ) { na nu ia iu }
  na nu supper { ka ku }
  ka ku asym-get 0= if
    mb-reset s"  error - '" mb+ ka ku mb+ s" ' is not an array symbol; '.index " mb+ ka ku mb+
    s" [...]' needs '.setsym::" mb+ ka ku mb+ s" ::[...]'." mb+ mb-get diag-e s" " exit
  then
  ka ku ia iu arr-index-of 0= if drop s" " exit then
  qn 10 radix-str ;
: txt-exp-text ( na nu -- a u ) { na nu }
  na nu varnames om-find 0= if
    mb-reset s"  error - '" mb+ na nu mb+ s" ' is not a pattern variable; '.exp(" mb+ na nu mb+
    s" )' needs '" mb+ na nu mb+ s" ' captured in the instruction field." mb+ mb-get diag-e s" " exit
  then
  na nu false vslot vtext ;

\ ---- 呼び出し形の読み取り ----
: txt-exp-call ( a u -- na nu true | false ) { s n }
  n 3 < if false exit then
  s 3 supper s" EXP" str=cs 0= if false exit then
  s 3 + n 3 - { ra ru }
  ru 0= if false exit then
  ra c@ dup 32 = over 9 = or swap 40 = or 0= if false exit then
  ra ru trim { ta tu }
  tu 0= if false exit then  ta c@ 40 <> if false exit then
  ta tu 0 close-paren { cb }
  cb 0< if false exit then
  ta cb 1+ + tu cb 1+ - trim nip 0<> if false exit then
  ta 1+ cb 1- trim { na nu }
  nu 0= if false exit then
  na nu var-name? 0= if false exit then
  na nu slower true ;
: txt-index-call ( a u -- na nu ia iu true | false ) { s n }
  n 5 < if false exit then
  s 5 supper s" INDEX" str=cs 0= if false exit then
  s 5 + n 5 - { ra ru }
  ru 0= if false exit then
  ra c@ dup 32 = over 9 = or swap 40 = or 0= if false exit then
  ra ru trim { ta tu }
  tu 0> if ta c@ 40 = else false then if
    ta tu 0 close-paren { cp }
    cp 0< if false exit then
    ta cp 1+ + tu cp 1+ - trim nip 0<> if false exit then
    ta 1+ cp 1- to tu to ta
  then
  ta tu bare-indexed ;
: txt-conv-name ( a u -- nl kind true | false ) { s n }
  n 5 >= if s 5 supper s" FLOAT" str=cs if s 5 + c@ 40 = if 5 3 true exit then then then
  n 3 >= if s 3 supper s" HEX" str=cs if s 3 + c@ 40 = if 3 0 true exit then then then
  n 3 >= if s 3 supper s" DEC" str=cs if s 3 + c@ 40 = if 3 1 true exit then then then
  n 3 >= if s 3 supper s" BIN" str=cs if s 3 + c@ 40 = if 3 2 true exit then then then
  false ;

: render-inner ( ia iu out -- ) { ia iu out } 0 { j }
  begin j iu < if ia j + c@ 32 = else false then while j 1+ to j repeat
  ia j + iu j - { ra ru }
  ru 0> if ra c@ 46 = else false then if
    ra 1+ ru 1- txt-exp-call if txt-exp-text out sb+ exit then
    ra 1+ ru 1- txt-index-call if txt-index-text out sb+ exit then
    ra 1+ ru 1- txt-conv-name if
      { nl kind }
      ra ru nl 1+ close-paren { cp }
      cp 0> if
        ra nl + 2 + cp nl - 2 - kind out txt-emit-expr exit
      then
    then
  then
  ia iu bare-indexed if txt-indexed-text out sb+ exit then
  ia iu bare-name-up if
    2dup ssym-get if 2drop txt-name-text out sb+ exit then
    2dup asym-get if txt-name-text out sb+ exit then
    2drop
  then
  ia iu -1 out txt-emit-expr ;

: txt-render ( a u -- a' u' ) { s n } sb-new { out } 0 { i }
  begin i n < while
    s i + c@ 92 = i 1+ n < and if
      s i 1+ + c@ esc-ch out sb-c  i 2 + to i
    else
      s n i /string s" {{" starts? if
        s n s" }}" i 2 + str-pos { e }
        e 0< if s i + c@ out sb-c  i 1+ to i else
          s i 2 + + e i 2 + - out render-inner
          e 2 + to i
        then
      else s i + c@ out sb-c  i 1+ to i then
    then
  repeat
  out sb$ sdup out sb-free ;
