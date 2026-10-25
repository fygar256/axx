\ symtab.fs -- .setsym の各種シンボル (数値・文字列・配列/集合) と、文字列リストの道具
\
\ 配列 = ヒープの塊 [count][item * count]。item は 8 セル:
\   [0]=kind (0 数, 1 文字列) [1]=a [2]=u [3..6]=q
\ 一時のリストは領域 (arena) に取った item の配列で、arr-from-list で配列にする。

decimal

8 cells constant ITEMSZ
: item-kind ( it -- n ) @ ;
: item-str ( it -- a u ) cell+ s@ ;
: item-q ( it -- q ) 3 cells + ;
: item-str! ( a u it -- ) { a u it } 1 it ! a u hdup it cell+ s! ;
: item-num! ( q it -- ) { q it } 0 it !  q it item-q q! ;
: item-copy ( src dst -- ) { s d }
  s item-kind 1 = if s item-str d item-str! else s item-q d item-num! then ;
: item= ( a b -- f ) { a b }
  a item-kind b item-kind <> if false exit then
  a item-kind 1 = if a item-str b item-str str=cs else a item-q b item-q q= then ;

: arr-new ( n -- arr ) { n }
  n ITEMSZ * cell+ allocate throw { arr }
  n arr ! arr cell+ n ITEMSZ * erase arr ;
: arr-n ( arr -- n ) @ ;
: arr-item ( arr i -- it ) ITEMSZ * + cell+ ;
: arr-free ( arr -- ) ?dup if free throw then ;
: arr-clone ( arr -- arr' ) { a } a arr-n arr-new { r }
  a arr-n 0 ?do a i arr-item r i arr-item item-copy loop r ;

\ 一時リスト (領域に取る)
: lst-new ( cap -- l ) 1+ ITEMSZ * ar-alloc { l } 0 l ! l ;
: lst-n ( l -- n ) @ ;
: lst-item ( l i -- it ) ITEMSZ * + cell+ ;
: lst-add-str ( a u l -- ) { a u l }
  l lst-n { n }  l n lst-item { it }
  1 it !  a u sdup it cell+ s!  n 1+ l ! ;
: lst-add-q ( q l -- ) { q l }
  l lst-n { n }  l n lst-item { it }
  0 it !  q it item-q q!  n 1+ l ! ;
: lst-add-item ( src l -- ) { s l }
  l lst-n { n }  l n lst-item { it }
  s item-kind 1 = if 1 it ! s item-str sdup it cell+ s! else 0 it ! s item-q it item-q q! then
  n 1+ l ! ;
: lst-has? ( it l -- f ) { it l }
  l lst-n 0 ?do it l i lst-item item= if true unloop exit then loop false ;
: arr-from-list ( l -- arr ) { l } l lst-n arr-new { r }
  l lst-n 0 ?do l i lst-item r i arr-item item-copy loop r ;
: lst-from-arr ( arr -- l ) { a }
  a arr-n 16 + lst-new { l }
  a arr-n 0 ?do a i arr-item l lst-add-item loop l ;

\ ---- 3 つの表 ----
4 lazy-om numsyms           \ 名前(大文字) -> q
2 lazy-om strsyms           \ 名前 -> (a u)
1 lazy-om arrsyms           \ 名前 -> arr
4 lazy-om patsyms           \ パターンファイル読み込み後の数値シンボル
variable arrgen

: skey ( a u -- a' u' ) supper ;
: nsym-get ( a u -- q true | false ) skey numsyms om-find dup if qcopy true else drop false then ;
: nsym-set ( a u q -- ) { a u q } a u skey numsyms om-put q swap q! ;
: nsym-del ( a u -- ) skey numsyms om-del ;
: ssym-get ( a u -- a' u' true | false ) skey strsyms om-find ?dup if s@ true else false then ;
: ssym-set ( a u va vu -- ) { a u va vu } a u skey strsyms om-put va vu hdup rot s! ;
: ssym-del ( a u -- ) skey strsyms om-del ;
: asym-get ( a u -- arr|0 ) skey arrsyms om-find ?dup if @ else 0 then ;
: asym-set ( a u arr -- ) { a u arr }
  a u skey arrsyms om-put dup @ arr-free arr swap !  1 arrgen +! ;
: asym-del ( a u -- ) skey { ka ku }
  ka ku arrsyms om-find ?dup if @ arr-free then
  ka ku arrsyms om-del  1 arrgen +! ;

\ ---- 文字列の道具 ----
: bare-name ( a u -- a' u' true | false )         \ 裸の名前なら (綴りはそのまま)
  trim dup 0= if 2drop false exit then
  over c@ dup alnc? swap 95 = or 0= if 2drop false exit then
  over c@ digc? if 2drop false exit then
  2dup { a u }
  u 0 ?do a i + c@ corec? 0= if 2drop false unloop exit then loop
  true ;

\ トップレベルのカンマで割る: 項目を (a u) の一時リスト (文字列 item) にして返す
: split-commas ( a u -- l ) { a u }
  u 2 + lst-new { l }  0 { st } 0 { dp }
  u 0 ?do
    a i + c@ { c }
    c 40 = c 91 = or c 123 = or if dp 1+ to dp else
    c 41 = c 93 = or c 125 = or if dp 0> if dp 1- to dp then else
    c 44 = dp 0= and if
      a st + i st - trim l lst-add-str  i 1+ to st
    then then then
  loop
  a st + u st - trim l lst-add-str
  l ;

\ 配列リテラルを項目に割る (_arr_split)。q は "[" から始まる。結果は文字列 item のリスト
: arr-split ( a u -- l ) { q n }
  n 2 + lst-new { l }
  1 { i }  0 { b }  0 { dp }  false { inq }  false { dn }
  begin i n < while
    begin i n < if q i + c@ spc? else false then while i 1+ to i repeat
    i n >= if l exit then
    q i + c@ 93 = if l exit then
    i to b  0 to dp  false to inq  false to dn
    begin i n < dn 0= and while
      q i + c@ { c }
      inq if
        c 92 = i 1+ n < and if i 1+ to i else c 34 = if false to inq then then
        i 1+ to i
      else
        c 34 = if true to inq i 1+ to i else
        c 91 = c 40 = or if dp 1+ to dp i 1+ to i else
        c 41 = if dp 1- to dp i 1+ to i else
        c 93 = if dp 0= if true to dn else dp 1- to dp i 1+ to i then else
        c 44 = dp 0= and if true to dn else i 1+ to i then
        then then then then
      then
    repeat
    q b + i b - rstrip l lst-add-str
    i n < if q i + c@ 44 = else false then if i 1+ to i else l exit then
  repeat
  l ;

\ 文字列テンプレートの外側のクォートを外す (_txt_template_inner)。エスケープは残す。
: tmpl-inner ( a u -- a' u' ) { q n }
  n 1+ ar-alloc { d } 0 { k }
  1 { i }
  false { done }
  begin i n < done 0= and while
    q i + c@ 92 = i 1+ n < and if
      q i + c@ d k + c!  q i 1+ + c@ d k 1+ + c!  k 2 + to k  i 2 + to i
    else
      q i + c@ 34 = if true to done else
      q i + c@ d k + c!  k 1+ to k  i 1+ to i then
    then
  repeat
  d k ;

\ ---- 配列リテラルと集合 ----
: arr-items-from-text ( a u -- l ) { q n }
  q n arr-split { parts }
  parts lst-n 8 + lst-new { out }
  parts lst-n 0 ?do
    parts i lst-item item-str { ia iu }
    iu 0> if ia c@ 34 = else false then if
      ia iu tmpl-inner out lst-add-str
    else
      ia iu bare-name if out lst-add-str else
        iu 0> if ia iu 0 expr-pat drop out lst-add-q else 0 qn out lst-add-q then
      then
    then
  loop
  out ;

: set-name-token ( a u -- a' u' true | false )         \ 集合の項目として読める名前なら大文字にして返す
  trim dup 0= if 2drop false exit then
  over c@ digc? if 2drop false exit then
  2dup { a u }
  u 0 ?do a i + c@ dup spc? swap 127 > or if 2drop false unloop exit then loop
  supper true ;
: lst-dedupe ( l -- l' ) { l }
  l lst-n 8 + lst-new { r }
  l lst-n 0 ?do l i lst-item r lst-has? 0= if l i lst-item r lst-add-item then loop
  r ;
: set-literal-from-text ( a u -- l true | false ) { a u }
  a u split-commas { parts }
  parts lst-n 2 < if false exit then
  parts lst-n 64 + { cap }
  parts lst-n 0 ?do
    parts i lst-item item-str set-name-token if asym-get ?dup if arr-n cap + to cap then else then
  loop
  cap lst-new { items }
  parts lst-n 0 ?do
    parts i lst-item item-str set-name-token 0= if false unloop exit then { na nu }
    na nu asym-get ?dup if
      { arr } arr arr-n 0 ?do arr i arr-item items lst-add-item loop
    else na nu items lst-add-str then
  loop
  items lst-dedupe true ;
: set-operand ( a u -- l true | false )
  trim dup 0= if 2drop false exit then
  over c@ dup alnc? swap 95 = or 0= if 2drop false exit then
  over c@ digc? if 2drop false exit then
  2dup { a u }
  u 0 ?do a i + c@ corec? 0= if 2drop false unloop exit then loop
  asym-get ?dup 0= if false exit then
  lst-from-arr lst-dedupe true ;
: set-op-char? ( c -- f ) s" &|^+-" in-str? ;
: set-expr-from-text ( a u -- l true | false ) { a u }
  u 2 + 2 * lst-new { toks }                       \ トークン (文字列 item)
  0 { st }
  u 0 ?do
    a i + c@ set-op-char? if
      a st + i st - toks lst-add-str
      a i + 1 toks lst-add-str
      i 1+ to st
    then
  loop
  a st + u st - toks lst-add-str
  toks lst-n 3 < if false exit then
  toks 0 lst-item item-str set-operand 0= if false exit then { acc }
  1 { k }
  begin k 1+ toks lst-n < while
    toks k lst-item item-str drop c@ { op }
    toks k 1+ lst-item item-str set-operand 0= if false unloop exit then { rhs }
    acc lst-n rhs lst-n + 8 + lst-new { nr }
    op 38 = if                                            \ &
      acc lst-n 0 ?do acc i lst-item rhs lst-has? if acc i lst-item nr lst-add-item then loop
    else op 124 = op 43 = or if                           \ | +
      acc lst-n 0 ?do acc i lst-item nr lst-add-item loop
      rhs lst-n 0 ?do rhs i lst-item acc lst-has? 0= if rhs i lst-item nr lst-add-item then loop
    else op 94 = if                                       \ ^
      acc lst-n 0 ?do acc i lst-item rhs lst-has? 0= if acc i lst-item nr lst-add-item then loop
      rhs lst-n 0 ?do rhs i lst-item acc lst-has? 0= if rhs i lst-item nr lst-add-item then loop
    else                                                  \ -
      acc lst-n 0 ?do acc i lst-item rhs lst-has? 0= if acc i lst-item nr lst-add-item then loop
    then then then
    nr to acc
    k 2 + to k
  repeat
  acc true ;

: symbol-set-from-text ( dst-a dst-u va vu -- f ) { da du va vu }
  va vu set-expr-from-text if
  else va vu set-literal-from-text 0= if false exit then then
  arr-from-list da du rot asym-set true ;
: symbol-copy-from-name ( dst-a dst-u va vu -- f ) { da du va vu }
  va vu bare-name 0= if false exit then { ta tu }
  ta tu skey { sa su }
  sa su arrsyms om-find if
    sa su da du skey str=cs 0= if sa su asym-get arr-clone da du rot asym-set then
    true exit
  then
  sa su strsyms om-find if
    sa su da du skey str=cs 0= if sa su ssym-get drop da du 2swap ssym-set then
    true exit
  then
  da du ta tu ssym-set true ;
bind nsym-get sym-num-get
: arr-len-impl ( a u -- n ) asym-get ?dup if arr-n else -1 then ;
bind arr-len-impl arr-len
: arr-item-num-impl ( a u i -- q kind ) { a u i }
  a u asym-get i arr-item { it }
  it item-kind 1 = if q0 1 else it item-q qcopy 0 then ;
bind arr-item-num-impl arr-item-num
