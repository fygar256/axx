\ obj2.fs -- テキストテンプレートの展開 ({{ }} と配列の添字)

decimal

: esc-ch ( c -- c' )
  dup 110 = if drop 10 exit then
  dup 116 = if drop 9 exit then
  dup 114 = if drop 13 exit then ;
: close-paren ( a u i -- idx|-1 ) { a u i } 0 { dp }
  begin i u < while
    a i + c@ 40 = if dp 1+ to dp else
      a i + c@ 41 = if dp 1- to dp  dp 0= if i exit then then
    then
    i 1+ to i
  repeat
  -1 ;
: close-bracket ( a u i -- idx|-1 ) { a u i } 0 { dp }
  begin i u < while
    a i + c@ 91 = if dp 1+ to dp else
      a i + c@ 93 = if dp 1- to dp  dp 0= if i exit then then
    then
    i 1+ to i
  repeat
  -1 ;

: bare-name-up ( a u -- a' u' true | false )              \ _txt_bare_name: 大文字にして返す
  trim dup 0= if 2drop false exit then
  over c@ dup alnc? swap 95 = or 0= if 2drop false exit then
  over c@ digc? if 2drop false exit then
  2dup { a u }
  u 0 ?do a i + c@ corec? 0= if 2drop false unloop exit then loop
  supper true ;

\ {{名前[添字]}} の形: 名前と添字に割る
: bare-indexed ( a u -- na nu ia iu true | false ) trim { t n }
  n 0= if false exit then
  t c@ dup alnc? swap 95 = or 0= if false exit then
  t c@ digc? if false exit then
  1 { i }
  begin i n < if t i + c@ corec? else false then while i 1+ to i repeat
  i { nl }
  begin i n < if t i + c@ spc? else false then while i 1+ to i repeat
  i n >= if false exit then
  t i + c@ 91 <> if false exit then
  t n i close-bracket { cb }
  cb 0< if false exit then
  t cb 1+ + n cb 1+ - trim nip 0<> if false exit then
  t nl  t i 1+ + cb i 1+ - true ;

: txt-quoted ( a u -- a' u' true | false ) { t n }
  t n s\" \\\"" starts? if s\" \\\"" else t n s\" \"" starts? if s\" \"" else false exit then then
  { da du }
  sb-new { b }  du { i }
  begin i n < while
    t n i /string da du starts? if
      t i du + + n i - du - trim nip 0= if b sb$ sdup b sb-free true else b sb-free false then exit
    then
    t i + c@ 92 = i 1+ n < and if
      t i 1+ + c@ esc-ch b sb-c  i 2 + to i
    else t i + c@ b sb-c  i 1+ to i then
  repeat
  b sb-free false ;

: arr-index-check ( arr key-a key-u q -- n ok ) { arr ka ku v }
  v qundef? if 0 false exit then
  v @ { n }
  n 0< n arr arr-n >= or if
    mb-reset s"  error - index " mb+ n mb-n s"  is out of range for array symbol '" mb+ ka ku mb+
    s" ' (0.." mb+ arr arr-n 1- mb-n s" )." mb+ mb-get diag-e
    0 false exit
  then
  n true ;

: arr-index-of ( key-a key-u idx-a idx-u -- n ok ) { ka ku ia iu } 0 0 0 0 0 { ta tu na nu has }
  ka ku asym-get { arr }
  ia iu trim to tu to ta
  ta tu txt-quoted if trim to tu to ta then
  ta tu bare-name-up to has
  has if to nu to na then
  has if
    na nu ssym-get if
      trim to tu to ta
      ta tu bare-name-up to has
      has if to nu to na then
    then
  then
  ta tu slower ta tu str=cs { islow }
  islow if ta tu varnames om-find 0<> else false then { isvar }
  has isvar 0= and if
    arr arr-n 0 ?do
      arr i arr-item { it }
      it item-kind 1 = if it item-str supper na nu str=cs if i true unloop exit then then
    loop
    na nu nsym-get if { v } arr ka ku v arr-index-check exit then
  then
  undef-flag @ { sv }  false undef-flag !
  ta tu 0 expr-pat drop qcopy { v2 }
  undef-flag @ sv or undef-flag !
  arr ka ku v2 arr-index-check ;
