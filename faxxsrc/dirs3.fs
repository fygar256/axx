\ dirs3.fs -- パターン側ディレクティブ (check / map / free / enum / 各種フラグ / 振り分け)

decimal

defer dir-reloc ( row -- )
defer dir-clrreloc ( row -- )
defer dir-echo ( row -- )
defer dir-elf ( row mode -- )
defer dir-pat-clear-extra ( a u -- )              \ .free が reloc 系も消すための口
defer dir-as-extra ( sa su da du -- )             \ .as が reloc 系も写すための口
: dir-reloc-nn1 drop ; bind dir-reloc-nn1 dir-reloc
: dir-clrreloc-nn2 drop ; bind dir-clrreloc-nn2 dir-clrreloc
: dir-echo-nn3 drop ; bind dir-echo-nn3 dir-echo
: dir-elf-nn4 2drop ; bind dir-elf-nn4 dir-elf
: dir-pat-clear-extra-nn5 2drop ; bind dir-pat-clear-extra-nn5 dir-pat-clear-extra
: dir-as-extra-nn6 2drop 2drop ; bind dir-as-extra-nn6 dir-as-extra

2 lazy-om chk-cache                       \ 変数 + 欄 -> [世代][arr]
: exec-check-inner ( row -- ) { r }
  r 1 rf trim nip if r 1 rf r 2 rf else
    r 2 rf trim nip if r 2 rf s" " else
      s"  error - .check: variable name is not specified." diag-e exit
    then
  then
  { va vu sa su }
  va vu dir-var 0= if
    mb-reset s"  error - .check: variable should be a lower case name ('" mb+ va vu mb+ s" ')." mb+ mb-get diag-e exit
  then
  { na nu }
  na nu s\" \x01" sconcat sa su sconcat { ka ku }
  ka ku chk-cache om-find ?dup if
    dup @ arrgen @ = if
      cell+ @ arr-clone { c2 } na nu c2 chk-set exit
    then
    drop
  then
  sa su elem-list-expand omit-list-from-names { arr }
  ka ku chk-cache om-put { sl }
  sl @ 0<> if sl cell+ @ arr-free then
  arrgen @ sl !  arr arr-clone sl cell+ !
  na nu arr chk-set ;
: exec-check ( row -- ) exec-check-inner ;
: exec-clrcheck ( row -- ) 2 rf trim dup if
    2dup dir-var if 2swap 2drop chk-del2
    else
      mb-reset s"  error - .clrcheck: variable should be a lower case name ('" mb+ mb+ s" ')." mb+ mb-get diag-e
    then
  else 2drop chk-clear-all then ;

\ ---- .map ----
lazy-sb ms-b
: word-ch? ( c -- f ) corec? ;
: map-subst ( a u va vu n -- a' u' ) { a u va vu n }
  ms-b sb-clear
  0 { k }
  begin k u < while
    k vu + u <= if a k + vu va vu str=ci else false then if
      k 0> if a k 1- + c@ word-ch? else false then 0=
      k vu + u < if a k vu + + c@ word-ch? else false then 0= and if
        40 ms-b sb-c n ms-b sb-n 41 ms-b sb-c  k vu + to k
      else a k + c@ ms-b sb-c  k 1+ to k then
    else a k + c@ ms-b sb-c  k 1+ to k then
  repeat
  ms-b sb$ sdup ;

: map-apply ( row into set-check? -- ) { r into sc }
  r 1 rf trim { va vu }  r 2 rf { sa su }
  r 3 rf trim nip if r 3 rf else va vu then { ea eu }
  va vu dir-var 0= if exit then { na nu }
  sa su elem-list-expand { elems }
  ea eu split-commas { vals }
  vals lst-n 1 > vals lst-n elems lst-n <> and if
    mb-reset s"  error - .map: the value list has " mb+ vals lst-n mb-n s"  items but the name list has " mb+
    elems lst-n mb-n s" ." mb+ mb-get diag-e exit
  then
  elems lst-n 0 ?do
    elems i lst-item item-str { ia iu }
    iu 0<> if
      vals lst-n 1 > if vals i lst-item item-str else ea eu then na nu i map-subst
      0 expr-pat drop { v }
      ia iu into 0= if sym-target @ else into then om-put v swap q!
    then
  loop
  sc if na nu elems omit-list-from-names chk-set then ;
: exec-map ( row -- ) { r }
  unordered-on @ if
    r 1 rf dir-var 0= if exit then { na nu }
    4 om-new { tbl }
    r tbl false map-apply
    na nu vartabs om-put tbl swap !
    exit
  then
  r 0 true map-apply ;

: exec-free ( row -- ) { r }
  r 2 rf nip if r 2 rf else r 1 rf then { la lu }
  la lu trim nip 0= if s"  error - .free: needs '.free::<name,name,...>'." diag-e exit then
  0 { st }
  lu 1+ 0 ?do
    i lu = la i + c@ 44 = or if
      la st + i st - trim { na nu }
      nu 0> if
        na nu supper { ka ku }
        ka ku sym-target @ om-del  ka ku ssym-del  ka ku asym-del
        ka ku freed-subs om-put drop
        chkmap om-used 0 ?do
          i chkmap om-live? if
            i chkmap om-val @ { arr }
            arr arr-n 1+ lst-new { nl }
            arr arr-n 0 ?do arr i arr-item item-str ka ku str=cs 0= if arr i arr-item nl lst-add-item then loop
            nl arr-from-list  arr arr-free  i chkmap om-val !
          then
        loop
        na nu slower { va vu }
        va vu var-name? if
          va vu chk-del2  va vu enumdefs om-del  va vu dir-pat-clear-extra
        then
      then
      i 1+ to st
    then
  loop ;

: exec-enum ( row -- ) { r }
  r 1 rf trim { va vu }  r 2 rf { sa su }  r 3 rf { ea eu }
  va vu dir-var 0= if
    mb-reset s"  error - .enum: variable should be a lower case name ('" mb+ va vu mb+ s" ')." mb+ mb-get diag-e exit
  then { na nu }
  sa su elem-list-expand { el }
  el lst-n 1+ lst-new { names }
  el lst-n 0 ?do
    el i lst-item item-str { ia iu }
    iu 0> if
      false { f }  names lst-n 0 ?do names i lst-item item-str ia iu str=cs if true to f then loop
      f 0= if ia iu names lst-add-str then
    then
  loop
  names lst-n 0= if s"  error - .enum: no enumeration element is given." diag-e exit then
  ea eu trim nip 0= if s"  error - .enum: the value expression is missing." diag-e exit then
  na nu enumdefs om-put { slot }
  names arr-from-list slot !  ea eu hdup slot 2 cells + ! slot cell+ ! ;
: exec-clrenum ( row -- ) 2 rf trim dup if
    2dup dir-var if 2swap 2drop enumdefs om-del
    else mb-reset s"  error - .clrenum: variable should be a lower case name ('" mb+ mb+ s" ')." mb+ mb-get diag-e then
  else 2drop enumdefs om-clear then ;

\ ---- .as ----
\ `.as::<変数,...>::<変数>` の写し先の欄を、前後の空白を除いた綴りの並びに分ける
\ (空の項目は除く)。axx.py の _as_names() と同じ。並びには 1 つ余分に積める
: as-dests ( row -- l ) { r }
  r 1 rf { a u }
  a u 44 count-ch 2 + lst-new { l }
  0 { st }
  u 1+ 0 ?do
    i u = a i + c@ 44 = or if
      a st + i st - trim dup if l lst-add-str else 2drop then
      i 1+ to st
    then
  loop
  l ;
\ 変数 s の .check / .enum / .reloc / (.unordered の .map の表) を d へ写す。s に無いものは d から外す
: as-copy ( sa su da du -- ) { sa su da du }
  sa su chk-get ?dup if arr-clone { c } da du c chk-set else da du chk-del2 then
  sa su enumdefs om-find ?dup if
    dup @ over cell+ @ rot 2 cells + @ { n ea eu }
    da du enumdefs om-put { sl }  n sl !  ea sl cell+ !  eu sl 2 cells + !
  else da du enumdefs om-del then
  sa su vartabs om-find ?dup if
    @ { t }  t da du vartabs om-put !
  else da du vartabs om-del then
  sa su da du dir-as-extra ;
\ `.as::<変数,...>::<変数>` — 写し元の変数の設定を、その位置で写し先の変数へ写す。
\ 後で写し元を変えても写し先は変わらない。axx.py の as_processing() と同じ
: exec-as ( row -- ) { r }
  r as-dests { l }
  r 2 rf trim { sa su }
  l lst-n 0= su 0= or if s"  error - .as: needs '.as::<variable,...>::<variable>'." diag-e exit then
  sa su l lst-add-str
  l lst-n { n }
  n lst-new { vl }
  n 0 ?do
    l i lst-item item-str { ta tu }
    ta tu dir-var if vl lst-add-str else
      mb-reset s"  error - .as: variable should be a lower case name ('" mb+ ta tu mb+ s" ')." mb+ mb-get diag-e
      unloop exit
    then
  loop
  vl n 1- lst-item item-str { sva svu }
  n 1- 0 ?do
    vl i lst-item item-str { dva dvu }
    dva dvu sva svu str=cs 0= if sva svu dva dvu as-copy then
  loop ;

\ ---- on / off 形式 ----
: onoff-arg ( row -- -1|0|1 ) { r }                      \ 空/ON=1  OFF=0  その他=-1 (エラー済み)
  r 1 field-nonblank supper { a u }
  u 0= if 1 exit then
  a u s" ON" str=cs if 1 exit then
  a u s" OFF" str=cs if 0 exit then
  -1 ;
: onoff-err ( row name-a name-u -- ) { r na nu }
  r 1 field-nonblank supper { a u }
  mb-reset s"  error - " mb+ na nu mb+ s" : expected 'on' or 'off' ('" mb+ a u mb+ s" ')." mb+ mb-get diag-e ;
: exec-passthru ( row -- ) dup onoff-arg dup 0< if drop s" .passthru" onoff-err else nip passthru ! then ;
: exec-eol ( row -- ) dup onoff-arg dup 0< if drop s" .eol" onoff-err else nip eol-on ! then ;
: exec-textmode ( row -- ) dup onoff-arg dup 0< if drop s" .textmode" onoff-err else
    nip dup textmode ! dup passthru ! eol-on ! then ;

: exec-error ( row -- ) { r }
  r 1 rf trim { na nu }  r 2 rf { ma mu }
  nu 0= if s"  error - .error directive requires an error code (number)." diag-e exit then
  false undef-flag !
  na nu 0 expr-pat drop { n }
  undef-flag @ n qundef-derived? or false undef-flag !
  { bad }
  bad n q-neg? or n 1000000 q-nonneg-gt? or if
    mb-reset s"  error - .error: error code must be a non-negative integer (0-1000000), got " mb+ na nu repr1 mb+ s" ." mb+
    mb-get diag-e exit
  then
  ma mu trim { ta tu }
  tu 0= if false else ta c@ 34 = then 0= if
    mb-reset s"  error - .error: message must be a double-quoted string, got " mb+ ma mu repr1 mb+ s" ." mb+ mb-get diag-e exit
  then
  ta tu get-string { ga gu }
  n @ ga gu err-set ;

\ ---- 振り分け (mode 0 = 各行で, 1 = 読み込み時の setpatsymbols) ----
: exec-dir ( row mode -- ) { r mode }
  r rkind @ case
    1 of r exec-setsym endof
    2 of mode 0= if r exec-clearsym else r exec-clearsym then endof
    3 of mode 0= if r exec-padding then endof
    4 of r exec-bits endof
    5 of mode 0= if r exec-symbolc then endof
    6 of mode 0= if r exec-vliw then endof
    7 of mode 0= if r exec-check then endof
    8 of mode 0= if r exec-clrcheck then endof
    9 of mode 0= if r dir-reloc then endof
    10 of mode 0= if r dir-clrreloc then endof
    11 of mode 0= if r exec-map else r numsyms false map-apply then endof
    12 of r exec-free endof
    13 of mode 0= if r exec-passthru then endof
    14 of mode 0= if r exec-eol then endof
    15 of mode 0= if r exec-textmode then endof
    16 of mode 0= if r exec-enum then endof
    17 of mode 0= if r exec-clrenum then endof
    18 of mode 0= if r exec-error then endof
    19 of mode 0= if r dir-echo then endof
    20 of endof
    21 of mode 0= if r exec-epic then endof
    22 of mode 0= if r exec-as then endof
    30 of r mode dir-elf endof
  endcase ;
