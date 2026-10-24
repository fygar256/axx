\ labels.fs -- ラベル表 (LabelManager) とリラクゼーションの状態

decimal

10 om-new constant labels                \ 名前 -> [q:4][sec-a][sec-u][equ][imported][rtype]
1 om-new constant relax-prev-dummy
4 om-new constant relax-prev             \ 前回の反復のラベル値 (名前 -> q)
variable relax-optimistic
variable relax-iter
variable cur-sec-a  variable cur-sec-u   \ 現在のセクション名
1 om-new constant reported-lab-errs      \ 定義エラーを 1 回だけ出すための鍵

: lab-find ( a u -- slot|0 ) labels om-find ;
: lab-q ( slot -- q ) ;                                  \ 先頭 4 セルが値
: lab-sec ( slot -- a u ) 4 cells + s@ ;
: lab-equ? ( slot -- f ) 6 cells + @ ;
: lab-imported? ( slot -- f ) 7 cells + @ ;
: lab-rtype ( slot -- n ) 8 cells + @ ;
: lab-set-sec ( slot a u -- ) rot 4 cells + s! ;

defer lab-sec-adjust ( q secname-a secname-u -- q' )     \ セクション相対への補正 (-o / -E)
:noname 2drop ; is lab-sec-adjust
defer elf-note-label ( a u q -- )                         \ -o の追跡 (ラベルの読み)
:noname 2drop drop ; is elf-note-label

: label-value-impl ( a u -- q ) { a u }
  a u lab-find ?dup if
    { sl }
    sl qcopy { v }
    in-binlist @ if
      sl lab-sec cur-sec-a @ cur-sec-u @ str=cs if
        v sl lab-sec lab-sec-adjust to v
      then
    then
    a u v elf-note-label
    v exit
  then
  pass @ 1 = if
    a u relax-prev om-find ?dup if qcopy exit then
    relax-optimistic @ if true undef-flag ! pc @ qn exit then
  then
  size-mode @ if q0 exit then
  true undef-flag !
  report? if
    mb-reset s"  error - Label undefined: '" mb+ a u mb+ s" '" mb+ mb-get diag-e
  then
  qundef ;
' label-value-impl is label-get-value

: lab-report-err ( kind-a kind-u name-a name-u msg-a msg-u -- ) { ka ku na nu ma mu }
  ma mu sdup to mu to ma
  ka ku na nu sconcat { key-a key-u }
  key-a key-u reported-lab-errs om-find if exit then
  key-a key-u sdup reported-lab-errs om-put drop
  true had-error !
  mb-reset s"  error - " mb+ ma mu mb+ s"   [" mb+ file@ mb+ s" :" mb+ line-no @ mb-n s" ]" mb+
  mb-get diag-ef ;

: lab-put ( a u q sa su equ? rtype -- ok ) { a u q sa su eq rt }
  pass @ 1 = pass @ 0= or if
    a u lab-find ?dup if
      lab-imported? 0= if
        s" dup:" a u mb-reset s" label '" mb+ a u mb+ s" ' is already defined." mb+ mb-get lab-report-err
        false exit
      then
    then
  else pass @ 2 = if
    a u lab-find 0= if
      s" pass1:" a u mb-reset s" label '" mb+ a u mb+ s" ' not defined in pass 1." mb+ mb-get lab-report-err
      false exit
    then
  then then
  a u supper patsyms om-find if
    s" patsym:" a u mb-reset s" '" mb+ a u mb+ s" ' is a pattern file symbol." mb+ mb-get lab-report-err
    false exit
  then
  a u lab-find ?dup if lab-rtype else -1 then { old }
  rt 0< old 0>= and if old to rt then
  a u labels om-put { sl }
  q sl q!
  sa su sdup sl 4 cells + s!
  eq if 1 else 0 then sl 6 cells + !
  0 sl 7 cells + !
  rt sl 8 cells + !
  true ;
