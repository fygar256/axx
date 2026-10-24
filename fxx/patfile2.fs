\ patfile2.fs -- パターンファイル読み込みの後半 (行の登録・.sub・.include・本体)

decimal

: fld! ( a u i -- ) { a u i } a i cells fld-a + !  u i cells fld-u + ! ;

: store-row ( -- ) nflds @ { n }
  nrows @ MAXROWS >= abort" too many pattern rows"
  nrows @ row ROWSZ erase
  6 0 do
    n 1 = if i 0= if 0 else -1 then else
    n 2 = if i 0= if 0 else i 2 = if 1 else -1 then then else
    i then then { src }
    src 0< if 0 0 else src fld@ then
    sdup nrows @ row i 2* cells + s!
  loop
  nrows @ rf0 { f0a f0u }
  f0a f0u is-directive? if
    true nrows @ risdir !
    f0a f0u dir-id dup 0= if drop 21 then nrows @ rkind !
  else
    f0a f0u count-sub nrows @ rgrp !
  then
  1 nrows +! ;

\ ---- .sub 表 ----
1 om-new constant subs                       \ 名前 -> arr (pat, val, pat, val ...)
: sub-new ( a u -- ) subs om-put dup @ arr-free 0 arr-new swap ! ;
: sub-add ( na nu pa pu va vu -- ) { na nu pa pu va vu }
  na nu subs om-find { slot } slot @ { old }
  old arr-n { n }
  n 2 + arr-new { r }
  n 0 ?do old i arr-item r i arr-item item-copy loop
  pa pu r n arr-item item-str!
  va vu r n 1+ arr-item item-str!
  r slot !  old arr-free ;
: sub-name? ( a u -- f ) dup 0= if 2drop false exit then { a u }
  u 0 ?do a i + c@ corec? 0= if false unloop exit then loop true ;

\ ---- .func の本文の集め (ミニ言語が受け取る) ----
defer func-hdr ( a u file-a file-u ln -- )
defer func-line ( a u file-a file-u ln -- )
defer func-end ( -- )
:noname 5 0 do drop loop ; is func-hdr
:noname 5 0 do drop loop ; is func-line
:noname ; is func-end

: dot-kw ( a u -- ka ku )                     \ 行頭の .キーワードを大文字で
  trim dup 0= if exit then over c@ 46 <> if 2drop 0 0 exit then
  { a u } 1 { j }
  begin j u < if a j + c@ corec? else false then while j 1+ to j repeat
  a j supper ;

variable pat-depth
variable pat-dir-a  variable pat-dir-u
variable cur-sub-a  variable cur-sub-u  variable in-sub
variable fdpth     variable in-func
defer read-pattern

: dir-len ( a u -- n ) begin dup 0> while 2dup + 1- c@ 47 = if nip exit then 1- repeat nip ;
create pathbuf 4096 allot
: join-path ( da du fa fu -- a u )
  dup 0> if over c@ 47 = else false then if 2swap 2drop exit then
  { da du fa fu }
  da pathbuf du move  fa pathbuf du + fu move  pathbuf du fu + ;
: unquote ( a u -- a' u' ) { a u } 0 0 { k st }
  begin k u < if a k + c@ 34 <> else false then while k 1+ to k repeat
  k u >= if a 0 exit then
  k 1+ to st  st to k
  begin k u < if a k + c@ 34 <> else false then while k 1+ to k repeat
  a st + k st - ;

: do-include ( a u -- )
  unquote dup 0= if
    2drop s"  error - .INCLUDE directive has no filename." diag-e exit
  then
  sdup pat-dir-a @ pat-dir-u @ 2swap join-path sdup
  1 pat-depth +!  read-pattern  -1 pat-depth +! ;

: word-in? ( a u la lu -- f ) { a u la lu }               \ 空白区切りの語の一覧に a u があるか
  begin lu 0> while
    la lu 32 find-ch { n }
    a u la n str=cs if true exit then
    la n + 1+ to la  lu n - 1- 0 max to lu
  repeat
  false ;

: warn-nosep ( a u -- )
  mb-reset s"  warning - pattern line has no '::' field separator and can never match (likely a stray line left over from a multi-line comment, or a binary_list/error_patterns continued onto the next physical line without a '\' at the end of the line before): '" mb+ mb+ s" '" mb+ mb-get diag-w ;

: pat-line ( a u fa fu ln -- ) { a u fa fu ln }
  a u reduce-spaces { ra ru }
  ra ru dot-kw { ka ku }
  in-func @ ka ku s" .FUNC" str=cs or if
    ka ku s" .FUNC" str=cs if
      ra ru fa fu ln func-hdr  true in-func !  0 fdpth !
      exit
    then
    ka ku s" .ENDFUNC" str=cs if false in-func ! func-end exit then
    ka ku s" .IF" str=cs ka ku s" .FOR" str=cs or ka ku s" .WHILE" str=cs or if 1 fdpth +! then
    ka ku s" .ENDIF" str=cs ka ku s" .NEXT" str=cs or ka ku s" .ENDWHILE" str=cs or if -1 fdpth +! then
    ra ru trim nip if ra ru fa fu ln func-line then
    exit
  then
  ka ku s" .ECHO" str=cs if
    in-sub @ if
      s"  error - '.echo' cannot be written inside '.sub'." diag-e exit
    then
    6 nflds !  6 0 do 0 0 i fld! loop
    s" .echo" 0 fld!
    ra ru trim 5 /string 1 fld!
    store-row exit
  then
  ra ru lstrip { sa su }
  su 8 >= if sa 8 s" .INCLUDE" str=ci else false then
  if sa 8 + su 8 - do-include exit then
  ra ru split-fields
  0 fld@ trim supper { k0a k0u }
  k0a k0u s" .SUB" str=cs if
    1 fld@ trim 2dup sub-name? 0= nflds @ 2 < or if
      2drop s"  error - '.sub' needs a table name made of letters, digits and '_'." diag-e
    else
      in-sub @ if
        2drop s"  error - '.sub' inside a '.sub': sub tables cannot be nested." diag-e
      else
        sdup 2dup cur-sub-u ! cur-sub-a !  true in-sub !  sub-new
      then
    then
    exit
  then
  k0a k0u s" .RETURN" str=cs k0a k0u s" .ENDSUB" str=cs or if
    in-sub @ 0= if s"  error - '.return' without a matching '.sub'." diag-e then
    false in-sub !  exit
  then
  in-sub @ if
    nflds @ 2 < if
      0 fld@ trim nip if s"  error - sub table entry has no '::' field separator." diag-e then
      exit
    then
    cur-sub-a @ cur-sub-u @  0 fld@  nflds @ 1- fld@  sub-add
    exit
  then
  nflds @ 1 = if
    0 fld@ trim nip if
      k0a k0u s" .PASSTHRU .EOL .TEXTMODE .UNORDERED .CLEARSYM .CLRCHECK .CLRRELOC .CLRENUM" word-in?
      0= if 0 fld@ warn-nosep then
    then
  then
  store-row ;

: read-pattern-impl ( fa fu -- ) { fa fu } 0 0 0 0 0 0 0 0 0 0 0 { tab n li inc legacy was bare treat rc oda odu }
  pat-dir-a @ to oda  pat-dir-u @ to odu
  fa fa fu dir-len pat-dir-u !  pat-dir-a !
  fa fu load-lines to n to tab
  n 1+ cells allocate throw to rc
  false rc n cells + !
  n 0 ?do
    n 1- i - to li
    tab li tl@ s" */" search nip nip  li 1+ cells rc + @ or  li cells rc + !
  loop
  false to inc  false to legacy
  n 0 ?do
    i to li
    inc to was
    tab li tl@ inc rm-comment to inc
    inc 0= if false to legacy
    else was 0= if
      tab li tl@ starts-open? to bare
      legacy bare and if true to treat
      else
        li 1+ n < if tab li 1+ tl@ starts-open? else false then
        li 1+ cells rc + @ 0= or to treat
      then
      treat if false to inc  bare to legacy else false to legacy then
    then then
    tab li tl-file tab li tl-ln pat-line
  loop
  inc if
    mb-reset s"  warning - pattern file '" mb+ fa fu mb+
    s" ' ends while a /* ... */ comment is still open (missing closing '*/')." mb+ mb-get diag-w
  then
  rc free throw  tab free throw
  oda pat-dir-a !  odu pat-dir-u ! ;
' read-pattern-impl is read-pattern
