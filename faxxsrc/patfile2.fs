\ patfile2.fs -- パターンファイル読み込みの後半 (行の登録・.sub・.include・本体)

decimal

defer pat-repr ( a u -- a' u' )                  \ Python の repr (dirs2.fs で束ねる)
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
1 lazy-om subs                       \ 名前 -> arr (pat, val, pat, val ...)
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
defer func-handle ( ra ru ka ku fa fu ln -- )
: func-handle-nn54 7 0 do drop loop ; bind func-handle-nn54 func-handle
defer func-active? ( -- f )
: func-active?-nn55 false ; bind func-active?-nn55 func-active?
defer func-end-file ( fa fu -- )
: func-end-file-nn56 2drop ; bind func-end-file-nn56 func-end-file
defer pat-func-reset ( -- )
: pat-func-reset-nn57 ; bind pat-func-reset-nn57 pat-func-reset
defer pat-func-compile ( -- )
: pat-func-compile-nn58 ; bind pat-func-compile-nn58 pat-func-compile

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
defer pat-macro-reset ( -- )
: pat-macro-reset-nn59 ; bind pat-macro-reset-nn59 pat-macro-reset
defer pat-macro-expand ( tab n fa fu -- tab' n' )
: pat-macro-expand-nn60 2drop ; bind pat-macro-expand-nn60 pat-macro-expand

: dir-len ( a u -- n ) begin dup 0> while 2dup + 1- c@ 47 = if nip exit then 1- repeat nip ;
create pathbuf 4096 allot
: join-path ( da du fa fu -- a u )
  dup 0> if over c@ 47 = else false then if 2swap 2drop exit then
  { da du fa fu }
  da pathbuf du move  fa pathbuf du + fu move  pathbuf du fu + ;

\ os.path.pabspath 相当: 相対なら cwd とつなぎ、'.' '..' と重なった '/' をたたむ
: pabspath ( a u -- a' u' ) { a u }
  a c@ 47 = u 0> and if a u else 4096 ar-alloc 4096 get-dir s" /" sconcat a u sconcat then { fa fu }
  fu 2 + ar-alloc { out }  0 0 { n k }
  begin k fu < while
    k { st }
    begin k fu < if fa k + c@ 47 <> else false then while k 1+ to k repeat
    fa st + k st - { ca cu }
    k 1+ to k
    cu 0= if else
    ca cu s" ." compare 0= if else
    ca cu s" .." compare 0= if
      begin n 0> if out n 1- + c@ 47 <> else false then while n 1- to n repeat
      n 0> if n 1- to n then
    else
      47 out n + c!  n 1+ to n  ca out n + cu move  n cu + to n
    then then then
  repeat
  n 0= if 47 out c! 1 to n then
  out n ;
: abs-dir ( a u -- da du )                              \ ディレクトリ (末尾の / つき)
  pabspath 2dup dir-len nip ;

\ 引用符つきの文字列を 1 つ (axx_get_string)。先頭が " でなければ空
: get-qstr ( a u -- ra ru ) { a u }
  0 { k }
  begin k u < if a k + c@ dup 32 = swap 9 = or else false then while k 1+ to k repeat
  k u >= if 0 0 exit then
  a k + c@ 34 <> if 0 0 exit then
  k 1+ to k
  u 1+ ar-alloc { buf }  0 { n }
  begin k u < if a k + c@ 34 <> else false then while
    a k + c@ 92 = k 1+ u < and if
      a k 1+ + c@ dup 34 = over 92 = or if buf n + c! else
        dup 110 = if drop 10 buf n + c! else dup 116 = if drop 9 buf n + c! else
        dup 114 = if drop 13 buf n + c! else
        drop 92 buf n + c! n 1+ to n a k 1+ + c@ buf n + c! then then then
      then
      n 1+ to n  k 2 + to k
    else a k + c@ buf n + c! n 1+ to n  k 1+ to k then
  repeat
  buf n ;

create pat-chain-a 64 cells allot  create pat-chain-u 64 cells allot
: do-include ( sa su -- )                               \ sa su は .include の行 (キーワードから)
  { sa su }
  sa 8 + su 8 - get-qstr { ra ru }
  ru 0= if
    sa 8 + su 8 - lstrip { ta tu }
    0 { k }
    begin k tu < if ta k + c@ dup 32 <> swap 9 <> and else false then while k 1+ to k repeat
    k 0> if
      mb-reset s"  warning - .INCLUDE filename not quoted: '" mb+ ta k mb+ s" '. Please use double quotes." mb+ mb-get diag-w
      ta k to ru to ra
    else
      mb-reset s"  error - .INCLUDE directive has no filename: " mb+ sa su mb+ mb-get diag-e exit
    then
  then
  ra ru sdup pat-dir-a @ pat-dir-u @ 2swap join-path sdup
  1 pat-depth +!  read-pattern  -1 pat-depth +! ;

: word-in? ( a u la lu -- f ) { a u la lu }               \ 空白区切りの語の一覧に a u があるか
  begin lu 0> while
    la lu 32 find-ch { n }
    a u la n str=cs if true exit then
    la n + 1+ to la  lu n - 1- 0 max to lu
  repeat
  false ;

: warn-nosep ( a u -- )
  mb-reset s"  warning - pattern line has no '::' field separator and can never match (likely a stray line left over from a multi-line comment, or a binary_list/error_patterns continued onto the next physical line without a '\' at the end of the line before): " mb+ pat-repr mb+ mb-get diag-w ;

defer check-sub-refs ( -- )                       \ .sub の参照の検査 (読み込み時に一度)
: check-sub-refs-nn61 ; bind check-sub-refs-nn61 check-sub-refs
defer echo-validate ( a u -- )                   \ .echo の引数を検査 (誤りは診断)
: echo-validate-nn62 2drop ; bind echo-validate-nn62 echo-validate
: pat-line ( a u fa fu ln -- ) { a u fa fu ln }
  a u reduce-spaces { ra ru }
  ra ru dot-kw { ka ku }
  func-active? ka ku s" .FUNC" str=cs or if ra ru ka ku fa fu ln func-handle exit then
  ka ku s" .ECHO" str=cs if
    in-sub @ if
      mb-reset s"  error - '.echo' cannot be written inside '.sub::" mb+ cur-sub-a @ cur-sub-u @ mb+ s" '." mb+ mb-get diag-e exit
    then
    6 nflds !  6 0 do 0 0 i fld! loop
    s" .echo" 0 fld!
    ra ru trim 5 /string 1 fld!
    1 fld@ echo-validate
    store-row exit
  then
  ra ru lstrip { sa su }
  su 8 >= if sa 8 s" .INCLUDE" str=ci else false then
  if sa su do-include exit then
  ra ru split-fields
  0 fld@ trim supper { k0a k0u }
  k0a k0u s" .SUB" str=cs if
    nflds @ 1 > if 1 fld@ trim else s" " then { na nu }
    in-sub @ if
      mb-reset s"  error - '.sub' inside '.sub::" mb+ cur-sub-a @ cur-sub-u @ mb+ s" ': sub tables cannot be nested." mb+ mb-get diag-e
    else na nu sub-name? 0= if
      mb-reset s"  error - '.sub' needs a table name made of letters, digits and '_': '" mb+ na nu mb+ s" '" mb+ mb-get diag-e
    else
      na nu subs om-find if
        mb-reset s"  warning - sub table '" mb+ na nu mb+ s" ' is defined more than once; the later definition wins." mb+ mb-get diag-w
      then
      na nu sdup 2dup cur-sub-u ! cur-sub-a !  true in-sub !  sub-new
    then then
    exit
  then
  k0a k0u s" .RETURN" str=cs k0a k0u s" .ENDSUB" str=cs or if
    in-sub @ 0= if
      mb-reset s"  error - '" mb+ k0a k0u slower mb+ s" ' without a matching '.sub'." mb+ mb-get diag-e
    then
    false in-sub !  exit
  then
  in-sub @ if
    nflds @ 2 < if
      0 fld@ trim nip if
        mb-reset s"  error - sub table " mb+ cur-sub-a @ cur-sub-u @ pat-repr mb+ s" : entry has no '::' field separator: " mb+ 0 fld@ pat-repr mb+ mb-get diag-e
      then
      exit
    then
    cur-sub-a @ cur-sub-u @  0 fld@  nflds @ 1- fld@  sub-add
    exit
  then
  k0a k0u s" .MAP" str=cs if
    nflds @ 2 > if 1 fld@ trim else s" " then { va vu }
    vu 0= nflds @ 3 < or if
      s"  error - .map: needs '.map::<variable>::<name,name,...>[::<expression in the variable>]'." diag-e
    else va vu var-name? 0= if
      mb-reset s"  error - .map: variable should be a lower case name ('" mb+ va vu mb+ s" ')." mb+ mb-get diag-e
    then then
  then
  nflds @ 1 = if
    0 fld@ trim nip if
      k0a k0u s" .PASSTHRU .EOL .TEXTMODE .UNORDERED .CLEARSYM .CLRCHECK .CLRRELOC .CLRENUM" word-in?
      0= if 0 fld@ warn-nosep then
    then
  then
  nflds @ 6 > if
    mb-reset s"  warning - pattern line has more than 6 fields (extra fields ignored): [" mb+
    nflds @ 6 do i 6 > if s" , " mb+ then i fld@ pat-repr mb+ loop
    s" ]" mb+ mb-get diag-w
  then
  store-row ;

: pat-open-ok ( fa fu -- ok ) { fa fu }
  pat-depth @ 50 > if
    mb-reset s"  error - pattern .INCLUDE nesting exceeds 50: '" mb+ fa fu mb+ s" '" mb+ mb-get diag-e false exit
  then
  fa fu pabspath sdup { rpa rpu }
  pat-depth @ 0 ?do
    i cells pat-chain-a + @ i cells pat-chain-u + @ rpa rpu str=cs if
      mb-reset s"  error - circular pattern .INCLUDE detected: '" mb+ fa fu mb+ s" ' (already in include chain). Skipped." mb+ mb-get diag-e
      false unloop exit
    then
  loop
  fa fu r/o open-file { fid ior }
  ior 0<> if
    ior -512 <= if ior 512 + negate else 2 then { en }
    mb-reset s"  error - cannot open pattern file '" mb+ fa fu mb+ s" ': [Errno " mb+ en mb-n s" ] " mb+ en errno-text mb+
    s" : '" mb+ fa fu mb+ s" '" mb+ mb-get diag-e false exit
  then
  fid close-file drop
  pat-depth @ 64 < if rpa pat-depth @ cells pat-chain-a + !  rpu pat-depth @ cells pat-chain-u + ! then
  true ;
: read-pattern-impl ( fa fu -- ) { fa fu } 0 0 0 0 0 0 0 0 0 0 0 { tab n li inc legacy was bare treat rc oda odu }
  fa fu pat-open-ok 0= if exit then
  pat-dir-a @ to oda  pat-dir-u @ to odu
  in-sub @ { osub }  cur-sub-a @ { osa }  cur-sub-u @ { osu }  false in-sub !
  fa fu abs-dir pat-dir-u !  pat-dir-a !
  fa fu load-lines to n to tab
  pat-depth @ 0= if pat-macro-reset pat-func-reset then
  tab n fa fu pat-macro-expand to n to tab
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
  in-sub @ if
    mb-reset s"  error - pattern file '" mb+ fa fu mb+ s" ' ends while sub table '" mb+ cur-sub-a @ cur-sub-u @ mb+
    s" ' is still open (missing '.return' or '.endsub')." mb+ mb-get diag-e
  then
  osub in-sub !  osa cur-sub-a !  osu cur-sub-u !
  fa fu func-end-file
  pat-depth @ 0= if check-sub-refs pat-func-compile then
  rc free throw  tab free throw
  oda pat-dir-a !  odu pat-dir-u ! ;
bind read-pattern-impl read-pattern
