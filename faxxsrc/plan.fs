\ plan.fs -- `.unordered` の処理順 (_pat_unordered_plan) と、パターンファイルのシンボルの先読み (setpatsymbols)

decimal

\ ---- .unordered ----
: is-first-kind? ( kind -- f )          \ .unordered .symbolc .bits .padding .vliw .passthru .eol .textmode
  dup 20 = over 5 = or over 4 = or over 3 = or over 6 = or over 13 = or over 14 = or swap 15 = or ;
: is-banned-kind? ( kind -- f ) dup 2 = over 8 = or over 17 = or over 10 = or swap 12 = or ;
: kind-name ( kind -- a u )
  case
    1 of s" .setsym" endof   2 of s" .clearsym" endof  3 of s" .padding" endof  4 of s" .bits" endof
    5 of s" .symbolc" endof  6 of s" .vliw" endof      7 of s" .check" endof    8 of s" .clrcheck" endof
    9 of s" .reloc" endof    10 of s" .clrreloc" endof 11 of s" .map" endof     12 of s" .free" endof
    13 of s" .passthru" endof 14 of s" .eol" endof     15 of s" .textmode" endof 16 of s" .enum" endof
    17 of s" .clrenum" endof 18 of s" .error" endof    19 of s" .echo" endof    20 of s" .unordered" endof
    21 of s" EPIC" endof
    drop s" " 0
  endcase ;

lazy-sb uk-b
: row-text ( r -- a u ) { r }                         \ 欄を strip して '::' でつなぐ
  uk-b sb-clear
  6 0 ?do
    i if s" ::" uk-b sb+ then
    r i rf trim uk-b sb+
  loop
  uk-b sb$ ;
: setsym-name ( r -- a u ) { r } r 1 rf nip if r 1 rf else r 2 rf then trim ;

lazy-sb ul-b
\ 重複検査の鍵と、エラーで名指す言い方。返り値は ka ku la lu true | false
: unordered-key ( r -- ka ku la lu true | false ) { r }
  r rkind @ { k }
  k 1 = if
    r setsym-name supper { ua uu }
    s" .setsym " ua uu sconcat
    ul-b sb-clear s" symbol '" ul-b sb+ ua uu ul-b sb+ s" '" ul-b sb+  ul-b sb$ sdup true exit
  then
  k 7 = k 11 = or k 16 = or k 9 = or if
    r 1 rf trim nip if r 1 rf else r 2 rf then trim slower { va vu }
    k 7 = k 11 = or if s" check" else k 16 = if s" enum" else s" reloc" then then
    s"  " sconcat va vu sconcat
    ul-b sb-clear s" variable '" ul-b sb+ va vu ul-b sb+ s" ' (" ul-b sb+
    k 7 = k 11 = or if s" .check/.map" else k kind-name then ul-b sb+ s" )" ul-b sb+
    ul-b sb$ sdup true exit
  then
  k 18 = if
    r 1 rf trim { ca cu }
    s" .error " ca cu sconcat
    ul-b sb-clear s" error code " ul-b sb+ ca cu ul-b sb+  ul-b sb$ sdup true exit
  then
  k is-first-kind? k 20 <> and if
    k kind-name sdup
    ul-b sb-clear s" '" ul-b sb+ k kind-name ul-b sb+ s" '" ul-b sb+  ul-b sb$ sdup true exit
  then
  k 21 = if s" EPIC" s" 'EPIC'" true exit then
  false ;

3 lazy-om useen          \ 鍵 -> [row][text-a][text-u]

\ 値欄に現れる名前 (大文字) を 1 つずつ xt へ渡す。`"..."` の中は読まない
: each-ref ( a u xt -- ) { a u xt } 0 { k }
  begin k u < while
    a k + c@ { c }
    c 34 = if
      k 1+ to k
      begin k u < if a k + c@ 34 <> else false then while
        a k + c@ 92 = if k 2 + to k else k 1+ to k then
      repeat
      k 1+ to k
    else
      c 128 < c alnc? c 95 = or and if
        k { b }
        begin k u < if a k + c@ dup 128 < swap dup alnc? swap 95 = or and else false then while k 1+ to k repeat
        a b + k b - supper xt execute
      else k 1+ to k then
    then
  repeat ;

MAXROWS cells lazy u-firstv
MAXROWS cells lazy u-symv
MAXROWS cells lazy u-restv
MAXROWS cells lazy u-ordv
MAXROWS lazy u-donev
variable nu-first  variable nu-syms  variable nu-rest  variable nu-ord
variable u-cur
2 lazy-om u-definer
variable u-depmiss

: u-dep-hit ( a u -- )
  u-definer om-find ?dup if
    @ dup u-cur @ <> if u-donev + c@ 0= if true u-depmiss ! then else drop then
  then ;
: sym-deps-done? ( r -- f ) { r }
  r u-cur !  false u-depmiss !
  r 1 rf nip if r 2 rf ['] u-dep-hit each-ref then
  u-depmiss @ 0= ;

: unordered-plan ( -- )
  false unordered-on !  0 dirorder-n !
  false { any }
  nrows @ 0 ?do i risdir @ if i rkind @ 20 = if true to any then then loop
  any 0= if exit then
  true unordered-on !
  0 nu-first !  0 nu-syms !  0 nu-rest !
  useen om-clear  u-definer om-clear
  nrows @ 0 ?do
    i risdir @ if
      i row-blank? 0= if
        i rkind @ { k }
        k is-banned-kind? if
          mb-reset k kind-name mb+ s" : cannot be used in an .unordered pattern file (pattern line " mb+ i 1+ mb-n
          s" ); there every definition holds for the whole file." mb+ mb-get diag-e
        then
        i unordered-key if
          { ka ku la lu }
          i row-text sdup { ta tu }
          ka ku useen om-find ?dup if
            dup 1 cells + s@ ta tu str=cs 0= if
              mb-reset s" .unordered: pattern lines " mb+ dup @ 1+ mb-n s"  and " mb+ i 1+ mb-n
              s"  give " mb+ la lu mb+ s"  two different definitions." mb+ mb-get diag-e
            then
            drop
          else
            ka ku useen om-put { sl }  i sl !  ta tu hdup sl 1 cells + s!
          then
          k is-first-kind? k 21 = or if
            i nu-first @ cells u-firstv + !  1 nu-first +!
          else k 1 = if
            i nu-syms @ cells u-symv + !  1 nu-syms +!
          else
            i nu-rest @ cells u-restv + !  1 nu-rest +!
          then then
        else
          k is-first-kind? k 21 = or if
            i nu-first @ cells u-firstv + !  1 nu-first +!
          else k 1 = if
            i nu-syms @ cells u-symv + !  1 nu-syms +!
          else
            i nu-rest @ cells u-restv + !  1 nu-rest +!
          then then
        then
      then
    then
  loop
  \ .setsym の並べ替え (値が別の .setsym の名前を読むなら、その定義を先に)
  nu-syms @ 0 ?do
    i cells u-symv + @ setsym-name supper { na nu }
    na nu u-definer om-find 0= if na nu u-definer om-put i cells u-symv + @ swap ! then
  loop
  u-donev nrows @ erase
  0 nu-ord !
  nu-syms @ { npend }
  begin npend 0> while
    -1 { nxt }
    npend 0 ?do
      i cells u-symv + @ sym-deps-done? if i to nxt leave then
    loop
    nxt 0< if
      uk-b sb-clear
      npend 0 ?do
        i if s" , " uk-b sb+ then
        s" '" uk-b sb+ i cells u-symv + @ setsym-name supper uk-b sb+ s" '" uk-b sb+
      loop
      mb-reset s" .unordered: the .setsym definitions of " mb+ uk-b sb$ mb+
      s"  refer to each other in a cycle." mb+ mb-get diag-e
      npend 0 ?do i cells u-symv + @ nu-ord @ cells u-ordv + ! 1 nu-ord +! loop
      0 to npend
    else
      nxt cells u-symv + @ { r }
      r nu-ord @ cells u-ordv + !  1 nu-ord +!
      1 u-donev r + c!
      npend 1- nxt ?do i 1+ cells u-symv + @ i cells u-symv + ! loop
      npend 1- to npend
    then
  repeat
  \ first + 並べ替えた .setsym + その他
  0 dirorder-n !
  nu-first @ 0 ?do i cells u-firstv + @ dirorder dirorder-n @ cells + ! 1 dirorder-n +! loop
  nu-ord @ 0 ?do i cells u-ordv + @ dirorder dirorder-n @ cells + ! 1 dirorder-n +! loop
  nu-rest @ 0 ?do i cells u-restv + @ dirorder dirorder-n @ cells + ! 1 dirorder-n +! loop ;

\ ---- パターンファイルのシンボルの先読み ----
: pat-sym-row ( r -- ) dup rkind @ { k }
  k 1 = k 2 = or k 12 = or k 4 = or  k 11 = unordered-on @ 0= and or if ar-mark swap 1 exec-dir ar-release else drop then ;
: set-pat-symbols ( -- )
  numsyms om-clear  strsyms om-clear  arrsyms om-clear  1 arrgen +!
  numsyms sym-target !
  unordered-on @ if
    dirorder-n @ 0 ?do i cells dirorder + @ pat-sym-row loop
  else
    nrows @ 0 ?do i pat-sym-row loop
  then
  numsyms patsyms om-copy
  true nsym-dirty ! ;
