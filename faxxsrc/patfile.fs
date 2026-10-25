\ patfile.fs -- パターンファイルの読み込み (PatternFileReader)

decimal

\ ---- 行の表 (継続行を結んだ形) 1 行 = [a u file-a file-u lineno] ----
5 cells constant LTSZ
variable lt-tab  variable lt-n  variable lt-cap
: lt-add ( a u fa fu ln -- ) { a u fa fu ln }
  lt-n @ lt-cap @ >= abort" too many lines"
  lt-n @ LTSZ * lt-tab @ + { e }
  a u e s!  fa fu e 2 cells + s!  ln e 4 cells + !
  1 lt-n +! ;
: tl@ ( tab i -- a u ) LTSZ * + s@ ;
: tl-file ( tab i -- fa fu ) LTSZ * + 2 cells + s@ ;
: tl-ln ( tab i -- ln ) LTSZ * + 4 cells + @ ;

variable lp  variable le
variable join-cont  true join-cont !
: rd-line ( -- a u true | false )
  lp @ le @ >= if false exit then
  lp @
  begin lp @ le @ < while
    lp @ c@ dup 10 = swap 13 = or if
      lp @ over -
      lp @ c@ 13 = lp @ 1+ le @ < and if lp @ 1+ c@ 10 = if 1 lp +! then then
      1 lp +!
      true exit
    then
    1 lp +!
  repeat
  lp @ over - true ;
: count-lines ( a u -- n ) 0 -rot bounds ?do i c@ dup 10 = swap 13 = or if 1+ then loop 1+ ;

lazy-sb pend-b
: ends-bs? ( a u -- f ) dup 0> if + 1- c@ 92 = else 2drop false then ;

\ ファイルを読み、行末の \ で続く行を結んだ表を返す (結んだぶんの行は空行で残す)
: text-lines ( da du fa fu -- tab n ) { da du fa fu }
  da du
  2dup count-lines dup lt-cap !  LTSZ * allocate throw lt-tab !
  0 lt-n !  pend-b sb-clear
  over + le !  lp !
  false { open }
  begin rd-line while
    join-cont @ if 2dup ends-bs? else false then if
      1- pend-b sb+  s" " fa fu lt-n @ 1+ lt-add  true to open
    else
      pend-b sb-len if
        pend-b sb+ pend-b sb$ sdup fa fu lt-n @ 1+ lt-add  pend-b sb-clear
      else fa fu lt-n @ 1+ lt-add then
      false to open
    then
  repeat
  open if
    pend-b sb$ sdup lt-tab @ lt-n @ 1- LTSZ * + s!  pend-b sb-clear
  then
  lt-tab @ lt-n @ ;
: load-lines ( fa fu -- tab n ) 2dup slurp-file 2swap text-lines ;

\ ---- コメント除去 ----
lazy-sb cb
: quoted-span ( a u i -- n ) { a u i } 0 { j }
  a i + c@ { c }
  c 92 = i 1+ u < and if a i 1+ + c@ 34 = if 2 exit then then
  c 39 = i 2 + u < and if a i 1+ + c@ 34 = a i 2 + + c@ 39 = and if 3 exit then then
  c 34 <> if 0 exit then
  i 1+ to j
  begin j u < while
    a j + c@ 92 = j 1+ u < and if j 2 + to j else
      a j + c@ 34 = if j 1+ i - exit then
      j 1+ to j
    then
  repeat
  0 ;
: at2? ( a u k c1 c2 -- f ) { a u k c1 c2 }
  k 1+ u < if a k + c@ c1 = a k 1+ + c@ c2 = and else false then ;
: rm-comment ( a u inc -- a' u' inc' ) { a u inc } 0 0 { k n }
  cb sb-clear
  begin k u < while
    inc if
      a u k 42 47 at2? if false to inc  k 2 + to k else k 1+ to k then
    else
      a u k quoted-span to n
      n 0> if
        a k + n cb sb+  k n + to k
      else
        a u k 47 42 at2? if true to inc  k 2 + to k
        else a k + c@ cb sb-c  k 1+ to k then
      then
    then
  repeat
  cb sb$ inc ;

lazy-sb rb
: reduce-spaces ( a u -- a' u' ) { a u } false { inws }
  rb sb-clear
  u 0 ?do
    a i + c@ dup ws? if
      drop inws 0= if 32 rb sb-c then  true to inws
    else rb sb-c  false to inws then
  loop
  rb sb$ ;
: starts-open? ( a u -- f )
  lstrip dup 2 >= if drop dup c@ 47 = swap 1+ c@ 42 = and else 2drop false then ;

\ ---- 欄の分割 ----
: next-field ( a u idx -- fa fu idx' ) { a u idx } 0 0 0 0 { st en q f }
  begin idx u < if a idx + c@ spc? else false then while idx 1+ to idx repeat
  idx u >= if a 0 idx exit then
  idx to st  u to en  u to f
  begin idx u < while
    a u idx quoted-span to q
    q 0> if idx q + to idx else
      a u idx 58 58 at2? if idx to en  idx 2 + to f  u to idx
      else idx 1+ to idx then
    then
  repeat
  a st + en st - rstrip  f ;
4096 constant NFLD
create fld-a NFLD 2 + cells allot
create fld-u NFLD 2 + cells allot
variable nflds
: fld-at ( i -- a u ) { i } fld-a i cells + @  fld-u i cells + @ ;
: fld@ ( i -- a u )
  dup nflds @ < if fld-at else drop 0 0 then ;
: split-fields ( a u -- ) { a u } 0 { idx }
  0 nflds !
  begin
    a u idx next-field to idx
    nflds @ NFLD < if nflds @ cells fld-u + !  nflds @ cells fld-a + !  1 nflds +! else 2drop then
    u idx <=
  until ;

\ ---- パターン行の表 ----
65536 constant MAXROWS
16 cells constant ROWSZ
MAXROWS ROWSZ * lazy prows
variable nrows
: row ( i -- a ) ROWSZ * prows + ;
: rf ( i k -- a u ) swap row swap 2* cells + s@ ;     \ k 番目の欄 (0..5)
: rf0 ( i -- a u ) 0 rf ;
: rkind ( i -- a ) row 12 cells + ;
: risdir ( i -- a ) row 13 cells + ;
: rgrp ( i -- a ) row 14 cells + ;
: raux ( i -- a ) row 15 cells + ;

\ ---- ディレクティブ名 ----
: dir-id ( a u -- id )
  2dup s" .setsym" str=cs if 2drop 1 exit then
  2dup s" .clearsym" str=cs if 2drop 2 exit then
  2dup s" .padding" str=cs if 2drop 3 exit then
  2dup s" .bits" str=cs if 2drop 4 exit then
  2dup s" .symbolc" str=cs if 2drop 5 exit then
  2dup s" .vliw" str=cs if 2drop 6 exit then
  2dup s" .check" str=cs if 2drop 7 exit then
  2dup s" .clrcheck" str=cs if 2drop 8 exit then
  2dup s" .reloc" str=cs if 2drop 9 exit then
  2dup s" .clrreloc" str=cs if 2drop 10 exit then
  2dup s" .map" str=cs if 2drop 11 exit then
  2dup s" .free" str=cs if 2drop 12 exit then
  2dup s" .passthru" str=cs if 2drop 13 exit then
  2dup s" .eol" str=cs if 2drop 14 exit then
  2dup s" .textmode" str=cs if 2drop 15 exit then
  2dup s" .enum" str=cs if 2drop 16 exit then
  2dup s" .clrenum" str=cs if 2drop 17 exit then
  2dup s" .error" str=cs if 2drop 18 exit then
  2dup s" .echo" str=cs if 2drop 19 exit then
  2dup s" .unordered" str=cs if 2drop 20 exit then
  s" .elftype .elfmachine .elfclass .elfrela .elfwidth .elfextern .elfdwarf .elfheader .elfsection .elffield .elfpcguess .elfrelax .elfanchor .elfresolve .elfbuiltin .elfextra .elfdiff .elfencode .elfrinfo .elfunit .elflink .elfgroup .elfcfi .elfcfiinit .elfcfireg .elfunaligned"
  { a u la lu }
  begin lu 0> while
    la lu 32 find-ch { n }
    a u la n str=cs if 30 exit then
    la n + 1+ to la  lu n - 1- 0 max to lu
  repeat
  0 ;
: epic-name? ( a u -- f ) dup 4 = if s" EPIC" str=ci else 2drop false then ;
: is-directive? ( a u -- f ) 2dup dir-id 0<> if 2drop true exit then epic-name? ;

: count-sub ( a u -- n ) { a u } 0 0 { n k }
  begin k 1+ u < while
    a k + 2 s" [[" str=cs if n 1+ to n  k 2 + to k else k 1+ to k then
  repeat
  n ;
: all-blank? ( a u -- f ) 0 ?do dup i + c@ spc? 0= if drop false unloop exit then loop drop true ;

