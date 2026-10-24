\ base.fs -- 文字列・領域・順序つき辞書などの土台

decimal

\ ---- 出力 ----
: etype ( a u -- ) stderr write-file drop ;
: ecr ( -- ) s\" \n" etype ;
: n>s ( n -- a u ) dup >r abs s>d <# #s r> sign #> ;
: .en ( n -- ) n>s etype ;

\ ---- 文字クラス ----
: uc ( c -- C ) dup 97 123 within if 32 - then ;
: lc ( c -- c ) dup 65 91 within if 32 + then ;
: lowc? ( c -- f ) 97 123 within ;
: capc? ( c -- f ) 65 91 within ;
: digc? ( c -- f ) 48 58 within ;
: alnc? ( c -- f ) dup lowc? over capc? or swap digc? or ;
: corec? ( c -- f ) dup alnc? swap 95 = or ;
: spc? ( c -- f ) dup 32 = swap 9 = or ;
: ws? ( c -- f ) dup 32 = over 9 = or over 10 = or swap 13 = or ;
: xdig? ( c -- f ) uc dup 48 58 within swap 65 71 within or ;
: hexv ( c -- n ) uc dup 58 < if 48 - else 55 - then ;
: in-str? ( c a u -- f )
  rot >r
  begin dup while
    over c@ r@ = if 2drop r> drop true exit then
    1 /string
  repeat
  2drop r> drop false ;

\ ---- 文字列 ----
: str=ci ( a1 u1 a2 u2 -- f )
  rot over <> if 2drop drop false exit then
  0 ?do
    over i + c@ uc  over i + c@ uc <> if 2drop unloop false exit then
  loop
  2drop true ;
: str=cs ( a1 u1 a2 u2 -- f ) compare 0= ;
: lstrip ( a u -- a' u' ) begin dup 0> while over c@ spc? while 1 /string repeat then ;
: rstrip ( a u -- a' u' ) begin dup 0> while 2dup + 1- c@ spc? while 1- repeat then ;
: trim ( a u -- a' u' ) lstrip rstrip ;
: starts? ( a u pa pu -- f ) { a u pa pu } u pu >= if a pu pa pu str=cs else false then ;
: starts-ci? ( a u pa pu -- f ) { a u pa pu } u pu >= if a pu pa pu str=ci else false then ;
: ends? ( a u pa pu -- f ) { a u pa pu } u pu >= if a u + pu - pu pa pu str=cs else false then ;
: find-ch ( a u c -- n ) { a u c }                     \ 最初の c の位置 (なければ u)
  u 0 ?do a i + c@ c = if i unloop exit then loop u ;
: has-ch? ( a u c -- f ) { a u c } u 0 ?do a i + c@ c = if true unloop exit then loop false ;
: char-at ( a u i -- c ) 2dup <= if 2drop drop 0 exit then nip + c@ ;

\ ---- (a u) をセル対で出し入れする ----
: s! ( a u addr -- ) >r swap r> 2! ;
: s@ ( addr -- a u ) 2@ swap ;

\ ---- 領域 (一時の文字列用。mark / release で巻き戻す) ----
134217728 constant ARENA-SIZE
ARENA-SIZE allocate throw constant arena
variable ar-top
: ar-alloc ( n -- a )
  ar-top @ over + ARENA-SIZE > abort" arena full"
  ar-top @ arena + swap ar-top +! ;
: ar-mark ( -- m ) ar-top @ ;
: ar-release ( m -- ) ar-top ! ;
: sdup ( a u -- a' u )
  dup 1+ ar-alloc >r
  swap r@ rot dup >r move
  r> r> swap ;
: hdup ( a u -- a' u )                                  \ ヒープへ。解放しない
  dup 1+ allocate throw >r
  swap r@ rot dup >r move
  r> r> swap ;
: sconcat ( a1 u1 a2 u2 -- a u ) { a1 u1 a2 u2 }
  u1 u2 + 1+ ar-alloc { d }
  a1 d u1 move  a2 d u1 + u2 move  d u1 u2 + ;
: supper ( a u -- a' u ) { a u } u 1+ ar-alloc { d }
  u 0 ?do a i + c@ uc d i + c! loop  d u ;
: slower ( a u -- a' u ) { a u } u 1+ ar-alloc { d }
  u 0 ?do a i + c@ lc d i + c! loop  d u ;
: ssub ( a u from to -- a' u' ) { a u f t } a f + t f - ;

\ ---- 伸びる文字列バッファ (組み立て用) ----
\ 構造: [0]=ptr [1]=len [2]=cap
: sb-new ( -- sb ) 3 cells allocate throw { sb }
  256 allocate throw sb !  0 sb cell+ !  256 sb 2 cells + !  sb ;
: sb-free ( sb -- ) dup @ free throw free throw ;
: sb-clear ( sb -- ) 0 swap cell+ ! ;
: sb-need ( n sb -- ) { n sb }
  sb cell+ @ n + 1+ sb 2 cells + @ > if
    sb 2 cells + @ begin dup sb cell+ @ n + 1+ < while 2* repeat
    dup sb 2 cells + !
    sb @ swap resize throw sb !
  then ;
: sb+ ( a u sb -- ) { a u sb }
  u sb sb-need  a sb @ sb cell+ @ + u move  u sb cell+ +! ;
: sb-c ( c sb -- ) { c sb }
  1 sb sb-need  c sb @ sb cell+ @ + c!  1 sb cell+ +! ;
: sb-n ( n sb -- ) >r n>s r> sb+ ;
: sb$ ( sb -- a u ) dup @ swap cell+ @ ;
: sb-len ( sb -- u ) cell+ @ ;
: sb-trunc ( u sb -- ) cell+ ! ;

\ ---- 順序つき辞書 (文字列キー) ----
\ 構造: [0]=count [1]=used [2]=cap [3]=vcells [4]=index [5]=ents
\ エントリ: key-a key-u (key-a=0 は削除済み) value...
: om-esz ( om -- n ) 3 cells + @ 2 + cells ;
: fnv ( a u -- h ) { a u } 14695981039346656037 u 0 ?do a i + c@ xor 1099511628211 * loop ;
: om-new ( vcells -- om ) { vc } 6 cells allocate throw { om }
  0 om !  0 om cell+ !  64 om 2 cells + !  vc om 3 cells + !
  64 cells allocate throw dup 64 cells erase om 4 cells + !
  64 vc 2 + cells * allocate throw om 5 cells + !
  om ;
: om-count ( om -- n ) @ ;
: om-used ( om -- n ) cell+ @ ;
: om-ent ( i om -- e ) dup om-esz rot * swap 5 cells + @ + ;
: om-key ( i om -- a u ) om-ent s@ ;
: om-live? ( i om -- f ) om-ent @ 0<> ;
: om-val ( i om -- slot ) om-ent 2 cells + ;
: om-probe ( a u om -- idx|-1 ) { a u om }               \ index 表の位置。見つかればエントリ番号 + 1
  om 2 cells + @ { cap }
  a u fnv cap 1- and { h }
  begin
    om 4 cells + @ h cells + @ { v }
    v 0= if -1 exit then
    v 0> if
      v 1- om om-ent { e }
      e @ 0<> if e s@ a u str=cs if v exit then then
    then
    h 1+ cap 1- and to h
  again ;
: om-find ( a u om -- slot|0 ) { a u om }
  a u om om-probe dup 0< if drop 0 exit then
  1- om om-val ;
: om-reindex ( om -- ) { om }
  om 2 cells + @ 2* { ncap }
  ncap cells allocate throw dup ncap cells erase { nidx }
  om 4 cells + @ free throw  nidx om 4 cells + !
  om 5 cells + @ ncap 2 / ncap 4 / + om 3 cells + @ 2 + cells * resize throw om 5 cells + !
  ncap om 2 cells + !
  om om-used 0 ?do
    i om om-live? if
      i om om-key fnv ncap 1- and { h }
      begin nidx h cells + @ 0<> while h 1+ ncap 1- and to h repeat
      i 1+ nidx h cells + !
    then
  loop ;
: om-put ( a u om -- slot ) { a u om }
  a u om om-find ?dup if exit then
  om om-used 1+ om 2 cells + @ 2 / 1+ > if om om-reindex then
  om om-used { n }
  n om om-ent { e }
  a u hdup e s!
  e 2 cells + om 3 cells + @ cells erase
  a u fnv om 2 cells + @ 1- and { h }
  begin om 4 cells + @ h cells + @ 0> while h 1+ om 2 cells + @ 1- and to h repeat
  n 1+ om 4 cells + @ h cells + !
  n 1+ om cell+ !  om @ 1+ om !
  e 2 cells + ;
: om-del ( a u om -- ) { a u om }
  a u om om-probe dup 0< if drop exit then
  1- { n }
  \ index 表の該当位置を -1 (削除済み) にする
  a u fnv om 2 cells + @ 1- and { h }
  begin om 4 cells + @ h cells + @ n 1+ <> while h 1+ om 2 cells + @ 1- and to h repeat
  -1 om 4 cells + @ h cells + !
  0 n om om-ent !
  om @ 1- om ! ;
: om-clear ( om -- ) { om }
  om 4 cells + @ om 2 cells + @ cells erase
  0 om !  0 om cell+ ! ;
: om-each ( xt om -- ) { xt om }       \ xt: ( key-a key-u slot -- )
  om om-used 0 ?do
    i om om-live? if i om om-key i om om-val xt execute then
  loop ;

\ ---- メッセージの組み立て用バッファ ----
create mbuf 8192 allot
variable mb-u
: mb-reset ( -- ) 0 mb-u ! ;
: mb+ ( a u -- ) dup mb-u @ + 8191 > if 2drop exit then dup >r mbuf mb-u @ + swap move r> mb-u +! ;
: mb-n ( n -- ) n>s mb+ ;
: mb-c ( c -- ) mbuf mb-u @ + c! 1 mb-u +! ;
: mb-get ( -- a u ) mbuf mb-u @ ;

\ ---- 辞書の写し ----
: om-copy ( src dst -- ) { src dst }
  dst om-clear
  src om-used 0 ?do
    i src om-live? if
      i src om-key dst om-put
      i src om-val swap src 3 cells + @ cells move
    then
  loop ;
