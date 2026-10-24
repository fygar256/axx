\ elf5.fs -- -o のラベル参照の追跡 (label_refs_seen / var_to_label / insn_reloc_hint)

decimal


\ ---- .reloc の宣言 (変数名 -> rtype mask pairs) ----
3 om-new constant rcon
1 om-new constant reloc-badname

\ ---- 参照の記録 ----
8 cells constant REFSZ
16384 constant MAXREFS
MAXREFS REFSZ * allocate throw constant refs
variable nrefs
: ref@ ( i -- addr ) REFSZ * refs + ;
\ 参照: [0]=name-a [1]=name-u [2]=widx [3]=未使用 [4..7]=q
: ref-add ( a u q widx -- ) { a u q w }
  nrefs @ MAXREFS >= if exit then
  nrefs @ ref@ { e }
  a u intern e cell+ ! e !
  w e 2 cells + !
  q e 4 cells + q!
  1 nrefs +! ;
: ref-name ( e -- a u ) dup @ swap cell+ @ ;
: ref-widx ( e -- w ) 2 cells + @ ;
: ref-q ( e -- q ) 4 cells + ;

\ ---- ヒント ----
8 cells constant HSZ
4096 constant MAXH
MAXH HSZ * allocate throw constant hints
variable nhints
: hint@ ( i -- addr ) HSZ * hints + ;
\ [0]=kind (0 型つき / 1 'v' / 2 'd') [1]=widx [2]=a1 [3]=a2 [4]=a3 [5..]=q は別領域に
\ q は 4 セル必要なので 2 つの表に分ける
MAXH QB * allocate throw constant hintq
: hint-find ( kind widx -- idx|-1 ) { k w }
  nhints @ 0 ?do
    i hint@ { e }
    e @ k = e cell+ @ w = and if i unloop exit then
  loop -1 ;
\ setdefault。追加できたら添字、既にあれば -1
: hint-add ( kind widx -- idx|-1 ) { k w }
  k w hint-find 0>= if -1 exit then
  nhints @ MAXH >= if -1 exit then
  nhints @ { n }  n hint@ { e }
  k e !  w e cell+ !  0 e 2 cells + !  0 e 3 cells + !  0 e 4 cells + !
  n QB * hintq + QB erase
  1 nhints +!  n ;
: hint-q ( idx -- q ) QB * hintq + ;

\ ---- var_to_label ----
\ kind: 0 なし / 1 (name, value) / 2 リスト / 3 ラベル差 / 4 曖昧 (None)
create v2l-kind NVARS cells allot
create v2l-ptr  NVARS cells allot
: v2l-clear ( -- ) v2l-kind NVARS cells erase  v2l-ptr NVARS cells erase ;

\ 単一: [0]=a [1]=u [2..5]=q
: sg-new ( a u q -- p ) { a u q }
  6 cells ar-alloc { p }
  a u intern p cell+ ! p !
  q p 2 cells + q!  p ;
: sg-name ( p -- a u ) dup @ swap cell+ @ ;
: sg-q ( p -- q ) 2 cells + ;
\ リスト: [0]=n, 各項 6 セル
: ls-n ( p -- n ) @ ;
: ls-ent ( p i -- e ) 6 * 1+ cells + ;
: ls-new2 ( sg1 a u q -- p ) { s1 a u q }
  1 6 2 * + cells ar-alloc { p }
  2 p !
  s1 p 0 ls-ent 6 cells move
  a u intern p 1 ls-ent cell+ ! p 1 ls-ent !
  q p 1 ls-ent 2 cells + q!  p ;
: ls-append ( p a u q -- p' ) { p a u q }
  p ls-n { n }
  1 n 1+ 6 * + cells ar-alloc { r }
  n 1+ r !
  p cell+ r cell+ n 6 * cells move
  a u intern r n ls-ent cell+ ! r n ls-ent !
  q r n ls-ent 2 cells + q!  r ;

\ 取り込み中の変数 slot に 2 つ目以降のラベルが見えたとき
: v2l-second ( slot a u q -- ) { sl a u q }
  d-diff om-count 0> d-diff-t om-count 0> or mt-pcg? or 0= if 4 sl cells v2l-kind + ! exit then
  sl cells v2l-kind + @ case
    1 of sl cells v2l-ptr + @ a u q ls-new2 sl cells v2l-ptr + !  2 sl cells v2l-kind + ! endof
    2 of sl cells v2l-ptr + @ a u q ls-append sl cells v2l-ptr + ! endof
    4 sl cells v2l-kind + !
  endcase ;

\ ---- ラベルの読み ----
: trk-note-label ( a u q -- ) { a u q }
  trk-on @ 0= if exit then
  undef-flag @ if exit then
  a u lab-find ?dup if
    dup lab-equ? if lab-rtype 0>= 0= if exit then else drop then
  then
  trk-cap @ 0>= if
    trk-cap @ { sl }
    sl cells v2l-kind + @ 0= if
      a u q sg-new sl cells v2l-ptr + !  1 sl cells v2l-kind + !
    else sl a u q v2l-second then
  else trk-widx @ 0>= if a u q trk-widx @ ref-add then then ;
' trk-note-label is elf-note-label

\ ---- 変数の読み ----
: rcon-for ( slot -- sl|0 ) vslot-name rcon om-find ;
: rc-rt ( sl -- rt ) @ ;
: rc-mask ( sl -- m ) cell+ @ ;
: rc-pairs ( sl -- p ) 2 cells + @ ;

: note-var-diff ( slot x p -- ) { sl x p }
  p @ { nt } p 1 cells + { tot }
  \ p: [0]=nterms [1..4]=total q [5..]=項 (sign, a, u)
  \ 最初の足す項 (無ければ最初の項) の名前
  p 5 cells + 1 cells + @ p 5 cells + 2 cells + @ { ka ku }
  nt 0 ?do
    p 5 cells + i 3 * cells + { t }
    t @ 0> if t cell+ @ t 2 cells + @ to ku to ka leave then
  loop
  ka ku tot trk-widx @ ref-add
  x qundef-derived? if q0 else x tot q- then { cst }
  2 trk-widx @ hint-add { hi }
  hi 0>= if
    hi hint@ { e }
    p e 2 cells + !
    sl rcon-for ?dup if dup rc-rt e 3 cells + ! rc-mask else -1 e 3 cells + ! 0 then e 4 cells + !
    cst hi hint-q q!
  then ;

: trk-note-var ( slot x -- ) { sl x }
  trk-on @ 0= trk-widx @ 0< or if exit then
  sl 0< if exit then
  sl cells v2l-kind + @ case
    3 of sl x sl cells v2l-ptr + @ note-var-diff endof
    1 of
      sl cells v2l-ptr + @ { p }
      p sg-name p sg-q trk-widx @ ref-add
      x qundef-derived? 0= if
        1 trk-widx @ hint-add { hi }
        hi 0>= if x p sg-q q- hi hint-q q! then
        sl rcon-for ?dup if
          { rc }
          0 trk-widx @ hint-add { hj }
          hj 0>= if
            hj hint@ { e }
            rc rc-rt e 2 cells + !  rc rc-mask e 3 cells + !  rc rc-pairs e 4 cells + !
            x p sg-q q- hj hint-q q!
          then
        then
      then
    endof
  endcase ;
' trk-note-var is elf-note-var

\ ---- ラベル差 (_elf_diff_resolve) ----
64 constant DRMAX
create dr-ka DRMAX cells allot  create dr-ku DRMAX cells allot       \ 鍵 (大文字)
create dr-na DRMAX cells allot  create dr-nu DRMAX cells allot       \ 元の綴り
create dr-q  DRMAX QB * allot
create dr-cf DRMAX cells allot  create dr-seen DRMAX cells allot
create dr-ord DRMAX cells allot
create dr-stk 64 cells allot
variable dr-n  variable dr-nord

: diff-word? ( c -- f ) dup alnc? over 95 = or over 46 = or swap 36 = or ;

: dr-find ( a u -- idx|-1 ) { a u }
  dr-n @ 0 ?do i cells dr-ka + @ i cells dr-ku + @ a u str=cs if i unloop exit then loop -1 ;

\ pend: n 個の 6 セル項 (a u q4) の並び
: dr-load ( pend n -- ok ) { pend n }
  n DRMAX > if false exit then
  0 dr-n !
  n 0 ?do
    pend i 6 * cells + { e }
    e ref-name supper { ka ku }
    ka ku dr-find 0>= if false unloop exit then
    ka i cells dr-ka + !  ku i cells dr-ku + !
    e @ i cells dr-na + !  e cell+ @ i cells dr-nu + !
    e 2 cells + i QB * dr-q + q!
    0 i cells dr-cf + !  0 i cells dr-seen + !
    1 dr-n +!
  loop
  0 dr-nord !
  true ;

: dr-run ( ta tu -- p|0 ) { ta tu }
  1 dr-stk !  0 { sp }  1 { sign }  true { expect }  0 { i }
  begin i tu < while
    ta i + c@ { c }
    c 32 = c 9 = or c 0= or if i 1+ to i else
    c 43 = c 45 = or if
      c 45 = if -1 else 1 then { sg }
      expect if sign sg * to sign else sg to sign true to expect then
      i 1+ to i
    else c 40 = if
      expect 0= sp 62 > or if 0 exit then
      dr-stk sp cells + @ sign * dr-stk sp 1+ cells + !  sp 1+ to sp  1 to sign
      i 1+ to i
    else c 41 = if
      sp 0= expect or if 0 exit then
      sp 1- to sp  i 1+ to i
    else c diff-word? c 39 = or if
      expect 0= if 0 exit then
      i { j }
      c 39 = if
        i 1+ { k }
        begin k tu < if ta k + c@ 39 <> else false then while k 1+ to k repeat
        k tu >= if 0 exit then
        k 1+ to j
      else
        begin j tu < if ta j + c@ diff-word? else false then while j 1+ to j repeat
        ta i + j i - supper dr-find { ix }
        ix 0>= if
          ix cells dr-seen + @ 0= if
            1 ix cells dr-seen + !  0 ix cells dr-cf + !
            ix dr-nord @ cells dr-ord + !  1 dr-nord +!
          then
          ix cells dr-cf + @ dr-stk sp cells + @ sign * + ix cells dr-cf + !
        then
      then
      false to expect  1 to sign  j to i
    else 0 exit
    then then then then then
  repeat
  sp 0<> expect or if 0 exit then
  dr-nord @ dr-n @ <> if 0 exit then
  dr-nord @ 0 ?do
    dr-ord i cells + @ cells dr-cf + @ abs 1 <> if 0 unloop exit then
  loop
  \ 結果: [0]=nt [1..4]=total [5..]=項
  dr-nord @ 3 * 5 + cells ar-alloc { p }
  dr-nord @ p !
  q0 { tot }
  dr-nord @ 0 ?do
    dr-ord i cells + @ { ix }
    ix cells dr-cf + @ { cf }
    cf p 5 cells + i 3 * cells + !
    ix cells dr-na + @ p 5 cells + i 3 * cells + cell+ !
    ix cells dr-nu + @ p 5 cells + i 3 * cells + 2 cells + !
    cf qn ix QB * dr-q + q* tot q+ to tot
  loop
  tot p 1 cells + q!
  p ;

\ 変数 slot の取り込みが終わったところ
: v2l-finish ( slot ta tu -- ) { sl ta tu }
  trk-on @ 0= if exit then
  sl 0< if exit then
  sl cells v2l-kind + @ { kd }
  kd 2 = if
    sl cells v2l-ptr + @ { lp }
    lp cell+ lp ls-n dr-load if ta tu dr-run else 0 then ?dup if
      sl cells v2l-ptr + !  3 sl cells v2l-kind + !
    else 4 sl cells v2l-kind + ! then
    exit
  then
  kd 1 = if
    sl cells v2l-ptr + @ { sp }
    sl rcon-for 0= mt-pcg? and if
      12 cells ar-alloc { two }
      sp two 6 cells move
      s" $$" intern two 6 cells + cell+ ! two 6 cells + !
      loc-counter two 6 cells + 2 cells + q!
      two 2 dr-load if
        ta tu dr-run ?dup if
          { r }
          r @ 2 = if
            r 5 cells + @ { s0 }  r 8 cells + @ { s1 }
            r 5 cells + 1 cells + @ r 5 cells + 2 cells + @ { a0 u0 }
            r 8 cells + 1 cells + @ r 8 cells + 2 cells + @ { a1 u1 }
            sp sg-name { na nu }
            s0 -1 = if a0 u0 s" $$" str=cs s1 1 = and a1 u1 na nu str=cs and else false then
            s0 1 = if a0 u0 na nu str=cs s1 -1 = and a1 u1 s" $$" str=cs and or then
            if
              r sl cells v2l-ptr + !  3 sl cells v2l-kind + !  exit
            then
          then
        then
      then
    then
    sp 1 dr-load if
      ta tu dr-run ?dup if
        { r }
        r 5 cells + @ 0< if
          d-diff om-count 0> d-diff-t om-count 0> or if
            r sl cells v2l-ptr + !  3 sl cells v2l-kind + !
          else 4 sl cells v2l-kind + ! then
        then
      then
    then
  then ;
' v2l-finish is elf-cap-finish

\ ---- 行の始め・終わり ----
: trk-line-begin ( -- )
  pass @ 2 = o-obj-u @ 0<> and if
    true trk-on !  0 nrefs !  -1 trk-widx !  -1 trk-cap !  0 nhints !  v2l-clear
  then ;
: trk-line-end ( -- ) false trk-on ! ;
' trk-line-begin is elf-line-begin
' trk-line-end is elf-line-end

\ ---- 保存と復元 (候補の試行、[[ ]] の組合せ) ----
16 constant TFRAMES
create fr-nrefs TFRAMES cells allot
create fr-nhints TFRAMES cells allot
create fr-kind TFRAMES NVARS * cells allot
create fr-ptr  TFRAMES NVARS * cells allot
variable nfr
: trk-push-i ( -- )
  trk-on @ 0= if exit then
  nfr @ TFRAMES >= if exit then
  nrefs @ nfr @ cells fr-nrefs + !  nhints @ nfr @ cells fr-nhints + !
  v2l-kind nfr @ NVARS * cells fr-kind + NVARS cells move
  v2l-ptr nfr @ NVARS * cells fr-ptr + NVARS cells move
  1 nfr +! ;
' trk-push-i is trk-push
: trk-top-restore-i ( -- )
  trk-on @ 0= if exit then
  nfr @ 0= if exit then
  nfr @ 1- { f }
  f cells fr-nrefs + @ nrefs !  f cells fr-nhints + @ nhints !
  f NVARS * cells fr-kind + v2l-kind NVARS cells move
  f NVARS * cells fr-ptr + v2l-ptr NVARS cells move ;
' trk-top-restore-i is trk-top-restore
: trk-pop-i ( -- ) trk-on @ 0= if exit then nfr @ 0> if -1 nfr +! then ;
' trk-pop-i is trk-pop

\ ---- 最良の候補の写し ----
MAXREFS REFSZ * allocate throw constant best-refs
variable best-nrefs  variable best-base-r
MAXH HSZ * allocate throw constant best-hints
MAXH QB * allocate throw constant best-hintq
variable best-nhints  variable best-base-h
create best-kind NVARS cells allot
create best-ptr  NVARS cells allot
variable cand-nr  variable cand-nh
create cand-kind NVARS cells allot
create cand-ptr  NVARS cells allot
: trk-cand-begin-i ( -- )
  trk-on @ 0= if exit then
  nrefs @ cand-nr !  nhints @ cand-nh !
  v2l-kind cand-kind NVARS cells move  v2l-ptr cand-ptr NVARS cells move ;
' trk-cand-begin-i is trk-cand-begin
: trk-cand-best-i ( -- )
  trk-on @ 0= if exit then
  cand-nr @ best-base-r !  nrefs @ cand-nr @ - best-nrefs !
  best-nrefs @ 0 > if cand-nr @ ref@ best-refs best-nrefs @ REFSZ * move then
  cand-nh @ best-base-h !  nhints @ cand-nh @ - best-nhints !
  best-nhints @ 0> if
    cand-nh @ hint@ best-hints best-nhints @ HSZ * move
    cand-nh @ hint-q best-hintq best-nhints @ QB * move
  then
  v2l-kind best-kind NVARS cells move  v2l-ptr best-ptr NVARS cells move ;
' trk-cand-best-i is trk-cand-best
: trk-cand-restore-i ( -- )
  trk-on @ 0= if exit then
  cand-nr @ nrefs !  cand-nh @ nhints !
  cand-kind v2l-kind NVARS cells move  cand-ptr v2l-ptr NVARS cells move ;
' trk-cand-restore-i is trk-cand-restore
: trk-best-install-i ( -- )
  trk-on @ 0= if exit then
  best-base-r @ nrefs !
  best-nrefs @ 0> if best-refs nrefs @ ref@ best-nrefs @ REFSZ * move  best-nrefs @ nrefs +! then
  best-base-h @ nhints !
  best-nhints @ 0> if
    best-hints nhints @ hint@ best-nhints @ HSZ * move
    best-hintq nhints @ hint-q best-nhints @ QB * move
    best-nhints @ nhints +!
  then
  best-kind v2l-kind NVARS cells move  best-ptr v2l-ptr NVARS cells move ;
' trk-best-install-i is trk-best-install

\ 誤り条件の事前評価 (pass1-probe) の前後
variable probe-nr  variable probe-nh  variable probe-widx
: trk-probe-begin-i ( -- ) nrefs @ probe-nr !  nhints @ probe-nh !  trk-widx @ probe-widx ! ;
' trk-probe-begin-i is trk-probe-begin
: trk-probe-end-i ( -- ) probe-nr @ nrefs !  probe-nh @ nhints !  probe-widx @ trk-widx ! ;
' trk-probe-end-i is trk-probe-end

\ ---- 出力語ごと ----
: trk-word-begin ( -- ) nobj @ trk-widx ! ;
: trk-word-drop ( -- )                                 \ その語の参照を捨てる
  nrefs @ 0 ?do i ref@ ref-widx trk-widx @ = if -2 i ref@ 2 cells + ! then loop ;
: trk-call-drop-i ( w -- ) { w }
  nrefs @ 0 ?do i ref@ ref-widx w = if -2 i ref@ 2 cells + ! then loop
  nhints @ 0 ?do
    i hint@ { e }
    e cell+ @ w = e @ 2 <> and if -2 e cell+ ! then
  loop ;
' trk-call-drop-i is elf-call-drop
' trk-word-begin is elf-word-begin
' trk-word-drop is elf-word-drop

: trk-shift-refs ( n -- ) { n }
  nrefs @ 0 ?do i ref@ 2 cells + { p } p @ 0>= if n p +! then loop ;
' trk-shift-refs is elf-shift-refs
