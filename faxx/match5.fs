\ match5.fs -- 照合 (続き): .sub の展開と 1 行の照合

decimal

: sub-value ( a u -- q ) { a u } 0 { idx }
  16 QB * ar-alloc { vals }  0 { cnt }
  begin idx u < while
    a idx + c@ 44 = if idx 1+ to idx else
      a u idx expr-pat to idx { v }
      cnt 16 < if v vals cnt QB * + q! then
      cnt 1+ to cnt
      idx u < if a idx + c@ 44 = else false then if idx 1+ to idx else u to idx then
    then
  repeat
  cnt 0= if q0 exit then
  cnt 1 = if vals qcopy exit then
  bts @ 0> if bts @ else 8 then { bw }
  q1 bw qshl q1 q- { mask }
  q0 { acc }
  cnt 16 min 0 ?do acc bw qshl vals i QB * + mask qand qor to acc loop
  acc ;

: apply-binds ( -- )
  nbinds @ 0 ?do
    nbinds @ 1- i - { d }
    bind-va d cells + @ bind-vu d cells + @ true vslot { sl }
    bind-ea d cells + @ bind-eu d cells + @ sub-value { v }
    sl v false exp-float @ vput
  loop
  nbinds @ 0 ?do
    bind-va i cells + @ bind-vu i cells + @ true vslot { sl }
    sl span-s i cells + @ span-e i cells + @ 0 cap-text
  loop ;

: mk-open ( depth -- a u ) 2 ar-alloc { m } SUB-OPEN m c!  48 + m 1+ c!  m 2 ;
: mk-close ( depth -- a u ) 2 ar-alloc { m } SUB-CLOSE m c!  48 + m 1+ c!  m 2 ;

: match-sub ( a u depth -- flag ) { a u depth } 0 0 0 0 0 0 { st end na nu va vu }
  a u 0 sub-find-ref 0= if
    a u match-text if depth nbinds ! apply-binds true else false then exit
  then
  to vu to va to nu to na to end to st
  na nu subs om-find dup 0= na nu supper freed-subs om-find 0<> or if
    drop
    mb-reset s"  error - !S{{" mb+ na nu mb+ s" }}: no sub table named '" mb+ na nu mb+
    s" ' (define it with '.sub::" mb+ na nu mb+ s"  ... .return')." mb+ mb-get diag-e
    false exit
  then
  @ { arr }
  depth 8 >= if
    s"  error - !S{{...}}: sub table expansion exceeds maximum depth 8." diag-e false exit
  then
  arr arr-n 2 / 0 ?do
    ar-mark { mk }
    arr i 2 * arr-item item-str { pa pu }
    arr i 2 * 1+ arr-item item-str { xa xu }
    va depth cells bind-va + !  vu depth cells bind-vu + !
    xa depth cells bind-ea + !  xu depth cells bind-eu + !
    a st depth mk-open sconcat pa pu sconcat depth mk-close sconcat a end + u end - sconcat
    depth 1+ recurse if true unloop exit then
    mk ar-release
  loop
  false ;

\ 1 行 (row) のパターン欄 0 とソース (ms-a ms-u) の照合。成功ならスコアは n-expr n-lit n-sym
: match-row ( row -- flag ) rf0 0 match-sub ;

\ ---- 読み込み時の .sub 参照の検査 (axx.py の check_sub_refs) ----
: sub-check-unknown ( ta tu wa wu -- ) { ta tu wa wu }
  0 { from }
  begin ta tu from sub-find-ref while
    { st end na nu va vu }
    na nu subs om-find 0= if
      mb-reset s"  error - !S{{" mb+ na nu mb+ s" }} in " mb+ wa wu mb+
      s" : no sub table named '" mb+ na nu mb+ s" ' (define it with '.sub::" mb+ na nu mb+
      s"  ... .return')." mb+ mb-get diag-e
    then
    end to from
  repeat ;
2 lazy-om subchk-mark
create sub-stk-a 64 cells allot  create sub-stk-u 64 cells allot
: sub-walk ( na nu depth -- ) { na nu depth }
  na nu subchk-mark om-find ?dup if
    @ 2 = if exit then
    mb-reset s"  error - sub table '" mb+ na nu mb+ s" ' is circular (" mb+
    depth 0 ?do sub-stk-a i cells + @ sub-stk-u i cells + @ mb+ s"  -> " mb+ loop
    na nu mb+ s" ); expansion would not terminate." mb+ mb-get diag-e
    exit
  then
  na nu subchk-mark om-put 1 swap !
  depth 63 < if na depth cells sub-stk-a + !  nu depth cells sub-stk-u + ! then
  na nu subs om-find ?dup if
    @ { arr }
    arr arr-n 2 / 0 ?do
      arr i 2 * arr-item item-str { pa pu }
      0 { from }
      begin pa pu from sub-find-ref while
        { st end ra ru va vu }
        ra ru subs om-find if ra ru depth 1+ recurse then
        end to from
      repeat
    loop
  then
  na nu subchk-mark om-put 2 swap ! ;
: check-sub-refs-impl ( -- )
  nrows @ 0 ?do i rf0 trim nip if i rf0 s" pattern" sub-check-unknown then loop
  subs om-used 0 ?do
    i subs om-live? if
      i subs om-key { na nu }
      na nu subs om-find @ { arr }
      mb-reset s" sub table '" mb+ na nu mb+ s" '" mb+ mb-get sdup { wa wu }
      arr arr-n 2 / 0 ?do arr i 2 * arr-item item-str wa wu sub-check-unknown loop
    then
  loop
  subchk-mark om-clear
  subs om-used 0 ?do
    i subs om-live? if i subs om-key 0 sub-walk then
  loop ;
bind check-sub-refs-impl check-sub-refs
