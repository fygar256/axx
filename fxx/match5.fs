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

: match-sub ( a u depth -- flag ) { a u depth } 0 0 0 0 0 0 { i end na nu va vu }
  a u 0 sub-find-ref 0= if
    a u match-text if depth nbinds ! apply-binds true else false then exit
  then
  to vu to va to nu to na to end to i
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
    arr i 2 * arr-item item-str { pa pu }
    arr i 2 * 1+ arr-item item-str { xa xu }
    va depth cells bind-va + !  vu depth cells bind-vu + !
    xa depth cells bind-ea + !  xu depth cells bind-eu + !
    a i depth mk-open sconcat pa pu sconcat depth mk-close sconcat a end + u end - sconcat
    depth 1+ recurse if true unloop exit then
  loop
  false ;

\ 1 行 (row) のパターン欄 0 とソース (ms-a ms-u) の照合。成功ならスコアは n-expr n-lit n-sym
: match-row ( row -- flag ) rf0 0 match-sub ;
