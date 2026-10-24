\ elf8.fs -- リロケーションの記録 (ラベル差のグループ)

decimal

variable g-fm variable g-foff variable g-fsh variable g-fbias
: field-load ( rt -- f ) mt-field? if g-fbias ! g-fsh ! g-foff ! g-fm ! true else false then ;
variable g-na  variable g-nu  variable g-abs  variable g-first  variable g-nw  variable g-nb
: scale* ( q -- q' ) e-scale @ qn q* ;
: nbytes ( -- n ) g-nb @ ;

\ ラベル差 hint: terms [0]=n, 項 (sign a u) が cell 5 から
: terms-n ( terms -- n ) @ ;
: term@ ( terms i -- addr ) 3 * 5 + cells + ;
: term-sign ( terms i -- sg ) term@ @ ;
: term-name ( terms i -- a u ) term@ cell+ dup @ swap cell+ @ ;

: first-pos-term ( terms -- a u true | false ) { terms }
  terms terms-n 0 ?do terms i term-sign 0> if terms i term-name true unloop exit then loop false ;
: first-neg-term ( terms -- a u true | false ) { terms }
  terms terms-n 0 ?do terms i term-sign 0< if terms i term-name true unloop exit then loop false ;
: has-dollar-neg? ( terms -- f ) { terms }
  terms terms-n 0 ?do
    terms i term-sign 0< if terms i term-name s" $$" str=cs if true unloop exit then then
  loop false ;
: has-plus? ( terms -- f ) { terms }
  terms terms-n 0 ?do terms i term-sign 0> if true unloop exit then loop false ;
: terms-sum ( terms -- n ) { terms } 0 terms terms-n 0 ?do terms i term-sign + loop ;

\ 現在のセクションの先頭からのワード数 (欄の位置)
: field-pw ( w -- n ) pc @ + e-epc @ - e-cw @ + ;
: sec-bytes ( w -- n ) field-pw e-bpw @ * ;

: src-rtype ( sl -- rt|-1 ) ?dup if lab-rtype else -1 then ;

: sec-is-cur? ( sl -- f ) lab-sec e-sa @ e-su @ str=cs ;

\ ラベルの型が幅に合っていればそれを (_psrc の判定)
: pick-src-type ( a u sl -- rt|0 ) { na nu sl }
  sl src-rtype { rs }
  rs 0>= if
    na nu extern-untyped om-find 0= if
      rs mt-bytes@ { pex }
      pex 0< pex nbytes = or if rs exit then
    then
  then
  0 ;

: debug-warn ( -- ) ;

: diff-pc-case ( terms dcst -- ) { terms dcst }
  terms first-pos-term 0= if exit then { pa pu }
  pa pu lab-find { ple }
  ple 0<> if ple lab-imported? 0= ple sec-is-cur? and else false then if exit then
  0 { prt }
  ple 0<> if pa pu ple pick-src-type to prt then
  0 { pp0 }  0 { pp1 }  false { havep }
  prt 0= if
    nbytes n>s mt-diff om-find ?dup if dup @ to pp0 cell+ @ to pp1 true to havep then
  then
  prt 0= havep 0= and if nbytes reloc-data-pcrel to prt then
  prt 0= havep 0= and if
    opt-debug @ if
      mb-reset s"  warning - no PC-relative relocation type for a " mb+ nbytes mb-n s" -byte reference to '" mb+ pa pu mb+
      s" '; relocation omitted." mb+ mb-get diag-w
    then
    exit
  then
  mt-rela? if g-first @ g-nw @ words-zero then
  g-first @ sec-bytes { psec }
  e-sa @ e-su @ psec pa pu havep if pp0 else prt then dcst scale* nbytes 0 rel-add
  havep if
    e-sa @ e-su @ psec anchor-at { an anu }
    e-sa @ e-su @ psec an anu pp1 0 nbytes 0 rel-add-n
  then ;

\ 同じセクションの 1 つのセクションだけに定義されたラベルの、足し引きが釣り合う差は定数
: diff-const? ( terms -- f ) { terms }
  s" " { fa fu }  true { first }
  terms terms-n 0 ?do
    terms i term-name lab-find { dle }
    dle 0= if false unloop exit then
    dle lab-imported? if false unloop exit then
    dle lab-sec nip 0= if false unloop exit then
    first if dle lab-sec to fu to fa false to first
    else dle lab-sec fa fu str=cs 0= if false unloop exit then then
  loop
  terms terms-sum 0= ;

: diff-pcguess ( terms dcst -- handled? ) { terms dcst }
  terms first-pos-term { pa pu pok }
  terms first-neg-term { ma mu mok }
  pok 0= if false exit then
  mok 0= if false exit then
  ma mu lab-find { mle }
  mle 0= if false exit then
  mle lab-imported? if false exit then
  mle lab-sec nip 0= if false exit then
  mle sec-is-cur? 0= if false exit then
  nbytes n>s mt-diff om-find if false exit then
  e-sa @ e-su @ mle q>n sec-rel-offset-impl 0= if false exit then { mw }
  pa pu lab-find { lle }
  0 { prt }
  lle 0<> if pa pu lle pick-src-type to prt then
  prt 0= if nbytes reloc-data-pcrel to prt then
  prt 0= if
    opt-debug @ if
      mb-reset s"  warning - no PC-relative relocation type for a " mb+ nbytes mb-n s" -byte reference to '" mb+ pa pu mb+
      s" '; relocation omitted." mb+ mb-get diag-w
    then
    true exit
  then
  g-first @ field-pw { pwo }
  mt-rela? if g-first @ g-nw @ words-zero then
  e-sa @ e-su @ pwo e-bpw @ * pa pu prt
  dcst pwo mw - qn q+ scale* nbytes 0 rel-add
  true ;

: dexpr-warn ( terms -- ) { terms }
  mb-reset s"  warning - no .elfdiff pair for the difference '" mb+
  terms terms-n 0 ?do
    terms i term-sign 0> if i 0> if 43 mb-c then else 45 mb-c then
    terms i term-name mb+
  loop
  s" '; relocation omitted." mb+ mb-get diag-w ;

: diff-general ( terms drt dfm dcst -- ) { terms drt dfm dcst }
  0 { pp0 }  0 { pp1 }  false { havep }
  false { dfd? }
  drt 0>= if
    drt rtk mt-diff-t om-find ?dup if dup @ to pp0 cell+ @ to pp1 true to havep then
    drt field-load if true to dfd?  dfm if dfm g-fm ! then then
  else
    nbytes n>s mt-diff om-find ?dup if dup @ to pp0 cell+ @ to pp1 true to havep then
  then
  havep 0= if
    opt-debug @ if terms dexpr-warn then
    exit
  then
  q0 { dconst }  0 { dw }  0 { dnb }
  drt 0>= if
    dcst scale* to dconst
    g-first @ dfd? if g-foff @ e-bpw @ / else 0 then + to dw
    dfd? if drt mt-bytes@ 0 max dup 0= if drop nbytes then else nbytes then to dnb
    dfd? mt-rela? and if
      dnb e-bpw @ / 1 max { nw }
      dw nw + nobj @ <= if dw nw g-fm @ words-clear-mask then
    then
  else
    g-first @ g-nw @ field-raw g-abs @ q- scale* to dconst
    g-first @ to dw  nbytes to dnb
    mt-rela? if g-first @ g-nw @ words-zero then
  then
  dw sec-bytes { dsec }
  false { dput }
  terms has-plus? { hp }
  2 0 do
    terms terms-n 0 ?do
      terms i term-sign { sg }
      sg 0> j 0= = if
        q0 { da }
        dput 0= sg 0> hp 0= or and if
          sg 0> if dconst else dconst qneg then to da  true to dput
        then
        e-sa @ e-su @ dsec terms i term-name sg 0> if pp0 else pp1 then da dnb dfd? if g-fm @ else 0 then rel-add
      then
    loop
  loop ;

: emit-diff-group ( hd -- ) { hd }
  g-first @ nobj @ >= if exit then
  hd hint@ { he }
  he 2 cells + @ { terms }  he 3 cells + @ { drt }  he 4 cells + @ { dfm }  hd hint-q { dcst }
  drt -1 = terms terms-n 2 = and if
    terms first-pos-term if
      2drop
      terms has-dollar-neg? if terms dcst diff-pc-case exit then
    then
  then
  elf-relaxing? 0= if terms diff-const? if exit then then
  drt -1 = terms terms-n 2 = and mt-pcg? and if
    terms dcst diff-pcguess if exit then
  then
  terms drt dfm dcst diff-general ;
