\ match2.fs -- 照合 (続き): 変数の捕捉・1 文字ずつの本体・[[ ]]・.sub

decimal

defer cap-float ( kind -- ok )                 \ !F !D !Q (kind = 文字)
: cap-float-nn49 drop false ; bind cap-float-nn49 cap-float

: sym-get-for ( va vu wa wu -- q true | false ) { va vu wa wu }
  va vu vartabs om-find ?dup if
    @ wa wu supper rot om-find ?dup if qcopy true else false then
  else wa wu nsym-get then ;
: sym-exists? ( va vu wa wu -- f ) sym-get-for dup if nip then ;
: sword-end ( -- n )
  0 sc digc? 0= 0 sc swc? and 0= if 0 exit then
  1 begin dup sc swc? while 1+ repeat ;
: arr-has-str? ( arr a u -- f ) { arr a u }
  arr arr-n 0 ?do arr i arr-item item-str a u str=cs if true unloop exit then loop false ;

: sym-cap ( -- flag )
  0 vname-at dup 0= if drop false exit then { n } 0 0 0 0 0 0 0 { na prev allowed omit wl fl ok }
  mt-a @ ti @ + to na
  n ti +!
  si @ to prev
  false p-alnum !
  na n slower chk-get to allowed
  allowed if allowed s" " arr-has-str? to omit then
  sword-end to wl
  ms-a @ prev + wl supper { wa wu }
  0 to fl
  na n wa wu sym-exists? if wl to fl else
    wl 1- { k }
    begin k 0> fl 0= and while
      wa k + c@ corec? 0= if
        na n wa k sym-exists? if k to fl then
      then
      k 1- to k
    repeat
  then
  fl 0> to ok
  ok allowed 0<> and if
    allowed wa fl arr-has-str? 0= if false to ok then
  then
  ok 0= allowed 0<> and if
    allowed arr-n 0> if
      0 { best }
      allowed arr-n 0 ?do
        allowed i arr-item item-str { ia iu }
        iu 0> iu best > and if
          prev iu + ms-u @ <= if
            ms-a @ prev + iu supper ia iu str=cs if iu to best then
          then
        then
      loop
      best 0> if
        ms-a @ prev + best supper { ba bu }
        na n ba bu sym-exists? if best to fl  true to ok then
      then
    then
  then
  ok if
    prev fl + si !
    ms-a @ prev + fl supper { qa qu }
    na n qa qu sym-get-for drop { v }
    na n true vslot { sl }
    sl v false exp-float @ vput
    sl prev si @ 0 cap-text
    1 n-sym +!  true exit
  then
  omit if
    prev si !
    na n true vslot dup q0 false exp-float @ vput
    0 0 vput-text
    1 n-sym +!  true exit
  then
  false ;

\ !x !Lx !!x の捕捉。kind: 0 式 / 1 因子 / 2 !L (式。テキスト置換モードでは未定義を 0 にする)
: cap-expr ( kind -- ok ) { kind } 0 0 0 0 0 0 0 0 0 { n na stop sl pr st cu v lp }
  0 vname-at to n
  n 0= if false exit then
  mt-a @ ti @ + to na
  n ti +!
  kind 1 <> if 0 var-stopchar to stop then
  na n true vslot to sl
  undef-flag @ to pr  false undef-flag !  false expr-missing !
  si @ to st
  sl trk-cap !
  textmode-lcap @ to lp
  kind 2 = textmode @ 0<> and if true textmode-lcap ! then
  kind 1 <> if ms-a @ ms-u @ si @ stop expr-esc else ms-a @ ms-u @ si @ factor-at then
  si !  to v
  lp textmode-lcap !
  -1 trk-cap !
  ncloses @ 0 ?do SUB-CLOSE i cells closes + @ sub-mark loop
  sl ms-a @ st + si @ st - elf-cap-finish
  undef-flag @ to cu
  kind 2 = if
    textmode @ if
      pr undef-flag !
      cu v qundef-derived? or if q0 to v then
      sl v false exp-float @ vput
    else
      pr cu or undef-flag !
      sl v cu exp-float @ vput
    then
  else
    pr cu or undef-flag !
    sl v cu exp-float @ vput
  then
  sl st si @ stop cap-text
  expr-missing @ if false exit then
  stop 0<> if 0 sc stop = if 1 si +! then then
  true ;

: cap-enum ( -- ok ) 0 vname-at dup 0= if drop false exit then { n }
  mt-a @ ti @ + n slower { na nu }
  n ti +!
  na nu enumdefs om-find dup 0= if false exit then
  si @ { st }
  enum-capture 0= if false exit then { v e }
  na nu true vslot { sl }
  sl v false exp-float @ vput
  e si !
  sl st si @ 0 cap-text
  true ;

: symset-item-at ( idx arr -- k end ) { idx arr } -1 { best } idx { be }
  arr arr-n 0 ?do
    arr i arr-item { it }
    it item-kind 1 = if
      it item-str { na nu }
      nu be idx - > if
        idx nu + ms-u @ <= if
          ms-a @ idx + nu supper na nu supper str=cs if
            idx nu + { e }
            e ms-u @ < if e ms-ach corec? else false then 0= if i to best  e to be then
          then
        then
      then
    then
  loop
  best be ;
: cap-yset ( -- ok ) 0 vname-at dup 0= if drop false exit then { sl0 }
  mt-a @ ti @ + sl0 slower { ka ku }
  sl0 ti +!
  0 tcc 91 <> if false exit then
  1 ti +!
  0 vname-at dup 0= if drop false exit then { n }
  mt-a @ ti @ + n slower { na nu }
  n ti +!
  0 tcc 93 <> if false exit then
  1 ti +!
  ka ku supper asym-get dup 0= if false exit then { arr }
  arr arr-n 0= if false exit then
  si @ arr symset-item-at { k e }
  k 0< if false exit then
  na nu true vslot { sl }
  sl si @ e 0 cap-text
  e si !
  sl k qn false exp-float @ vput
  -1 n-expr +!  1 n-sym +!
  true ;

\ ---- 1 文字ずつの本体 ----
: step-bs ( -- code )
  1 ti +!
  0 tcc mcb @ = ti @ mt-u @ < and 0= if 1 exit then
  0 tcc alnc? { la }
  la p-alnum @ and wbrk @ and if 1 exit then
  1 ti +!  1 si +!  1 n-lit +!  la p-alnum !
  0 ;
: step-cap ( -- code )
  mca @ mcb @ uc <> if 1 exit then
  p-alnum @ wbrk @ and if 1 exit then
  1 si +!  1 ti +!  1 n-lit +!  true p-alnum !
  0 ;
: step-lit ( -- code )
  mca @ mcb @ <> if 1 exit then
  mca @ alnc? p-alnum @ and wbrk @ and if 1 exit then
  1 ti +!  1 si +!  1 n-lit +!  mca @ alnc? p-alnum !
  0 ;
: step-plus ( -- code ) 1 ti +!  1 n-lit +!  false p-alnum !  0 ;
: step-bang ( -- code )
  1 n-expr +!  false p-alnum !  1 ti +!
  0 tcc
  dup 0= if drop 1 exit then
  dup 70 = over 68 = or over 81 = or if
    1 ti +! cap-float if 0 else 1 then exit
  then
  dup 76 = if drop 1 ti +! 2 cap-expr if 0 else 1 then exit then
  dup 33 = if drop 1 ti +! 1 cap-expr if 0 else 1 then exit then
  dup 69 = if drop 1 ti +! cap-enum if 0 else 1 then exit then
  dup 89 = if drop 1 ti +! cap-yset if 0 else 1 then exit then
  dup 83 = if drop 1 exit then
  drop 0 cap-expr if 0 else 1 then ;
: step-sym ( -- code ) sym-cap if 0 else 1 then ;

: step ( -- code )
  0 sc spc? s-sp !  0 tcc spc? t-sp !
  sskip tskip
  begin 0 tcc dup SUB-OPEN = swap SUB-CLOSE = or while
    0 tcc 1 tcc sub-mark
    2 ti +!
    0 tcc spc? if true t-sp ! then
    tskip
  repeat
  s-sp @ t-sp @ 0= and wbrk !
  0 sc mcb !  0 tcc mca !
  mca @ 0= mcb @ 0= and if 2 exit then
  mca @ 92 = if step-bs exit then
  mca @ capc? if step-cap exit then
  mca @ 33 = if step-bang exit then
  mca @ lowc? if step-sym exit then
  mca @ 43 = mcb @ 45 = and 1 expects-expr? and if step-plus exit then
  step-lit ;

: match1 ( -- flag )
  0 si !  0 ti !  0 n-expr !  0 n-lit !  0 n-sym !  false p-alnum !
  8 0 do 0 i cells span-s + !  0 i cells span-e + ! loop
  sskip tskip
  begin step dup 0= while drop repeat
  2 = ;
