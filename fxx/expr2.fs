\ expr2.fs -- 式評価器の二項演算子以降

decimal

: fop2 ( a b xt -- q ) { a b xt } a qd b qd xt execute dq ;
: fzero? ( a -- f ) qd 0e f= ;
: div0-err ( -- )
  fdiv0-defer @ exp-float @ and if true fdiv0-seen ! else s"  error - Division by 0 error." xerr then ;
: fmod-py ( F: x b -- r )
  fover fover f/ ftrunc fover f* frot fswap f-
  fdup f0= 0= if
    fdup f0< fover f0< <> if fover f+ then
  then
  fswap fdrop ;

: pow-op ( x t -- q ) { x t }
  x t u2? if qundef exit then
  exp-float @ if x qd t qd f** dq exit then
  t q-neg? if
    s"  error - Negative exponent in ** expression; result set to 0." xerr q0 exit
  then
  t 1024 q-nonneg-gt? if
    mb-reset s"  error - Exponent " mb+ t q>dec mb+
    s"  exceeds maximum 1024 in ** expression; result set to 0." mb+ mb-get xerr q0 exit
  then
  t q>n { ti }
  x qnbit { bb }
  ti 1 max { ef }
  bb ef * 256 > if
    s"  error - ** result would exceed 256 bits (chained exponentiation); result set to 0." xerr q0 exit
  then
  x t qpow ;

: term0_0 ( -- q )
  factor
  begin s" **" qtxt? while 2 adv factor pow-op repeat ;

: mul-op ( x t -- q ) 2dup u2? if 2drop qundef exit then exp-float @ if ['] f* fop2 else q* then ;
: floordiv-op ( x t -- q ) { x t }
  x t u2? if qundef exit then
  exp-float @ if
    t fzero? if div0-err 0e dq exit then
    x qd t qd f/ floor dq exit
  then
  t q-zero? if div0-err q0 exit then
  x t qfloordiv ;
: div-op ( x t -- q ) { x t }
  x t u2? if qundef exit then
  exp-float @ if
    t fzero? if div0-err 0e dq exit then
    x qd t qd f/ dq exit
  then
  t q-zero? if div0-err q0 exit then
  x t qtruncdiv ;
: mod-op ( x t -- q ) { x t }
  x t u2? if qundef exit then
  exp-float @ if
    t fzero? if div0-err 0e dq exit then
    x qd t qd fmod-py dq exit
  then
  t q-zero? if div0-err q0 exit then
  x t qmod ;

: term0 ( -- q )
  term0_0
  begin
    cur 42 = 1 ch 42 <> and if 1 adv term0_0 mul-op true else
    s" //" qtxt? if 2 adv term0_0 floordiv-op true else
    cur 47 = 1 ch 47 <> and if 1 adv term0_0 div-op true else
    cur 37 = if 1 adv term0_0 mod-op true else
    false
    then then then then
  0= until ;

: add-op ( x t -- q ) 2dup u2? if 2drop qundef exit then exp-float @ if ['] f+ fop2 else q+ then ;
: sub-op ( x t -- q ) 2dup u2? if 2drop qundef exit then exp-float @ if ['] f- fop2 else q- then ;
: term1 ( -- q )
  term0
  begin
    cur 43 = if 1 adv term0 add-op true else
    cur 45 = if 1 adv term0 sub-op true else
    false
    then then
  0= until ;

65536 constant SHIFT-MAX
: shift-count ( t opname-a u -- n ok ) { t oa ou }        \ エラーなら ok=false
  t oa ou safe-bw { sop }
  sop q-neg? if
    mb-reset s"  error - negative shift count (" mb+ sop q>dec mb+ s" ) in " mb+ oa ou mb+ s"  expression." mb+
    mb-get xerr 0 false exit
  then
  sop SHIFT-MAX q-nonneg-gt? if
    mb-reset s"  error - shift count " mb+ sop q>dec mb+ s"  exceeds maximum 65536 in " mb+ oa ou mb+
    s"  expression." mb+ mb-get xerr 0 false exit
  then
  sop q>n true ;
: term2 ( -- q )
  term1
  begin
    s" <<" qtxt? if
      2 adv term1 { t } { x }
      x t u2? if qundef else
        t s" <<" shift-count if { n } x s" <<" safe-bw n qshl bw-result else drop q0 then
      then true
    else
    s" >>" qtxt? if
      2 adv term1 { t } { x }
      x t u2? if qundef else
        t s" >>" shift-count if { n } x s" >>" safe-bw n qsar bw-result else drop q0 then
      then true
    else
    false
    then then
  0= until ;

: bitop ( x t xt opname-a u -- q ) { x t xt oa ou }
  x t u2? if qundef exit then
  x oa ou safe-bw  t oa ou safe-bw  xt execute bw-result ;
: term3 ( -- q )
  term2
  begin cur 38 = 1 ch 38 <> and while 1 adv term2 ['] qand s" &" bitop repeat ;
: term4 ( -- q )
  term3
  begin cur 124 = 1 ch 124 <> and while 1 adv term3 ['] qor s" |" bitop repeat ;
: term5 ( -- q )
  term4
  begin cur 94 = while 1 adv term4 ['] qxor s" ^" bitop repeat ;

: sext-op? ( -- f ) 1 begin dup ch spc? while 1+ repeat ch dup digc? swap 40 = or ;
: sext-apply ( x t -- q ) { x t }
  x t u2? if qundef exit then
  x num-operand 0= if drop q0 bw-result exit then { xv }
  t num-operand 0= if drop q0 bw-result exit then { tv }
  xv tv qsext { r warn }
  warn report? and if
    mb-reset s"  warning - sign-extension bit width " mb+ tv q>dec mb+
    s"  exceeds maximum 128, result set to 0." mb+ mb-get xwarn
  then
  r bw-result ;
: term6 ( -- q )
  term5
  begin cur 39 = sext-op? and while 1 adv term5 sext-apply repeat ;

: cmp-op ( x t kind -- q ) { x t kind }
  x t u2? if qundef exit then
  exp-float @ if
    x qd t qd
    kind case
      0 of f<= endof  1 of f< endof  2 of f>= endof  3 of f> endof  4 of f= endof  5 of f<> endof
    endcase
  else
    kind case
      0 of x t q<= endof  1 of x t q< endof  2 of x t q>= endof  3 of x t q> endof
      4 of x t q= endof   5 of x t q= 0= endof
    endcase
  then
  expr-bool ;
: term7 ( -- q )
  term6
  begin
    s" <=" qtxt? if 2 adv term6 0 cmp-op true else
    cur 60 = 1 ch 60 <> and if 1 adv term6 1 cmp-op true else
    s" >=" qtxt? if 2 adv term6 2 cmp-op true else
    cur 62 = 1 ch 62 <> and if 1 adv term6 3 cmp-op true else
    s" ==" qtxt? if 2 adv term6 4 cmp-op true else
    s" !=" qtxt? if 2 adv term6 5 cmp-op true else
    false
    then then then then then then
  0= until ;

\ ---- 読み飛ばし (短絡) ----
: skip-char-literal ( i -- i' ) { i }
  i 1+ { j }
  j ach 92 = j 1+ ex-u @ < and if
    j 1+ ach { e }
    e uc 88 = if
      j 2 + { k } 0 { nd }
      begin k ex-u @ < nd 2 < and if k ach xdig? else false then while k 1+ to k nd 1+ to nd repeat
      k ex-u @ < if k ach 39 = if k 1+ exit then then
    else
      j 2 + ex-u @ < if j 2 + ach 39 = if j 3 + exit then then
    then
  else
    j ex-u @ < j 1+ ex-u @ < and if j 1+ ach 39 = if j 2 + exit then then
  then
  i 1+ ;
: skip-sub ( i until-or? -- i' ) { i uo } 0 0 0 { pd bd od }
  begin i ex-u @ < i ach 0<> and while
    i ach { c }
    c 39 = if i skip-char-literal to i else
    uo pd 0= and bd 0= and od 0= and c 124 = and i 1+ ach 124 = and if i exit then
    c 40 = if pd 1+ to pd i 1+ to i else
    c 41 = if pd 0> if pd 1- to pd i 1+ to i else i exit then else
    c 91 = if bd 1+ to bd i 1+ to i else
    c 93 = if bd 0> if bd 1- to bd i 1+ to i else i exit then else
    pd 0= bd 0= and od 0= and c 63 = c 44 = or c 59 = or and if i exit then
    pd 0= bd 0= and od 0= and c 58 = and i 1+ ach 61 <> and if i exit then
    i 1+ to i
    then then then then then
  repeat
  i ;
: skip-ternary ( i depth -- i' ) { i dp }
  dp EXPR-MAX-DEPTH > if i exit then
  i false skip-sub to i
  i ach 63 = i 1+ ach 61 <> and if
    i 1+ to i
    begin i ach spc? while i 1+ to i repeat
    i dp 1+ recurse to i
    begin i ach spc? while i 1+ to i repeat
    i ach 58 = i 1+ ach 61 <> and if
      i 1+ to i
      begin i ach spc? while i 1+ to i repeat
      i dp 1+ recurse to i
    then
  then
  i ;

: term9 ( -- q )
  term7
  begin s" &&" qtxt? while
    dup qundef? 0= over expr-false? and if
      drop ep @ 2 + true skip-sub ep ! 0 expr-bool
    else
      2 adv term7 { t } { x }
      x t u2? if qundef else x expr-false? 0= t expr-false? 0= and expr-bool then
    then
  repeat ;
: term10 ( -- q )
  term9
  begin s" ||" qtxt? while
    dup qundef? 0= over expr-false? 0= and if
      drop ep @ 2 + false skip-sub ep ! 1 expr-bool
    else
      2 adv term9 { t } { x }
      x t u2? if qundef else x expr-false? 0= t expr-false? 0= or expr-bool then
    then
  repeat ;

: colon-sep? ( i -- f ) dup ach 58 = swap 1+ ach 61 <> and ;
: term11 ( -- q )
  term10
  cur 63 = if
    expr-depth @ EXPR-MAX-DEPTH >= if
      s"  error - expression nesting too deep." xerr
      drop 1 adv skipsp
      ep @ 0 skip-ternary ep !  skipsp
      ep @ colon-sep? if ep @ 1+ ep ! skipsp ep @ 0 skip-ternary ep ! then
      q0 exit
    then
    1 expr-depth +!
    1 adv skipsp
    expr-false? if
      ep @ 0 skip-ternary { se }
      se colon-sep? if
        se 1+ ep !  skipsp recurse
      else se ep ! q0 then
    else
      recurse skipsp
      ep @ colon-sep? if ep @ 1+ ep ! skipsp ep @ 0 skip-ternary ep ! then
    then
    -1 expr-depth +!
  then ;

: expr-top ( -- q ) skipsp term11 ;
' expr-top is expr

\ ---- 入口 ----
: ev-ctx ( a u pos xt -- q pos' ) { a u pos xt } 0 0 0 { oa ou op }
  ex-a @ to oa  ex-u @ to ou  ep @ to op
  a ex-a !  u ex-u !  pos ep !
  xt execute ep @
  oa ex-a !  ou ex-u !  op ep ! ;
: ev-caps ( a u pos pv vl xt -- q pos' ) { a u pos pv vl xt } 0 0 { opv ovl }
  caps-pat @ to opv  caps-vliw @ to ovl
  pv caps-pat !  vl caps-vliw !
  a u pos xt ev-ctx
  opv caps-pat !  ovl caps-vliw ! ;
: expr-pat ( a u pos -- q pos' ) true true ['] expr-top ev-caps ;     \ パターン行の式
: expr-asm ( a u pos -- q pos' ) false false ['] expr-top ev-caps ;   \ アセンブリ行の式
: expr-mini ( a u pos -- q pos' ) false false ['] expr-top ev-caps ;
: factor-at ( a u pos -- q pos' ) ['] factor ev-ctx ;
: esc-limit ( a u pos stop -- lim ) { a u pos stop } 0 { dp }
  u pos ?do
    a i + c@ { c }
    c stop = dp 0= and if i unloop exit then
    c 40 = c 91 = or if dp 1+ to dp else
    c 41 = c 93 = or if dp 0> if dp 1- to dp then then then
  loop
  u ;
: expr-esc ( a u pos stop -- q pos' ) { a u pos stop } 0 { lim }
  stop 0= if a u pos ['] expr-top ev-ctx exit then
  a u pos stop esc-limit to lim
  a lim pos ['] expr-top ev-ctx ;
: expr-esc-float ( a u pos stop -- q pos' )
  exp-float @ { pf }  true exp-float !
  expr-esc
  pf exp-float ! ;
