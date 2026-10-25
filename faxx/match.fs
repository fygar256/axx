\ match.fs -- 命令の書式の照合 (PatternMatcher)

decimal

variable ms-a  variable ms-u        \ ソース行
variable mt-a  variable mt-u        \ パターン
variable si  variable ti
variable n-expr  variable n-lit  variable n-sym  variable p-alnum
variable s-sp  variable t-sp  variable wbrk  variable mca  variable mcb
30 constant SUB-OPEN
31 constant SUB-CLOSE
create span-s 8 cells allot
create span-e 8 cells allot
variable nbinds
create bind-va 8 cells allot   create bind-vu 8 cells allot
create bind-ea 8 cells allot   create bind-eu 8 cells allot

: sc ( off -- c ) si @ + dup ms-u @ < if ms-a @ + c@ else drop 0 then ;
: tcc ( off -- c ) ti @ + dup mt-u @ < if mt-a @ + c@ else drop 0 then ;
: ms-ach ( i -- c ) dup ms-u @ < if ms-a @ + c@ else drop 0 then ;
: sskip ( -- ) begin 0 sc spc? while 1 si +! repeat ;
: tskip ( -- ) begin 0 tcc spc? while 1 ti +! repeat ;
: sskip-from ( i -- i' ) begin dup ms-ach spc? while 1+ repeat ;
: expects-expr? ( off -- f )
  begin dup tcc dup spc? swap 30 = or over tcc 31 = or while
    dup tcc spc? if 1+ else 2 + then
  repeat tcc 33 = ;

: vname-at ( off -- n ) { off } 0 { n }                  \ パターン変数名の長さ
  off tcc lowc? 0= if 0 exit then
  1 to n
  begin off n + tcc dup lowc? over digc? or swap 95 = or while n 1+ to n repeat
  n ;

: sub-mark ( kind k -- ) { kind k }
  k 48 - { kk }
  kk 0 8 within 0= if exit then
  kind SUB-OPEN = if si @ kk cells span-s + !  si @ kk cells span-e + !
  else si @ kk cells span-e + ! then ;
: cap-text ( slot b e stop -- ) { sl b e stop }
  e b - { n }
  ms-a @ b + n
  stop 0<> n 0> and if 2dup + 1- c@ stop = if 1- then then
  trim sl -rot vput-text ;

\ 変数名の後ろの \c 止め文字。off は ti からの位置 (変数名の直後)
create closes 8 cells allot  variable ncloses
: var-stopchar ( off -- stopchar ) { off } off { j }
  0 ncloses !
  begin j tcc spc? while j 1+ to j repeat
  begin j tcc SUB-CLOSE = while
    j 1+ tcc ncloses @ 8 < if ncloses @ cells closes + ! 1 ncloses +! else drop then
    j 2 + to j
    begin j tcc spc? while j 1+ to j repeat
  repeat
  j tcc 92 = if
    j 1+ tcc { sc }  j 2 + ti +!  sc exit
  then
  0 ncloses !
  off { k }
  begin k tcc spc? while k 1+ to k repeat
  k ti +!  0 ;

\ ---- .enum ----
variable eb-names  variable eb-vals
: enum-name-at ( a u idx arr -- k end ) { a u idx arr } -1 { best } idx { be }
  arr arr-n 0 ?do
    arr i arr-item item-str { na nu }
    nu be idx - > if
      idx nu + u <= if
        a idx + nu na nu str=ci if
          idx nu + { e }
          e u < if a e + c@ corec? else false then 0= if i to best  e to be then
        then
      then
    then
  loop
  best be ;
: enum-match-impl ( -- q true | false )
  eb-names @ 0= if false exit then
  ex-a @ ex-u @ ep @ eb-names @ enum-name-at { k e }
  k 0< if false exit then
  e ep !  eb-vals @ k QB * + qcopy true ;
bind enum-match-impl enum-match

: enum-eval ( ea eu names present -- q true | false ) { ea eu names present }
  names arr-n QB * allocate throw { vals }
  names arr-n 0 ?do
    present i cells + @ 0= if vals i QB * + QB erase else
      names i arr-item item-str nsym-get 0= if vals free throw false unloop exit then
      vals i QB * + q!
    then
  loop
  eb-names @ { on }  eb-vals @ { ov }
  names eb-names !  vals eb-vals !
  ea eu 0 expr-pat drop qcopy { v }
  on eb-names !  ov eb-vals !
  vals free throw
  v true ;

: enum-capture ( slot -- q end true | false ) { slot } 0 0 0 0 0 0 { names ea eu present k1 e1 }
  slot @ to names  slot cell+ @ to ea  slot 2 cells + @ to eu
  names arr-n 1+ cells allocate throw to present  present names arr-n 1+ cells erase
  0 0 { pos pr }
  ms-a @ ms-u @ si @ sskip-from names enum-name-at to e1 to k1
  k1 0< if present free throw false exit then
  begin
    e1 to pos
    e1 sskip-from to pr
    pr ms-ach 45 = if
      ms-a @ ms-u @ pr 1+ sskip-from names enum-name-at { k2 e2 }
      k2 k1 >= if k2 1+ k1 ?do 1 present i cells + ! loop e2 to pos
      else 1 present k1 cells + ! then
    else 1 present k1 cells + ! then
    pos sskip-from { ps }
    ps ms-ach dup 44 = swap 47 = or if
      ms-a @ ms-u @ ps 1+ sskip-from names enum-name-at { k3 e3 }
      k3 0>= if k3 to k1  e3 to e1  false else true then
    else true then
  until
  ea eu names present enum-eval { v ok }
  present free throw
  ok 0= if false exit then
  v pos true ;
