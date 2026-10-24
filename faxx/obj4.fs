\ obj4.fs -- binary_list の評価: @@[ ] の展開、%% の添字、要素の走査 (makeobj)

decimal

defer mini-call ( a u k semi drp -- k' )         \ .call。語を objl に足し、読み終えた位置を返す
:noname 2drop 2drop drop 1000000 ; is mini-call
defer elf-word-begin ( -- )
defer elf-word-drop ( -- )                       \ 出力しなかった語の参照記録を捨てる
:noname ; is elf-word-begin
:noname ; is elf-word-drop

sb-new constant epb
variable epb-hc

: skip-qstr ( a u i0 -- i' ) { a u i0 } i0 1+ { k }
  begin k u < while
    a k + c@ dup 92 = if drop k 2 + to k else
      34 = if k 1+ exit then
      k 1+ to k
    then
  repeat
  u ;
: at@@[? ( a u i -- f )
  dup 3 + 2 pick > if drop 2drop false exit then
  nip + 3 s" @@[" str=cs ;

defer ep-expand
: ep-scan ( a u i0 -- cm end ) { a u i0 } 0 0 0 { k dpt cm }
  i0 to k  1 to dpt  -1 to cm
  begin k u < dpt 0> and while
    a k + c@ 34 = if a u k skip-qstr to k else
      a k + c@
      dup 91 = if drop dpt 1+ to dpt  k 1+ to k else
      dup 93 = if drop dpt 1- to dpt  dpt 0> if k 1+ to k then else
      44 = dpt 1 = and cm 0< and if k to cm then
      k 1+ to k
      then then
    then
  repeat
  cm k ;
: ep-rep ( a u es cm end -- ) { a u es cm en } 0 0 0 0 0 0 { cnt ra ru st shc prior }
  undef-flag @ to prior
  false undef-flag !
  a es + cm es - 0 expr-pat drop @ to cnt
  undef-flag @ if 0 to cnt then
  prior undef-flag @ or undef-flag !
  cnt 16777216 > if
    mb-reset s"  error - @@[n,...]: repeat count " mb+ cnt mb-n s"  exceeds maximum 16777216." mb+ mb-get diag-e 0 to cnt
  then
  cnt 0> if
    epb sb-len to st
    epb-hc @ to shc
    a cm 1+ + en cm - 1- ep-expand
    shc epb-hc !
    true epb-hc !
    epb sb$ drop st + epb sb-len st - sdup to ru to ra
    st epb sb-trunc
    cnt 0 ?do
      i 0> if 44 epb sb-c then
      ra ru epb sb+
    loop
  then ;
: ep-expand-impl ( a u -- ) { a u } 0 0 0 0 0 { k es cm en e }
  begin k u < while
    a u k at@@[? if
      k 3 + to es
      a u es ep-scan to en to cm
      cm 0>= cm es >= and if
        a u es cm en ep-rep
        en 1+ to k
      else
        s"  error - @@[...]: missing ',' separating count and pattern." diag-e
        s" @@[" epb sb+  true epb-hc !
        en to k
      then
    else
      a k + c@ 34 = if
        a u k skip-qstr to e
        a k + e k - epb sb+
        true epb-hc !  e to k
      else
        a k + c@ epb sb-c  true epb-hc !  k 1+ to k
      then
    then
  repeat ;
' ep-expand-impl is ep-expand

: expand-binlist ( a u -- a' u' empty? )
  epb sb-clear  false epb-hc !
  ep-expand
  epb sb$ sdup epb-hc @ 0= ;

sb-new constant pb
: pct-replace ( a u -- a' u' ) { a u } 0 0 0 { k cnt e }
  pb sb-clear
  begin k u < while
    a k + c@ 34 = if
      a u k skip-qstr to e
      a k + e k - pb sb+
      e to k
    else
      k 1+ u < a k + c@ 37 = and if
        a k 1+ + c@ 37 = if
          cnt n>s pb sb+
          cnt 1+ to cnt  k 2 + to k
        else a k 1+ + c@ 48 = if 0 to cnt  k 2 + to k
        else 37 pb sb-c k 1+ to k then then
      else a k + c@ pb sb-c k 1+ to k then
    then
  repeat
  pb sb$ sdup ;

: word-mask ( -- q ) bts @ 0> if q1 bts @ qshl q1 q- else q0 qnot then ;
: obj-byte ( n -- ) qn obj+ ;

: emit-template ( ta tu -- ) { ta tu }
  asmtext-set @ 0= if true asmtext-set ! then
  ta tu asmtext sb+
  asmdisp sb-len if 44 asmdisp sb-c then
  34 asmdisp sb-c  ta tu asmdisp txt-escaped  34 asmdisp sb-c ;

: makeobj-run ( a u -- ) { a u } 0 0 0 0 { k semi drp stp }
  begin k u < stp 0= and while
    a k + c@ 44 = if k 1+ to k else
      false to semi  false to drp
      a k + c@ 59 = if
        true to semi  k 1+ to k
        k u < if a k + c@ 59 = if true to drp  k 1+ to k then then
      then
      k { qs }
      begin qs u < if a qs + c@ spc? else false then while qs 1+ to qs repeat
      qs u < if a qs + c@ 34 = else false then if
        a qs + u qs - tmpl-inner txt-render { ta tu }
        drp 0= semi tu 0= and 0= and if
          tu 0 ?do ta i + c@ obj-byte loop
          ta tu emit-template
        then
        a u qs skip-qstr to k
        begin k u < if a k + c@ spc? else false then while k 1+ to k repeat
        k u < if a k + c@ 44 = else false then if k 1+ to k else true to stp then
      else
        a k + 5 + u <= if a k + 5 supper s" .CALL" str=cs else false then
        a k 5 + + c@ corec? 0= k 5 + u >= or and if
          a u k semi drp mini-call to k
          k u < if a k + c@ 44 = else false then if k 1+ to k else true to stp then
        else
          elf-word-begin
          pass @ 1 = if true size-mode ! then
          a u k expr-pat to k { x }
          pass @ 1 = if false size-mode !  false undef-flag ! then
          drp 0= semi 0= x q-zero? 0= or and if x obj+ else elf-word-drop then
          k u < if a k + c@ 44 = else false then if k 1+ to k else true to stp then
        then
      then
    then
  repeat ;

: makeobj ( a u -- )
  0 nobj !
  expand-binlist if 2drop exit then
  pct-replace
  undef-flag @ { prior }  false undef-flag !
  true in-binlist !
  makeobj-run
  false in-binlist !
  undef-flag @ prior or undef-flag ! ;
