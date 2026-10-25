\ line1.fs -- ソース 1 行の文字列処理とラベル

decimal

254 constant VLIW-SEP-C
255 constant VLIW-STOP-C

\ 文字定数 'c' の終わり (skip_squote_literal)
: skip-squote ( a u i -- j ) { a u i } 0 0 0 { j k dg }
  i 1+ to j
  j u < if
    a j + c@ 92 = j 1+ u < and if
      a j 1+ + c@ uc 88 = if
        j 2 + to k
        begin k u < dg 2 < and if a k + c@ xdig? else false then while k 1+ to k dg 1+ to dg repeat
        k u < if a k + c@ 39 = if k 1+ exit then then
      else
        j 2 + u < if a j 2 + + c@ 39 = if j 3 + exit then then
      then
    else
      j 1+ u < if
        a j 1+ + c@ 39 = a j + c@ 128 < and if j 2 + exit then
        a j 1+ + c@ 39 = a j + c@ 128 >= a j + c@ 255 <= and and if j 2 + exit then
      then
    then
  then
  i 1+ ;

sb-new constant nws-b
: normalize-ws ( a u -- a' u' ) { a u } 0 false false { k inq inws }
  nws-b sb-clear
  begin k u < while
    inq if
      a k + c@ 92 = k 1+ u < and if
        a k + c@ nws-b sb-c  a k 1+ + c@ nws-b sb-c  k 2 + to k
      else
        a k + c@ dup nws-b sb-c  34 = if false to inq then
        k 1+ to k
      then
    else
      a k + c@ 34 = if
        true to inq  false to inws  34 nws-b sb-c  k 1+ to k
      else
        a k + c@ 39 = if
          a u k skip-squote { j }
          a k + j k - nws-b sb+
          false to inws  j to k
        else
          a k + c@ ws? if
            inws 0= if 32 nws-b sb-c  true to inws then
          else
            a k + c@ nws-b sb-c  false to inws
          then
          k 1+ to k
        then
      then
    then
  repeat
  nws-b sb$ ;

sb-new constant cmt-b
: rstrip-ws ( a u -- a' u' ) begin dup 0> while 2dup + 1- c@ ws? while 1- repeat then ;
: split-comment ( a u -- ca cu ma mu ) { a u } 0 false -1 { k inq cpos }
  cmt-b sb-clear
  begin k u < cpos 0< and while
    a k + c@ 92 = inq and k 1+ u < and if
      a k + c@ cmt-b sb-c  a k 1+ + c@ cmt-b sb-c  k 2 + to k
    else
      a k + c@ 92 = inq 0= and k 1+ u < and if
        a k 1+ + c@ 59 = if 59 cmt-b sb-c  k 2 + to k else 92 cmt-b sb-c  k 1+ to k then
      else
        a k + c@ 34 = if
          inq 0= to inq  34 cmt-b sb-c  k 1+ to k
        else
          a k + c@ 39 = inq 0= and if
            a u k skip-squote { j }
            a k + j k - cmt-b sb+
            j to k
          else
            a k + c@ 59 = inq 0= and if k to cpos
            else a k + c@ cmt-b sb-c  k 1+ to k then
          then
        then
      then
    then
  repeat
  cpos 0< inq and if
    mb-reset s"  warning - unterminated string literal in line: " mb+ a u repr1 mb+ mb-get diag-w
  then
  cmt-b sb$ cpos 0>= if rstrip else rstrip-ws then sdup
  cpos 0>= if a cpos + u cpos - rstrip-ws sdup else s" " then ;

sb-new constant vle-b
: resolve-vliw-escapes ( a u -- a' u' ) { a u } 0 false { k inq }
  vle-b sb-clear
  begin k u < while
    a k + c@ { c }
    c 92 = inq and if
      k 1+ u < if c vle-b sb-c a k 1+ + c@ vle-b sb-c k 2 + to k else c vle-b sb-c k 1+ to k then
    else
      inq 0= c 92 = and k 1+ u < and if a k 1+ + c@ 33 = else false then if
        33 vle-b sb-c k 2 + to k
      else
        c 34 = if inq 0= to inq  c vle-b sb-c k 1+ to k else
          c 39 = inq 0= and if
            a u k skip-squote { j }
            a k + j k - vle-b sb+  j to k
          else
            inq 0= if a u k 33 33 at2? a u k 2 + 33 33 at2? and else false then if
              VLIW-STOP-C vle-b sb-c k 4 + to k
            else
              inq 0= if a u k 33 33 at2? else false then if
                VLIW-SEP-C vle-b sb-c k 2 + to k
              else c vle-b sb-c k 1+ to k then
            then
          then
        then
      then
    then
  repeat
  vle-b sb$ ;

\ ---- テキスト置換モードの断片 ----
sb-new constant label-text
sb-new constant comment-text
sb-new constant indent-text

\ 空白で区切った最初の語 (get_param_to_spc) と残り (get_param_to_eon)
: param-spc ( a u -- ra ru ta tu ) lstrip { a u } 0 { k }
  begin k u < if a k + c@ 32 <> else false then while k 1+ to k repeat
  a k + u k -  a k ;

\ ---- label: と label: .equ ----
defer equ-reloc-named ( a u -- n )
defer equ-machine-no ( -- n )
defer equ-sort-om ( om -- arr n )
: equ-sec-warn ( na nu -- ) { na nu }
  equ-secs equ-sort-om { arr n }
  mb-reset s"  warning - .EQU '" mb+ na nu mb+
  s" ': expression combines labels from multiple sections (" mb+
  n 0 ?do
    i 0> if s" , " mb+ then
    arr i cells + @ equ-secs om-key mb+
  loop
  s" ) without an explicit ::reloctype; the resulting constant assumes a specific section layout and will NOT be relocated by the linker." mb+
  mb-get diag-w
  arr free drop ;
: do-equ ( na nu ra ru -- ) { na nu ra ru }
  ra ru trim { ea eu }
  -1 { rt }
  ea eu s" ::" search if
    { pa pu }
    pa 2 + pu 2 - trim slower { ta tu }
    ea pa ea - trim to eu to ea
    ta tu equ-reloc-named to rt
    rt -1 = if
      mb-reset s"  warning - unknown reloctype '" mb+ ta tu mb+ s" ' in .EQU for machine " mb+ equ-machine-no mb-n mb-get diag-w
    then
  else 2drop then
  false undef-flag !
  size-mode @ { sm }
  pass @ 1 = if true size-mode ! then
  rt -1 = { track }
  track if equ-secs om-clear true equ-track ! then
  ea eu 0 expr-asm { v pe }
  sm size-mode !
  false equ-track !
  track equ-secs om-used 0> and if
    0 { cnt } equ-secs om-used 0 ?do i equ-secs om-live? if cnt 1+ to cnt then loop
    cnt 1 > report? and if na nu equ-sec-warn then
  then
  undef-flag @ if
    mb-reset s"  error - .EQU '" mb+ na nu mb+ s" ': expression contains undefined label." mb+ mb-get diag-e
  then
  ea eu pe mb-reset s" .EQU '" mb+ na nu mb+ s" '" mb+ mb-get sdup dir-rest-error drop
  na nu v cur-section 1 rt lab-put drop ;

: label-proc ( a u -- ra ru ) { a u } 0 0 0 { k nl lend }
  u 0= if a u exit then
  a c@ 46 = a c@ digc? 0= a c@ lwc? and or 0= if a u exit then
  1 to k
  begin k u < if a k + c@ lwc? else false then while k 1+ to k repeat
  k to nl
  k u < if a k + c@ 58 = else false then 0= if a u exit then
  k 1+ u < if a k 1+ + c@ 61 = else false then if a u exit then
  nl 1+ to lend
  a lend + u lend - param-spc { ra ru ta tu }
  ta tu s" .EQU" str=ci if
    a nl ra ru do-equ
    textmode @ if
      label-text sb-clear a lend label-text sb+
      a lend + u lend - exit
    then
    a 0 exit
  then
  a nl pc @ qn cur-section 0 -1 lab-put 0= if a 0 exit then
  label-text sb-clear a lend label-text sb+
  a lend + u lend - ;
