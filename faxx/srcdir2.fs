\ srcdir2.fs -- ソース側のディレクティブ (続き): align / zero / res / ascii / section / include

decimal

defer sec-rel-offset ( a u wordpc -- off true | false )        \ セクション相対の位置 (-o / -E)
:noname 2drop drop false ; is sec-rel-offset

: align-up ( addr -- addr' ) align-v @ 0<= if exit then
  dup align-v @ mod dup 0= if drop exit then align-v @ swap - + ;

: dir-align ( a u -- ) { a u }
  a u trim nip if
    a u arg-eval { v idx un }
    a u idx s" .ALIGN" dir-rest-error if exit then
    un v qundef-derived? or if s"  error - .ALIGN argument contains undefined label." diag-e exit then
    v q-neg? v q-zero? or if
      mb-reset s"  error - .ALIGN requires a positive value, got " mb+ v q>dec mb+ s" ." mb+ mb-get diag-e exit
    then
    v @ align-v !
  then
  elf-sectioned? if cur-section pc @ sec-rel-offset else false then
  if { off } off else pc @ then { base }
  base align-up base - pc +! ;

: res-count ( a u name-a name-u -- n ok ) { a u na nu }
  a u arg-eval { v idx un }
  a u idx na nu dir-rest-error if 0 false exit then
  un v qundef-derived? or if
    mb-reset s"  error - " mb+ na nu mb+ s"  argument contains undefined label." mb+ mb-get diag-e 0 false exit
  then
  v q-neg? if
    mb-reset s"  error - " mb+ na nu mb+ s"  requires a non-negative count, got " mb+ v q>dec mb+ s" ." mb+ mb-get diag-e 0 false exit
  then
  v @ true ;
268435456 constant RES-MAX
: dir-zero ( a u -- ) s" .ZERO" res-count 0= if drop exit then { n }
  n RES-MAX > if mb-reset s"  error - .ZERO count " mb+ n mb-n s"  exceeds maximum 268435456." mb+ mb-get diag-e exit then
  n 0 ?do pc @ 0 outbin2-n 1 pc +! loop ;
: dir-res ( a u name-a name-u mul -- ) { a u na nu mul }
  a u na nu res-count 0= if drop exit then { n }
  n RES-MAX mul / > if
    mb-reset s"  error - " mb+ na nu mb+ s"  count " mb+ n mb-n s"  (x" mb+ mul mb-n s" ) exceeds maximum 268435456 words." mb+ mb-get diag-e exit
  then
  n mul * pc +! ;

\ ---- .ascii / .asciz ----
: put-word ( n -- ) pc @ swap outbin-n 1 pc +! ;
: ascii-str ( a u -- ok ) { a u } 0 0 0 { k trunc v }
  u 0= if false exit then
  a c@ 34 <> if false exit then
  1 to k
  begin k u < if a k + c@ 34 <> else false then while
    a k + c@ 92 = k 1+ u < and if
      a k 1+ + c@ { nc }
      nc 48 = if 0 put-word k 2 + to k else
      nc 116 = if 9 put-word k 2 + to k else
      nc 110 = if 10 put-word k 2 + to k else
      nc 114 = if 13 put-word k 2 + to k else
      nc 92 = if 92 put-word k 2 + to k else
      nc 34 = if 34 put-word k 2 + to k else
      nc uc 88 = if
        a u k 2 + 2 hex-run { hv k2 hn }
        hn 0= if
          mb-reset s"  error - '\x' escape requires at least one hex digit in string: " mb+ a u repr1 mb+ mb-get diag-w
          false exit
        then
        k2 to k
        hv wmask u> if true to trunc then
        hv put-word
      else nc uc 85 = if
        nc 117 = if 4 else 8 then { nd }
        a u k 2 + nd hex-run { hv k2 hn }
        hn nd <> if
          mb-reset s"  error - '\" mb+ nc mb-c s" ' escape requires " mb+ nd mb-n s"  hex digits in string: " mb+ a u repr1 mb+ mb-get diag-w
          false exit
        then
        k2 to k
        hv wmask u> if true to trunc then
        hv put-word
      else
        92 put-word k 1+ to k
      then then then then then then then then
    else
      a k + c@ dup wmask u> if true to trunc then put-word
      k 1+ to k
    then
  repeat
  k u >= if
    mb-reset s"  warning - unterminated string literal in .ASCII/.ASCIZ: " mb+ a u repr1 mb+ mb-get diag-w
  else
    a u k 1+ s" .ASCII/.ASCIZ" dir-rest-error drop
  then
  trunc report? and if
    mb-reset s"  warning - .ASCII/.ASCIZ: one or more characters exceed the output word width (" mb+ bts @ mb-n
    s"  bit(s)) and were truncated (high bits discarded): " mb+ a u repr1 mb+ mb-get diag-w
  then
  true ;
: dir-ascii ( a u -- )
  2dup ascii-str 0= if
    mb-reset s"  error - .ASCII: failed to process string argument: " mb+ repr1 mb+ mb-get diag-e
  else 2drop then ;
: dir-asciz ( a u -- )
  2dup ascii-str if 2drop 0 put-word else
    s"  error - .ASCIZ requires a quoted string." diag-e
    mb-reset s"  error - .ASCIZ: failed to process string argument: " mb+ repr1 mb+ mb-get diag-e
  then ;

\ ---- .section / .endsection ----
: sec-entry-pc ( slot -- n ) 2 cells + @ ;
: dir-section ( a u -- ) { a u }
  0 { e }
  begin e u < if a e + c@ dup spc? swap 44 = or 0= else false then while e 1+ to e repeat
  e u < if a u e s" .SECTION" dir-rest-error if exit then then
  u 0= if exit then
  cur-section sec-entry { old }
  old sec-entry-pc { epc }
  pc @ epc - { tent }
  tent 0> if
    old cell+ dup @ tent + swap !
    cur-section epc tent range+
  then
  a u cur-section!
  cur-section sections om-find dup 0= if
    drop cur-section sec-entry { ne } pc @ ne !  0 ne cell+ !  pc @ ne 2 cells + !  0 ne 3 cells + !
  else
    { ex }
    ex @ { es }  ex cell+ @ { esz }  ex 3 cells + @ { econf }
    esz 0= econf 0= and if pc @ else es pc @ min then { ns }
    ns ex !  esz ex cell+ !  pc @ ex 2 cells + !  0 ex 3 cells + !
  then ;
: dir-endsection ( -- )
  cur-section sections om-find dup 0= if
    drop mb-reset s"  error - .ENDSECTION without matching .SECTION for '" mb+ cur-section mb+ s" '." mb+ mb-get diag-e exit
  then
  { en }
  en @ { start }  en 2 cells + @ { epc }
  pc @ epc - { blk }
  blk 0< if
    mb-reset s"  warning - ENDSECTION: computed block size " mb+ blk mb-n s"  < 0 for '" mb+ cur-section mb+
    s" '; keeping previous size." mb+ mb-get diag-w exit
  then
  en cell+ @ blk + { nsz }
  blk 0> if cur-section epc blk range+ then
  start en !  nsz en cell+ !  pc @ en 2 cells + !  1 en 3 cells + ! ;

: dir-labelc ( a u -- ) dup if
    lw-tab 256 erase
    256 0 do i alnc? if 1 lw-tab i + c! then loop
    0 ?do dup i + c@ 255 and 1 swap lw-tab + c! loop drop
  else 2drop then ;
