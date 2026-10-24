\ obj5.fs -- error_patterns の評価 (DirectiveProcessor.error)

decimal

defer cond-relocated? ( a u -- f )                  \ -o で、リンカが埋める変数を見ている条件か
:noname 2drop false ; is cond-relocated?

: err-text ( code -- a u true | false )
  n>s errtab om-find ?dup if s@ true else false then ;

: error-eval ( a u -- triggered? ) { a u }
  a u 0 ?do a i + c@ 32 <> if leave then loop
  true { allblank } u 0 ?do a i + c@ 32 <> if false to allblank then loop
  allblank if false exit then
  0 false { idx trig }
  begin idx u < if a idx + c@ else 0 then dup 0<> while
    44 = if idx 1+ to idx else
      idx { ib }
      exp-float @ { pf }  undef-flag @ { prior }
      false exp-float !  false read-float-var !  false undef-flag !
      a u ib expr-pat { uq in } { cu } undef-flag @ uq qundef? or to cu
      false { iok }  0 { tq } in { idx2 }
      idx2 u < if a idx2 + c@ 59 = else false then if
        a u idx2 1+ expr-pat to idx to tq
        idx u >= if true else a idx + c@ 44 = then read-float-var @ 0= and if true to iok then
        iok if
          a ib + idx ib - s" /" search nip nip a ib + idx ib - s" **" search nip nip or if false to iok then
        then
      then
      iok 0= if
        true exp-float !  false undef-flag !
        a u ib expr-pat to idx2 to uq
        undef-flag @ uq qundef? or to cu
        idx2 to idx
        idx u < if a idx + c@ 59 = else false then if idx 1+ to idx then
        a u idx expr-pat to idx to tq
      then
      pf exp-float !  prior undef-flag @ or undef-flag !
      idx ib <= if u to idx else
        uq exp-float @ if qd 0e f= 0= else q-zero? 0= then
        true { dummy } drop
        iok 0= if uq qd 0e f= 0= else uq q-zero? 0= then { ut }
        ut cu 0= and report? and in-match @ 0= and
        a ib + idx ib - cond-relocated? 0= and if
          tq qundef? if 0 else tq qi>f fdup f0= 0= if fdup 9223372036854775808e f< fdup -9223372036854775808e f> and if f>s else fdrop 0 then else fdrop 0 then then { ti }
          s" Line " etype line-no @ .en s"  Error code " etype ti .en s"  " etype
          ti 0>= if ti err-text if etype then then
          s" : " etype ecr
          true to trig  true had-error !
        then
      then
    then
  repeat
  drop trig ;
