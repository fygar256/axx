\ obj5.fs -- error_patterns の評価 (DirectiveProcessor.error)

decimal

defer cond-relocated? ( a u -- f )        \ -o で、リンカが埋める変数を見ている条件か
: cond-relocated?-nn53 2drop false ; bind cond-relocated?-nn53 cond-relocated?

: err-text ( code -- a u true | false )
  n>s errtab om-find ?dup if s@ true else false then ;

: blank? ( a u -- f ) true -rot 0 ?do dup i + c@ 32 <> if swap drop false swap then loop drop ;

: has-str? ( a u pa pu -- f ) search nip nip ;

: truthy? ( q float? -- f ) if qd 0e f= 0= else q-zero? 0= then ;

: cond-code ( q float? -- n )                  \ 倍精度を経て 64 ビットの範囲で読む
  { q fl } q qundef? if 0 exit then
  fl if q qd else q qi>f then
  fdup f0= if fdrop 0 exit then
  fdup TWO63 f< fdup TWO63 fnegate f> and if f>s else fdrop 0 then ;

: error-eval ( a u -- triggered? ) { a u }
  a u blank? if false exit then
  0 false { idx trig }
  begin idx u < while
    a idx + c@ 44 = if idx 1+ to idx else
      idx { ib }
      exp-float @ { pf }  undef-flag @ { prior }
      false exp-float !  false read-float-var !  false undef-flag !
      a u ib expr-pat { uq i2 }
      undef-flag @ uq qundef? or { cu }
      false { iok }  false { ufl }  q0 { tq }  i2 to idx
      idx u < if a idx + c@ 59 = else false then if
        a u idx 1+ expr-pat to idx to tq
        idx u >= if true else a idx + c@ 44 = then
        read-float-var @ 0= and if
          true to iok
          a ib + idx ib - s" /" has-str?  a ib + idx ib - s" **" has-str? or if false to iok then
        then
      then
      iok 0= if
        true to ufl
        true exp-float !  false undef-flag !
        a u ib expr-pat to idx to uq
        undef-flag @ uq qundef? or to cu
        idx u < if a idx + c@ 59 = else false then if idx 1+ to idx then
        a u idx expr-pat to idx to tq
      then
      pf exp-float !  prior undef-flag @ or undef-flag !
      idx ib <= if u to idx else
        uq ufl truthy? { ut }
        ut cu 0= and report? and in-match @ 0= and
        a ib + idx ib - cond-relocated? 0= and if
          tq ufl cond-code { ti }
          s" Line " etype line-no @ .en s"  Error code " etype ti .en s"  " etype
          ti 0>= if ti err-text if etype then then
          s" : " etype ecr
          true to trig  true had-error !
        then
      then
    then
  repeat
  trig ;
