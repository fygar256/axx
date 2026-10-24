\ vliw.fs -- VLIW / EPIC のバンドルの組み立て (VLIWProcessor.vliwprocess)

decimal

MAXOBJ QB * allocate throw constant vbuf
variable vbuf-n
64 QB * allocate throw constant vidx
variable vidx-n

: vb-append ( -- )
  nobj @ 0 ?do
    vbuf-n @ MAXOBJ >= abort" VLIW packet too long"
    i obj-q vbuf vbuf-n @ QB * + q!  1 vbuf-n +!
  loop ;
: vidx-add ( q -- ) vidx-n @ 64 < if vidx vidx-n @ QB * + q! 1 vidx-n +! else drop then ;
: vb-q ( i -- q ) QB * vbuf + ;
: q-ones ( n -- q ) q1 swap qshl q1 q- ;

: vliw-skip-sp ( a u i -- i' ) { a u i } begin i u < if a i + c@ spc? else false then while i 1+ to i repeat i ;
: peek-lstrip ( a u i -- c ) { a u i }          \ i 以降の最初の空白でない文字 (なければ 0)
  begin i u < if a i + c@ dup 32 = over 9 = or over 10 = or over 13 = or swap 12 = or else false then while i 1+ to i repeat
  i u < if a i + c@ else 0 then ;

\ idxlst と EPIC の組の添字列が同じか
: epic-match? ( k -- f ) { k }
  vliw-idx-a k cells + @ { arr }
  arr arr-n vidx-n @ <> if false exit then
  vidx-n @ 0 ?do arr i arr-item item-q vidx i QB * + q= 0= if false unloop exit then loop
  true ;

\ 組み立てた res を出力する
: vliw-emit ( res vbits -- ) { res vbits }
  0 { q }
  vbits 8 < if
    pc @ res vbits q-ones qand outbin  1 to q
  else vbits 7 + 8 / { tb }
    endian-big @ 0= if
      tb 0 ?do
        pc @ i + res 255 qn qand outbin
        res 8 qshr to res
        q 1+ to q
      loop
    else
      tb 0 ?do
        pc @ i + res tb 1- i - 8 * qshr 255 qn qand outbin
        q 1+ to q
      loop
    then
  then
  q pc +! ;

: vliw-build ( k -- ok ) { k }
  vliw-bits @ abs { vbits }
  vliw-instbits @ q-ones { im }
  vliw-tmplbits @ abs q-ones { tm }
  vbits q-ones { pm }
  undef-flag @ { prior }  false undef-flag !
  vliw-pat-a k cells + @ vliw-pat-u k cells + @ 0 expr-pat drop
  undef-flag @ report? and if true had-error ! then
  prior undef-flag @ or undef-flag !
  tm qand { templ }
  vliw-instbits @ 7 + 8 / { ibyte }
  vbits vliw-tmplbits @ abs - vliw-instbits @ / { noi }
  noi 0<= if
    mb-reset s"  error - .vliw: vliwtemplatebits (" mb+ vliw-tmplbits @ mb-n s" ) leaves no room for instruction slots in a " mb+
    vbits mb-n s" -bit packet (vliwinstbits=" mb+ vliw-instbits @ mb-n s" )." mb+ mb-get diag-e false exit
  then
  ibyte noi * { target }
  vbuf-n @ { nv }
  nv target > if
    mb-reset s"  error - VLIW: the packet's instructions take " mb+ nv mb-n s"  byte(s) but its slots hold only " mb+ target mb-n s" ." mb+ mb-get diag-e
    target to nv
  else
    target nv - { deficit }
    deficit ibyte / { fulls }  deficit ibyte mod { rem }
    fulls 0 ?do
      vliw-nopn @ 0 ?do vliw-nop i + c@ qn  vbuf nv QB * + q!  nv 1+ to nv loop
    loop
    rem 0> if
      rem 0 ?do
        i vliw-nopn @ < if vliw-nop i + c@ else 0 then qn  vbuf nv QB * + q!  nv 1+ to nv
      loop
    then
  then
  0 { cnt } 0 { r }  q0 to r
  noi 0 ?do
    q0 { vv }
    endian-big @ 0= if
      ibyte 0 ?do
        cnt nv < if cnt vb-q @ 255 and qn i 8 * qshl vv qor to vv then
        cnt 1+ to cnt
      loop
    else
      ibyte 0 ?do
        vv 8 qshl to vv
        cnt nv < if cnt vb-q @ 255 and qn vv qor to vv then
        cnt 1+ to cnt
      loop
    then
    r vliw-instbits @ qshl vv im qand qor to r
  loop
  r pm qand to r
  vliw-tmplbits @ 0< if
    templ vbits vliw-tmplbits @ abs - qshl r qor
  else
    r vliw-tmplbits @ qshl templ qor
  then { res }
  res vbits vliw-emit true ;

: vliw-empty-slot ( -- ) s"  error - VLIW: empty slot in the packet (nothing before or after a '!!')." diag-e ;

: vliw-process-impl ( la lu idxs flag idx -- vflag ) { la lu idxs flag idx }
  0 vbuf-n !  0 vidx-n !
  vb-append  idxs vidx-add
  0 vliw-stop !
  begin
    la lu idx vliw-skip-sp to idx
    idx lu < if la idx + c@ VLIW-STOP-C = else false then if
      idx 1+ to idx  1 vliw-stop !  true
    else idx lu < if la idx + c@ VLIW-SEP-C = else false then if
      idx 1+ to idx
      la lu idx peek-lstrip { pk }
      pk 0= pk VLIW-SEP-C = or pk VLIW-STOP-C = or if vliw-empty-slot false exit then
      pk 46 = if
        s"  error - directives (e.g. .section/.endsection/.INCLUDE) are not allowed inside VLIW slots (the packet's PC has not advanced yet at this point in the packet)." diag-e
        false exit
      then
      la lu idx lineassemble2 { ni nf nidx }
      nf 0= if false exit then
      nidx to idx
      vb-append  ni vidx-add
      true
    else false then then
  0= until
  vliw-tmplbits @ 0= if
    1 arr-new { ia } q0 ia 0 arr-item item-num!
    ia vliw-idx-a !  s" 0" hdup vliw-pat-u ! vliw-pat-a !  1 vliw-set !
  then
  vliw-instbits @ 0= if s"  error - vliwinstbits is zero; cannot compute instruction slots." diag-e false exit then
  false { done }  false { ok }
  vliw-set @ 0 ?do
    done 0= if
      i epic-match? vliw-tmplbits @ 0= or if
        i vliw-build to ok  true to done
      then
    then
  loop
  done 0= if s"  error - No vliw instruction-set defined." diag-e false exit then
  ok ;
' vliw-process-impl is vliw-process
