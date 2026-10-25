\ elf13.fs -- ELF オブジェクトの書き出し (4): CFI (.eh_frame)

decimal

: uleb ( v sb -- ) { v sb }
  begin
    v 127 and { b }  v 7 rshift to v
    v 0<> if b 128 or sb sb-c false else b sb sb-c true then
  until ;
: sleb ( v sb -- ) { v sb }
  begin
    v 127 and { b }  v 7 arshift to v
    v 0= b 64 and 0= and v -1 = b 64 and 0<> and or if b sb sb-c true else b 128 or sb sb-c false then
  until ;

\ ---- 命令 ----
variable cfa-reg  variable cfa-off
create rstk 128 cells allot  variable rstk-n
variable cfi-err-a  variable cfi-err-u
create cvals MAXCA cells allot  variable cvn
: cfi-fac ( o -- f true | false ) { o }
  d-cfi-da @ { da }
  o da mod 0<> if false exit then
  o da / true ;
: cfi-err-off ( o -- )
  mb-reset s" offset " mb+ mb-n s"  is not a multiple of the data alignment factor " mb+ d-cfi-da @ mb-n mb-get intern cfi-err-u ! cfi-err-a ! ;

\ op (a u) と vals (cvals[0..cvn-1]) から sb へ。成功なら true、だめなら cfi-err に文面
: cfi-op-bytes ( op-a op-u sb -- ok ) { oa ou sb }
  oa ou s" def_cfa" str=cs if
    cvals @ cfa-reg !  cvals cell+ @ cfa-off !
    cfa-off @ 0>= if 12 sb sb-c cfa-reg @ sb uleb cfa-off @ sb uleb true exit then
    cfa-off @ cfi-fac if { f } 18 sb sb-c cfa-reg @ sb uleb f sb sleb true else cfa-off @ cfi-err-off false then exit
  then
  oa ou s" def_cfa_offset" str=cs oa ou s" adjust_cfa_offset" str=cs or if
    oa ou s" def_cfa_offset" str=cs if cvals @ else cfa-off @ cvals @ + then { o }
    o cfa-off !
    o 0>= if 14 sb sb-c o sb uleb true exit then
    o cfi-fac if { f } 19 sb sb-c f sb sleb true else o cfi-err-off false then exit
  then
  oa ou s" def_cfa_register" str=cs if cvals @ cfa-reg ! 13 sb sb-c cvals @ sb uleb true exit then
  oa ou s" offset" str=cs oa ou s" rel_offset" str=cs or oa ou s" val_offset" str=cs or if
    cvals @ { r }  cvals cell+ @ { o }
    oa ou s" rel_offset" str=cs if o cfa-off @ - to o then
    o cfi-fac 0= if o cfi-err-off false exit then
    { f }
    oa ou s" val_offset" str=cs if
      f 0>= if 20 sb sb-c r sb uleb f sb uleb else 21 sb sb-c r sb uleb f sb sleb then true exit
    then
    f 0>= if
      r 64 < if 128 r or sb sb-c f sb uleb else 5 sb sb-c r sb uleb f sb uleb then
    else 17 sb sb-c r sb uleb f sb sleb then
    true exit
  then
  oa ou s" restore" str=cs if
    cvals @ { r }
    r 64 < if 192 r or sb sb-c else 6 sb sb-c r sb uleb then true exit
  then
  oa ou s" undefined" str=cs if 7 sb sb-c cvals @ sb uleb true exit then
  oa ou s" same_value" str=cs if 8 sb sb-c cvals @ sb uleb true exit then
  oa ou s" register" str=cs if 9 sb sb-c cvals @ sb uleb cvals cell+ @ sb uleb true exit then
  oa ou s" remember_state" str=cs if
    rstk-n @ 63 < if cfa-reg @ rstk rstk-n @ 2* cells + ! cfa-off @ rstk rstk-n @ 2* 1+ cells + ! 1 rstk-n +! then
    10 sb sb-c true exit
  then
  oa ou s" restore_state" str=cs if
    rstk-n @ 0= if s" restore_state without remember_state" intern cfi-err-u ! cfi-err-a ! false exit then
    -1 rstk-n +!
    rstk rstk-n @ 2* cells + @ cfa-reg !  rstk rstk-n @ 2* 1+ cells + @ cfa-off !
    11 sb sb-c true exit
  then
  oa ou s" window_save" str=cs oa ou s" negate_ra_state" str=cs or if 45 sb sb-c true exit then
  oa ou s" escape" str=cs if cvn @ 0 ?do cvals i cells + @ sb sb-c loop true exit then
  mb-reset s" '" mb+ oa ou mb+ s" ' cannot be used here" mb+ mb-get intern cfi-err-u ! cfi-err-a !
  false ;

: cfi-run-op ( op-a op-u sb -- ) { oa ou sb }
  oa ou sb cfi-op-bytes 0= if
    mb-reset s"  error - CFI: .cfi_" mb+ oa ou mb+ s" : " mb+ cfi-err-a @ cfi-err-u @ mb+ s" ." mb+ mb-get diag-e
  then ;

: cfi-ptr-size ( enc psize -- n ) { enc ps }
  enc 15 and case
    0 of ps endof
    2 of 2 endof  10 of 2 endof
    3 of 4 endof  11 of 4 endof
    4 of 8 endof  12 of 8 endof
    0 swap
  endcase ;

\ ---- .eh_frame ----
variable eh-sb
4096 constant MAXER
create er-at MAXER cells allot  create er-si MAXER cells allot  create er-rt MAXER cells allot  create er-ad MAXER cells allot
variable er-n
create ini-op-a 64 cells allot  create ini-op-u 64 cells allot  create ini-nv 64 cells allot
create ini-vals 64 16 * cells allot
variable ini-n
variable eh-psize  variable eh-pad  variable eh-pcrel4  variable eh-relax?  variable eh-rp0  variable eh-rp1
variable eh-ok

: er-add ( at si rt ad -- ) { at si rt ad }
  er-n @ MAXER >= if exit then
  at er-n @ cells er-at + !  si er-n @ cells er-si + !  rt er-n @ cells er-rt + !  ad er-n @ cells er-ad + !
  1 er-n +! ;

: eh-fail ( a u -- ) diag-e false eh-ok ! ;

\ ポインタ (enc, シンボル名) を 0 で置いてリロケーションを足す。n 個のゼロを sb へ
: eh-ptr ( enc na nu at sb -- ) { enc na nu at sb }
  enc eh-psize @ cfi-ptr-size { n }
  enc 112 and { app }
  n 0= app 0<> app 16 <> and or if
    mb-reset s"  error - CFI: pointer encoding 0x" mb+ enc hexs mb+ s"  is not supported." mb+ mb-get diag-e
    n sb put-zero exit
  then
  app 16 = if n reloc-data-pcrel else n reloc-data-abs then { rt }
  rt 0= if
    mb-reset s"  error - CFI: no relocation type for a " mb+ n mb-n s" -byte pointer (encoding 0x" mb+ enc hexs mb+ s" )." mb+ mb-get diag-e
    n sb put-zero exit
  then
  na nu symidx om-find ?dup 0= if
    mb-reset s"  error - CFI: unknown symbol '" mb+ na nu mb+ s" '." mb+ mb-get diag-e
    n sb put-zero exit
  then
  @ { si }
  at si rt 0 er-add
  n sb put-zero ;

\ 長さの欄を付けて詰めて eh-sb へ
: eh-emit ( body-sb -- ) { b }
  b bb-len 4 + { tot }
  tot negate eh-pad @ mod dup 0< if eh-pad @ + then { padn }
  padn b put-zero
  b bb-len 4 eh-sb @ put
  b sb$ eh-sb @ put-bytes ;

\ CIE の候補
64 constant MAXCIE
create ci-ra MAXCIE cells allot  create ci-sig MAXCIE cells allot  create ci-simple MAXCIE cells allot
create ci-penc MAXCIE cells allot  create ci-pna MAXCIE cells allot  create ci-pnu MAXCIE cells allot
create ci-lenc MAXCIE cells allot  create ci-off MAXCIE cells allot
variable ci-n

\ [+-]?(0[xX][0-9a-fA-F]+|[0-9]+) だけ
: init-num ( a u -- n ok ) { a u }
  false { neg }  0 { k }
  u 0= if 0 false exit then
  a c@ 45 = if true to neg 1 to k else a c@ 43 = if 1 to k then then
  k u >= if 0 false exit then
  a k + c@ 48 = k 2 + u < and a k 1+ + c@ lc 120 = and if
    k 2 + to k
    0 { v }
    u k ?do
      a i + c@ lc { c }
      c digc? if c 48 - else c 97 >= c 102 <= and if c 87 - else 0 false unloop exit then then
      v 16 * + to v
    loop
    neg if v negate to v then v true exit
  then
  0 { v }
  u k ?do
    a i + c@ { c }
    c digc? 0= if 0 false unloop exit then
    v 10 * c 48 - + to v
  loop
  neg if v negate to v then v true ;

variable ip-ok
: ini-one ( ta tu -- ) { ta tu }
  ta tu 32 find-ch { sp }
  ta sp slower { oa ou }
  oa ou cfi-spec { spa spu spok }
  spok ip-ok !
  spok if
    oa ou s" startproc" str=cs
    oa ou s" endproc" str=cs or  oa ou s" sections" str=cs or
    oa ou s" return_column" str=cs or  oa ou s" signal_frame" str=cs or
    oa ou s" personality" str=cs or  oa ou s" lsda" str=cs or
    oa ou s" adjust_cfa_offset" str=cs or  oa ou s" rel_offset" str=cs or
    oa ou s" remember_state" str=cs or  oa ou s" restore_state" str=cs or
    if false ip-ok ! then
  then
  sp tu < if ta sp 1+ + tu sp 1+ - else ta tu + 0 then split-args
  ip-ok @ if spa spu s" *" str=cs 0= ca-n @ spu <> and if false ip-ok ! then then
  ini-n @ 64 >= if false ip-ok ! then
  ip-ok @ if
    ini-n @ 16 * cells ini-vals + { vp }
    0 { nv }
    ca-n @ 0 ?do
      ip-ok @ if
        i cells ca-a + @ i cells ca-u + @ { xa xu }
        xa xu slower d-cfireg om-find ?dup if @ true else xa xu init-num then
        0= if drop false ip-ok ! else
          { rv }
          spa spu s" *" str=cs if rv 0 256 within 0= if false ip-ok ! then then
          nv 16 >= if false ip-ok ! then
          ip-ok @ if rv vp nv cells + !  nv 1+ to nv then
        then
      then
    loop
    nv ini-n @ cells ini-nv + !
    oa ou intern ini-n @ cells ini-op-u + ! ini-n @ cells ini-op-a + !
  then ;

\ 初期命令の並びを読む。だめなら false
: parse-initops ( -- ok )
  0 ini-n !
  d-cfiinit om-used 0 ?do
    i d-cfiinit om-live? if
      i d-cfiinit om-key ini-one
      ip-ok @ 0= if
        mb-reset s"  error - .elfcfiinit: cannot use '" mb+ i d-cfiinit om-key mb+ s" '." mb+ mb-get diag-e
        false unloop exit
      then
      1 ini-n +!
    then
  loop
  true ;

: hexw2 ( u -- a u ) hexs dup 1 = if s" 0" 2swap sconcat then ;

: cfi-point-idx ( sa su b -- symidx ) { sa su b }
  cfp-n @ 0 ?do
    i cells cfp-b + @ b = if i cells cfp-sec + @ i cells cfp-secu + @ sa su str=cs if i cells cfsyn + @ unloop exit then then
  loop 0 ;

variable cie-key-i
: cie-find ( ra sig simple pers? penc pna pnu lenc -- off|-1 ) { ra sig simple pers? penc pna pnu lenc }
  ci-n @ 0 ?do
    i cells ci-ra + @ ra =  i cells ci-sig + @ sig = and  i cells ci-simple + @ simple = and
    i cells ci-lenc + @ lenc = and
    i cells ci-penc + @ pers? if penc = else drop true then and
    pers? if i cells ci-pna + @ i cells ci-pnu + @ pna pnu str=cs else true then and
    if i cells ci-off + @ unloop exit then
  loop -1 ;

variable fe-cur  variable fe-ra  variable fe-sa  variable fe-su  variable fe-coff  variable fe-foff

: eh-make-cie ( fde ra -- ) { f ra }
  eh-sb @ bb-len fe-coff !
  bb-new { body }
  0 4 body put
  ra 255 <= if 1 else 3 then { ver }
  ver body put8
  s" z" body put-bytes
  f F-PERS? fd@ if s" P" body put-bytes then
  f F-LSDA? fd@ if s" L" body put-bytes then
  s" R" body put-bytes
  f F-SIGNAL fd@ if s" S" body put-bytes then
  0 body put8
  d-cfi-ca @ body uleb  d-cfi-da @ body sleb
  ver 1 = if ra body put8 else ra body uleb then
  bb-new { augd }  -1 { ppos }
  f F-PERS? fd@ if
    f F-PENC fd@ augd put8  augd bb-len to ppos
    f F-PENC fd@ eh-psize @ cfi-ptr-size augd put-zero
  then
  f F-LSDA? fd@ if f F-LENC fd@ augd put8 then
  27 augd put8
  bb-new { lb }  augd bb-len lb uleb
  ppos 0>= if
    fe-coff @ 4 + body bb-len + lb bb-len + ppos +
    bb-new { scratch }
    { at }
    f F-PENC fd@ f F-PNA fd@ f F-PNU fd@ at scratch eh-ptr
  then
  lb sb$ body put-bytes  augd sb$ body put-bytes
  f F-SIMPLE fd@ 0= if
    0 cfa-reg !  0 cfa-off !  0 rstk-n !
    ini-n @ 0 ?do
      i 16 * cells ini-vals + { vp }
      i cells ini-nv + @ cvn !
      cvn @ 0 ?do vp i cells + @ cvals i cells + ! loop
      i cells ini-op-a + @ i cells ini-op-u + @ body cfi-run-op
    loop
  then
  body eh-emit
  ci-n @ MAXCIE < if
    ra ci-n @ cells ci-ra + !  f F-SIGNAL fd@ ci-n @ cells ci-sig + !  f F-SIMPLE fd@ ci-n @ cells ci-simple + !
    f F-PERS? fd@ if f F-PENC fd@ else 0 then ci-n @ cells ci-penc + !
    f F-PNA fd@ ci-n @ cells ci-pna + !  f F-PNU fd@ ci-n @ cells ci-pnu + !
    f F-LSDA? fd@ if f F-LENC fd@ else -1 then ci-n @ cells ci-lenc + !
    fe-coff @ ci-n @ cells ci-off + !
    1 ci-n +!
  then ;

: eh-fde-body ( fde ra -- ) { f ra }
  fe-sa @ fe-su @ { sa su }
  eh-sb @ bb-len fe-foff !
  0 cfa-reg !  0 cfa-off !  0 rstk-n !
  f F-SIMPLE fd@ 0= if
    bb-new { scratch }
    ini-n @ 0 ?do
      i 16 * cells ini-vals + { vp }
      i cells ini-nv + @ cvn !
      cvn @ 0 ?do vp i cells + @ cvals i cells + ! loop
      i cells ini-op-a + @ i cells ini-op-u + @ scratch cfi-run-op
    loop
    0 rstk-n !
  then
  f F-START fd@ e-bpw @ * { sb0 }
  f F-END fd@ e-bpw @ * { eb0 }
  bb-new { body }
  fe-foff @ 4 + fe-coff @ - 4 body put
  fe-foff @ 4 + body bb-len + { at }
  eh-relax? @ if
    at sa su sb0 cfi-point-idx eh-pcrel4 @ 0 er-add
    4 body put-zero
  else
    sa su cs-find 1+ { ssym }
    at ssym eh-pcrel4 @ sb0 er-add
    mt-rela? if 0 else sb0 4294967295 and then 4 body put
  then
  fe-foff @ 4 + body bb-len + to at
  eh-relax? @ if
    at sa su eb0 cfi-point-idx eh-rp0 @ 0 er-add
    at sa su sb0 cfi-point-idx eh-rp1 @ 0 er-add
    4 body put-zero
  else
    eb0 sb0 - 4294967295 and 4 body put
  then
  f F-LSDA? fd@ if
    f F-LENC fd@ eh-psize @ cfi-ptr-size { n }
    n body uleb
    fe-foff @ 4 + body bb-len + to at
    f F-LENC fd@ f F-LNA fd@ f F-LNU fd@ at body eh-ptr
  else 0 body uleb then
  sb0 { cur }
  f F-OPS fd@ { op }
  begin op while
    op cell+ @ e-bpw @ * { ob }
    op 2 cells + @ op 3 cells + @ { oa ou }
    ob cur < if
      mb-reset s"  error - CFI: a .cfi_" mb+ oa ou mb+ s"  is placed before the previous one." mb+ mb-get diag-e
    else
      ob cur > if
        eh-relax? @ if
          fe-foff @ 4 + body bb-len + 1+ to at
          at sa su ob cfi-point-idx eh-rp0 @ 0 er-add
          at sa su cur cfi-point-idx eh-rp1 @ 0 er-add
          4 body put8  4 body put-zero
        else
          ob cur - { d }
          d d-cfi-ca @ mod 0<> if
            mb-reset s"  error - CFI: an advance of " mb+ d mb-n s"  bytes is not a multiple of the code alignment factor " mb+ d-cfi-ca @ mb-n s" ." mb+ mb-get diag-e
          then
          d d-cfi-ca @ / { fa }
          fa 64 < if 64 fa or body put8 else
          fa 255 <= if 2 body put8 fa body put8 else
          fa 65535 <= if 3 body put8 fa body put16 else
          4 body put8 fa 4294967295 and body put32 then then then
        then
        ob to cur
      then
      op 4 cells + @ cvn !
      cvn @ 0 ?do op 5 i + cells + @ cvals i cells + ! loop
      oa ou body cfi-run-op
    then
    op @ to op
  repeat
  body eh-emit ;

: build-eh-frame ( -- )
  true eh-ok !
  bb-new eh-sb !  0 er-n !  0 ci-n !
  cfi-head @ 0= if exit then
  d-cfi? @ 0= if s"  error - CFI: the pattern file has no .elfcfi declaration." eh-fail exit then
  w-64 @ if 8 else 4 then eh-psize !
  d-cfi-pad @ eh-pad !  eh-pad @ 0= if eh-psize @ eh-pad ! then
  4 reloc-data-pcrel eh-pcrel4 !
  eh-pcrel4 @ 0= if
    s"  error - CFI: no 4-byte PC-relative relocation type for the FDE address; declare one with .elftype." eh-fail exit
  then
  cfi-relax? if eh-rp1 ! eh-rp0 ! true else false then eh-relax? !
  eh-relax? @ d-cfi-ca @ 1 <> and if
    s"  error - CFI: relocated advances need a code alignment factor of 1." eh-fail exit
  then
  parse-initops 0= if false eh-ok ! exit then
  cfi-head @ { f }
  begin f while
    f F-SECA fd@ f F-SECU fd@ fe-su ! fe-sa !
    fe-sa @ fe-su @ cs-find 0< if
      mb-reset s"  error - CFI: section '" mb+ fe-sa @ fe-su @ mb+ s" ' of a function is not in the output." mb+ mb-get diag-e
    else
      f F-RA fd@ dup 0< if drop d-cfi-ra @ then { ra }
      f F-LSDA? fd@ if f F-LENC fd@ else -1 then { lenc }
      ra f F-SIGNAL fd@ f F-SIMPLE fd@ f F-PERS? fd@ f F-PENC fd@ f F-PNA fd@ f F-PNU fd@ lenc cie-find
      dup 0< if drop f ra eh-make-cie fe-coff @ else dup fe-coff ! then drop
      f ra eh-fde-body
    then
    f F-NEXT fd@ to f
  repeat ;
