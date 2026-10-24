\ elf9.fs -- リロケーションの記録 (命令欄・データ欄) と 1 行ぶんの処理

decimal

\ ---- 命令欄の hint (型つき) ----
variable h-rt  variable h-fm0  variable h-pairs  variable h-ib  variable h-iw  variable h-fw
variable h-addq 4 cells allot
variable h-forced

: h-field-mask ( -- m ) h-fm0 @ if h-fm0 @ else g-fm @ then ;

: weak? ( a u -- f ) SA-WEAK sym-attr@ 0<> ;

\ .elfresolve: 同じセクションの局所ラベルならリロケーションを出さず値を詰める。処理したら true
: hint-resolve ( na nu -- done? ) { na nu }
  mach-table
  mt-resolve om-count 0= if false exit then
  elf-relaxing? if false exit then
  h-rt @ rtk mt-resolve om-find 0= if false exit then
  h-fw @ h-iw @ + nobj @ > if false exit then
  na nu lab-find { rle }
  rle 0= if false exit then
  rle lab-imported? rle lab-equ? or if false exit then
  rle lab-sec nip 0= if false exit then
  rle sec-is-cur? 0= if false exit then
  na nu export-labels om-find if false exit then
  na nu weak? if false exit then
  e-sa @ e-su @ rle q>n sec-rel-offset-impl 0= if rle q>n then { lw }
  h-fw @ field-pw { pw }
  lw qn pw qn q- scale*  h-addq scale* q+  g-fbias @ qn q+ { val }
  val g-fsh @ qsar { sv }
  h-field-mask popcount { nb }
  nb 64 >= if true else
    q1 nb 1- qshl { hi }  hi qneg { lo }
    sv lo q>= sv hi q< and
  then { fits }
  g-fsh @ 0> g-fsh @ 63 < and if
    val g-fsh @ mask-q qand q-zero? 0= if false to fits then
  then
  fits 0= report? and if
    mb-reset s"  error - the reference to '" mb+ na nu mb+ s" ' resolved in its section does not fit the field.  [" mb+ file@ mb+ s" :" mb+ line-no @ mb-n s" ]" mb+
    mb-get diag-e
  then
  \ 命令語を組む
  q0 { iv }
  h-iw @ 0 ?do
    endian-big @ 0= if e-bts @ i * else e-bts @ h-iw @ 1- i - * then { sh }
    h-fw @ i + obj-q e-mask qand sh qshl iv qor to iv
  loop
  h-rt @ rtk mt-encode om-find ?dup if
    dstr@ s" .elfencode" 2swap iv val elf-call-func if to iv then
  else
    iv h-field-mask qun qnot qand sv h-field-mask field-deposit qun qor to iv
  then
  h-iw @ 0 ?do
    endian-big @ 0= if e-bts @ i * else e-bts @ h-iw @ 1- i - * then { sh }
    iv sh qsar e-mask qand h-fw @ i + obj-q q!
  loop
  true ;

: hint-pairs ( na nu sec-rel-h -- ) { na nu srh }
  h-pairs @ 0= if exit then
  h-pairs @ @ 0 ?do
    h-pairs @ 1+ i 2* cells + @ { prt }
    h-pairs @ 2 + i 2* cells + @ { poff }
    prt field-load if
      g-fm @ { pmask }  g-fbias @ { pbias }
      prt mt-bytes@ 0 max dup 0= if drop 4 then { pbytes }
      pbytes e-bpw @ / 1 max { pwords }
      g-first @ poff e-bpw @ / + { pw }
      pw pwords + nobj @ <= if
        mt-rela? if pw pwords pmask words-clear-mask then
        prt rtk mt-anchor om-find 0<> { panc }
        panc if e-sa @ e-su @ srh anchor-at else na nu then { sa su2 }
        pw sec-bytes { psp }
        e-sa @ e-su @ psp sa su2 prt
        panc if q0 else h-addq scale* then pbias qn q+ pbytes 0 rel-add
      then
    then
  loop ;

\ 型つきの命令欄。処理を終えたら true。そうでなければ h-forced に型を入れて false
: emit-hint-group ( hi -- done? ) { hi }
  hi hint@ { he }
  he 2 cells + @ h-rt !  he 3 cells + @ h-fm0 !  he 4 cells + @ h-pairs !
  hi hint-q h-addq q!
  g-na @ g-nu @ lab-find { le }
  le src-rtype { srt }
  srt 0>= if g-na @ g-nu @ extern-untyped om-find 0= if srt h-rt ! then then
  h-rt @ field-load 0= if h-rt @ h-forced !  false exit then
  -1 h-forced !
  h-fm0 @ if h-fm0 @ g-fm ! then
  h-rt @ mt-bytes@ dup 0< if drop 4 then h-ib !
  h-ib @ e-bpw @ / 1 max h-iw !
  g-first @ g-foff @ e-bpw @ / + h-fw !
  g-na @ g-nu @ hint-resolve if true exit then
  h-fw @ h-iw @ + nobj @ <= if h-fw @ h-iw @ g-fm @ words-clear-mask then
  h-fw @ sec-bytes { srh }
  e-sa @ e-su @ srh g-na @ g-nu @ h-rt @ h-addq scale* g-fbias @ qn q+ h-ib @ h-fm0 @ rel-add
  g-na @ g-nu @ srh hint-pairs
  true ;

\ ---- データ欄 ----
variable d-rtype  variable d-guess
variable d-raw-q 4 cells allot

: ovr@ ( n -- rt|0 ) dup 0 9 within if cells reloctype-override + @ else drop 0 then ;
: v-hint-q ( -- q ) 1 g-first @ hint-find dup 0>= if hint-q else drop q0 then ;

: data-type ( -- )
  0 d-rtype !  false d-guess !
  g-na @ g-nu @ lab-find src-rtype { srt }
  nbytes ovr@ { ovr }
  h-forced @ 0>= if h-forced @ d-rtype ! exit then
  srt 0>= ovr 0<> g-na @ g-nu @ extern-untyped om-find 0<> and 0= and if
    srt mt-bytes@ { ex }
    ex 0< ex nbytes = or if srt d-rtype ! exit then
    ovr if ovr else nbytes mt-wg@ then d-rtype !  ovr 0= d-guess !
    exit
  then
  ovr if ovr else nbytes mt-wg@ then d-rtype !  ovr 0= d-guess ! ;

: emit-data-group ( -- )
  data-type
  g-first @ nobj @ >= if exit then
  d-rtype @ 0= if
    opt-debug @ if
      mb-reset s"  warning - no relocation type available for a " mb+ nbytes mb-n s" -byte reference to '" mb+ g-na @ g-nu @ mb+
      s" '; relocation omitted." mb+ mb-get diag-w
    then
    exit
  then
  g-first @ field-pw e-bpw @ * { sec-rel }
  g-first @ g-nw @ field-raw { raw }
  g-abs @ qundef-derived? if exit then
  g-nw @ e-bts @ * { fb }
  g-abs @ { abs }
  d-guess @ d-rtype @ mt-pc? and raw abs q= and if
    nbytes false reloc-same-width ?dup if d-rtype ! then
  then
  raw abs v-hint-q q+ q- { pcgd0 }
  fb 0> fb 64 < and if pcgd0 fb mask-q qand to pcgd0 then
  d-guess @ mt-pcg? and d-rtype @ mt-pc? 0= and pcgd0 q-zero? 0= and if
    nbytes reloc-data-pcrel ?dup if d-rtype ! then
  then
  d-rtype @ rtk mt-unal om-find ?dup if
    @ nbytes 0> sec-rel nbytes mod 0<> and if d-rtype ! else drop then
  then
  \ .elfresolve
  mt-resolve om-count 0<> elf-relaxing? 0= and d-rtype @ rtk mt-resolve om-find 0<> and if
    g-na @ g-nu @ lab-find { r0 }
    r0 0<> if
      r0 lab-imported? r0 lab-equ? or 0=
      r0 lab-sec nip 0<> and  r0 sec-is-cur? and
      g-na @ g-nu @ export-labels om-find 0= and
      g-na @ g-nu @ weak? 0= and if exit then
    then
  then
  q0 { addend }
  d-rtype @ mt-pc? if
    e-sa @ e-su @ pc @ g-first @ + sec-rel-offset-impl 0= if pc @ g-first @ + then { pw }
    v-hint-q { cst }
    raw abs q- pw qn q+ cst q- { pd }
    fb 0> fb 64 < and if
      pd fb mask-q qand to pd
      pd q1 fb 1- qshl q>= if pd q1 fb qshl q- to pd then
    then
    cst pd q+ scale* to addend
  else
    raw abs q- scale* to addend
  then
  mt-rela? if g-first @ g-nw @ words-zero then
  e-sa @ e-su @ sec-rel g-na @ g-nu @ d-rtype @ addend nbytes 0 rel-add ;

: emit-group ( -- )
  2 g-first @ hint-find dup 0>= if emit-diff-group exit then drop
  -1 h-forced !
  0 g-first @ hint-find dup 0>= if
    emit-hint-group if exit then
  else drop then
  emit-data-group ;

\ ---- 1 行ぶん ----
create vr MAXREFS cells allot  create vr2 MAXREFS cells allot
variable nvr  variable nvr2

: vr-collect ( -- )
  0 nvr !
  nrefs @ 0 ?do i ref@ ref-widx 0>= if i nvr @ cells vr + ! 1 nvr +! then loop
  nvr @ 1 > if
    nvr @ 1 do
      vr i cells + @ { x }  x ref@ ref-widx { xw }  i { j }
      begin j 0> if vr j 1- cells + @ ref@ ref-widx xw > else false then while
        vr j 1- cells + @ vr j cells + !  j 1- to j
      repeat
      x vr j cells + !
    loop
  then ;
: vr-dedupe ( -- )
  0 nvr2 !
  nvr @ 0 ?do
    vr i cells + @ ref@ { e }
    false { dup? }
    nvr2 @ 0 ?do
      vr2 i cells + @ ref@ { f }
      f ref-widx e ref-widx = if f ref-name e ref-name str=cs if true to dup? leave then then
    loop
    dup? 0= if vr i cells + @ vr2 nvr2 @ cells + !  1 nvr2 +! then
  loop
  \ 同じ語に 2 つ以上 (名前が違う) あれば全部捨てる
  0 nvr !
  nvr2 @ 0 ?do
    vr2 i cells + @ ref@ ref-widx { w }
    0 { cnt }
    nvr2 @ 0 ?do vr2 i cells + @ ref@ ref-widx w = if cnt 1+ to cnt then loop
    cnt 1 = if vr2 i cells + @ vr nvr @ cells + !  1 nvr +! then
  loop ;

: elf-emit-relocs-impl ( -- )
  o-obj-u @ 0= pass @ 2 <> or nobj @ 0= or nrefs @ 0= or if exit then
  bts @ 7 + 8 / 1 max e-bpw !
  bts @ e-bts !
  cur-section intern e-su ! e-sa !
  e-sa @ e-su @ sections om-find ?dup if dup cell+ @ e-cw ! 2 cells + @ e-epc ! else 0 e-cw ! 0 e-epc ! then
  mach-table
  mt-word-unit? if 1 else e-bpw @ then e-scale !
  bts @ mask-q e-mask q!
  vr-collect
  nvr @ 0= if exit then
  vr-dedupe
  0 { ix }
  begin ix nvr @ < while
    vr ix cells + @ ref@ { e }
    e ref-name { na nu }  e ref-widx { w0 }
    ix 1+ { j }
    begin j nvr @ < if
      vr j cells + @ ref@ { f }
      f ref-name na nu str=cs f ref-widx w0 j ix - + = and
    else false then while j 1+ to j repeat
    na g-na !  nu g-nu !  e ref-q g-abs !  w0 g-first !  j ix - g-nw !
    j ix - e-bpw @ * g-nb !
    emit-group
    j to ix
  repeat ;
' elf-emit-relocs-impl is elf-emit-relocs
