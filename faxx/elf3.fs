\ elf3.fs -- ソース側の ELF ディレクティブ (.extern .global .type .size .weak .comm .cfi_* ...)

decimal

\ ---- セクション相対 ----
: sec-rel-offset-impl ( a u wpc -- off true | false ) { a u w }
  0 { cum }
  nranges @ 0 ?do
    i cells range-na + @ i cells range-nu + @ a u str=cs if
      i cells range-s + @ { rs }  i cells range-l + @ { rl }
      w rs >= w rs rl + <= and if cum w rs - + true unloop exit then
      cum rl + to cum
    then
  loop
  a u sections om-find ?dup if
    2 cells + @ { epc }
    w epc >= if cum w epc - + true exit then
  then
  false ;
bind sec-rel-offset-impl sec-rel-offset

: elf-sectioned-impl ( -- f ) o-obj-u @ 0<> o-expe-u @ 0<> or ;
bind elf-sectioned-impl elf-sectioned?

: lab-sec-adjust-impl ( q a u -- q' ) { q a u }
  elf-sectioned? 0= if q exit then
  a u q q>n sec-rel-offset-impl if qn else q then ;
bind lab-sec-adjust-impl lab-sec-adjust

: sec-rel-pc-impl ( q -- q' ) { q }
  elf-sectioned? 0= if q exit then
  cur-section q q>n sec-rel-offset-impl if qn else q then ;
bind sec-rel-pc-impl sec-rel-pc

\ ---- シンボル属性 ----
7 lazy-om sym-attrs        \ 名前 -> type size_set size other weak common align
1 lazy-om extern-untyped
7 lazy-om export-labels    \ 名前 -> q(4) sec-a sec-u equ
0 constant SA-TYPE   1 constant SA-SIZE-SET   2 constant SA-SIZE   3 constant SA-OTHER
4 constant SA-WEAK   5 constant SA-COMMON     6 constant SA-ALIGN
: sym-attr-slot ( a u -- slot ) sym-attrs om-put ;
: sym-attr@ ( a u k -- v ) { a u k } a u sym-attrs om-find ?dup if k cells + @ else 0 then ;

create reloctype-override 9 cells allot
: ovr-clear ( -- ) reloctype-override 9 cells erase ;

\ ラベル表へ外部シンボルを入れる
: lab-extern-put ( a u rt -- ) { a u rt }
  a u labels om-put { sl }
  q0 sl q!  s" .text" intern sl 4 cells + s!
  0 sl 6 cells + !  1 sl 7 cells + !  rt sl 8 cells + ! ;
: sym-declare-extern ( a u -- ) { a u }
  a u lab-find if exit then
  a u extern-untyped om-put drop
  a u mt-extern lab-extern-put ;

\ ---- 名前の並びの走査 (_sym_decl_scan) ----
variable sa-a  variable sa-u  variable sa-i
variable sa-na variable sa-nu
create sf-a 2 cells allot  create sf-u 2 cells allot
: sa-init ( a u -- ) sa-u ! sa-a ! 0 sa-i ! ;
: sa-ch ( i -- c ) dup sa-u @ < if sa-a @ + c@ else drop 0 then ;

\ get_label_word (コロンを食べる)。( a u i -- na nu i' )
: lw-scan ( a u i -- na nu i' ) { a u i }
  i u >= if a 0 i exit then
  a i + c@ { c }
  c 46 = c digc? 0= c lwc? and or 0= if a i + 0 i exit then
  i { st }  i 1+ to i
  begin i u < if a i + c@ lwc? else false then while i 1+ to i repeat
  i { en }
  i u < if a i + c@ 58 = else false then
  if i 1+ u >= if true else a i 1+ + c@ 61 <> then else false then
  if i 1+ to i then
  a st + en st - i ;

: sa-skip ( -- ) sa-a @ sa-u @ sa-i @ skip-sp-from sa-i ! ;

\ 次の名前と nf 個の欄。無ければ false
: sa-next ( nf -- flag ) { nf }
  sa-i @ sa-u @ >= if false exit then
  sa-skip
  sa-a @ sa-u @ sa-i @ lw-scan { na nu ix }
  nu 0= if false exit then
  ix sa-i !  na sa-na !  nu sa-nu !
  sa-i @ 0> if sa-i @ 1- sa-ch 58 = sa-i @ sa-ch 58 = and if -1 sa-i +! then then
  2 0 do 0 i cells sf-a + ! 0 i cells sf-u + ! loop
  0 { k }
  begin k nf < sa-i @ sa-ch 58 = and sa-i @ 1+ sa-ch 58 = and while
    2 sa-i +!
    sa-i @ { s0 }
    begin sa-i @ sa-u @ < if sa-i @ sa-ch dup 32 <> over 9 <> and over 44 <> and swap 58 <> and else false then while 1 sa-i +! repeat
    sa-a @ s0 + sa-i @ s0 - strip-st k cells sf-u + ! k cells sf-a + !
    k 1+ to k
  repeat
  sa-i @ sa-ch 58 = if 1 sa-i +! then
  sa-skip
  sa-i @ sa-ch 44 = if 1 sa-i +! then
  true ;

: sfld@ ( k -- a u ) dup cells sf-a + @ swap cells sf-u + @ ;

\ ---- 数の欄 (_sym_decl_num) ----
: sym-num ( dname-a du name-a nu text-a tu lo hi -- n ok ) { da du na nu ta tu lo hi }
  tu 0= if
    mb-reset s"  error - " mb+ da du mb+ s" : a number is required for '" mb+ na nu mb+ s" '." mb+ mb-get diag-e 0 false exit
  then
  false undef-flag !
  ta tu 0 expr-asm drop { v }
  undef-flag @ { un }  false undef-flag !
  un v qundef-derived? or v qnbit 63 > or if
    0 false
  else
    v q>n { n }  n lo >= n hi <= and if n true else 0 false then
  then
  { n ok }
  ok 0= if
    mb-reset s"  error - " mb+ da du mb+ s" : value for '" mb+ na nu mb+ s" ' must be an integer in " mb+ lo mb-n s" .." mb+ hi mb-n
    s" , got '" mb+ ta tu mb+ s" '." mb+ mb-get diag-e
    0 false exit
  then
  n true ;

\ ---- エクスポートの記録 ----
: exp-put ( a u -- ) { a u }
  a u label-get-value { v }
  a u export-labels om-put { sl }
  v sl q!
  a u lab-find ?dup if
    dup lab-sec intern sl 4 cells + s!
    lab-equ? if 1 else 0 then sl 6 cells + !
  else s" " sl 4 cells + s!  0 sl 6 cells + ! then ;

: warn-unknown-reloc ( ra ru dname-a dname-u -- )
  mb-reset s"  warning - unknown reloc type '" mb+ 2swap mb+ s" ' in " mb+ mb+ s"  for machine " mb+ elf-machine @ mb-n mb-get diag-w ;

\ ---- .extern ----
: dir-extern ( l2a l2u -- )
  sa-init
  begin 1 sa-next while
    sa-na @ sa-nu @ { na nu }
    mt-extern { rt }  false { explicit }
    0 sfld@ nip if
      0 sfld@ slower { ra ru }
      ra ru reloc-named-t if to rt true to explicit else -1 to rt ra ru s" .EXTERN" warn-unknown-reloc then
    then
    na nu lab-find { ex }
    explicit if na nu extern-untyped om-del
    else ex 0= if na nu extern-untyped om-put drop then then
    ex 0= if na nu rt lab-extern-put
    else
      ex lab-imported? if explicit if rt ex 8 cells + ! then
      else
        mb-reset s"  warning - .EXTERN: '" mb+ na nu mb+ s" ' is already defined locally; ignoring extern declaration" mb+ mb-get diag-w
      then
    then
  repeat ;

\ ---- .export / .global ----
: dir-export ( l2a l2u -- )
  report? 0= if 2drop exit then
  sa-init
  begin 1 sa-next while
    sa-na @ sa-nu @ { na nu }
    0 sfld@ nip if
      0 sfld@ slower { ra ru }
      ra ru reloc-named-t if
        na nu lab-find ?dup if 8 cells + ! else drop then
      else ra ru s" .GLOBAL" warn-unknown-reloc then
    then
    na nu exp-put
  repeat ;

\ ---- .type .size .hidden .other .weak .comm ----
: sym-type-num ( a u -- n true | false )
  2dup s" notype" str=cs if 2drop 0 true exit then
  2dup s" object" str=cs if 2drop 1 true exit then
  2dup s" func" str=cs if 2drop 2 true exit then
  2dup s" function" str=cs if 2drop 2 true exit then
  2dup s" section" str=cs if 2drop 3 true exit then
  2dup s" file" str=cs if 2drop 4 true exit then
  2dup s" common" str=cs if 2drop 5 true exit then
  2dup s" tls" str=cs if 2drop 6 true exit then
  2dup s" tls_object" str=cs if 2drop 6 true exit then
  2dup s" gnu_ifunc" str=cs if 2drop 10 true exit then
  s" ifunc" str=cs if 10 true else false then ;

: dir-type ( l2a l2u -- )
  report? 0= if 2drop exit then
  sa-init
  begin 1 sa-next while
    sa-na @ sa-nu @ { na nu }
    0 sfld@ slower { ka ku }
    ku 0= if
      mb-reset s"  error - .TYPE: a symbol type is required for '" mb+ na nu mb+ s" '." mb+ mb-get diag-e
    else
      ka ku sym-type-num if true else s" .TYPE" na nu ka ku 0 15 sym-num then
      if { v } v na nu sym-attr-slot SA-TYPE cells + ! else drop then
    then
  repeat ;

: dir-size ( l2a l2u -- )
  report? 0= if 2drop exit then
  sa-init
  begin 1 sa-next while
    sa-na @ sa-nu @ { na nu }
    s" .SIZE" na nu 0 sfld@ 0 9223372036854775807 sym-num
    if { v } na nu sym-attr-slot { sl } 1 sl SA-SIZE-SET cells + !  v sl SA-SIZE cells + ! else drop then
  repeat ;

: dir-weak ( l2a l2u -- )
  report? { rec }
  sa-init
  begin 0 sa-next while
    sa-na @ sa-nu @ { na nu }
    na nu sym-declare-extern
    rec if
      1 na nu sym-attr-slot SA-WEAK cells + !
      na nu lab-find ?dup if lab-imported? else false then 0= if na nu exp-put then
    then
  repeat ;

: dir-vis ( l2a l2u vis -- ) { vis }
  report? 0= if 2drop exit then
  sa-init
  begin 0 sa-next while
    sa-na @ sa-nu @ sym-attr-slot SA-OTHER cells + { p }
    p @ 3 invert and vis or p !
  repeat ;

: dir-other ( l2a l2u -- )
  report? 0= if 2drop exit then
  sa-init
  begin 1 sa-next while
    sa-na @ sa-nu @ { na nu }
    s" .OTHER" na nu 0 sfld@ 0 255 sym-num
    if na nu sym-attr-slot SA-OTHER cells + ! else drop then
  repeat ;

: dir-comm ( l2a l2u -- )
  report? { rec }
  sa-init
  begin 2 sa-next while
    sa-na @ sa-nu @ { na nu }
    na nu sym-declare-extern
    rec if
      s" .COMM" na nu 0 sfld@ 0 9223372036854775807 sym-num
      if { sz }
        1 { al } true { ok }
        1 sfld@ nip if
          s" .COMM" na nu 1 sfld@ 0 1073741824 sym-num
          if to al else drop false to ok then
          ok if al al 1- and if
            mb-reset s"  error - .COMM: alignment must be 0 or a power of two, got '" mb+ al mb-n s" ' for '" mb+ na nu mb+ s" '." mb+ mb-get diag-e
            false to ok
          then then
        then
        ok if
          na nu sym-attr-slot { sl }
          1 sl SA-COMMON cells + !  1 sl SA-SIZE-SET cells + !
          sz sl SA-SIZE cells + !  al sl SA-ALIGN cells + !
          sl SA-TYPE cells + @ 0= if 1 sl SA-TYPE cells + ! then
        then
      else drop then
    then
  repeat ;

: dir-reloctype ( l2a l2u -- ) { a u }
  mach-table
  mt-named om-count 0= if
    mb-reset s"  warning - .RELOCTYPE: no relocation type is known for machine " mb+ elf-machine @ mb-n
    s" ; declare them with .elftype" mb+ mb-get diag-w exit
  then
  u 0= if exit then
  0 { st } 0 { n }
  u 1+ 0 ?do
    i u = a i + c@ 44 = or if
      n 4 >= if
        s"  warning - .RELOCTYPE: too many arguments (only 4 widths -- 8/16/32/64-bit -- are supported)" diag-w
        leave
      then
      a st + i st - strip-st slower { na nu }
      nu if
        na nu reloc-named-t if
          { rt }
          1 n lshift { wd }
          rt mt-bytes@ { act }
          act 0>= act wd <> and if
            mb-reset s"  warning - .RELOCTYPE: '" mb+ na nu mb+ s" ' is a " mb+ act 8 * mb-n
            s" -bit relocation type, but was given in the " mb+ wd 8 * mb-n s" -bit position; ignored" mb+ mb-get diag-w
          else rt wd cells reloctype-override + ! then
        else na nu s" .RELOCTYPE" warn-unknown-reloc then
      then
      n 1+ to n  i 1+ to st
    then
  loop ;

\ ---- .cfi_* ----
18 constant FDE-SZ
variable cfi-head  variable cfi-tail  variable cfi-cur
0 constant F-SECA 1 constant F-SECU 2 constant F-START 3 constant F-END 4 constant F-SIMPLE
5 constant F-RA 6 constant F-SIGNAL 7 constant F-PERS? 8 constant F-PENC 9 constant F-PNA
10 constant F-PNU 11 constant F-LSDA? 12 constant F-LENC 13 constant F-LNA 14 constant F-LNU
15 constant F-OPS 16 constant F-OPST 17 constant F-NEXT
: fd@ ( fde k -- v ) cells + @ ;
: fd! ( v fde k -- ) cells + ! ;

: cfi-spec ( a u -- sa su true | false )
  2dup s" startproc" str=cs if 2drop s" " true exit then
  2dup s" endproc" str=cs if 2drop s" " true exit then
  2dup s" sections" str=cs if 2drop s" " true exit then
  2dup s" def_cfa" str=cs if 2drop s" rn" true exit then
  2dup s" def_cfa_offset" str=cs if 2drop s" n" true exit then
  2dup s" def_cfa_register" str=cs if 2drop s" r" true exit then
  2dup s" adjust_cfa_offset" str=cs if 2drop s" n" true exit then
  2dup s" offset" str=cs if 2drop s" rn" true exit then
  2dup s" val_offset" str=cs if 2drop s" rn" true exit then
  2dup s" rel_offset" str=cs if 2drop s" rn" true exit then
  2dup s" restore" str=cs if 2drop s" r" true exit then
  2dup s" undefined" str=cs if 2drop s" r" true exit then
  2dup s" same_value" str=cs if 2drop s" r" true exit then
  2dup s" register" str=cs if 2drop s" rr" true exit then
  2dup s" remember_state" str=cs if 2drop s" " true exit then
  2dup s" restore_state" str=cs if 2drop s" " true exit then
  2dup s" return_column" str=cs if 2drop s" r" true exit then
  2dup s" signal_frame" str=cs if 2drop s" " true exit then
  2dup s" window_save" str=cs if 2drop s" " true exit then
  2dup s" negate_ra_state" str=cs if 2drop s" " true exit then
  2dup s" escape" str=cs if 2drop s" *" true exit then
  2dup s" personality" str=cs if 2drop s" ns" true exit then
  s" lsda" str=cs if s" ns" true else false then ;

: cfi-num ( op-a op-u text-a text-u -- n ok ) { oa ou ta tu }
  false undef-flag !
  ta tu 0 expr-asm drop { v }
  undef-flag @ { un }  false undef-flag !
  un v qundef-derived? or v qnbit 63 > or if
    mb-reset s"  error - .cfi_" mb+ oa ou mb+ s" : '" mb+ ta tu mb+ s" ' is not a constant." mb+ mb-get diag-e
    0 false exit
  then
  v q>n true ;
: cfi-reg ( op-a op-u text-a text-u -- n ok ) { oa ou ta tu }
  ta tu slower d-cfireg om-find ?dup if @ true exit then
  oa ou ta tu cfi-num 0= if drop 0 false exit then
  dup 0< if
    drop mb-reset s"  error - .cfi_" mb+ oa ou mb+ s" : '" mb+ ta tu mb+ s" ' is not a register." mb+ mb-get diag-e 0 false exit
  then
  true ;

256 constant MAXCA
create ca-a MAXCA cells allot  create ca-u MAXCA cells allot  variable ca-n
create cv MAXCA cells allot
: split-args ( a u -- ) { a u }
  0 ca-n !
  a u nonblank? 0= if exit then
  0 { st }
  u 1+ 0 ?do
    i u = a i + c@ 44 = or if
      ca-n @ MAXCA < if
        a st + i st - strip-st ca-n @ cells ca-u + ! ca-n @ cells ca-a + !
        1 ca-n +!
      then
      i 1+ to st
    then
  loop ;

: fde-new ( sa su start simple -- fde ) { sa su start simple }
  FDE-SZ cells allocate throw { f }
  f FDE-SZ cells erase
  sa su intern f F-SECU fd! f F-SECA fd!
  start f F-START fd!  start f F-END fd!  simple f F-SIMPLE fd!  -1 f F-RA fd! 
  f ;
: fde-op-add ( fde off op-a op-u nvals -- ) { f off oa ou nv }
  nv 5 + cells allocate throw { e }
  0 e !  off e cell+ !  oa ou intern e 3 cells + ! e 2 cells + !  nv e 4 cells + !
  nv 0 ?do cv i cells + @ e 5 i + cells + ! loop
  f F-OPS fd@ 0= if e f F-OPS fd! else e f F-OPST fd@ ! then
  e f F-OPST fd! ;

variable cfi-opa variable cfi-opu variable cfi-nv


: cfi-arg ( i kind -- n ok ) { i kind }
  cfi-opa @ cfi-opu @ i cells ca-a + @ i cells ca-u + @ { oa ou ta tu }
  kind 114 = if oa ou ta tu cfi-reg exit then
  kind 115 = if 0 true exit then
  oa ou ta tu cfi-num { n ok }
  ok kind 42 = and if
    n 0 256 within 0= if
      mb-reset s"  error - .cfi_" mb+ oa ou mb+ s" : '" mb+ ta tu mb+ s" ' is not a byte." mb+ mb-get diag-e
      0 false exit
    then
  then
  n ok ;

\ 引数を spec に従って cv へ。成功なら true
: cfi-vals ( spec-a spec-u -- ok ) { sa su }
  sa su s" *" str=cs if
    ca-n @ 0= if
      mb-reset s"  error - .cfi_" mb+ cfi-opa @ cfi-opu @ mb+ s" : at least one argument is required." mb+ mb-get diag-e false exit
    then
  else
    ca-n @ su <> if
      mb-reset s"  error - .cfi_" mb+ cfi-opa @ cfi-opu @ mb+ s" : " mb+ su mb-n s"  argument(s) expected." mb+ mb-get diag-e false exit
    then
  then
  ca-n @ 0 ?do
    sa su s" *" str=cs if 42 else sa i + c@ then i swap cfi-arg
    0= if drop false unloop exit then
    i cells cv + !
  loop
  ca-n @ cfi-nv !
  true ;

: dir-cfi ( l1a l1u l2a l2u -- ) { l1a l1u l2a l2u }
  report? o-obj-u @ 0<> and 0= if exit then
  l1a 5 + l1u 5 - slower { oa ou }
  oa ou cfi-spec 0= if
    mb-reset s"  error - unknown CFI directive '" mb+ l1a l1u mb+ s" '." mb+ mb-get diag-e exit
  then
  { sa su }
  oa ou s" sections" str=cs if exit then
  oa cfi-opa !  ou cfi-opu !
  l2a l2u split-args
  cur-section { csa csu }
  csa csu pc @ sec-rel-offset-impl 0= if pc @ then { off }
  oa ou s" startproc" str=cs if
    cfi-cur @ if
      s"  error - .cfi_startproc: the previous .cfi_startproc has no .cfi_endproc." diag-e exit
    then
    ca-n @ if
      ca-n @ 1 <> if true else 0 cells ca-a + @ 0 cells ca-u + @ slower s" simple" str=cs 0= then if
        mb-reset s"  error - .cfi_startproc: unknown argument '" mb+ l2a l2u strip-st mb+ s" '." mb+ mb-get diag-e exit
      then
    then
    csa csu off ca-n @ 0<> if 1 else 0 then fde-new cfi-cur ! exit
  then
  cfi-cur @ 0= if
    mb-reset s"  error - .cfi_" mb+ oa ou mb+ s" : not inside .cfi_startproc." mb+ mb-get diag-e exit
  then
  cfi-cur @ { cur }
  csa csu cur F-SECA fd@ cur F-SECU fd@ str=cs 0= if
    mb-reset s"  error - .cfi_" mb+ oa ou mb+ s" : the section changed inside the function." mb+ mb-get diag-e exit
  then
  sa su cfi-vals 0= if exit then
  oa ou s" endproc" str=cs if
    off cur F-END fd!
    cfi-head @ 0= if cur cfi-head ! else cur cfi-tail @ F-NEXT fd! then
    cur cfi-tail !  0 cfi-cur ! exit
  then
  oa ou s" return_column" str=cs if cv @ cur F-RA fd! exit then
  oa ou s" signal_frame" str=cs if 1 cur F-SIGNAL fd! exit then
  oa ou s" personality" str=cs oa ou s" lsda" str=cs or if
    cv @ 0 256 within 0= if
      mb-reset s"  error - .cfi_" mb+ oa ou mb+ s" : '" mb+ 0 cells ca-a + @ 0 cells ca-u + @ mb+ s" ' is not an encoding byte." mb+ mb-get diag-e exit
    then
    oa ou s" personality" str=cs { isp }
    cv @ 255 = if
      0 cur isp if F-PERS? else F-LSDA? then fd!
    else
      1 cur isp if F-PERS? else F-LSDA? then fd!
      cv @ cur isp if F-PENC else F-LENC then fd!
      1 cells ca-a + @ 1 cells ca-u + @ intern
      isp if cur F-PNU fd! cur F-PNA fd! else cur F-LNU fd! cur F-LNA fd! then
    then
    exit
  then
  cur off oa ou cfi-nv @ fde-op-add ;

\ ---- 振り分け ----
: elf-src-dir-impl ( la lu l2a l2u -- handled? ) { la lu l2a l2u }
  la lu supper { ua uu }
  ua uu s" .EXTERN" str=cs if l2a l2u dir-extern true exit then
  ua uu s" .RELOCTYPE" str=cs if l2a l2u dir-reloctype true exit then
  ua uu s" .EXPORT" str=cs ua uu s" .GLOBAL" str=cs or if l2a l2u dir-export true exit then
  uu 5 >= if ua 5 s" .CFI_" str=cs else false then if la lu l2a l2u dir-cfi true exit then
  ua uu s" .TYPE" str=cs if l2a l2u dir-type true exit then
  ua uu s" .SIZE" str=cs if l2a l2u dir-size true exit then
  ua uu s" .WEAK" str=cs if l2a l2u dir-weak true exit then
  ua uu s" .HIDDEN" str=cs if l2a l2u 2 dir-vis true exit then
  ua uu s" .PROTECTED" str=cs if l2a l2u 3 dir-vis true exit then
  ua uu s" .INTERNAL" str=cs if l2a l2u 1 dir-vis true exit then
  ua uu s" .OTHER" str=cs if l2a l2u dir-other true exit then
  ua uu s" .COMM" str=cs if l2a l2u dir-comm true exit then
  false ;
bind elf-src-dir-impl elf-src-dir
