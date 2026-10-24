\ elf12.fs -- ELF オブジェクトの書き出し (3): グループ、シンボル表

decimal

\ ---- セクショングループ ----
variable G
64 constant MAXGRP
create gr-na MAXGRP cells allot  create gr-nu MAXGRP cells allot       \ グループ名
create gr-sa MAXGRP cells allot  create gr-su MAXGRP cells allot       \ 署名
create gr-fl MAXGRP cells allot
create gr-mem MAXGRP 256 * cells allot  create gr-nm MAXGRP cells allot   \ メンバー (セクション番号 1 始まり)
create grp-member 4096 cells allot                                        \ セクション番号 -> 1
variable ngr

: build-groups ( -- )
  0 ngr !  grp-member 4096 cells erase
  d-group om-used 0 ?do
    i d-group om-live? if
      i d-group om-val { sl }
      sl dstr@ { gn gnu }  sl 2 cells + dstr@ { sg sgu }  sl 4 cells + @ { fl }
      sl 5 cells + dstr@ { ma mu }
      0 { nm }
      ngr @ MAXGRP < if
        ngr @ 256 * cells gr-mem + { mp }
        0 { st }
        mu 1+ 0 ?do
          i mu = ma i + c@ 44 = or if
            ma st + i st - { xa xu }
            xa xu cs-find-ci { k }
            k 0< if
              mb-reset s"  warning - .elfgroup: member section '" mb+ xa xu mb+ s" ' of group '" mb+ gn gnu mb+ s" ' is not in the output; ignored." mb+ mb-get diag-w
            else
              false nm 0 ?do mp i cells + @ k 1+ = if drop true then loop 0= if
                nm 256 < if k 1+ mp nm cells + !  nm 1+ to nm then
              then
            then
            i 1+ to st
          then
        loop
      then
      nm 0> ngr @ MAXGRP < and if
        gn gnu ngr @ cells gr-nu + ! ngr @ cells gr-na + !
        sg sgu ngr @ cells gr-su + ! ngr @ cells gr-sa + !
        fl ngr @ cells gr-fl + !  nm ngr @ cells gr-nm + !
        1 ngr +!
      else
        mb-reset s"  warning - .elfgroup: group '" mb+ gn gnu mb+ s" ' has no member in the output; not written." mb+ mb-get diag-w
      then
    then
  loop
  ngr @ G !
  ngr @ 0 ?do
    i 256 * cells gr-mem + { mp }
    i cells gr-nm + @ 0 ?do
      mp i cells + @ { k }
      cs-fl k 1- cells + dup @ 512 or swap !
      1 k cells grp-member + !
    loop
  loop ;

\ ---- CFI の局所シンボル ----
variable cfp-n
4096 constant MAXCFP
create cfp-sec MAXCFP cells allot  create cfp-secu MAXCFP cells allot  create cfp-b MAXCFP cells allot
create cfp-nm MAXCFP cells allot   create cfp-nmu MAXCFP cells allot

: cfi-relax? ( -- pa pb true | false )
  elf-relaxing? 0= if false exit then
  cfi-head @ 0= if false exit then
  4 n>s mt-diff om-find ?dup if dup @ swap cell+ @ true else false then ;

: cfp-has? ( sa su b -- f ) { sa su b }
  cfp-n @ 0 ?do
    i cells cfp-b + @ b = if i cells cfp-sec + @ i cells cfp-secu + @ sa su str=cs if true unloop exit then then
  loop false ;
: cfp-add ( sa su b -- ) { sa su b }
  sa su b cfp-has? if exit then
  cfp-n @ MAXCFP >= if exit then
  sa su intern cfp-n @ cells cfp-secu + ! cfp-n @ cells cfp-sec + !
  b cfp-n @ cells cfp-b + !
  1 cfp-n +! ;

: cfi-points ( -- )
  0 cfp-n !
  cfi-head @ { f }
  begin f while
    f F-SECA fd@ f F-SECU fd@ { sa su }
    f F-START fd@ e-bpw @ * { cur }
    sa su cur cfp-add
    f F-OPS fd@ { op }
    begin op while
      op cell+ @ e-bpw @ * { ob }
      ob cur > if sa su ob cfp-add ob to cur then
      op @ to op
    repeat
    sa su f F-END fd@ e-bpw @ * cfp-add
    f F-NEXT fd@ to f
  repeat ;

\ ---- シンボル表 ----
variable sy-sb  variable st-sb  variable sx-base  variable sx-n  variable sy-n
variable sy-first-global
1 om-new constant symidx
create cfsyn MAXCFP cells allot                    \ .Lcfi<n> の番号 (シンボル表の添字)

: sym-special-xidx ( shndx special -- shndx' )
  { sh sp }
  sp 0= sh 65280 >= and if sh sx-n @ cells sx-base @ + ! 65535 else 0 sx-n @ cells sx-base @ + ! sh then
  1 sx-n +! ;

: pack-sym ( nm info oth shndx val sz -- ) { nm info oth shndx val sz }
  val word-mask-v to val  sz word-mask-v to sz
  w-64 @ if
    nm sy-sb @ put32  info sy-sb @ put8  oth sy-sb @ put8  shndx sy-sb @ put16  val sy-sb @ put64  sz sy-sb @ put64
  else
    nm sy-sb @ put32  val sy-sb @ put32  sz sy-sb @ put32  info sy-sb @ put8  oth sy-sb @ put8  shndx sy-sb @ put16
  then ;
: psym ( nm info oth shndx special val sz -- ) { nm info oth shndx sp val sz }
  shndx sp sym-special-xidx { sh2 }
  nm info oth sh2 val sz pack-sym
  1 sy-n +! ;

: st-info ( a u bind -- info ) { a u bind }
  a u SA-WEAK sym-attr@ if 2 to bind then
  bind 15 and 4 lshift  a u SA-TYPE sym-attr@ 15 and or ;
: sym-bpw ( -- n ) mt-word-unit? if 1 else e-bpw @ then ;
: sym-size ( a u -- n ) { a u }
  a u SA-SIZE-SET sym-attr@ if a u SA-SIZE sym-attr@ sym-bpw * else 0 then ;
: strtab-add ( a u -- off ) st-sb @ bb-len -rot st-sb @ put-cstr ;

\ find_shndx: ( byte-addr sec-a sec-u -- shndx symval )
: find-shndx ( ba sa su -- shndx val ) { ba sa su }
  ba e-bpw @ / { wpc }
  su 0> if
    sa su cs-find { ix }
    ix 0>= if
      sa su wpc addr>woff if e-bpw @ * ix 1+ G @ + swap exit then
    then
  then
  ncs @ 0 ?do
    i cs-name wpc addr>woff if e-bpw @ * i 1+ G @ + swap unloop exit then
  loop
  ncs @ if
    0 { bi }  0 cs-bs @ { bst }
    ncs @ 0 ?do
      i cells cs-bs + @ { sb0 }
      sb0 ba <= sb0 bst >= and if i to bi sb0 to bst then
    loop
    ba bi cells cs-bs + @ - 0 max { sv }
    bi 1+ G @ + sv exit
  then
  65521 ba ;


\ ラベル 1 個をシンボルにする。slot は先頭 7 セルが (q×4, sec-a, sec-u, equ) の記録
: emit-label-sym ( a u slot bind -- ) { a u slot bind }
  a u lab-find { le }
  le 0<> if le lab-rtype 0>= else false then { eqr }
  slot 6 cells + @ 0<> { eq }
  slot q>n { val }
  slot 4 cells + s@ { sa su }
  eq eqr 0= and if
    65521 val true
  else
    val e-bpw @ * sa su find-shndx { sh sv }
    ncs @ 0= { sp }
    mt-word-unit? if sv e-bpw @ / to sv then
    sh sv sp
  then
  { shndx sval special }
  sval word-mask-v to sval
  a u sym-size { sz }
  a u SA-COMMON sym-attr@ if
    a u SA-ALIGN sym-attr@ to sval
    a u SA-SIZE sym-attr@ sym-bpw * to sz
    65522 to shndx
  then
  a u strtab-add { noff }
  noff a u bind st-info a u SA-OTHER sym-attr@ shndx
  special a u SA-COMMON sym-attr@ 0<> or
  sval sz psym ;

: sy-locals ( la ln -- ) { la ln }
  ln 0 ?do
    la i cells + @ { ix }
    ix labels om-key { na nu }
    ix labels om-val { sl }
    na nu export-labels om-find 0= sl lab-imported? 0= and if
      na nu symidx om-put sy-n @ swap !
      na nu sl 0 emit-label-sym
    then
  loop ;

: sy-cfi-synth ( -- )
  cfp-n @ 0 ?do
    mb-reset s" .Lcfi" mb+ i mb-n
    begin mb-get lab-find 0<> mb-get export-labels om-find 0<> or while 95 mb-c repeat
    mb-get intern { na nu }
    i cells cfp-sec + @ i cells cfp-secu + @ cs-find { sx }
    0 i cells cfsyn + !
    sx 0>= if
      sy-n @ i cells cfsyn + !
      na nu strtab-add { noff }
      i cells cfp-b + @ { cb }
      noff 0 0 sx 1+ G @ + false  mt-word-unit? if cb e-bpw @ / else cb then  0 psym
    then
  loop ;

: sy-anchors ( -- )
  an-n @ 0 ?do
    i cells an-sa + @ i cells an-su + @ cs-find { sx }
    sx 0>= if
      i cells an-na + @ i cells an-nu + @ symidx om-put sy-n @ swap !
      i cells an-na + @ i cells an-nu + @ strtab-add { noff }
      i cells an-off + @ { ao }
      noff 0 0 sx 1+ G @ + false  mt-word-unit? if ao e-bpw @ / else ao then  0 psym
    then
  loop ;

: sy-imported ( la ln -- ) { la ln }
  ln 0 ?do
    la i cells + @ { ix }
    ix labels om-key { na nu }
    ix labels om-val { sl }
    sl lab-imported? na nu export-labels om-find 0= and if
      na nu symidx om-put sy-n @ swap !
      na nu sym-size { sz }  0 { sval }  0 { shndx }
      na nu SA-COMMON sym-attr@ if
        na nu SA-ALIGN sym-attr@ to sval
        na nu SA-SIZE sym-attr@ sym-bpw * to sz
        65522 to shndx
      then
      na nu strtab-add { noff }
      noff na nu 1 st-info na nu SA-OTHER sym-attr@ shndx true sval sz psym
    then
  loop ;

: sy-exports ( -- )
  export-labels sort-om { ea en }
  en 0 ?do
    ea i cells + @ { ix }
    ix export-labels om-key { na nu }
    ix export-labels om-val { sl }
    sl qundef-derived? 0= if
      na nu symidx om-put sy-n @ swap !
      na nu sl 1 emit-label-sym
    then
  loop
  ea free throw ;

: build-symtab ( -- )
  bb-new sy-sb !  bb-new st-sb !
  0 st-sb @ sb-c
  labels om-count export-labels om-count + ncs @ + an-n @ + cfp-n @ + 8 + cells allocate throw sx-base !
  0 sx-n !  0 sy-n !
  symidx om-clear
  0 0 0 0 true 0 0 psym
  ncs @ 0 ?do 0 3 0 i 1+ G @ + false 0 0 psym loop
  cfi-relax? if 2drop cfi-points else 0 cfp-n ! then
  labels sort-om { la ln }
  la ln sy-locals
  sy-cfi-synth
  sy-anchors
  sy-n @ sy-first-global !
  la ln sy-imported
  sy-exports
  la free throw ;
