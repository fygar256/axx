\ elf2.fs -- ELF マシン表 (elf_machine_table): 組み込みの表に宣言をかぶせた実表

decimal

\ ---- 基盤 (組み込みの表) ----
2 lazy-om bs-named                          \ 名前 -> rt w
1 lazy-om bs-bytes                          \ rt -> w
create bs-wg 9 cells allot
1 lazy-om bs-pc
4 lazy-om bs-field
variable bs-ext  variable bs-dwarf  variable bs-rela  variable bs-class  variable bs-pcg
variable bs-name-a  variable bs-name-u

: rtk ( rt -- a u ) n>s ;

: b-name ( a u -- ) bs-name-u ! bs-name-a ! ;
: b-class ( n -- ) bs-class ! ;
: b-rela ( n -- ) bs-rela ! ;
: b-wg ( nbytes rt -- ) swap cells bs-wg + ! ;
: b-pc ( rt -- ) rtk bs-pc om-put 1 swap ! ;
: b-ext ( rt -- ) bs-ext ! ;
: b-dwarf ( rt -- ) bs-dwarf ! ;
: b-pcg ( n -- ) bs-pcg ! ;
: b-named ( a u rt w -- ) { a u rt w }
  a u bs-named om-put { sl }  rt sl !  w sl cell+ !
  rt rtk bs-bytes om-put w swap ! ;
: b-field ( rt mask off sh bias -- ) { rt m off sh bias }
  rt rtk bs-field om-put { sl }
  m sl !  off sl cell+ !  sh sl 2 cells + !  bias sl 3 cells + ! ;
lazy-sb known-sb
: b-known+ ( a u -- ) known-sb sb-len if s" , " known-sb sb+ then known-sb sb+ ;

: bs-clear ( -- )
  bs-named om-clear  bs-bytes om-clear  bs-pc om-clear  bs-field om-clear
  bs-wg 9 cells erase
  0 bs-ext !  0 bs-dwarf !  1 bs-rela !  2 bs-class !  0 bs-pcg !
  0 bs-name-a !  0 bs-name-u ! ;

s" elfmach.fs" included

\ ---- 実表 ----
1 lazy-om mt-named                          \ 名前 -> rt
1 lazy-om mt-bytes                          \ rt -> 幅
2 lazy-om mt-rev                            \ rt -> 名前
1 lazy-om mt-pc
4 lazy-om mt-field                          \ rt -> mask off sh bias
1 lazy-om mt-extra                          \ rt -> 配列 [n][crt sym]*
2 lazy-om mt-diff                           \ 幅 -> ra rb
2 lazy-om mt-diff-t                         \ rt -> ra rb
2 lazy-om mt-encode                         \ rt -> 関数名
1 lazy-om mt-anchor
1 lazy-om mt-resolve
1 lazy-om mt-unal                           \ rt -> 代わりの rt
create mt-wg 9 cells allot
variable mt-ext  variable mt-dwarf  variable mt-rela  variable mt-class  variable mt-pcg
variable mt-name-a  variable mt-name-u
variable mt-rinfo-a variable mt-rinfo-u
variable mt-unit                                    \ 0 byte / 1 word
variable mt-key-m  -1 mt-key-m !  variable mt-key-g  -1 mt-key-g !

: mt-named-find-impl ( a u -- rt true | false ) mt-named om-find ?dup if @ true else false then ;
bind mt-named-find-impl mt-named-find

: ml-add ( list crt csym -- list' ) { l crt cs }
  l 0= if 3 cells allocate throw to l 0 l ! else
    l @ 2* 1+ 1+ cells l swap resize throw to l then
  l @ { n }
  crt l n 2* 1+ cells + !  cs l n 2* 2 + cells + !
  n 1+ l !  l ;
: ml-n ( l -- n ) ?dup if @ else 0 then ;
: ml-crt ( l i -- crt ) 2* 1+ cells + @ ;
: ml-sym ( l i -- sym ) 2* 2 + cells + @ ;

: mt-clear ( -- )
  mt-named om-clear mt-bytes om-clear mt-rev om-clear mt-pc om-clear mt-field om-clear
  mt-extra om-clear mt-diff om-clear mt-diff-t om-clear mt-encode om-clear
  mt-anchor om-clear mt-resolve om-clear mt-unal om-clear ;

: mt-merge-base ( -- )
  bs-named om-used 0 ?do
    i bs-named om-live? if
      i bs-named om-key { na nu }
      na nu elftypes om-find 0= if
        i bs-named om-val @ { rt }
        na nu mt-named om-find 0= if na nu mt-named om-put rt swap ! then
        rt rtk mt-rev om-find 0= if rt rtk mt-rev om-put na nu intern rot s! then
        rt rtk bs-bytes om-find ?dup if @ else 0 then { w }
        w if rt rtk mt-bytes om-find 0= if rt rtk mt-bytes om-put w swap ! then then
      then
    then
  loop ;
: mt-merge-decl ( -- )
  elftypes om-used 0 ?do
    i elftypes om-live? if
      i elftypes om-key { na nu }
      i elftypes om-val @ { rt }
      na nu mt-named om-find 0= if na nu mt-named om-put rt swap ! then
      rt rtk mt-rev om-find 0= if rt rtk mt-rev om-put na nu intern rot s! then
      na nu type-width om-find ?dup if @ else 0 then { w }
      w if rt rtk mt-bytes om-find 0= if rt rtk mt-bytes om-put w swap ! then then
    then
  loop
  type-pcrel om-used 0 ?do
    i type-pcrel om-live? if
      i type-pcrel om-key elftypes om-find ?dup if @ rtk mt-pc om-put 1 swap ! then
    then
  loop ;
: mt-decl-scalars ( -- )
  d-width om-used 0 ?do
    i d-width om-live? if
      i d-width om-key parse-int0 drop { nb }
      i d-width om-val dstr@ decl-type if nb 0 max 8 min cells mt-wg + ! then
    then
  loop
  d-extern-u @ if d-extern-a @ d-extern-u @ decl-type if mt-ext ! then then
  d-dwarf-u @ if d-dwarf-a @ d-dwarf-u @ decl-type if mt-dwarf ! then then
  d-rela @ 0>= if d-rela @ 0<> if 1 else 0 then mt-rela ! then
  d-class @ if d-class @ mt-class ! then
  d-pcguess @ 0>= if d-pcguess @ mt-pcg ! then
  bs-name-a @ bs-name-u @ mt-name-u ! mt-name-a !
  d-name-u @ if
    d-machine @ 0< d-machine @ elf-machine @ = or if
      d-name-a @ d-name-u @ mt-name-u ! mt-name-a !
    then
  then
  mt-name-u @ 0= if
    mb-reset s" machine " mb+ elf-machine @ mb-n mb-get intern mt-name-u ! mt-name-a !
  then ;
: field-copy ( src dst -- ) { s d }
  s @ d !  s cell+ @ d cell+ !  s 2 cells + @ d 2 cells + !  s 3 cells + @ d 3 cells + ! ;
: mt-fields ( -- )
  d-field om-used 0 ?do
    i d-field om-live? if
      i d-field om-key decl-type if
        { rt }
        rt rtk mt-field om-find 0= if
          i d-field om-val  rt rtk mt-field om-put  field-copy
        then
      then
    then
  loop
  bs-field om-used 0 ?do
    i bs-field om-live? if
      i bs-field om-key { ka ku }
      ka ku mt-field om-find 0= if
        i bs-field om-val  ka ku mt-field om-put  field-copy
      then
    then
  loop ;
: mt-extras ( -- )
  d-extra om-used 0 ?do
    i d-extra om-live? if
      i d-extra om-key decl-type if
        { rt }
        rt rtk mt-extra om-find 0= if rt rtk mt-extra om-put 0 swap ! then
        rt rtk mt-extra om-find { esl }
        i d-extra om-val @ { co }
        co om-used 0 ?do
          i co om-live? if
            i co om-key decl-type if
              { crt }
              esl @ crt i co om-val @ ml-add esl !
            then
          then
        loop
      then
    then
  loop ;
: mt-diffs ( -- )
  d-diff om-used 0 ?do
    i d-diff om-live? if
      i d-diff om-val { sl }
      sl dstr@ decl-type if
        sl 2 cells + dstr@ decl-type if
          { ra rb }
          i d-diff om-key mt-diff om-put { ds }  ra ds !  rb ds cell+ !
        else drop then
      then
    then
  loop
  d-diff-t om-used 0 ?do
    i d-diff-t om-live? if
      i d-diff-t om-val { sl }
      i d-diff-t om-key decl-type if
        { rt }
        sl dstr@ decl-type if
          sl 2 cells + dstr@ decl-type if
            { ra rb }
            rt rtk mt-diff-t om-find 0= if rt rtk mt-diff-t om-put { ds } ra ds ! rb ds cell+ ! then
          else drop then
        then
      then
    then
  loop ;
: mt-misc ( -- )
  d-encode om-used 0 ?do
    i d-encode om-live? if
      i d-encode om-key decl-type if
        { rt }
        rt rtk mt-encode om-find 0= if
          rt rtk mt-encode om-put { ds }  0 ds ! 0 ds cell+ !
          i d-encode om-val dstr@ ds dstr
        then
      then
    then
  loop
  d-anchor om-used 0 ?do
    i d-anchor om-live? if i d-anchor om-key decl-type if rtk mt-anchor om-put drop then then
  loop
  d-resolve om-used 0 ?do
    i d-resolve om-live? if i d-resolve om-key decl-type if rtk mt-resolve om-put drop then then
  loop
  d-unaligned om-used 0 ?do
    i d-unaligned om-live? if
      i d-unaligned om-key decl-type if
        { rt }
        i d-unaligned om-val dstr@ decl-type if
          { urt } rt rtk mt-unal om-find 0= if rt rtk mt-unal om-put urt swap ! then
        then
      then
    then
  loop
  d-rinfo-a @ mt-rinfo-a !  d-rinfo-u @ mt-rinfo-u !
  d-unit @ 2 = if 1 else 0 then mt-unit ! ;

: mt-build ( -- )
  mt-clear  bs-clear
  d-builtin @ 0= if
    0 0 bs-name-u ! bs-name-a !  2 bs-class !  1 bs-rela !
  else
    elf-machine @ base-known? if elf-machine @ base-load then
  then
  bs-wg mt-wg 9 cells move
  bs-pc om-used 0 ?do i bs-pc om-live? if i bs-pc om-key mt-pc om-put 1 swap ! then loop
  bs-ext @ mt-ext !  bs-dwarf @ mt-dwarf !  bs-rela @ mt-rela !  bs-class @ mt-class !  bs-pcg @ mt-pcg !
  mt-merge-base  mt-merge-decl
  mt-decl-scalars  mt-fields  mt-extras  mt-diffs  mt-misc
  elf-machine @ mt-key-m !  decl-gen @ mt-key-g ! ;

: mach-table ( -- ) elf-machine @ mt-key-m @ <> decl-gen @ mt-key-g @ <> or if mt-build then ;

\ ---- 引き口 ----
: mt-wg@ ( n -- rt ) mach-table dup 0 9 within if cells mt-wg + @ else drop 0 then ;
: mt-bytes@ ( rt -- w|-1 ) mach-table rtk mt-bytes om-find ?dup if @ else -1 then ;
: mt-pc? ( rt -- f ) mach-table rtk mt-pc om-find 0<> ;
: mt-field? ( rt -- mask off sh bias true | false ) mach-table rtk mt-field om-find ?dup if
    { sl } sl @ sl cell+ @ sl 2 cells + @ sl 3 cells + @ true else false then ;
: mt-rev@ ( rt -- a u ) mach-table rtk mt-rev om-find ?dup if s@ else s" " then ;
: mt-name ( -- a u ) mach-table mt-name-a @ mt-name-u @ ;
: mt-extern ( -- rt ) mach-table mt-ext @ ;
: mt-dwarf@ ( -- rt ) mach-table mt-dwarf @ ;
: mt-rela? ( -- f ) mach-table mt-rela @ 0<> ;
: mt-class@ ( -- n ) mach-table mt-class @ ;
: mt-pcg? ( -- f ) mach-table mt-pcg @ 0<> ;
: mt-word-unit? ( -- f ) mach-table mt-unit @ 0<> ;

: reloc-named-t ( a u -- rt true | false )
  mach-table slower 2dup elftypes om-find ?dup if nip nip @ true exit then
  mt-named om-find ?dup if @ true else false then ;
: reloc-named-nn8 ( a u -- n ) reloc-named-t if else -1 then ; bind reloc-named-nn8 reloc-named
bind reloc-named equ-reloc-named
: equ-machine-no-nn9 elf-machine @ ; bind equ-machine-no-nn9 equ-machine-no

\ ---- 名前順の並べ替え (Python の sorted(dict.items())) ----
\ om のエントリ番号の列を鍵 (a u) のバイト順で並べる。生きているものだけ。
variable so-om
: so-key ( idx -- a u ) so-om @ om-key ;
variable so-num                                     \ 1 なら鍵を数として比べる
: so-less? ( i j -- f ) so-num @ if
    so-key parse-int0 drop >r so-key parse-int0 drop r> <
  else so-key rot so-key 2swap compare 0< then ;   \ key(i) < key(j)
: sort-om ( om -- arr n ) { om }
  om so-om !
  om om-count 1 max cells allocate throw { arr }  0 { n }
  om om-used 0 ?do i om om-live? if i arr n cells + ! n 1+ to n then loop
  \ 挿入ソート (安定)
  n 1 > if n 1 do
    arr i cells + @ { x }  i { j }
    begin j 0> if x arr j 1- cells + @ so-less? else false then while
      arr j 1- cells + @ arr j cells + !  j 1- to j
    repeat
    x arr j cells + !
  loop then
  arr n ;
bind sort-om equ-sort-om
: sort-om-num ( om -- arr n ) 1 so-num ! sort-om 0 so-num ! ;
