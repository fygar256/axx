\ elf1.fs -- ELF の状態、パターンファイルの .elf* 宣言

decimal

\ ---- 状態 ----
variable elf-machine   62 elf-machine !
variable elf-mach-cli  false elf-mach-cli !         \ -m が与えられたか
variable elf-class-cli 0 elf-class-cli !            \ -f: 0 なし / 1 = 32 / 2 = 64
variable elf-osabi-v   0 elf-osabi-v !
variable decl-gen      0 decl-gen !

1 lazy-om elftypes                          \ 型名(小文字) -> 型番号
1 lazy-om type-width                        \ 型名 -> 欄の幅
1 lazy-om type-pcrel                        \ 型名 -> 1

variable d-machine  -1 d-machine !
create d-name 2 cells allot  d-name 2 cells erase
: d-name-a d-name ;  : d-name-u d-name cell+ ;
variable d-class    0 d-class !                     \ 0 なし / 1 / 2
variable d-rela     -1 d-rela !
2 lazy-om d-width                           \ 幅(10 進) -> 型の綴り
create d-extern 2 cells allot  d-extern 2 cells erase
: d-extern-a d-extern ;  : d-extern-u d-extern cell+ ;
create d-dwarf 2 cells allot  d-dwarf 2 cells erase
: d-dwarf-a d-dwarf ;  : d-dwarf-u d-dwarf cell+ ;
1 lazy-om d-hdr                             \ 欄名 -> 値
4 lazy-om d-field                           \ 型の綴り -> mask off sh bias
4 lazy-om d-sec                             \ 名前(小文字) -> fl ty al es (-1 = なし)
variable d-pcguess  -1 d-pcguess !
variable d-relax    -1 d-relax !
variable d-builtin  -1 d-builtin !
1 lazy-om d-extra                           \ 型の綴り -> om (添える型の綴り -> シンボル)
4 lazy-om d-diff                            \ 幅 -> 足す型 a u, 引く型 a u
4 lazy-om d-diff-t
2 lazy-om d-encode                          \ 型の綴り -> 関数名
1 lazy-om d-anchor
1 lazy-om d-resolve
2 lazy-om d-unaligned
create d-rinfo 2 cells allot  d-rinfo 2 cells erase
: d-rinfo-a d-rinfo ;  : d-rinfo-u d-rinfo cell+ ;
variable d-unit     0 d-unit !                      \ 0 なし / 1 byte / 2 word
4 lazy-om d-link                            \ 名前(小文字) -> lk a u, inf a u
7 lazy-om d-group                           \ 鍵 -> gn a u, sig a u, fl, mem a u
variable d-cfi?     false d-cfi? !
variable d-cfi-ra  variable d-cfi-ca  variable d-cfi-da  variable d-cfi-pad
1 lazy-om d-cfiinit
1 lazy-om d-cfireg

: elf-gen+ ( -- ) 1 decl-gen +! ;

\ ---- 小道具 ----
: strip-spaces2 ( a u -- a' u' )                     \ 空白とタブをすべて除く
  { a u } u 1+ ar-alloc { d } 0 { k }
  u 0 ?do a i + c@ dup 32 <> over 9 <> and if d k + c! k 1+ to k else drop then loop
  d k ;
: nonblank? ( a u -- f ) strip-st nip 0<> ;

: dset ( n addr -- ) { n ad } ad @ n <> if n ad ! elf-gen+ then ;
: dstr ( a u addr -- ) { a u ad }                    \ addr は (a u) の 2 セル
  ad @ if ad @ ad cell+ @ a u str=cs if exit then then
  a u intern ad cell+ ! ad ! elf-gen+ ;
: dstr@ ( addr -- a u ) dup @ swap cell+ @ ;

: fld4= ( e m off sh bias -- f ) { e m off sh bias } e @ m = e cell+ @ off = and e 2 cells + @ sh = and e 3 cells + @ bias = and ;
: dstr2= ( e a u b bu -- f ) { e a u b bu } e dstr@ a u str=cs e 2 cells + dstr@ b bu str=cs and ;
: grp= ( e ga gu sa su fl mb k -- f ) { e ga gu sa su fl mb k }
  e dstr@ ga gu str=cs e 2 cells + dstr@ sa su str=cs and e 4 cells + @ fl = and e 5 cells + dstr@ mb k str=cs and ;
: sec4= ( e fl ty al es -- f ) { e fl ty al es } e @ fl = e cell+ @ ty = and e 2 cells + @ al = and e 3 cells + @ es = and ;

\ Python の int(s, 0) (符号と 0x 0o 0b、'_' 可)
: parse-int0 ( a u -- n ok ) { a u }
  a u strip-st to u to a
  u 0= if 0 false exit then
  false { neg }  0 { k }
  a c@ 45 = if true to neg 1 to k else a c@ 43 = if 1 to k then then
  k u >= if 0 false exit then
  10 { base }
  a k + c@ 48 = k 1+ u < and if
    a k 1+ + c@ lc { px }
    px 120 = if 16 to base k 2 + to k else
    px 111 = if 8 to base k 2 + to k else
    px 98 = if 2 to base k 2 + to k then then then
  then
  k u >= if 0 false exit then
  0 { v }  false { prev-us }  false { any }
  begin k u < while
    a k + c@ { c }
    c 95 = if
      any 0= prev-us or if 0 false exit then
      true to prev-us
    else
      c digc? if c 48 - else c lc 97 >= c lc 102 <= and if c lc 87 - else 100 then then { d }
      d base >= if 0 false exit then
      v base * d + to v  true to any  false to prev-us
    then
    k 1+ to k
  repeat
  prev-us any 0= or if 0 false exit then
  neg if v negate else v then true ;

\ 式を評価して lo..hi の整数として読む (メッセージなし)。hi = -1 は 2^64-1
: elf-eval ( a u lo hi -- n ok ) { a u lo hi }
  false undef-flag !
  a u 0 expr-pat drop { v }
  undef-flag @ { un }
  false undef-flag !
  un v qundef-derived? or if 0 false exit then
  v qnbit 64 > if 0 false exit then
  v q-neg? v qnbit 63 > and if 0 false exit then
  v q>n { n }
  v q-neg? if
    n lo < if 0 false exit then
  else
    hi -1 = if
      n lo u< if 0 false exit then
    else
      n 0< if 0 false exit then
      n lo < n hi > or if 0 false exit then
    then
  then
  n true ;

: u64s ( n -- a u ) 0 <# #s #> ;
: range-msg ( lo hi -- ) { lo hi }
  lo mb-n s" .." mb+ hi -1 = if -1 u64s mb+ else hi mb-n then ;

: elf-num ( a u dname-a dname-u lo hi -- n ok ) { a u da du lo hi }
  a u strip-st to u to a
  u 0= if
    mb-reset s"  error - " mb+ da du mb+ s" : a number is required." mb+ mb-get diag-e 0 false exit
  then
  a u lo hi elf-eval { n ok }
  ok 0= if
    mb-reset s"  error - " mb+ da du mb+ s" : value must be an integer in " mb+ lo hi range-msg
    s" , got '" mb+ a u mb+ s" '." mb+ mb-get diag-e
    0 false exit
  then
  n true ;

\ 欄の詰め方の違い (_elf_decl_fields): ( row -- 値 名前 )
: decl-fields ( row -- va vu na nu ) { r }
  r 1 rf strip-st nip if r 1 rf r 2 rf else r 2 rf s" " then ;
: rf-nb? ( row k -- a u f ) rf 2dup nonblank? ;
: dir-fail ( a u -- ) diag-e ;

\ 型の綴りを型番号へ (_elf_decl_type): 数ならそのまま、名前なら .elftype、次に表
defer mt-named-find ( a u -- rt true | false )
: mt-named-find-nn6 2drop false ; bind mt-named-find-nn6 mt-named-find

: decl-type ( a u -- rt true | false ) { a u }
  a u strip-spaces2 to u to a
  u 0= if false exit then
  a u parse-int0 if true exit then drop
  a u slower { ka ku }
  ka ku elftypes om-find ?dup if @ true exit then
  ka ku mt-named-find ;

\ ---- .elftype ----
: de-type ( row -- ) { r }
  r 1 rf nip if r 1 rf r 2 rf else r 2 rf s" " then { na nu va vu }
  na nu strip-spaces2 slower { nma nmu }
  nmu 0= if s"  error - .elftype: type name is not specified." diag-e exit then
  vu 0= if mb-reset s"  error - .elftype: type number is not specified ('" mb+ nma nmu mb+ s" ')." mb+ mb-get diag-e exit then
  va vu 1 2147483647 elf-eval 0= if
    drop mb-reset s"  error - .elftype: type number must be an integer in 1..2147483647, got '" mb+ va vu mb+ s" '." mb+ mb-get diag-e exit
  then
  { v }
  -1 { w }
  r 3 rf-nb? if s" .elftype" 1 8 elf-num 0= if drop exit then to w else 2drop then
  -1 { pc }
  r 4 rf-nb? if s" .elftype" 0 1 elf-num 0= if drop exit then to pc else 2drop then
  false { chg }
  nma nmu elftypes om-find ?dup if @ v <> else true then if true to chg then
  nma nmu type-width om-find ?dup if @ else -1 then w <> if true to chg then
  nma nmu type-pcrel om-find 0<> pc 0> <> if true to chg then
  chg if
    nma nmu elftypes om-put v swap !
    w 0< if nma nmu type-width om-del else nma nmu type-width om-put w swap ! then
    pc 0> if nma nmu type-pcrel om-put 1 swap ! else nma nmu type-pcrel om-del then
    elf-gen+
  then ;

\ ---- 単純な宣言 ----
: de-machine ( row -- ) { r }
  r decl-fields { va vu na nu }
  va vu s" .elfmachine" 0 65535 elf-num 0= if drop exit then { v }
  v d-machine dset
  na nu strip-st d-name-a dstr
  elf-mach-cli @ 0= elf-machine @ v <> and if v elf-machine ! elf-gen+ then ;
: de-class ( row -- ) decl-fields 2drop strip-st
  2dup s" 32" str=cs if 2drop 1 d-class dset exit then
  2dup s" 64" str=cs if 2drop 2 d-class dset exit then
  mb-reset s"  error - .elfclass: value must be 32 or 64, got '" mb+ mb+ s" '." mb+ mb-get diag-e ;
: de-rela ( row -- ) decl-fields 2drop strip-st slower
  2dup s" 1" str=cs >r 2dup s" rela" str=cs r> or if 2drop 1 d-rela dset exit then
  2dup s" 0" str=cs >r 2dup s" rel" str=cs r> or if 2drop 0 d-rela dset exit then
  mb-reset s"  error - .elfrela: value must be 1/rela or 0/rel, got '" mb+ mb+ s" '." mb+ mb-get diag-e ;
: de-width ( row -- ) { r }
  r decl-fields { wa wu ta tu }
  wa wu s" .elfwidth" 1 8 elf-num 0= if drop exit then { w }
  ta tu strip-st { ta2 tu2 }
  tu2 0= if s"  error - .elfwidth: relocation type is not specified." diag-e exit then
  w n>s d-width om-find ?dup if
    dup dstr@ ta2 tu2 str=cs if drop exit then
    ta2 tu2 rot dstr exit
  then
  w n>s d-width om-put { sl } 0 sl ! 0 sl cell+ !
  ta2 tu2 sl dstr ;
: de-extern ( row -- ) decl-fields 2drop strip-st
  dup 0= if 2drop s"  error - .elfextern: relocation type is not specified." diag-e exit then
  d-extern-a dstr ;
: de-dwarf ( row -- ) decl-fields 2drop strip-st
  dup 0= if 2drop s"  error - .elfdwarf: relocation type is not specified." diag-e exit then
  d-dwarf-a dstr ;

: hdr-range ( a u -- lo hi ok )
  2dup s" type" str=cs if 2drop 0 65535 true exit then
  2dup s" flags" str=cs if 2drop 0 4294967295 true exit then
  2dup s" version" str=cs if 2drop 0 4294967295 true exit then
  2dup s" entry" str=cs if 2drop 0 9223372036854775807 true exit then
  2dup s" osabi" str=cs if 2drop 0 255 true exit then
  s" abiversion" str=cs if 0 255 true exit then
  0 0 false ;
: de-header ( row -- ) { r }
  r decl-fields { fa fu va vu }
  fa fu strip-spaces2 slower { fl fln }
  fl fln hdr-range 0= if
    2drop mb-reset s"  error - .elfheader: unknown field '" mb+ fl fln mb+ s" ' (type, flags, version, entry, osabi, abiversion)." mb+ mb-get diag-e exit
  then
  { lo hi }
  va vu s" .elfheader" lo hi elf-num 0= if drop exit then { v }
  fl fln d-hdr om-find ?dup if @ v = else false then if exit then
  fl fln d-hdr om-put v swap !  elf-gen+ ;

: de-field ( row -- ) { r }
  r decl-fields { ta tu ma mu }
  ta tu strip-st { t tl }
  tl 0= if s"  error - .elffield: relocation type is not specified." diag-e exit then
  ma mu s" .elffield" 1 -1 elf-num 0= if drop exit then { m }
  0 { off }
  r 3 rf-nb? if s" .elffield" 0 255 elf-num 0= if drop exit then to off else 2drop then
  0 { sh }
  r 4 rf-nb? if s" .elffield" 0 63 elf-num 0= if drop exit then to sh else 2drop then
  0 { bias }
  r 5 rf-nb? if s" .elffield" -2147483647 2147483647 elf-num 0= if drop exit then to bias else 2drop then
  t tl d-field om-find ?dup if
    m off sh bias fld4= if exit then
  then
  t tl d-field om-put { sl }
  m sl !  off sl cell+ !  sh sl 2 cells + !  bias sl 3 cells + !  elf-gen+ ;

: de-01 ( row dname-a dname-u addr -- ) { r da du ad }
  r decl-fields 2drop strip-st
  2dup s" 0" str=cs if 2drop 0 ad dset exit then
  2dup s" 1" str=cs if 2drop 1 ad dset exit then
  mb-reset s"  error - " mb+ da du mb+ s" : value must be 0 or 1, got '" mb+ mb+ s" '." mb+ mb-get diag-e ;
: de-pcguess ( row -- ) s" .elfpcguess" d-pcguess de-01 ;
: de-relaxd ( row -- ) s" .elfrelax" d-relax de-01 ;
: de-builtin ( row -- ) s" .elfbuiltin" d-builtin de-01 ;

: de-list ( row dname-a dname-u om -- ) { r da du om }
  r decl-fields 2drop lstrip-st rstrip-st
  dup 0= if 2drop mb-reset s"  error - " mb+ da du mb+ s" : relocation type is not specified." mb+ mb-get diag-e exit then
  2dup om om-find if 2drop exit then
  om om-put drop elf-gen+ ;
: de-anchor ( row -- ) s" .elfanchor" d-anchor de-list ;
: de-resolve ( row -- ) s" .elfresolve" d-resolve de-list ;

: de-extra ( row -- ) { r }
  r 1 rf strip-st { ta tu }
  r 2 rf strip-st { ca cu }
  tu 0= cu 0= or if s"  error - .elfextra: two relocation types are required." diag-e exit then
  0 { sym }
  r 3 rf-nb? if s" .elfextra" 0 1 elf-num 0= if drop exit then to sym else 2drop then
  ta tu d-extra om-find ?dup if
    @ { co }
    ca cu co om-find ?dup if @ sym = if exit then then
    ca cu co om-put sym swap !  elf-gen+ exit
  then
  1 om-new { co }
  ca cu co om-put sym swap !
  ta tu d-extra om-put co swap !  elf-gen+ ;

: plain-num? ( a u -- f ) { a u }                   \ _PLAIN_NUM_RE: 10 進か 0x 16 進のみ
  u 0= if false exit then
  a u s" 0x" starts-ci? u 2 > and if
    u 2 ?do a i + c@ lc { c } c digc? c 97 >= c 102 <= and or 0= if false unloop exit then loop true exit
  then
  u 0 ?do a i + c@ digc? 0= if false unloop exit then loop true ;

: de-diff ( row -- ) { r }
  r 1 rf strip-st { f1a f1u }
  r 2 rf strip-st { aa au }
  r 3 rf strip-st { ba bu }
  f1u 0> if f1a f1u plain-num? 0= else false then if
    au 0= bu 0= or if s"  error - .elfdiff: an add type and a subtract type are required." diag-e exit then
    f1a f1u d-diff-t om-find ?dup if
      aa au ba bu dstr2= if exit then
    then
    f1a f1u d-diff-t om-put { sl }
    aa au sl dstr  ba bu sl 2 cells + dstr  elf-gen+ exit
  then
  f1a f1u s" .elfdiff" 1 8 elf-num 0= if drop exit then { w }
  au 0= bu 0= or if s"  error - .elfdiff: an add type and a subtract type are required." diag-e exit then
  w n>s d-diff om-find ?dup if
    aa au ba bu dstr2= if exit then
  then
  w n>s d-diff om-put { sl }
  0 sl ! 0 sl cell+ ! 0 sl 2 cells + ! 0 sl 3 cells + !
  aa au sl dstr  ba bu sl 2 cells + dstr  elf-gen+ ;

: de-unaligned ( row -- ) { r }
  r 1 rf strip-st { ta tu }  r 2 rf strip-st { ua uu }
  tu 0= uu 0= or if s"  error - .elfunaligned: a relocation type and its unaligned type are required." diag-e exit then
  ta tu d-unaligned om-find ?dup if dstr@ ua uu str=cs if exit then then
  ta tu d-unaligned om-put { sl }  0 sl ! 0 sl cell+ !
  ua uu sl dstr ;

: de-encode ( row -- ) { r }
  r 1 rf strip-st { ta tu }  r 2 rf strip-st { fa fu }
  tu 0= fu 0= or if s"  error - .elfencode: a relocation type and a function name are required." diag-e exit then
  ta tu d-encode om-find ?dup if dstr@ fa fu str=cs if exit then then
  ta tu d-encode om-put { sl }  0 sl ! 0 sl cell+ !
  fa fu sl dstr ;

: de-rinfo ( row -- ) decl-fields 2drop strip-st
  dup 0= if 2drop s"  error - .elfrinfo: a function name is required." diag-e exit then
  d-rinfo-a dstr ;

: de-unit ( row -- ) decl-fields 2drop strip-st slower
  2dup s" byte" str=cs if 2drop 1 d-unit dset exit then
  2dup s" word" str=cs if 2drop 2 d-unit dset exit then
  mb-reset s"  error - .elfunit: value must be byte or word, got '" mb+ mb+ s" '." mb+ mb-get diag-e ;

: de-link ( row -- ) { r }
  r 1 rf strip-st { na nu }  r 2 rf strip-st { la lu }  r 3 rf strip-st { ia iu }
  nu 0= if s"  error - .elflink: section name is not specified." diag-e exit then
  na nu slower { ka ku }
  ka ku d-link om-find ?dup if
    la lu ia iu dstr2= if exit then
  then
  ka ku d-link om-put { sl }
  0 sl ! 0 sl cell+ ! 0 sl 2 cells + ! 0 sl 3 cells + !
  la lu sl dstr  ia iu sl 2 cells + dstr  elf-gen+ ;

: de-cfi ( row -- ) { r }
  r 1 rf s" .elfcfi" 0 65535 elf-num 0= if drop exit then { ra }
  r 2 rf s" .elfcfi" 1 65535 elf-num 0= if drop exit then { ca }
  r 3 rf s" .elfcfi" -65535 65535 elf-num 0= if drop exit then { da }
  da 0= if s"  error - .elfcfi: the data alignment factor must not be 0." diag-e exit then
  0 { pad }
  r 4 rf-nb? if
    s" .elfcfi" 1 64 elf-num 0= if drop exit then to pad
    pad pad 1- and if
      mb-reset s"  error - .elfcfi: the padding alignment must be a power of two, got '" mb+ pad mb-n s" '." mb+ mb-get diag-e exit
    then
  else 2drop then
  d-cfi? @ d-cfi-ra @ ra = and d-cfi-ca @ ca = and d-cfi-da @ da = and d-cfi-pad @ pad = and if exit then
  true d-cfi? !  ra d-cfi-ra !  ca d-cfi-ca !  da d-cfi-da !  pad d-cfi-pad !  elf-gen+ ;

: de-cfiinit ( row -- ) decl-fields 2drop
  \ 空白を 1 つに畳む
  { a u }
  u 1+ ar-alloc { d } 0 { k } false { sp } false { st }
  u 0 ?do
    a i + c@ { c }
    c 32 = c 9 = or c 10 = or c 13 = or if sp 0= st and if true to sp then
    else
      sp if 32 d k + c! k 1+ to k false to sp then
      c d k + c! k 1+ to k true to st
    then
  loop
  d k { t tl }
  tl 0= if s"  error - .elfcfiinit: an instruction is required." diag-e exit then
  t tl d-cfiinit om-find if exit then
  t tl d-cfiinit om-put drop elf-gen+ ;

: de-cfireg ( row -- ) { r }
  r 1 rf strip-st slower { na nu }
  nu 0= if s"  error - .elfcfireg: a register name is required." diag-e exit then
  r 2 rf s" .elfcfireg" 0 65535 elf-num 0= if drop exit then { v }
  na nu d-cfireg om-find ?dup if @ v = if exit then then
  na nu d-cfireg om-put v swap !  elf-gen+ ;

: de-group ( row -- ) { r }
  r 1 rf strip-st { ga gu }  r 2 rf strip-st { sa su }
  gu 0= su 0= or if s"  error - .elfgroup: a group name and a signature symbol are required." diag-e exit then
  r 3 rf s" .elfgroup" 0 4294967295 elf-num 0= if drop exit then { fl }
  \ メンバー: カンマで割って各項を strip、空は除く。"," で再結合して持つ
  r 4 rf { ma mu }
  mu 1+ ar-alloc { mb } 0 { k }  0 { st }
  mu 1+ 0 ?do
    i mu = ma i + c@ 44 = or if
      ma st + i st - strip-st { xa xu }
      xu if
        k if 44 mb k + c! k 1+ to k then
        xa mb k + xu move  k xu + to k
      then
      i 1+ to st
    then
  loop
  k 0= if s"  error - .elfgroup: no member section is given." diag-e exit then
  ga gu slower s\" \x01" sconcat sa su sconcat { ka ku }
  ka ku d-group om-find ?dup if
    ga gu sa su fl mb k grp= if exit then
  then
  ka ku d-group om-put { sl }
  0 sl ! 0 sl cell+ ! 0 sl 2 cells + ! 0 sl 3 cells + !
  0 sl 5 cells + ! 0 sl 6 cells + !
  ga gu sl dstr  sa su sl 2 cells + dstr  fl sl 4 cells + !  mb k sl 5 cells + dstr
  elf-gen+ ;

: de-section ( row -- ) { r }
  r decl-fields { nma nmu fla flu }
  nma nmu strip-st { nm nml }
  nml 0= if s"  error - .elfsection: section name is not specified." diag-e exit then
  fla flu s" .elfsection" 0 4294967295 elf-num 0= if drop exit then { fl }
  -1 { ty }
  r 3 rf-nb? if s" .elfsection" 0 4294967295 elf-num 0= if drop exit then to ty else 2drop then
  -1 { al }
  r 4 rf-nb? if
    s" .elfsection" 0 1073741824 elf-num 0= if drop exit then to al
    al al 1- and if
      mb-reset s"  error - .elfsection: alignment must be 0 or a power of two, got '" mb+ al mb-n s" '." mb+ mb-get diag-e exit
    then
  else 2drop then
  -1 { es }
  r 5 rf-nb? if s" .elfsection" 0 4294967295 elf-num 0= if drop exit then to es else 2drop then
  nm nml slower { ka ku }
  ka ku d-sec om-find ?dup if
    fl ty al es sec4= if exit then
  then
  ka ku d-sec om-put { sl }
  fl sl !  ty sl cell+ !  al sl 2 cells + !  es sl 3 cells + !  elf-gen+ ;

: dir-elf-impl ( row mode -- ) { r mode }
  r 0 rf slower { ka ku }
  ka ku s" .elftype" str=cs if r de-type exit then
  ka ku s" .elfmachine" str=cs if r de-machine exit then
  ka ku s" .elfclass" str=cs if r de-class exit then
  ka ku s" .elfrela" str=cs if r de-rela exit then
  ka ku s" .elfwidth" str=cs if r de-width exit then
  ka ku s" .elfextern" str=cs if r de-extern exit then
  ka ku s" .elfdwarf" str=cs if r de-dwarf exit then
  ka ku s" .elfheader" str=cs if r de-header exit then
  ka ku s" .elfsection" str=cs if r de-section exit then
  ka ku s" .elffield" str=cs if r de-field exit then
  ka ku s" .elfpcguess" str=cs if r de-pcguess exit then
  ka ku s" .elfrelax" str=cs if r de-relaxd exit then
  ka ku s" .elfanchor" str=cs if r de-anchor exit then
  ka ku s" .elfresolve" str=cs if r de-resolve exit then
  ka ku s" .elfbuiltin" str=cs if r de-builtin exit then
  ka ku s" .elfextra" str=cs if r de-extra exit then
  ka ku s" .elfdiff" str=cs if r de-diff exit then
  ka ku s" .elfencode" str=cs if r de-encode exit then
  ka ku s" .elfrinfo" str=cs if r de-rinfo exit then
  ka ku s" .elfunit" str=cs if r de-unit exit then
  ka ku s" .elflink" str=cs if r de-link exit then
  ka ku s" .elfgroup" str=cs if r de-group exit then
  ka ku s" .elfcfi" str=cs if r de-cfi exit then
  ka ku s" .elfcfiinit" str=cs if r de-cfiinit exit then
  ka ku s" .elfcfireg" str=cs if r de-cfireg exit then
  ka ku s" .elfunaligned" str=cs if r de-unaligned exit then ;
bind dir-elf-impl dir-elf
