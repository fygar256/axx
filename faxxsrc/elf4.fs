\ elf4.fs -- .elf* 宣言の登録と検査、--elfdesc、ミニ言語の関数呼び出し

decimal

\ ---- ミニ言語の関数 (.elfencode / .elfrinfo) ----
\ 数を返せば ( n true )、だめなら診断して false
: elf-call-func ( dname-a du fname-a fu q1 q2 -- n true | false ) { da du fa fu q1 q2 }
  fa fu mfuncs om-find ?dup 0= if false exit then
  @ { fn }
  0 mia-top !
  2 cells mi-alloc { args }
  q1 mi-int args !  q2 mi-int args cell+ !
  fn args 2 ['] mini-run catch dup X-MINI = if
    drop mb-reset s"  error - " mb+ da du mb+ s" : " mb+ merr-buf merr-u @ mb+ mb-get diag-e false exit
  then
  throw
  { ret }
  ret 0= if
    mb-reset s"  error - " mb+ da du mb+ s" : function '" mb+ fa fu mb+ s" ' must return a number." mb+ mb-get diag-e false exit
  then
  ret v-arr? ret v-str? or if
    mb-reset s"  error - " mb+ da du mb+ s" : function '" mb+ fa fu mb+ s" ' must return a number." mb+ mb-get diag-e false exit
  then
  ret v-q q>n true ;

\ ---- 検査 (check_elfdecls) ----
: warn-ut ( t-a t-u dname-a du -- )
  mb-reset s"  warning - " mb+ mb+ s" : unknown relocation type '" mb+ mb+ s" ' for " mb+ mt-name mb+ s" ; ignored." mb+ mb-get diag-w ;
: chk-type ( t-a t-u dname-a du -- ) { ta tu da du }
  ta tu decl-type if drop else ta tu da du warn-ut then ;
: chk-fn ( dname-a du fname-a fu -- ) { da du fa fu }
  fa fu mfuncs om-find ?dup if
    @ mf-np 2 <> if
      mb-reset s"  error - " mb+ da du mb+ s" : function '" mb+ fa fu mb+ s" ' must take 2 arguments." mb+ mb-get diag-e
    then
  else
    mb-reset s"  error - " mb+ da du mb+ s" : no function named '" mb+ fa fu mb+ s" '." mb+ mb-get diag-e
  then ;

: check-elfdecls ( -- )
  o-obj-u @ 0= if exit then
  mach-table
  d-width sort-om-num { wa wn }
  wn 0 ?do wa i cells + @ d-width om-val dstr@ s" .elfwidth" chk-type loop
  wa free throw
  d-extern-u @ if d-extern-a @ d-extern-u @ s" .elfextern" chk-type then
  d-dwarf-u @ if d-dwarf-a @ d-dwarf-u @ s" .elfdwarf" chk-type then
  d-field om-used 0 ?do i d-field om-live? if i d-field om-key s" .elffield" chk-type then loop
  d-extra om-used 0 ?do
    i d-extra om-live? if
      i d-extra om-key s" .elfextra" chk-type
      i d-extra om-val @ { co }
      co om-used 0 ?do i co om-live? if i co om-key s" .elfextra" chk-type then loop
    then
  loop
  d-diff sort-om-num { da dn }
  dn 0 ?do
    da i cells + @ d-diff om-val { sl }
    sl dstr@ s" .elfdiff" chk-type  sl 2 cells + dstr@ s" .elfdiff" chk-type
  loop
  da free throw
  d-diff-t om-used 0 ?do
    i d-diff-t om-live? if
      i d-diff-t om-key s" .elfdiff" chk-type
      i d-diff-t om-val { sl }
      sl dstr@ s" .elfdiff" chk-type  sl 2 cells + dstr@ s" .elfdiff" chk-type
    then
  loop
  d-unaligned om-used 0 ?do
    i d-unaligned om-live? if
      i d-unaligned om-key s" .elfunaligned" chk-type
      i d-unaligned om-val dstr@ s" .elfunaligned" chk-type
    then
  loop
  d-encode om-used 0 ?do
    i d-encode om-live? if i d-encode om-key s" .elfencode" chk-type then
  loop
  d-encode om-used 0 ?do
    i d-encode om-live? if s" .elfencode" i d-encode om-val dstr@ chk-fn then
  loop
  d-rinfo-u @ if s" .elfrinfo" d-rinfo-a @ d-rinfo-u @ chk-fn then ;

: register-elfdecls-impl ( -- )
  nrows @ 0 ?do
    i rkind @ 30 = if i 0 dir-elf then
  loop
  check-elfdecls ;
bind register-elfdecls-impl register-elfdecls

\ ---- --elfdesc ----
: hexs ( u -- a u ) base @ >r hex 0 <# #s #> r> base ! 2dup slower 2swap 2drop ;
: ou ( a u -- ) type ;
: tname ( rt -- a u ) { rt }
  rt mt-rev@ { na nu }
  nu if na nu slower reloc-named-t if rt = else false then else false then
  if na nu else rt n>s then ;
: dnl ( -- ) 10 emit ;
: desc-types ( -- )
  mt-named om-used 0 ?do
    i mt-named om-live? if
      i mt-named om-key { na nu }
      i mt-named om-val @ { rt }
      rt mt-bytes@ 0 max { w }
      rt mt-pc? { pc }
      s" .elftype::" ou na nu ou s" ::" ou rt n>s ou
      w 0<> pc or if s" ::" ou w if w n>s ou then then
      pc if s" ::1" ou then
      dnl
    then
  loop ;
: desc-main ( -- )
  s" .elfbuiltin::0" ou dnl
  mt-name { na nu }
  na nu mb-reset s" machine " mb+ elf-machine @ mb-n mb-get str=cs 0= nu 0<> and if
    s" .elfmachine::" ou elf-machine @ n>s ou s" ::" ou na nu ou
  else s" .elfmachine::" ou elf-machine @ n>s ou then dnl
  s" .elfclass::" ou mt-class@ 2 = if s" 64" else s" 32" then ou dnl
  s" .elfrela::" ou mt-rela? if s" 1" else s" 0" then ou dnl
  desc-types
  9 1 ?do i mt-wg@ ?dup if s" .elfwidth::" ou i n>s ou s" ::" ou tname ou dnl then loop
  s" .elfextern::" ou mt-extern tname ou dnl
  s" .elfdwarf::" ou mt-dwarf@ tname ou dnl
  s" .elfpcguess::" ou mt-pcg? if s" 1" else s" 0" then ou dnl
  d-relax @ 0>= if s" .elfrelax::" ou d-relax @ n>s ou dnl then
  d-anchor om-used 0 ?do i d-anchor om-live? if s" .elfanchor::" ou i d-anchor om-key ou dnl then loop
  d-resolve om-used 0 ?do i d-resolve om-live? if s" .elfresolve::" ou i d-resolve om-key ou dnl then loop ;
: desc-unal ( -- )
  mt-unal sort-om-num { ar n }
  n 0 ?do
    ar i cells + @ { ix }
    ix mt-unal om-key parse-int0 drop { rt }
    s" .elfunaligned::" ou rt tname ou s" ::" ou ix mt-unal om-val @ tname ou dnl
  loop ar free throw ;
: desc-diff ( -- )
  mt-diff sort-om-num { ar n }
  n 0 ?do
    ar i cells + @ { ix }
    s" .elfdiff::" ou ix mt-diff om-key ou s" ::" ou ix mt-diff om-val @ tname ou s" ::" ou ix mt-diff om-val cell+ @ tname ou dnl
  loop ar free throw
  mt-diff-t sort-om-num to n to ar
  n 0 ?do
    ar i cells + @ { ix }
    s" .elfdiff::" ou ix mt-diff-t om-key parse-int0 drop tname ou s" ::" ou
    ix mt-diff-t om-val @ tname ou s" ::" ou ix mt-diff-t om-val cell+ @ tname ou dnl
  loop ar free throw ;
: desc-extra ( -- )
  mt-extra sort-om-num { ar n }
  n 0 ?do
    ar i cells + @ { ix }
    ix mt-extra om-key parse-int0 drop { rt }
    ix mt-extra om-val @ { l }
    l ml-n 0 ?do
      s" .elfextra::" ou rt tname ou s" ::" ou l i ml-crt tname ou s" ::" ou l i ml-sym n>s ou dnl
    loop
  loop ar free throw ;
: desc-encode ( -- )
  mt-encode sort-om-num { ar n }
  n 0 ?do
    ar i cells + @ { ix }
    s" .elfencode::" ou ix mt-encode om-key parse-int0 drop tname ou s" ::" ou ix mt-encode om-val dstr@ ou dnl
  loop ar free throw ;
: desc-cfi ( -- )
  d-cfi? @ if
    s" .elfcfi::" ou d-cfi-ra @ n>s ou s" ::" ou d-cfi-ca @ n>s ou s" ::" ou d-cfi-da @ n>s ou
    d-cfi-pad @ if s" ::" ou d-cfi-pad @ n>s ou then dnl
  then
  d-cfiinit om-used 0 ?do i d-cfiinit om-live? if s" .elfcfiinit::" ou i d-cfiinit om-key ou dnl then loop
  d-cfireg sort-om { ar n }
  n 0 ?do
    ar i cells + @ { ix }
    s" .elfcfireg::" ou ix d-cfireg om-key ou s" ::" ou ix d-cfireg om-val @ n>s ou dnl
  loop ar free throw ;
: desc-fields ( -- )
  mt-field sort-om-num { ar n }
  n 0 ?do
    ar i cells + @ { ix }
    ix mt-field om-val { sl }
    s" .elffield::" ou ix mt-field om-key parse-int0 drop tname ou s" ::0x" ou sl @ hexs ou
    s" ::" ou sl cell+ @ n>s ou s" ::" ou sl 2 cells + @ n>s ou s" ::" ou sl 3 cells + @ n>s ou dnl
  loop ar free throw ;
: desc-hdr ( -- )
  s" type" d-hdr om-find ?dup if s" .elfheader::type::0x" ou @ hexs ou dnl then
  s" flags" d-hdr om-find ?dup if s" .elfheader::flags::0x" ou @ hexs ou dnl then
  s" version" d-hdr om-find ?dup if s" .elfheader::version::0x" ou @ hexs ou dnl then
  s" entry" d-hdr om-find ?dup if s" .elfheader::entry::0x" ou @ hexs ou dnl then
  s" osabi" d-hdr om-find ?dup if s" .elfheader::osabi::0x" ou @ hexs ou dnl then
  s" abiversion" d-hdr om-find ?dup if s" .elfheader::abiversion::0x" ou @ hexs ou dnl then ;
: desc-sec ( -- )
  d-sec sort-om { ar n }
  n 0 ?do
    ar i cells + @ { ix }
    ix d-sec om-val { sl }
    s" .elfsection::" ou ix d-sec om-key ou s" ::0x" ou sl @ hexs ou
    3 { last }
    3 0 ?do sl i 1+ cells + @ 0>= if i to last then loop
    \ 末尾の None は書かない
    -1 to last
    3 0 ?do sl i 1+ cells + @ 0>= if i to last then loop
    last 1+ 0 ?do
      s" ::" ou sl i 1+ cells + @ dup 0>= if n>s ou else drop then
    loop
    dnl
  loop ar free throw ;
: desc-link ( -- )
  d-link sort-om { ar n }
  n 0 ?do
    ar i cells + @ { ix }
    ix d-link om-val { sl }
    s" .elflink::" ou ix d-link om-key ou s" ::" ou sl dstr@ ou
    sl 2 cells + dstr@ dup if s" ::" ou ou else 2drop then dnl
  loop ar free throw ;
: desc-group ( -- )
  d-group om-used 0 ?do
    i d-group om-live? if
      i d-group om-val { sl }
      s" .elfgroup::" ou sl dstr@ ou s" ::" ou sl 2 cells + dstr@ ou s" ::0x" ou sl 4 cells + @ hexs ou
      s" ::" ou sl 5 cells + dstr@ ou dnl
    then
  loop ;
: elf-desc-impl ( -- )
  mach-table
  desc-main
  desc-unal
  s" .elfunit::" ou mt-word-unit? if s" word" else s" byte" then ou dnl
  desc-diff desc-extra desc-encode
  mt-rinfo-u @ if s" .elfrinfo::" ou mt-rinfo-a @ mt-rinfo-u @ ou dnl then
  desc-cfi desc-fields desc-hdr desc-sec desc-link desc-group ;
bind elf-desc-impl elf-desc-out

\ ---- オプション (-m -f --osabi) ----
: elf-options-impl ( -- ok )
  o-fmt @ 64 = if 2 elf-class-cli ! else o-fmt @ 32 = if 1 elf-class-cli ! then then
  o-osabi-a @ o-osabi-u @ slower s" freebsd" str=cs if 9 else 0 then elf-osabi-v !
  o-machine? @ 0= if true exit then
  o-machine @ 0 65535 within 0= if
    mb-reset s"  error - -m/--machine value " mb+ o-machine @ mb-n
    s"  is out of range (an ELF e_machine number is 0..65535)." mb+ mb-get diag-wf false exit
  then
  o-machine @ elf-machine !  true elf-mach-cli !
  o-machine @ base-known? 0= o-obj-u @ 0<> and if
    known-sb sb-clear base-list
    mb-reset s"  warning - -m/--machine value " mb+ o-machine @ mb-n
    s"  is not one of the machines axx has built-in relocation numbering for (" mb+ known-sb sb$ mb+
    s" ); relocation types must come from the pattern file (.elftype / .elfwidth / .elfextern). References whose type is not declared get no relocation entry, rather than a guessed (and wrong) one." mb+
    mb-get diag-wf
  then
  true ;
bind elf-options-impl apply-elf-options
