\ elf6.fs -- .reloc / .clrreloc、状態の写し、エラー条件の判定

decimal

3 lazy-om rcon-snap
: rcon-take ( -- ) rcon rcon-snap om-copy ;
: rcon-restore ( -- ) rcon-snap rcon om-copy ;
bind rcon-take snap-extra-take
bind rcon-restore snap-extra-restore
: lineclear-extra-nn10 rcon om-clear ; bind lineclear-extra-nn10 lineclear-extra
: dir-pat-clear-extra-nn11 ( a u -- ) rcon om-del ; bind dir-pat-clear-extra-nn11 dir-pat-clear-extra

: reloc-name-err ( ta tu -- ) { ta tu }                  \ 同じ (名前, 機種) では 1 回だけ
  ta tu slower s\" \x01" sconcat elf-machine @ n>s sconcat { ka ku }
  ka ku reloc-badname om-find if exit then
  ka ku reloc-badname om-put drop
  mb-reset s"  error - .reloc: unknown relocation type '" mb+ ta tu mb+ s" ' for " mb+ mt-name mb+ s" ." mb+ mb-get diag-e ;

: pairs-new ( n -- p ) 2* 1+ cells allocate throw { p } 0 p ! p ;

\ 第 5 欄 (追加の再配置) を読む。成功なら pairs 配列 (または 0) と true
create px-rt 8 cells allot  create px-off 8 cells allot
: reloc-pairs ( row -- p ok ) { r }
  r 4 rf { pa pu }
  pa pu nonblank? 0= if 0 true exit then
  0 { n }  0 { st }
  pu 1+ 0 ?do
    i pu = pa i + c@ 44 = or if
      pa st + i st - { ia iu }
      iu if
        ia iu 64 has-ch? 0= if
          mb-reset s"  error - .reloc: an extra relocation is written <type>@<offset> ('" mb+ ia iu lstrip-st rstrip-st mb+ s" ')." mb+ mb-get diag-e
          0 false unloop exit
        then
        \ 最後の '@' で割る
        iu { at } iu 0 ?do ia iu 1- i - + c@ 64 = if iu 1- i - to at leave then loop
        ia at lstrip-st rstrip-st slower { pn pnl }
        pn pnl reloc-named-t if
          { prt }
          prt 0<= if
            mb-reset s"  error - .reloc: unknown relocation type '" mb+ pn pnl mb+ s" ' for " mb+ mt-name mb+ s" ." mb+ mb-get diag-e
            0 false unloop exit
          then
          prt mt-field? if 2drop 2drop else
            mb-reset s"  error - .reloc: an extra relocation needs a type declared with .elffield ('" mb+ pn pnl mb+ s" ')." mb+ mb-get diag-e
            0 false unloop exit
          then
          ia at 1+ + iu at - 1- s" .reloc" 0 255 elf-num 0= if drop 0 false unloop exit then { po }
          n 8 >= if
            s"  error - .reloc: at most 8 extra relocations." diag-e 0 false unloop exit
          then
          prt n cells px-rt + !  po n cells px-off + !  n 1+ to n
        else
          mb-reset s"  error - .reloc: unknown relocation type '" mb+ pn pnl mb+ s" ' for " mb+ mt-name mb+ s" ." mb+ mb-get diag-e
          0 false unloop exit
        then
      then
      i 1+ to st
    then
  loop
  n 0= if 0 true exit then
  n pairs-new { p }  n p !
  n 0 ?do px-rt i cells + @ p i 2* 1+ cells + !  px-off i cells + @ p i 2* 2 + cells + ! loop
  p true ;

: dir-reloc-impl ( row -- ) { r }
  r 1 rf nonblank? 0= if s"  error - .reloc: variable name is not specified." diag-e exit then
  r 1 rf { va vu }  r 2 rf { ta tu }
  va vu dir-var 0= if
    mb-reset s"  error - .reloc: variable should be a lower case name ('" mb+ va vu mb+ s" ')." mb+ mb-get diag-e exit
  then
  { na nu }
  ta tu strip-st { tn tnl }
  tnl 0= if s"  error - .reloc: relocation type is not specified." diag-e exit then
  o-obj-u @ 0= if exit then
  tn tnl reloc-named-t 0= if tn tnl reloc-name-err exit then
  { rt }
  0 { fmask }
  r 3 rf nonblank? if
    rt mt-field? if 2drop 2drop else
      mb-reset s"  error - .reloc: a field mask needs a type declared with .elffield ('" mb+ ta tu mb+ s" ')." mb+ mb-get diag-e exit
    then
    r 3 rf s" .reloc" 1 -1 elf-num 0= if drop exit then to fmask
  then
  r reloc-pairs 0= if drop exit then { pp }
  na nu rcon om-put { sl }
  rt sl !  fmask sl cell+ !  pp sl 2 cells + ! ;
bind dir-reloc-impl dir-reloc

: dir-clrreloc-impl ( row -- ) { r }
  r 2 rf strip-st { va vu }
  vu 0= if r 1 rf strip-st to vu to va then
  vu if
    va vu dir-var if rcon om-del else
      mb-reset s"  error - .clrreloc: variable should be a lower case name ('" mb+ va vu mb+ s" ')." mb+ mb-get diag-e
    then
  else rcon om-clear then ;
bind dir-clrreloc-impl dir-clrreloc

\ ---- エラー条件の判定 (_cond_tests_relocated_var / _cond_tests_linked_label) ----
: cw-in? ( cond-a cond-u va vu -- f ) { ca cu va vu }
  vu 0= if false exit then
  cu vu - 1+ 0 max 0 ?do
    ca i + vu va vu str=cs if
      i 0> if ca i 1- + c@ corec? else false then 0=
      i vu + cu < if ca i vu + + c@ corec? else false then 0= and if true unloop exit then
    then
  loop false ;

: cond-reloc-var? ( a u -- f ) { a u }
  o-obj-u @ 0= if false exit then
  rcon om-used 0 ?do
    i rcon om-live? if
      i rcon om-val @ mt-field? if
        2drop 2drop
        a u i rcon om-key cw-in? if true unloop exit then
      then
    then
  loop false ;

\ _captext_has_linked_label
: captext-linked? ( a u -- f ) { a u }
  0 { i }
  begin i u < while
    a i + c@ { c }
    c 34 = c 39 = or if
      i 1+ { j }
      begin j u < if a j + c@ c <> else false then while
        a j + c@ 92 = j 1+ u < and if j 1+ to j then j 1+ to j
      repeat
      j 1+ to i
    else c 36 = if
      i 1+ u < if a i 1+ + c@ dup 36 = swap 46 = or else false then if i 2 + to i else i 1+ to i then
    else c 35 = c digc? or if
      i 1+ to i
      begin i u < if a i + c@ dup alnc? over 95 = or swap 46 = or else false then while i 1+ to i repeat
    else c lwc? if
      i { j }
      begin j u < if a j + c@ lwc? else false then while j 1+ to j repeat
      a i + j i - 511 min lab-find { sl }
      j to i
      sl 0<> if
        sl lab-equ? sl lab-rtype 0< and 0= if
          sl lab-imported? if true exit then
          sl lab-sec nip if sl lab-sec cur-section str=cs 0= if true exit then then
        then
      then
    else i 1+ to i
    then then then then
  repeat false ;

: cond-linked? ( a u -- f ) { a u }
  o-obj-u @ 0= if false exit then
  nvslots @ 0 ?do
    i vtext ?dup if
      captext-linked? if
        a u i vslot-name cw-in? if true unloop exit then
      then
    else drop then
  loop false ;

: cond-relocated-impl ( a u -- f ) 2dup cond-reloc-var? if 2drop true exit then cond-linked? ;
bind cond-relocated-impl cond-relocated?
