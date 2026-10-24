\ macro4.fs -- マクロ層: !include、展開の入口、フック、-P / -p

decimal

\ ---- !include ----
: inc-find ( a u -- f ) { a u }
  mp.incn mp@ 0 ?do
    mp.inca mp@ i 2 * cells + s@ a u str=cs if true unloop exit then
  loop false ;

: m-do-include-impl ( v fa fu ln -- ) { v fa fu ln }
  v mv-str? 0= if fa fu ln mfail-pos s" '!include' needs a file name string" mb+ mfail then
  v mv-s { na nu }
  fa fu dir-len { dl }
  na c@ 47 <> dl 0> and if fa dl na nu sconcat else na nu then { pa pu }
  pa pu abspath sdup { ra ru }
  ra ru inc-find if fa fu ln mfail-pos s" circular '!include' of " mb+ na nu repr1 mb+ mfail then
  mp.incn mp@ MACRO-MAX-INC >= if fa fu ln mfail-pos s" '!include' nested deeper than 64" mb+ mfail then
  pa pu file-status nip if
    fa fu ln mfail-pos s" cannot '!include' " mb+ na nu repr1 mb+ s" : [Errno 2] No such file or directory: " mb+ pa pu repr1 mb+ mfail
  then
  pa pu hdup load-lines { tab n }
  pl-tab @ pl-n @ { stab sn }
  tab pl-tab ! n pl-n !
  ra ru hdup mp.inca mp@ mp.incn mp@ 2 * cells + s!  mp.incn mp@ 1+ mp.incn mp!
  0 0 parse-block drop exec-block
  mp.incn mp@ 1- mp.incn mp!
  stab pl-tab ! sn pl-n ! ;
' m-do-include-impl is m-do-include

\ ---- 展開の前判定 ----
: has-interp? ( a u -- f ) { a u }
  0 { i }
  begin i 1+ u < while
    a i + 2 s" !{" str=cs if
      i 0= if true unloop exit then
      a i 1- + c@ 92 <> if true exit then
      i 2 + to i
    else i 1+ to i then
  repeat false ;
: contains-macros? ( tab n -- f ) { tab n }
  n 0 ?do
    tab i tl@ { a u }
    a u 33 has-ch? if true unloop exit then
    a u lstrip-st dup 0> if drop c@ 125 = else 2drop false then if true unloop exit then
  loop false ;
: macro-constructs? ( tab n -- f ) { tab n }
  n 0 ?do
    tab i tl@ { a u }
    a u lstrip-st dup 0> if drop c@ 125 = else 2drop false then if true unloop exit then
    a u has-interp? if true unloop exit then
    a u lstrip-st statement-word if
      { wa wu ra ru }
      wa wu kw? wa wu func-find 0<> or wa wu declared? or ra ru looks-like-call? or if true unloop exit then
    then
  loop false ;

\ ---- 展開 ----
: mp-state-reset ( -- )
  1 mp.scopen mp!  0 mp.depth mp!  0 ctl!  0 x-sup !  0 bt-top !  0 mp.exprd mp! ;

: mfail-pos-1 ( a u -- ) mb-reset mb+ s" : " mb+ ;

: expand-body ( tab n -- ) pl-n ! pl-tab !
  0 0 parse-block drop exec-block
  ctl@ 3 = if
    0 ctl! mp.keya mp@ mp.keyu mp@ mfail-pos-1 s" '!return' outside a macro definition" mb+ mfail
  then
  ctl@ 0<> if
    0 ctl! mp.keya mp@ mp.keyu mp@ mfail-pos-1 s" '!break'/'!continue' outside a '!while' loop" mb+ mfail
  then ;

: mac-expand ( tab n fa fu -- tab' n' ) { tab n fa fu }
  mp.enabled mp@ 0= if tab n exit then
  mp-pat? if tab n macro-constructs? else tab n contains-macros? then 0= if tab n exit then
  mp.hadErr mp@ if tab 0 exit then
  mp.out mp@ mp.outn mp@ mp.outcap mp@ mp.keya mp@ mp.keyu mp@ { so son soc ska sku }
  fa mp.keya mp! fu mp.keyu mp!
  0 mp.outn mp!  0 mp.outcap mp!  0 mp.out mp!
  tab n ['] expand-body catch { rc }
  rc X-MERR = if
    merr-buf merr-u @ m-fail-report
    mp-state-reset
    0 mp.outn mp!
  else rc if rc throw then then
  mp.out mp@ mp.outn mp@ { rt rn }
  so mp.out mp!  son mp.outn mp!  soc mp.outcap mp!  ska mp.keya mp!  sku mp.keyu mp!
  rt rn ;


\ ---- ソース側・パターン側のフック ----
: src-mexpand ( tab n fa fu -- tab' n' ) mp-src mp !  mac-expand ;
' src-mexpand is macro-expand
: src-mreset ( -- ) mp-src mp !  mm-reset  reset-pass-mp ;
' src-mreset is macro-reset-pass
: pat-mexpand ( tab n fa fu -- tab' n' ) mp-pat mp !  mac-expand ;
' pat-mexpand is pat-macro-expand
: pat-mreset ( -- ) mp-pat mp !  mm-reset  reset-pass-mp ;
' pat-mreset is pat-macro-reset

\ ---- -P / -p ----
: mx-out ( tab n da du -- ok ) { tab n da du }
  da du s" -" str=cs da du nip 0= or { to-stdout }
  to-stdout if
    n 0 ?do tab i tl@ type 10 emit loop true
  else
    da du w/o create-file if
      drop mb-reset s"  error - cannot write '" mb+ da du mb+ s" ': [Errno 2] No such file or directory: '" mb+ da du mb+ s" '" mb+ mb-get diag-wf false exit
    then
    { fid }
    n 0 ?do tab i tl@ fid write-file throw s\" \n" fid write-file throw loop
    fid close-file throw true
  then ;
: macro-expand-only-impl ( fa fu da du pat? -- ok ) { fa fu da du pat }
  pat if mp-pat else mp-src then mp !
  mm-reset reset-pass-mp
  fa fu file-status nip if
    mb-reset s"  error - cannot open " mb+ pat if s" pattern" else s" source" then mb+ s"  file '" mb+ fa fu mb+
    s" ': [Errno 2] No such file or directory: '" mb+ fa fu mb+ s" '" mb+ mb-get diag-wf false exit
  then
  fa fu load-lines { tab n }
  tab n fa fu mac-expand { t2 n2 }
  mp.hadErr mp@ had-error @ or if false exit then
  t2 n2 da du mx-out ;
' macro-expand-only-impl is macro-expand-only
