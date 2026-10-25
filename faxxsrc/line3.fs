\ line3.fs -- ソース 1 行の処理 (lineassemble / lineassemble0) とファイルの読み込み (fileassemble)

decimal

variable gen-debug
variable vliw-flag-dummy

defer vliw-process ( la lu idxs flag idx -- vflag )      \ `!!` で区切った VLIW パケット
: vliw-process-nn31 2drop 2drop drop false ; bind vliw-process-nn31 vliw-process
defer elf-line-begin ( -- )                              \ -o のパス 2 の追跡の起点
: elf-line-begin-nn32 ; bind elf-line-begin-nn32 elf-line-begin
defer elf-line-end ( -- )
: elf-line-end-nn33 ; bind elf-line-end-nn33 elf-line-end
defer elf-emit-relocs ( -- )                             \ 行の出力語に対するリロケーション
: elf-emit-relocs-nn34 ; bind elf-emit-relocs-nn34 elf-emit-relocs
defer elf-shift-refs ( n -- )                            \ 先頭に n 語足したときの参照位置の補正
: elf-shift-refs-nn35 drop ; bind elf-shift-refs-nn35 elf-shift-refs
defer line-map-add ( -- )                                \ -g の行表
: line-map-add-nn36 ; bind line-map-add-nn36 line-map-add
defer macro-expand ( tab n fa fu -- tab' n' )
: macro-expand-nn37 2drop ; bind macro-expand-nn37 macro-expand
defer macro-reset-pass ( -- )
: macro-reset-pass-nn38 ; bind macro-reset-pass-nn38 macro-reset-pass

: nsym-reset ( -- ) nsym-dirty @ if patsyms numsyms om-copy false nsym-dirty ! then ;

: vliw-parts ( a u -- n ) { a u } 0 false { n inpart }
  u 0 ?do
    a i + c@ vliw-sep? if false to inpart else
      inpart 0= if n 1+ to n true to inpart then
    then
  loop n ;

: empty-slot-msg ( -- a u ) s"  error - VLIW: empty slot in the packet (nothing before or after a '!!')." ;
: no-vliw-msg ( -- a u ) s"  error - '!!' separates VLIW slots, but the pattern file has no .vliw." ;

: lead-ws ( a u -- n ) { a u } 0 { k }
  begin k u < if a k + c@ dup 32 = swap 9 = or else false then while k 1+ to k repeat k ;

: lstrip-tab ( a u -- a' u' ) begin dup 0> if over c@ dup 32 = swap 9 = or else false then while 1 /string repeat ;

: lstrip-sp ( a u -- a' u' ) begin dup 0> if over c@ 32 = else false then while 1 /string repeat ;
: first-vliw? ( a u -- f ) lstrip-tab dup 0> if drop c@ vliw-sep? else 2drop false then ;

: textmode-label? ( -- f )
  textmode @ 0= if false exit then
  label-text sb-len 0= if false exit then
  vliw-flag @ if false exit then
  asmtext-set @ nobj @ 0= or ;
: textmode-comment? ( -- f )
  textmode @ 0= if false exit then
  comment-text sb-len 0= if false exit then
  vliw-flag @ if false exit then
  asmtext-set @ nobj @ 0= or ;

: add-label-text ( -- )
  label-text sb$ sdup { la lu }
  asmtext sb$ sdup { ta tu }
  asmtext-set @ 0= if 0 to tu then
  tu 0> if la lu s"  " sconcat to lu to la then
  la lu obj-prepend
  la lu ta tu sconcat asm-text!
  lu elf-shift-refs ;
: add-comment-text ( -- )
  comment-text sb$ sdup { ca cu }
  asmtext-set @ if asmtext sb$ sdup else 0 0 then { ta tu }
  tu 0> if s"  " ca cu sconcat else ca cu then { sa su }
  sa su text-words
  ta tu sa su sconcat asm-text! ;
: add-indent-text ( -- )
  indent-text sb$ sdup { ia iu }
  ia iu obj-prepend
  ia iu asmtext sb$ sconcat asm-text!
  iu elf-shift-refs ;


: emit-words ( -- ) nobj @ 0 ?do pc @ i + i obj-q outbin loop nobj @ pc +! ;

: lineassemble ( a u -- flag ) { a u }
  a u lead-ws { ik }
  indent-text sb-clear
  textmode @ if a ik 511 min indent-text sb+ then
  a u normalize-ws split-comment { ca cu ma mu }
  comment-text sb-clear
  textmode @ if ma mu comment-text sb+ then
  cu 0= comment-text sb-len 0= and if false exit then
  ca cu resolve-vliw-escapes { la lu }
  \ 行ごとの表の初期化
  chk-clear-all  enumdefs om-clear  freed-subs om-clear
  lineclear-extra
  nsym-reset
  label-text sb-clear
  la lu label-proc to lu to la
  la lu vliw-parts vliw-cnt !
  elf-line-begin
  la lu 0 lineassemble2 { idxs flag idx }
  elf-line-end
  flag 0= if
    la lu first-vliw? report? and if empty-slot-msg diag-e then
    false exit
  then
  textmode-label? if add-label-text then
  textmode-comment? if add-comment-text then
  textmode @ indent-text sb-len 0<> and vliw-flag @ 0= and asmtext-set @ and asmtext sb-len 0<> and
  if add-indent-text then
  eol-on @ nobj @ 0<> and vliw-flag @ 0= and if 10 obj-byte then
  \ `.vliw` の無いパターンで `!!` が続く行は、後ろを捨てずにエラーにする
  idx lu < if
    la idx + lu idx - lstrip-sp first-vliw? vliw-flag @ 0= and if
      report? if no-vliw-msg diag-e then
      false exit
    then
  then
  vliw-flag @ 0= if true else idx lu >= if true else la idx + c@ vliw-sep? 0= then then
  if
    nobj @ { of }
    elf-emit-relocs
    gen-debug @ pass @ 2 = and of 0> and if line-map-add then
    emit-words
    true
  else
    la lu idxs flag idx vliw-process
  then ;

: lineassemble0 ( a u -- flag ) { a u }
  seen-reset  ar-mark { amk }
  a u { ra ru } 0 { k }
  ru 1+ ar-alloc { cl } 0 to k
  ru 0 ?do ra i + c@ dup 10 <> over 13 <> and if cl k + c! k 1+ to k else drop then loop
  cl k { ca cu }
  pass @ 2 = verbose @ and pass @ 0= or { show }
  show if
    listing-open @ if cr then
    pc @ 16 hexw  32 emit
    file@ type 32 emit line-no @ 0 .r 32 emit ca cu type s"  //" type
    true listing-open !
  then
  asmtext-clear
  ca cu lineassemble { f }
  asmtext-set @ pass @ 2 = pass @ 0= or and if
    show if 32 emit asmdisp sb$ type
    else text-output @ if asmtext sb$ type cr then then
  then
  asmtext-clear
  show listing-open @ and if cr then
  show if false listing-open ! then
  1 line-no +!
  amk ar-release
  f ;

\ ---- ファイルの読み込み ----
variable fn-depth
create fn-stack-a 128 cells allot   create fn-stack-u 128 cells allot
create ln-stack 128 cells allot
create cwdbuf 4096 allot
lazy-sb ap-b
: abspath ( a u -- a' u' ) { a u }
  u 0= if a u exit then
  a u s" stdin" str=cs if a u exit then
  ap-b sb-clear
  a c@ 47 <> if cwdbuf 4096 get-dir ap-b sb+  s" /" ap-b sb+ then
  a u ap-b sb+
  \ . と .. と // を畳む
  ap-b sb$ { pa pu }
  pu 2 + ar-alloc { out } 0 { o } 0 { k }
  begin k pu < while
    k { st }
    begin k pu < if pa k + c@ 47 <> else false then while k 1+ to k repeat
    pa st + k st - { sa su }
    su 0= su 1 = sa c@ 46 = and or if
    else su 2 = sa c@ 46 = and sa 1+ c@ 46 = and if
      begin o 0> if out o 1- + c@ 47 <> else false then while o 1- to o repeat
      o 0> if o 1- to o then
      begin o 0> if out o 1- + c@ 47 <> else false then while o 1- to o repeat
      o 0> if o 1- to o then
    else
      47 out o + c! o 1+ to o
      sa out o + su move  o su + to o
    then then
    k 1+ to k
  repeat
  o 0= if 47 out c! 1 to o then
  out o ;

: fn-depth-max 100 ;

: slurp-stdin ( -- a u ) 0 0 { buf n }
  4096 allocate throw to buf
  begin buf n + 4096 stdin-read throw dup 0> while
    n + to n
    buf n 4096 + resize throw to buf
  repeat drop
  buf n ;

variable stdin-cache-a  variable stdin-cache-u  variable stdin-cached

defer asm-file-hook ( -- )
: asm-file-hook-nn39 ; bind asm-file-hook-nn39 asm-file-hook

: read-source ( fa fu -- tab n ok ) { fa fu }
  fa fu s" stdin" str=cs if
    stdin-cached @ 0= if slurp-stdin stdin-cache-u ! stdin-cache-a ! true stdin-cached ! then
    stdin-cache-a @ stdin-cache-u @
  else
    fa fu file-status nip if
      mb-reset s"  error - cannot open source file '" mb+ fa fu mb+ s" ': [Errno 2] No such file or directory: '" mb+ fa fu mb+ s" '" mb+ mb-get diag-e
      0 0 false exit
    then
    fa fu slurp-file
  then
  { da du }
  da du fa fu text-lines true ;

: fileassemble ( a u -- ) { fa fu }
  fn-depth @ 0= if macro-reset-pass then
  fn-depth @ fn-depth-max >= if
    mb-reset s"  error - .INCLUDE nesting depth exceeds 100: '" mb+ fa fu mb+ s" '" mb+ mb-get diag-e exit
  then
  fa fu abspath { aa au }
  fn-depth @ 0 ?do
    i cells fn-stack-a + @ i cells fn-stack-u + @ abspath aa au str=cs if
      mb-reset s"  error - circular .INCLUDE detected: '" mb+ fa fu mb+ s" ' is already being assembled." mb+ mb-get diag-e
      unloop exit
    then
  loop
  file@ { cfa cfu }  line-no @ { cln }
  fa fu hdup fn-depth @ cells fn-stack-u + ! fn-depth @ cells fn-stack-a + !
  1 fn-depth +!
  fa fu read-source if
    { tab n }
    fa fu file!  1 line-no !
    tab n fa fu macro-expand { t2 n2 }
    n2 1+ cells allocate throw { pcs }
    fa fu mline-pcs-cur om-put { psl }  pcs psl !  n2 psl cell+ !
    n2 0 ?do
      pc @ pcs i cells + !
      t2 i tl-file file!
      t2 i tl-ln line-no !
      t2 i tl@ lineassemble0 drop
    loop
  else 2drop then
  -1 fn-depth +!
  cfa cfu file!  cln line-no ! ;

\ ---- .include ----
: dirname-len ( a u -- n ) begin dup 0> while 2dup + 1- c@ 47 = if nip exit then 1- repeat nip ;
: do-asm-include ( l2a l2u -- ) { l2a l2u }
  l2a l2u get-string { sa su }
  su 0= if
    l2a l2u trim { ra ru }
    ru 0> if
      ra ru 0 p-spc drop { fa fu }
      fu 0> if
        mb-reset s"  warning - .INCLUDE filename not quoted: " mb+ fa fu repr1 mb+ s" . Please use double quotes." mb+ mb-get diag-w
        fa fu to su to sa
      else
        mb-reset s"  error - .INCLUDE directive has no filename: " mb+ l2a l2u repr1 mb+ mb-get diag-e exit
      then
    else
      mb-reset s"  error - .INCLUDE directive has no filename: " mb+ l2a l2u repr1 mb+ mb-get diag-e exit
    then
  then
  sa su s" stdin" str=cs 0= sa c@ 47 <> and if
    file@ { cfa cfu }
    cfu 0<> if cfa cfu s" (stdin)" str=cs 0= else false then if
      cfa cfu abspath dirname-len { dl }
      cfa cfu abspath drop dl sa su sconcat to su to sa
    then
  then
  sa su fileassemble ;
bind do-asm-include asm-include
