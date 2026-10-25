\ echo1.fs -- パターン本文の .echo (axx.py の echo_processing / _echo_items_parse)

decimal

variable echo-ma  variable echo-mu
: echo-bad ( a u -- ) sdup echo-mu ! echo-ma ! -4712 throw ;
: ec ( a i -- c ) + c@ ;
: ews? ( c -- f ) dup 32 = swap 9 = or ;
: ws-lskip ( a u -- a' u' ) begin dup 0> if over c@ ews? else false then while 1 /string repeat ;
: ws-rtrim ( a u -- a u' ) begin dup 0> if 2dup 1- + c@ ews? else false then while 1- repeat ;
: ws-trim ( a u -- a' u' ) ws-lskip ws-rtrim ;
: open-c? ( c -- f ) dup 40 = over 91 = or swap 123 = or ;
: close-c? ( c -- f ) dup 41 = over 93 = or swap 125 = or ;

\ 閉じ ')' の位置 (深さ 0 の)。文字列の中は読み飛ばす。無ければ -1
: echo-close ( a u -- idx ) { a u }
  0 0 false { i depth instr }
  begin i u < while
    instr if
      a i ec 92 = if i 2 + to i else
        a i ec 34 = if false to instr then i 1+ to i
      then
    else
      a i ec 34 = if true to instr
      else a i ec open-c? if depth 1+ to depth
      else a i ec close-c? if
        depth 0= a i ec 41 = and if i exit then
        depth 0> if depth 1- to depth then
      then then then
      i 1+ to i
    then
  repeat
  -1 ;

\ 項目の部分: [種類 0 文字列 / 1 式][a][u] の 3 セルずつ
variable ep-n  variable ep-arr
: ep-slot ( i -- addr ) 3 * cells ep-arr @ + ;
: unesc-bad ( c -- ) mb-reset s" unknown escape '\" mb+ mb-c s" ' in a string" mb+ mb-get echo-bad ;
: echo-unescape ( a u -- a' u' ) { a u }                \ 引用符の内側
  u 1+ ar-alloc { buf }  0 0 { n k }
  begin k u < while
    a k ec 92 = if
      k 1+ u >= if s" dangling '\' in a string" echo-bad then
      a k 1+ ec dup 92 = if drop 92 else dup 34 = if drop 34 else
        dup 110 = if drop 10 else dup 116 = if drop 9 else unesc-bad then then then then
      buf n + c!  n 1+ to n  k 2 + to k
    else
      a k ec buf n + c!  n 1+ to n  k 1+ to k
    then
  repeat
  buf n ;
: unq-bad ( a u msg-a msg-u -- ) mb-reset mb+ s" : '" mb+ mb+ s" '" mb+ mb-get echo-bad ;
: ep-add ( a u -- ) ws-trim { a u }
  u 0= if s" empty item in the argument list" echo-bad then
  ep-n @ ep-slot { sl }
  a c@ 34 = if
    1 { j }
    begin j u < if a j ec 34 <> else false then while
      a j ec 92 = if j 2 + to j else j 1+ to j then
    repeat
    j u >= if a u s" unterminated string" unq-bad then
    j u 1- <> if a u s" unexpected text after a string" unq-bad then
    a 1+ u 2 - echo-unescape { ua uu }
    0 sl !  ua sl cell+ !  uu sl 2 cells + !
  else
    1 sl !  a sl cell+ !  u sl 2 cells + !
  then
  1 ep-n +! ;
: echo-split ( ia e -- ) { ia e }
  0 0 false 0 { ps pk instr dp }
  begin pk e < while
    instr if
      ia pk ec 92 = if pk 2 + to pk else
        ia pk ec 34 = if false to instr then pk 1+ to pk
      then
    else
      ia pk ec 34 = if true to instr pk 1+ to pk
      else ia pk ec open-c? if dp 1+ to dp pk 1+ to pk
      else ia pk ec close-c? if dp 0> if dp 1- to dp then pk 1+ to pk
      else ia pk ec 44 = dp 0= and if
        ia ps + pk ps - ep-add  pk 1+ to pk  pk to ps
      else pk 1+ to pk then then then then
    then
  repeat
  ia ps + e ps - ep-add ;
: echo-parse-inner ( a u -- ) { a u }
  a u ws-lskip to u to a
  u 0= if s" needs '.echo(item, item, ...)'" echo-bad then
  a c@ 40 <> if s" needs '.echo(item, item, ...)'" echo-bad then
  a 1+ u 1- { ia iu }
  ia iu echo-close { e }
  e 0< if s" missing ')'" echo-bad then
  ia e + 1+ iu e - 1- ws-lskip nip 0<> if s" unexpected text after '.echo(...)'" echo-bad then
  0 ep-n !
  u 2 + 3 * cells ar-alloc ep-arr !
  ia e ws-trim nip 0= if exit then
  ia e echo-split ;
\ 成功なら true (項目は ep-arr / ep-n)。誤りなら理由を echo-ma / echo-mu に置いて false
: echo-parse ( a u -- ok ) ['] echo-parse-inner catch 0= ;

: echo-check ( a u -- ) ar-mark { mk }
  echo-parse 0= if
    mb-reset s"  error - '.echo': " mb+ echo-ma @ echo-mu @ mb+ mb-get diag-e
  then
  mk ar-release ;
bind echo-check echo-validate

\ 裸の名前か (bare_name_of)
: bare-name? ( a u -- f ) ws-trim { a u }
  u 0= if false exit then
  a c@ dup alpha? swap 95 = or 0= if false exit then
  u 1 ?do a i ec dup alnc? swap 95 = or 0= if false unloop exit then loop
  true ;

: echo-arr-text ( arr sb -- ) { arr sb }
  91 sb sb-c
  arr arr-n 0 ?do
    i 0> if s" , " sb sb+ then
    arr i arr-item { it }
    it item-kind 1 = if
      34 sb sb-c
      it item-str 0 ?do dup i + c@ dup 0= if drop s" \0" sb sb+ else sb sb-c then loop drop
      34 sb sb-c
    else it item-q q>dec sb sb+ then
  loop
  93 sb sb-c ;

: dir-echo-impl ( row -- ) { row }
  report? 0= size-mode @ or if exit then
  ar-mark { mk }
  row 1 rf echo-parse 0= if mk ar-release exit then
  sb-new { out }
  ep-n @ 0 ?do
    i 0> if 32 out sb-c then
    i ep-slot { sl }
    sl @ 0= if sl cell+ @ sl 2 cells + @ out sb+ else
      sl cell+ @ sl 2 cells + @ ws-trim { va vu }
      va vu bare-name? if
        va vu ssym-get if out sb+ else
          va vu asym-get ?dup if out echo-arr-text else
            va vu 0 expr-pat drop dup qundef? if drop s" UNDEF" out sb+ else q>dec out sb+ then
          then
        then
      else
        va vu 0 expr-pat drop dup qundef? if drop s" UNDEF" out sb+ else q>dec out sb+ then
      then
    then
  loop
  out sb$ etype ecr
  out sb-free
  mk ar-release ;
bind dir-echo-impl dir-echo
