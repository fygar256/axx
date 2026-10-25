\ dirs2.fs -- パターン側ディレクティブ (続き)

decimal

\ ---- UTF-8 と get_string ----
: utf8-enc ( cp sb -- ) { cp sb }
  cp 128 < if cp sb sb-c exit then
  cp 2048 < if cp 6 rshift 192 or sb sb-c  cp 63 and 128 or sb sb-c exit then
  cp 65536 < if cp 12 rshift 224 or sb sb-c  cp 6 rshift 63 and 128 or sb sb-c  cp 63 and 128 or sb sb-c exit then
  cp 18 rshift 240 or sb sb-c  cp 12 rshift 63 and 128 or sb sb-c
  cp 6 rshift 63 and 128 or sb sb-c  cp 63 and 128 or sb sb-c ;

sb-new constant rp-b
: utf8-seq-len ( a u -- n )                           \ 先頭の UTF-8 文字のバイト数 (不正なら 1)
  { a u }
  u 0= if 0 exit then
  a c@ { c }
  c $80 < if 1 exit then
  c $c2 >= c $df <= and if u 2 >= if a 1+ c@ $c0 and $80 = if 2 exit then then 1 exit then
  c $e0 >= c $ef <= and if
    u 3 >= if a 1+ c@ $c0 and $80 = a 2 + c@ $c0 and $80 = and if
      c $e0 = if a 1+ c@ $a0 >= else true then
      c $ed = if a 1+ c@ $9f <= and then if 3 exit then
    then then 1 exit
  then
  c $f0 >= c $f4 <= and if
    u 4 >= if a 1+ c@ $c0 and $80 = a 2 + c@ $c0 and $80 = and a 3 + c@ $c0 and $80 = and if
      c $f0 = if a 1+ c@ $90 >= else true then
      c $f4 = if a 1+ c@ $8f <= and then if 4 exit then
    then then 1 exit
  then
  1 ;
: hex2 ( n -- ) dup 4 rshift dup 10 < if 48 + else 87 + then rp-b sb-c 15 and dup 10 < if 48 + else 87 + then rp-b sb-c ;
: repr1 ( a u -- a' u' ) { a u }                       \ Python の repr
  false false { sq dq }
  u 0 ?do a i + c@ dup 39 = if true to sq then 34 = if true to dq then loop
  sq dq 0= and if 34 else 39 then { q }
  rp-b sb-clear  q rp-b sb-c
  0 { k }
  begin k u < while
    a k + c@ { c }
    c 92 = c q = or if 92 rp-b sb-c c rp-b sb-c k 1+ to k else
    c 10 = if s" \n" rp-b sb+ k 1+ to k else
    c 9 = if s" \t" rp-b sb+ k 1+ to k else
    c 13 = if s" \r" rp-b sb+ k 1+ to k else
    c 32 < c 127 = or if s" \x" rp-b sb+ c hex2 k 1+ to k else
    c 128 >= if
      a k + u k - utf8-seq-len { l }
      l 1 = if s" \udc" rp-b sb+ c hex2 k 1+ to k
      else a k + l rp-b sb+ k l + to k then
    else c rp-b sb-c k 1+ to k then then then then then then
  repeat
  q rp-b sb-c
  rp-b sb$ sdup ;
' repr1 is pat-repr

sb-new constant gs-b
: hex-run ( a u k maxn -- val k' n ) { a u k mx } 0 0 { v n }
  begin k u < n mx < and if a k + c@ xdig? else false then while
    v 16 * a k + c@ hexv + to v  k 1+ to k  n 1+ to n
  repeat
  v k n ;
: get-string ( a u -- a' u' ) { a u } 0 { k }
  gs-b sb-clear
  begin k u < if a k + c@ spc? else false then while k 1+ to k repeat
  k u >= if s" " exit then
  a k + c@ 34 <> if s" " exit then
  k 1+ to k
  begin k u < while
    a k + c@ 92 = k 1+ u < and if
      a k 1+ + c@ { nc }
      nc 34 = if 34 gs-b sb-c k 2 + to k else
      nc 92 = if 92 gs-b sb-c k 2 + to k else
      nc 110 = if 10 gs-b sb-c k 2 + to k else
      nc 116 = if 9 gs-b sb-c k 2 + to k else
      nc 114 = if 13 gs-b sb-c k 2 + to k else
      nc uc 88 = if
        a u k 2 + 2 hex-run { v k2 n }
        k2 to k
        n 0> if v gs-b utf8-enc else
          mb-reset s"  warning - '\x' escape requires at least one hex digit; treated as literal 'x' in: " mb+ a u repr1 mb+
          mb-get diag-w  120 gs-b sb-c
        then
      else nc uc 85 = if
        nc 117 = if 4 else 8 then { nd }
        a u k 2 + nd hex-run { v k2 n }
        k2 to k
        n nd = if v gs-b utf8-enc else
          mb-reset s"  warning - '\" mb+ nc mb-c s" ' escape requires " mb+ nd mb-n s"  hex digits; treated as literal characters in: " mb+ a u repr1 mb+
          mb-get diag-w
          nc gs-b sb-c  a k n - + n gs-b sb+
        then
      else nc gs-b sb-c k 2 + to k
      then then then then then then then
    else
      a k + c@ 34 = if gs-b sb$ exit then
      a k + c@ gs-b sb-c  k 1+ to k
    then
  repeat
  mb-reset s"  warning - unterminated string literal: " mb+ a u repr1 mb+ mb-get diag-w
  gs-b sb$ ;

\ ---- 小さなもの ----
: field-nonblank ( row first -- a u )                      \ i[first..] の最初の空でない欄 (空白を除く)
  { r f }
  6 f ?do r i rf trim dup if unloop exit then 2drop loop 0 0 ;

: exec-clearsym ( row -- ) 2 rf dup if
    2dup skey sym-target @ om-del 2dup ssym-del asym-del
  else 2drop  sym-target @ om-clear  strsyms om-clear
    arrsyms om-used 0 ?do i arrsyms om-live? if i arrsyms om-val @ arr-free then loop arrsyms om-clear
  then ;

: low-word ( q -- n ) @ ;
: exec-padding ( row -- ) { r }
  r 2 rf nip if r 2 rf else r 1 rf nip if r 1 rf else s" " then then
  dup 0= if 2drop 0 else 0 expr-pat drop @ then padding-v ! ;

: exec-bits ( row -- ) { r } 0 0 { wa wu }
  3 1 do
    r i rf { fa fu }
    fu 0> if
      fa fu slower s" big" str=cs if true endian-big ! else
      fa fu slower s" little" str=cs if false endian-big ! else
      wu 0= if fa to wa  fu to wu else
        mb-reset s"  error - .bits: multiple word-width fields given (" mb+ wa wu repr1 mb+ s"  and " mb+ fa fu repr1 mb+ s" )." mb+
        mb-get diag-e
      then then then
    then
  loop
  wu 0> if
    false undef-flag !
    wa wu 0 expr-pat drop { v }
    undef-flag @ 0= v qundef-derived? 0= and
    v q-neg? 0= and v 64 q-nonneg-gt? 0= and v q-zero? 0= and if
      v @ bts !
    else
      mb-reset s"  error - .bits: word width must be an integer in 1..64, got " mb+ wa wu repr1 mb+ s" ." mb+ mb-get diag-e
    then
    false undef-flag !
  then ;

: exec-symbolc ( row -- ) 2 rf dup 0> if
    sw-tab 256 erase
    256 0 do i alnc? if 1 sw-tab i + c! then loop
    0 ?do dup i + c@ 255 and 1 swap sw-tab + c! loop drop
  else 2drop then ;

: exec-vliw ( row -- ) { r }
  r 1 rf 0 expr-pat drop { v1 }  r 2 rf 0 expr-pat drop { v2 }
  r 3 rf 0 expr-pat drop { v3 }  r 4 rf 0 expr-pat drop { v4 }
  v1 @ { b }  v2 @ { n }  v3 @ { t }  v4 @ { nop }
  b -8192 < b 8192 > or if s"  error - .vliw: vliwbits is out of range (must be -8192..8192)." diag-e exit then
  n 0< n 8192 > or if
    mb-reset s"  error - .vliw: vliwinstbits " mb+ n mb-n s"  is out of range (must be 0-8192)." mb+ mb-get diag-e exit
  then
  t -8192 < t 8192 > or if s"  error - .vliw: vliwtemplatebits is out of range (must be -8192..8192)." diag-e exit then
  b vliw-bits !  n vliw-instbits !  t vliw-tmplbits !  true vliw-flag !
  n 8 / n 8 mod 0= if 0 else 1 then + { nb }
  nb vliw-nopn !
  nb 0 ?do nop 255 and vliw-nop i + c!  nop 8 rshift to nop loop ;

: exec-epic ( row -- ) { r }
  r 1 rf nip 0= if exit then
  r 1 rf { sa su }
  64 arr-new { ia }  0 { cnt } 0 { idx }
  begin
    sa su idx expr-pat { v ni }
    cnt 64 < if v ia cnt arr-item item-num! then
    cnt 1+ to cnt  ni to idx
    idx su < if sa idx + c@ 44 = else false then if idx 1+ to idx false else true then
  until
  cnt ia ! \ 個数を格納
  \ 重複を避けて追加
  false { dup? }
  vliw-set @ 0 ?do
    vliw-idx-a i cells + @ { oa }
    oa arr-n cnt = if
      true { same }
      cnt 0 ?do oa i arr-item item-q ia i arr-item item-q q= 0= if false to same then loop
      same if vliw-pat-a i cells + @ vliw-pat-u i cells + @ r 2 rf str=cs if true to dup? then then
    then
  loop
  dup? 0= if
    ia vliw-idx-a vliw-set @ cells + !
    r 2 rf hdup vliw-pat-u vliw-set @ cells + !  vliw-pat-a vliw-set @ cells + !
    1 vliw-set +!
  then ;
