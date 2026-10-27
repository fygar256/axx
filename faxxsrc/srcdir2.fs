\ srcdir2.fs -- ソース側のディレクティブ (続き): align / zero / res / ascii / section / include

decimal

defer sec-rel-offset ( a u wordpc -- off true | false )        \ セクション相対の位置 (-o / -E)
: sec-rel-offset-nn64 2drop drop false ; bind sec-rel-offset-nn64 sec-rel-offset

: align-up ( addr -- addr' ) align-v @ 0<= if exit then
  dup align-v @ mod dup 0= if drop exit then align-v @ swap - + ;

: dir-align ( a u -- ) { a u }
  a u trim nip if
    a u arg-eval { v idx un }
    a u idx s" .ALIGN" dir-rest-error if exit then
    un v qundef-derived? or if s"  error - .ALIGN argument contains undefined label." diag-e exit then
    v q-neg? v q-zero? or if
      mb-reset s"  error - .ALIGN requires a positive value, got " mb+ v q>dec mb+ s" ." mb+ mb-get diag-e exit
    then
    v @ align-v !
  then
  elf-sectioned? if cur-section pc @ sec-rel-offset else false then
  if { off } off else pc @ then { base }
  base align-up base - pc +! ;

: res-count ( a u name-a name-u -- n ok ) { a u na nu }
  a u arg-eval { v idx un }
  a u idx na nu dir-rest-error if 0 false exit then
  un v qundef-derived? or if
    mb-reset s"  error - " mb+ na nu mb+ s"  argument contains undefined label." mb+ mb-get diag-e 0 false exit
  then
  v q-neg? if
    mb-reset s"  error - " mb+ na nu mb+ s"  requires a non-negative count, got " mb+ v q>dec mb+ s" ." mb+ mb-get diag-e 0 false exit
  then
  v @ true ;
268435456 constant RES-MAX
: dir-zero ( a u -- ) s" .ZERO" res-count 0= if drop exit then { n }
  n RES-MAX > if mb-reset s"  error - .ZERO count " mb+ n mb-n s"  exceeds maximum 268435456." mb+ mb-get diag-e exit then
  n 0 ?do pc @ 0 outbin2-n 1 pc +! loop ;
: dir-res ( a u name-a name-u mul -- ) { a u na nu mul }
  a u na nu res-count 0= if drop exit then { n }
  n RES-MAX mul / > if
    mb-reset s"  error - " mb+ na nu mb+ s"  count " mb+ n mb-n s"  (x" mb+ mul mb-n s" ) exceeds maximum 268435456 words." mb+ mb-get diag-e exit
  then
  n mul * pc +! ;

\ ---- .ascii / .asciz ----
: put-word ( n -- ) pc @ swap outbin-n 1 pc +! ;
\ 文字列の値を 1 つずつ渡す先 ( n -- )。.ascii は put-word、.db は出力ワードの列
variable str-sink
: str-put ( n -- ) str-sink @ execute ;
\ a u の k0 にある `"` から始まる文字列を読み、値を str-put に渡す。.ascii / .asciz と
\ .db で共通の規則 (axx.py の _string_words、caxx.c の string_words と同じ)。
\ k は閉じる `"` の次の位置。status: 0 読めた / 1 閉じていない / 2 エスケープの誤り
\ (文面は mb に入れてある)。trunc は出力ワード幅を超えた値があったか。
: str-scan ( a u k0 -- k status trunc ) { a u k0 } 0 0 { k trunc }
  k0 1+ to k
  begin k u < if a k + c@ 34 <> else false then while
    a k + c@ 92 = k 1+ u < and if
      a k 1+ + c@ { nc }
      nc 48 = if 0 str-put k 2 + to k else
      nc 116 = if 9 str-put k 2 + to k else
      nc 110 = if 10 str-put k 2 + to k else
      nc 114 = if 13 str-put k 2 + to k else
      nc 92 = if 92 str-put k 2 + to k else
      nc 34 = if 34 str-put k 2 + to k else
      nc uc 88 = if
        a u k 2 + 2 hex-run { hv k2 hn }
        hn 0= if
          mb-reset s"  error - '\x' escape requires at least one hex digit in string: " mb+ a u repr1 mb+
          k 2 trunc exit
        then
        k2 to k
        hv wmask u> if true to trunc then
        hv str-put
      else nc uc 85 = if
        nc 117 = if 4 else 8 then { nd }
        a u k 2 + nd hex-run { hv k2 hn }
        hn nd <> if
          mb-reset s"  error - '\" mb+ nc mb-c s" ' escape requires " mb+ nd mb-n s"  hex digits in string: " mb+ a u repr1 mb+
          k 2 trunc exit
        then
        k2 to k
        hv wmask u> if true to trunc then
        hv str-put
      else
        92 str-put k 1+ to k
      then then then then then then then then
    else
      a k + c@ dup wmask u> if true to trunc then str-put
      k 1+ to k
    then
  repeat
  k u >= if k 1 trunc else k 1+ 0 trunc then ;
: ascii-str ( a u -- ok ) { a u }
  u 0= if false exit then
  a c@ 34 <> if false exit then
  ['] put-word str-sink !
  a u 0 str-scan { k st trunc }
  st 2 = if mb-get diag-w false exit then
  st 1 = if
    mb-reset s"  warning - unterminated string literal in .ASCII/.ASCIZ: " mb+ a u repr1 mb+ mb-get diag-w
  else
    a u k s" .ASCII/.ASCIZ" dir-rest-error drop
  then
  trunc report? and if
    mb-reset s"  warning - .ASCII/.ASCIZ: one or more characters exceed the output word width (" mb+ bts @ mb-n
    s"  bit(s)) and were truncated (high bits discarded): " mb+ a u repr1 mb+ mb-get diag-w
  then
  true ;
: dir-ascii ( a u -- )
  2dup ascii-str 0= if
    mb-reset s"  error - .ASCII: failed to process string argument: " mb+ repr1 mb+ mb-get diag-e
  else 2drop then ;
: dir-asciz ( a u -- )
  2dup ascii-str if 2drop 0 put-word else
    s"  error - .ASCIZ requires a quoted string." diag-e
    mb-reset s"  error - .ASCIZ: failed to process string argument: " mb+ repr1 mb+ mb-get diag-e
  then ;

\ ---- .db / .dw / .dd / .dq / .do / .dy / .dz ----
\ いまの行が .db などだったか。立っていれば .eol の改行を足さない (.ascii と同じく、
\ データに改行を混ぜない)。lineassemble2 が行ごとに倒す。axx.py の _data_dir_line と同じ。
variable data-line  false data-line !
\ -o の追跡で、1 つの変数スロットの「取り込んだラベル」を消す (elf5.fs が結ぶ)
defer v2l-slot-clear ( slot -- )
: v2l-slot-clear-nn77 drop ; bind v2l-slot-clear-nn77 v2l-slot-clear
\ -o の追跡で、変数スロットが取り込んだものの種類 (1 はラベル＋定数、3 はラベル差。elf5.fs が結ぶ)
defer v2l-slot-kind ( slot -- k )
: v2l-slot-kind-nn78 drop 0 ; bind v2l-slot-kind-nn78 v2l-slot-kind
\ 値を取り込む内部の変数。データ指令の行はパターンを照合しないので、同じ名前の
\ パターン変数があっても互いに触れない。-2 はまだ作っていない印。
variable data-vslot  -2 data-vslot !
\ -o の追跡で、.db などの 2 つ目以降の値が始まる出力ワードの位置。リロケーションの欄を
\ まとめるとき、同じラベルが続いていてもここで切る (.dq L1, L1 を 1 つの 16 バイトの
\ 欄と読まない)。trk-line-begin が行ごとに空にする。axx.py の _elf_field_breaks と同じ。
4096 constant MAXDBRK
create dbreaks MAXDBRK cells allot
variable ndbreaks  0 ndbreaks !
: dbreak+ ( w -- ) ndbreaks @ MAXDBRK >= if drop exit then  ndbreaks @ cells dbreaks + !  1 ndbreaks +! ;
: dbreak? ( w -- f ) { w } false ndbreaks @ 0 ?do i cells dbreaks + @ w = if drop true leave then loop ;
\ .db などの値が始まる出力ワードの位置。その欄の推測の型は同じ幅の絶対型にする (データの
\ 欄は式の値そのものなので、命令の変位を見込んだ PC 相対の推測をかけない)。
\ trk-line-begin が行ごとに空にする。axx.py の _elf_data_fields と同じ。
create ddfields MAXDBRK cells allot
variable nddfields  0 nddfields !
: ddfield+ ( w -- ) nddfields @ MAXDBRK >= if drop exit then  nddfields @ cells ddfields + !  1 nddfields +! ;
: ddfield? ( w -- f ) { w } false nddfields @ 0 ?do i cells ddfields + @ w = if drop true leave then loop ;
: d-skip ( a u i -- i' ) { a u i }
  begin i u < if a i + c@ dup 32 = swap 9 = or else false then while i 1+ to i repeat i ;
: d-put ( n -- ) wmask and qun obj+ ;
\ 1 つの値 v (q) を n ワードにして出力ワードの列に積む。
: d-words ( v n -- ) { v n }
  n 0 ?do
    endian-big @ if n 1- i - else i then bts @ * { sh }
    v sh qsar q>n wmask and qun obj+
  loop ;
\ dir-data が 1 行のあいだ使う値
variable dd-a  variable dd-u  variable dd-na  variable dd-nu  variable dd-n  variable dd-vi
: dd-name ( -- a u ) dd-na @ dd-nu @ ;
: d-err ( ma mu -- ) { ma mu } report? if mb-reset s"  error - " mb+ dd-name mb+ ma mu mb+ mb-get diag-e then ;
\ 値 v を欄の幅 (nbits) に収まるか調べる。収まらなければ報告して 0 にする。
: d-range ( v -- v' ) { v }
  dd-n @ bts @ * { nbits }
  nbits 256 >= if v exit then
  q1 nbits 1- qshl qneg { lo }
  q1 nbits qshl q1 q- { hi }
  v lo q< v hi q> or if
    report? if
      mb-reset s"  error - " mb+ dd-name mb+ s" : value out of range (" mb+ nbits mb-n
      s" -bit field)." mb+ mb-get diag-e
    then
    q0 exit
  then v ;
\ k の `"` から文字列を読んで積む (.db だけ)。読めたら k' true、誤りなら k false。
: d-string ( k -- k' ok ) { k }
  dd-n @ 1 <> if s" : string literals are allowed only in .DB." d-err k false exit then
  ['] d-put str-sink !
  nobj @ { n0 }
  dd-a @ dd-u @ k str-scan { k2 st trunc }
  st 2 = if report? if mb-get diag-e then  n0 nobj !  k false exit then
  st 1 = if s" : unterminated string literal." d-err  n0 nobj !  k false exit then
  trunc report? and if
    mb-reset s"  warning - " mb+ dd-name mb+
    s" : one or more characters exceed the output word width (" mb+ bts @ mb-n
    s"  bit(s)) and were truncated (high bits discarded)." mb+ mb-get diag-w
  then
  k2 true ;
\ 取り込んだ式の綴り (後ろの空白を除く) を -o の追跡に渡す。
: d-cap-finish ( start end -- ) { start e }
  begin e start > if dd-a @ e 1- + c@ dup 32 = swap 9 = or else false then while e 1- to e repeat
  dd-vi @ dd-a @ start + e start - elf-cap-finish ;
\ 出力ワード base から n 個が、取り込んだ値 x を使ったことを記録する。
: d-note ( base x -- ) { base x }
  dd-n @ 0 ?do base i + trk-widx !  dd-vi @ x elf-note-var loop
  -1 trk-widx ! ;
\ 式の綴り (start から end まで) に $$ があるか
variable dd-pc
\ k の式を読んで積む。読めたら k' true、式が無ければ k false。
: d-expr ( k -- k' ok ) { k }
  false undef-flag !
  dd-vi @ 0>= if dd-vi @ v2l-slot-clear  dd-vi @ trk-cap ! then
  pass @ 1 = if true size-mode ! then
  dd-a @ dd-u @ k expr-asm { x k2 }
  -1 trk-cap !
  pass @ 1 = if false size-mode ! then
  undef-flag @ x qundef? or pass @ 1 <> and { uh }
  false undef-flag !
  k2 k = if s" : missing value." d-err k false exit then
  dd-a @ k + k2 k - s" $$" search nip nip dd-pc !
  dd-vi @ 0>= if k k2 d-cap-finish then
  q0 { v }
  uh if s"  argument contains undefined label." d-err
  else x qundef? 0= if x d-range to v then then
  nobj @ { base }
  \ 絶対型にするのは、値が「ラベル＋定数」で $$ を含まない欄だけ。$$ を使った値は
  \ PC 相対の推測にかけるので、パターンと同じ扱い
  dd-vi @ 0>= if
    dd-vi @ v2l-slot-kind 1 = dd-pc @ 0= and if base ddfield+ then
    base 0> if base dbreak+ then
  then
  v dd-n @ d-words
  dd-vi @ 0>= uh 0= and if base x d-note then
  k2 true ;
\ 1 つの値を読む。読めたら k' true、誤りなら k false。
: d-item ( k -- k' ok ) { k }
  dd-a @ dd-u @ k d-skip to k
  k dd-u @ >= if s" : missing value after ','." d-err k false exit then
  dd-a @ k + c@ 34 = if k d-string else k d-expr then ;
\ 値の後ろ。`,` なら次の値の位置と true、行末か誤りなら false。
: d-sep ( k -- k' more ) { k }
  dd-a @ dd-u @ k d-skip to k
  k dd-u @ >= if k false exit then
  dd-a @ k + c@ 44 = if k 1+ true exit then
  dd-a @ dd-u @ k dd-name dir-rest-error drop  k false ;
\ `.db` / `.dw` / `.dd` / `.dq` / `.do` / `.dy` / `.dz` — 式の値をワード列にして
\ 出す (5.3 節)。1 つの値は n (1 / 2 / 4 / 8 / 16 / 32 / 64) ワードで、.bits のバイト順に
\ 従って little なら下位のワードから、big なら上位のワードから並べる。.db だけは "..." の
\ 文字列も書ける (.ascii と同じ規則)。ワード列は binary_list の出力と同じ経路で書き出すので、
\ -o ではパターンの出力と同じ仕組みでリロケーションが付く (ラベル＋定数の欄は同じ幅の
\ 絶対型)。.vliw の中では直接書き出す。値の誤りがあってもその値の分のワード (0) は出す。
\ axx.py の data_processing()、caxx.c の adir_data() と同じ。
: dir-data ( a u na nu n -- ) dd-n !  dd-nu !  dd-na !  dd-u !  dd-a !
  true data-line !
  -1 dd-vi !
  trk-on @ if
    data-vslot @ -2 = if s" axx_data_" true vslot data-vslot ! then
    data-vslot @ dd-vi !
  then
  0 nobj !
  dd-a @ dd-u @ 0 d-skip { k }
  k dd-u @ >= if s"  requires at least one value." d-err exit then
  begin
    k d-item if d-sep else false then
    swap to k
  while repeat
  vliw-flag @ if
    nobj @ 0 ?do i obj-q q>n put-word loop
    0 nobj !
  then ;

\ ---- .section / .endsection ----
: sec-entry-pc ( slot -- n ) 2 cells + @ ;
: dir-section ( a u -- ) { a u }
  0 { e }
  begin e u < if a e + c@ dup spc? swap 44 = or 0= else false then while e 1+ to e repeat
  e u < if a u e s" .SECTION" dir-rest-error if exit then then
  u 0= if exit then
  cur-section sec-entry { old }
  old sec-entry-pc { epc }
  pc @ epc - { tent }
  tent 0> if
    old cell+ dup @ tent + swap !
    cur-section epc tent range+
  then
  a u cur-section!
  cur-section sections om-find dup 0= if
    drop cur-section sec-entry { ne } pc @ ne !  0 ne cell+ !  pc @ ne 2 cells + !  0 ne 3 cells + !
  else
    { ex }
    ex @ { es }  ex cell+ @ { esz }  ex 3 cells + @ { econf }
    esz 0= econf 0= and if pc @ else es pc @ min then { ns }
    ns ex !  esz ex cell+ !  pc @ ex 2 cells + !  0 ex 3 cells + !
  then ;
: dir-endsection ( -- )
  cur-section sections om-find dup 0= if
    drop mb-reset s"  error - .ENDSECTION without matching .SECTION for '" mb+ cur-section mb+ s" '." mb+ mb-get diag-e exit
  then
  { en }
  en @ { start }  en 2 cells + @ { epc }
  pc @ epc - { blk }
  blk 0< if
    mb-reset s"  warning - ENDSECTION: computed block size " mb+ blk mb-n s"  < 0 for '" mb+ cur-section mb+
    s" '; keeping previous size." mb+ mb-get diag-w exit
  then
  en cell+ @ blk + { nsz }
  blk 0> if cur-section epc blk range+ then
  start en !  nsz en cell+ !  pc @ en 2 cells + !  1 en 3 cells + ! ;

: dir-labelc ( a u -- ) dup if
    lw-tab 256 erase
    256 0 do i alnc? if 1 lw-tab i + c! then loop
    0 ?do dup i + c@ 255 and 1 swap lw-tab + c! loop drop
  else 2drop then ;
