\ expr.fs -- 式評価器 (axx.py の ExpressionEvaluator / caxx.c の expr_*)
\
\ 優先順位ごとに 1 語の再帰下降。値は q (256 ビット) へのアドレス。
\ 浮動小数点の文脈 (exp-float) では値は倍精度のビット列 (w0) で持つ。
\ 文字列は ex-a ex-u、位置は ep。語はすべて ( -- q ) で ep を進める。

decimal

variable ex-a  variable ex-u  variable ep
variable exp-float                 \ 浮動小数点モードか (exp_typ == 'f')
variable caps-pat                  \ パターン変数を読めるか
variable caps-vliw                 \ !!! / !!!! を読めるか
variable undef-flag                \ error_undefined_label
variable expr-missing
variable expr-depth
variable size-mode                 \ _pass1_size_mode
variable fdiv0-defer
variable fdiv0-seen
variable read-float-var            \ _expr_read_float_var
variable vliw-cnt  variable vliw-stop
variable in-binlist
\ パターンの照合 (オペランドの取り込みと error_patterns) と .db などの式を読んでいる
\ 間だけ立つ印。-o / -E では binary_list の中と同じく、同じセクションのラベルと
\ $$ / $. をセクション相対で読む。そうしないと取り込んだ $$+5 やラベルが通し番地の
\ まま binary_list の $$ と混ざり、2 つ目以降のセクションで値と加数がずれる。
\ axx.py の _sec_frame、caxx.c の sec_frame と同じ。
variable sec-frame  false sec-frame !
variable equ-track                  \ .equ の式を評価中 (セクションの追跡)
variable pc  variable pc-start  variable pc-end
1000 constant EXPR-MAX-DEPTH

\ ---- 語を構成する文字の表 (.labelc / .symbolc で変わる) ----
create lw-tab 256 allot
create sw-tab 256 allot
: lwc? ( c -- f ) 255 and lw-tab + c@ 0<> ;
: swc? ( c -- f ) 255 and sw-tab + c@ 0<> ;
: tab-init ( tab chars-a chars-u -- ) { tab ca cu }
  tab 256 erase
  256 0 do i alnc? i 95 = or if 1 tab i + c! then loop
  cu 0 ?do 1 tab ca i + c@ + c! loop ;
: lw-default ( -- ) lw-tab s" ." tab-init ;
: sw-default ( -- ) sw-tab s" %$-~&|" tab-init ;
lw-default sw-default

defer label-get-value ( a u -- q )
defer sym-num-get ( a u -- q true | false )
defer arr-len ( a u -- n | -1 )
defer arr-item-num ( a u i -- q kind )         \ kind 0=数 1=文字列
defer enum-match ( -- q true | false )         \ ep の位置の .enum 要素
defer brace-eval ( kind -- q true | false )    \ flt dbl qad enflt endbl の波括弧
defer loc-counter ( -- q )                     \ $$
defer sec-rel-pc ( q -- q' )                   \ $. をセクション相対にする
defer elf-note-var ( slot q -- )               \ -o の追跡 (変数の読み)
: label-get-value-nn12 ( a u -- q ) 2drop q0 ; bind label-get-value-nn12 label-get-value
: sym-num-get-nn13 ( a u -- q true | false ) 2drop false ; bind sym-num-get-nn13 sym-num-get
: arr-len-nn14 ( a u -- n ) 2drop -1 ; bind arr-len-nn14 arr-len
: arr-item-num-nn15 ( a u i -- q kind ) drop 2drop q0 0 ; bind arr-item-num-nn15 arr-item-num
: enum-match-nn16 ( -- q true | false ) false ; bind enum-match-nn16 enum-match
: brace-eval-nn17 ( kind -- q true | false ) drop false ; bind brace-eval-nn17 brace-eval
: loc-counter-nn18 ( -- q ) in-binlist @ if pc-start @ else pc @ then qn
  in-binlist @ sec-frame @ or equ-track @ or if sec-rel-pc then ; bind loc-counter-nn18 loc-counter
: sec-rel-pc-nn19 ( q -- q' ) ; bind sec-rel-pc-nn19 sec-rel-pc
: elf-note-var-nn20 ( slot q -- ) 2drop ; bind elf-note-var-nn20 elf-note-var

\ ---- 文字の読み出し ----
: ch ( off -- c ) ep @ + dup ex-u @ < if ex-a @ + c@ else drop 0 then ;
: cur ( -- c ) 0 ch ;
: adv ( n -- ) ep +! ;
: skipsp ( -- ) begin cur spc? while 1 adv repeat ;
: qtxt? ( a u -- f )                   \ ep の位置が a u に (大文字小文字を無視して) 一致するか
  true -rot 0 ?do
    dup i + c@ uc  i ch uc <> if swap drop false swap then
  loop drop ;
: qtxt-cs? ( a u -- f )                \ 同じ、大文字小文字を区別する
  true -rot 0 ?do
    dup i + c@  i ch <> if swap drop false swap then
  loop drop ;
: nxt-brace? ( off -- f )              \ ep+off 以降の最初の空白でない文字が { か
  begin dup ch spc? while 1+ repeat ch 123 = ;
: ach ( i -- c ) dup ex-u @ < if ex-a @ + c@ else drop 0 then ;   \ 絶対位置

\ ---- 浮動小数点の入れ物 ----
: qd ( a -- ) ( F: -- r ) f@ ;
: dq ( F: r -- ) ( -- a ) q0 dup f! ;
18446744073709551616e fconstant TWO64
9223372036854775808e fconstant TWO63
: u>f ( u -- ) ( F: -- r )                       \ 符号なし 64 ビットを正しく丸めて
  dup 0< if dup 1 rshift swap 1 and or s>f 2e f* else s>f then ;
create p2buf 8 allot
: fpow2 ( n -- ) ( F: -- r )                    \ 2^n (n は 0..1023)
  1023 min 1023 + 52 lshift p2buf ! p2buf f@ ;
: f>u ( F: r -- ) ( -- u )
  fdup TWO63 f>= if TWO63 f- f>s 1 63 lshift or else f>s then ;
: qmag ( a -- m ) dup q-neg? if qneg then ;
: qi>f ( a -- ) ( F: -- r )                      \ 整数 -> 倍精度 (偶数丸め)
  { a } a q-neg? { neg }  a qmag { m }  m qnbit { nb }
  nb 64 <= if m @ u>f else
    nb 64 - { sh }
    m sh qshr { top }
    top sh qshl m q= 0= { sticky }
    top @ sticky if 1 or then u>f
    sh fpow2 f*
  then
  neg if fnegate then ;
: qi>dq ( a -- q ) qi>f dq ;                     \ 整数 -> 倍精度ビット列
: dq-trunc ( F: r -- ) ( -- q )                  \ 倍精度 -> 整数 (ゼロ方向)。ビット列から直接作る
  dq @ { bits }
  bits 52 rshift $7ff and { ex }
  q0 { r }
  ex 1023 < if r exit then
  bits 1 52 lshift 1- and 1 52 lshift or r !
  ex 1075 - { e }
  e 0>= if r e 255 min qshl to r else r e negate qshr to r then
  bits 0< if r qneg else r then ;
: qd-fin? ( a -- f ) @ 52 rshift 2047 and 2047 <> ;
: dtxt ( a -- c-addr u )                         \ inf / -inf / nan の綴り
  dup @ 63 rshift { neg }  dup @ $fffffffffffff and 0= { zm }  drop
  zm if neg if s" -inf" else s" inf" then else s" nan" then ;

: u2? ( x t -- f ) qundef? swap qundef? or ;
: xerr ( a u -- ) diag-e ;
variable lit-ovf
variable band-warned
: qband-warn-impl ( -- ) band-warned @ if exit then  true band-warned !
  s"  warning - a value whose signed absolute magnitude is >= 2**192 was computed and is being treated as UNDEF-derived; this heuristic cannot distinguish it from a genuine large 256-bit constant (e.g. an all-ones bitmask) because uint256_t has no headroom beyond 256 bits for a true out-of-band sentinel." diag-w ;
bind qband-warn-impl qband-warn
variable wrap-warned
: warn-wrap ( a u -- ) wrap-warned @ if 2drop exit then  true wrap-warned !
  mb-reset s"  warning - a value overflowed 256 bits in '" mb+ mb+
  s" ' and was wrapped; axx.py keeps the full precision there, so the two implementations disagree above 2**256 (manual 6.4)." mb+ mb-get diag-wf ;
: xwarn ( a u -- ) diag-w ;

\ ---- ビット演算の前処理 ----
: safe-bw ( q opname-a opname-u -- q' ) { q oa ou }
  exp-float @ if
    q qd-fin? 0= if
      mb-reset s"  error - non-finite value " mb+ q dtxt mb+ s"  in bitwise '" mb+ oa ou mb+
      s" ' operation; treated as 0." mb+ mb-get xerr
      q0 exit
    then
    q qd dq-trunc exit
  then
  q ;
: bw-result ( q -- q' ) exp-float @ if qi>dq then ;
: num-operand ( q -- q' ok ) { q }
  exp-float @ if
    q qd-fin? 0= if q0 false exit then
    q qd dq-trunc true exit
  then
  q true ;
: expr-bool ( f -- q ) exp-float @ if if 1e else 0e then dq else if 1 else 0 then qn then ;
: expr-false? ( q -- f ) dup qundef? 0= exp-float @ and if qd 0e f= else q-zero? then ;

\ 数値の字面
: plit-end ( q -- q ) lit-ovf @ if s" literal" warn-wrap then ;
: pdec ( -- q ) q0 false lit-ovf ! begin cur digc? while 10 cur 48 - q*small+ lit-ovf @ or lit-ovf ! 1 adv repeat plit-end ;
: phex ( -- q ) q0 false lit-ovf ! begin cur xdig? while 16 cur hexv q*small+ lit-ovf @ or lit-ovf ! 1 adv repeat plit-end ;
: pbin ( -- q ) q0 false lit-ovf ! begin cur dup 48 = swap 49 = or while 2 cur 48 - q*small+ lit-ovf @ or lit-ovf ! 1 adv repeat plit-end ;
\ 浮動小数点の字面 (get_floatstr)
: float-start? ( -- f )
  s" -inf" qtxt-cs? s" inf" qtxt-cs? or s" nan" qtxt-cs? or if true exit then
  cur dup digc? swap 46 = or ;
create fsbuf 512 allot
variable fs-u
: fs-c ( c -- ) fs-u @ 511 >= if drop exit then fsbuf fs-u @ + c! 1 fs-u +! ;
: pfloat ( -- q )
  0 fs-u !
  s" -inf" qtxt-cs? if 4 adv $fff0 48 lshift qun exit then
  s" inf" qtxt-cs? if 3 adv $7FF0000000000000 qun exit then
  s" nan" qtxt-cs? if 3 adv $7FF8000000000000 qun exit then
  begin cur digc? cur 46 = or while cur fs-c 1 adv repeat
  cur dup 101 = swap 69 = or if
    ep @ { sidx }  fs-u @ { sfs }
    cur fs-c 1 adv
    cur dup 43 = swap 45 = or if cur fs-c 1 adv then
    ep @ { ds }
    begin cur digc? while cur fs-c 1 adv repeat
    ep @ ds = if sidx ep !  sfs fs-u ! then
  then
  fs-u @ 0= if q0 exit then
  fsbuf fs-u @ >float if dq else 0e dq then ;

\ 文字定数
: esc-val ( c -- x true | false )
  case
    [char] t of 9 true endof
    [char] ' of 39 true endof
    [char] \ of 92 true endof
    [char] n of 10 true endof
    [char] 0 of 0 true endof
    [char] r of 13 true endof
    [char] a of 7 true endof
    [char] b of 8 true endof
    [char] f of 12 true endof
    [char] v of 11 true endof
    false swap
  endcase ;
: hexlit? ( -- x true | false )
  1 ch 92 <> if false exit then
  2 ch uc 88 <> if false exit then
  3 ch xdig? 0= if false exit then
  4 ch xdig? if
    5 ch 39 = if 3 ch hexv 16 * 4 ch hexv + 6 adv true else false then
  else
    4 ch 39 = if 3 ch hexv 5 adv true else false then
  then ;
: charlit? ( -- x true | false )
  cur 39 <> if false exit then
  1 ch 92 = 3 ch 39 = and if
    2 ch esc-val if 4 adv true exit then
  then
  hexlit? if true exit then
  1 ch 92 <> 1 ch 0<> and 2 ch 39 = and if 1 ch 3 adv true exit then
  false ;
: int-or-float ( q -- q ) exp-float @ if qi>dq then ;

\ 語の読み取り
: symword ( -- a u )          \ シンボルの語 (swordchars)
  ex-a @ ep @ + 0 { a n }
  cur digc? 0= cur swc? and if
    begin cur swc? while n 1+ to n 1 adv repeat
  then
  a n ;
: labword ( -- a u )          \ ラベルの語 (lwordchars)
  ex-a @ ep @ + 0 { a n }
  cur 46 = cur digc? 0= cur lwc? and or if
    begin cur lwc? while n 1+ to n 1 adv repeat
  then
  a n ;
: varlen ( -- n )             \ パターン変数名の長さ (0 なら変数でない)
  cur lowc? 0= if 0 exit then
  1 begin dup ch dup lowc? swap digc? or over ch 95 = or while 1+ repeat ;
: patvarlen ( -- n ) varlen dup 0= if exit then dup ch lwc? if drop 0 then ;

\ ---- 変数の読み ----
: var-for-mode ( slot -- q ) { sl }
  sl 0< if q0 exit then
  sl vval { v }
  exp-float @ if
    sl vfloat? 0= v qundef? 0= and if v qi>dq exit then
  else
    sl vfloat? if true read-float-var ! then
  then
  v ;

defer expr

: patvar-term ( n -- q ) { n } 0 0 0 0 0 { a sl x prior cu }
  ex-a @ ep @ + to a
  n ch 58 = n 1+ ch 61 = and if
    n 2 + adv
    a n true vslot to sl
    undef-flag @ to prior  false undef-flag !
    expr to x
    undef-flag @ to cu
    prior cu or undef-flag !
    sl x cu exp-float @ vput
    x exit
  then
  n adv
  a n false vslot to sl
  sl var-for-mode to x
  in-match @ 0= size-mode @ 0= and report? and if
    sl vundef? x qundef-derived? or if
      true undef-flag !
      mb-reset s"  error - Label undefined: variable '" mb+ sl vslot-name mb+
      s" ' contains undefined value" mb+ mb-get diag-w
    then
  then
  sl x elf-note-var
  x ;

\ ---- 因子 ----
: fin ( q -- q ) skipsp ;
: finite-brace-kind ( -- kind true | false )
  s" qad" qtxt? 3 nxt-brace? and if 0 3 adv true exit then
  s" enflt" qtxt? 5 nxt-brace? and if 1 5 adv true exit then
  s" endbl" qtxt? 5 nxt-brace? and if 2 5 adv true exit then
  s" dbl" qtxt? 3 nxt-brace? and if 3 3 adv true exit then
  s" flt" qtxt? 3 nxt-brace? and if 4 3 adv true exit then
  false ;

: hash-term ( -- q )                               \ #name / #name[i]
  1 adv symword supper { ta tu }
  ta tu arr-len { alen }
  alen 0>= cur 91 = and if
    caps-pat @ { sp }  true caps-pat !
    1 adv expr { iv }
    sp caps-pat !
    cur 93 = if 1 adv else
      mb-reset s"  error - '#" mb+ ta tu mb+ s" [': missing ']'." mb+ mb-get xerr
    then
    iv @ { n }
    iv q-neg? n alen >= or if
      mb-reset s"  error - index " mb+ iv q>dec mb+ s"  is out of range for array symbol '" mb+ ta tu mb+
      s" ' (0.." mb+ alen 1- mb-n s" )." mb+ mb-get xerr
      q0 exit
    then
    ta tu n arr-item-num { kind }
    kind 1 = if
      drop mb-reset s"  error - '#" mb+ ta tu mb+ s" [" mb+ n mb-n s" ]' is a string item and has no numeric value." mb+
      mb-get xerr q0 exit
    then
    exit
  then
  ta tu sym-num-get if exit then
  mb-reset s"  error - undefined symbol: '#" mb+ ta tu mb+ s" '" mb+ mb-get xerr
  q0 ;

: factor1 ( -- q )
  skipsp
  cur 0= if q0 exit then
  cur 40 = if
    1 adv expr
    cur 41 = if 1 adv else s"  error - missing closing ')' in expression." xerr then
    fin exit
  then
  charlit? if qn int-or-float fin exit then
  s" $$" qtxt? if 2 adv loc-counter int-or-float fin exit then
  s" $." qtxt? if
    2 adv pc-end @ qn
    in-binlist @ sec-frame @ or equ-track @ or if sec-rel-pc then
    int-or-float fin exit
  then
  cur 35 = if hash-term int-or-float fin exit then
  s" 0b" qtxt? if 2 adv pbin int-or-float fin exit then
  s" 0x" qtxt? if 2 adv phex int-or-float fin exit then
  finite-brace-kind if
    brace-eval if fin exit then
    q0 fin exit
  then
  s" not(" qtxt? if
    4 adv expr skipsp
    cur 41 = if 1 adv else s"  error - missing closing ')' in not(...) expression." xerr then
    q-zero? if 1 else 0 then qn fin exit
  then
  exp-float @ float-start? and if pfloat fin exit then
  cur digc? if pdec fin exit then
  enum-match if fin exit then
  caps-pat @ if
    patvarlen dup 0> if patvar-term fin exit then
    drop
  then
  cur lwc? if
    labword dup 0> if
      label-get-value
      exp-float @ if dup qundef? 0= if qi>dq then then
      fin exit
    then
    2drop
  then
  q0 fin ;

\ ---- 単項 ----
: byte-extract ( x ix -- q ) { x ix } 0 { bn }
  x ix u2? if qundef exit then
  ix num-operand 0= if
    drop s"  error - non-finite byte-extract offset in *(expr, expr)." xerr q0 bw-result exit
  then
  to ix
  ix q-neg? if s"  error - negative byte-extract offset in *(expr, expr)." xerr q0 bw-result exit then
  x num-operand 0= if
    drop s"  error - non-finite value in *(expr, expr) byte extract." xerr q0 bw-result exit
  then
  to x
  x ix qbyte drop bw-result ;

defer recurse-factor
: factor-impl ( -- q )
  skipsp
  s" !!!!" qtxt? caps-vliw @ and if 4 adv vliw-stop @ qn exp-float @ if qi>dq then skipsp exit then
  s" !!!" qtxt? caps-vliw @ and if 3 adv vliw-cnt @ qn exp-float @ if qi>dq then skipsp exit then
  cur 45 = if
    1 adv recurse-factor dup qundef? 0= if
      exp-float @ if qd fnegate dq else qneg then
    then skipsp exit
  then
  cur 126 = if
    1 adv recurse-factor dup qundef? 0= if s" ~" safe-bw qnot bw-result then skipsp exit
  then
  cur 64 = if
    1 adv recurse-factor dup qundef? 0= if
      s" @" safe-bw qnbit qn exp-float @ if qi>dq then
    then skipsp exit
  then
  cur 42 = if
    1 ch 40 = if
      2 adv expr { x }
      cur 44 = if
        1 adv expr { x2 }
        cur 41 = if 1 adv x x2 byte-extract
        else s"  error - missing ')' in *(expr, expr) expression." xerr q0 then
      else s"  error - missing ',' in *(expr, expr) expression." xerr q0 then
    else
      s"  error - expected '(' after '*' in *(expr,expr) expression." xerr 1 adv q0
    then
    skipsp exit
  then
  ep @ { p0 }
  factor1
  ep @ p0 = if true expr-missing ! then
  ep @ p0 = if
    cur dup 0<> over 44 <> and over 41 <> and over 93 <> and over 32 <> and over 9 <> and
    in-match @ 0= and report? and if
      mb-reset s"  warning - unrecognized token at position " mb+ ep @ mb-n
      s"  in expression: '" mb+ ex-a @ ep @ + ex-u @ ep @ - 8 min mb+ s" ' (treated as 0)" mb+
      mb-get xwarn
    then
    drop
  then
  skipsp ;
: factor ( -- q )
  expr-depth @ EXPR-MAX-DEPTH >= if
    s"  error - expression nesting too deep." xerr q0 exit
  then
  1 expr-depth +!  factor-impl  -1 expr-depth +! ;
bind factor recurse-factor

