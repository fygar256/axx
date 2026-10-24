\ axx.fs -- axx 汎用アセンブラの gforth 実装 (愛称 Fxx)
\
\ axx.py (Paxx) の中核部分を Forth に写したものです。
\
\   gforth axx.fs <パターンファイル.axx> <ソース.s> [-b 出力ファイル]
\
\ 移した範囲:
\   パターンファイルの読み込み (コメント・継続行・.include)
\   .setsym / .check / .clrcheck / .padding / .error
\   命令の書式の照合 (大文字=文字定数, 小文字=シンボル, !x !!x !Lx, [[ ]], \ 止め文字)
\   特異度スコア (n_expr, -n_lit, n_sym) による最良パターンの選択
\   error_patterns / binary_list の評価 (@@[n,..], %%, ;, ;;)
\   式 (Paxx と同じ優先順位。:= 、? : 、&& || の短絡、' 、@ 、*(x,y) を含む)
\   ラベル・.equ・.org・.align・.ascii・.asciz・.zero・.resb/.resw/.resd/.resq
\   パス1の収束まで反復 → パス2 で生成 (-b で生のバイナリ)
\
\ 移していないもの: マクロ層, ミニ言語 (.func/.call), ELF/DWARF (-o), VLIW,
\   浮動小数点 (!F/!D/!Q), .sub/.enum/.map などの拡張, .bits の 8 以外, テキスト置換。

decimal

\ ====================================================================
\ 基本ユーティリティ
\ ====================================================================

: etype ( a u -- ) stderr write-file drop ;
: ecr ( -- ) s\" \n" etype ;
: n>s ( n -- a u ) dup >r abs s>d <# #s r> sign #> ;
: .en ( n -- ) n>s etype ;

: uc ( c -- C ) dup 97 123 within if 32 - then ;
: lowc? ( c -- f ) 97 123 within ;
: capc? ( c -- f ) 65 91 within ;
: digc? ( c -- f ) 48 58 within ;
: alnc? ( c -- f ) dup lowc? over capc? or swap digc? or ;
: corec? ( c -- f ) dup alnc? swap 95 = or ;
: lwc? ( c -- f ) dup corec? swap 46 = or ;
: spc? ( c -- f ) dup 32 = swap 9 = or ;
: xdig? ( c -- f ) uc dup 48 58 within swap 65 71 within or ;
: hexv ( c -- n ) uc dup 58 < if 48 - else 55 - then ;

: in-str? ( c a u -- f )
  rot >r
  begin dup while
    over c@ r@ = if 2drop r> drop true exit then
    1 /string
  repeat
  2drop r> drop false ;
: swc? ( c -- f ) dup corec? if drop true exit then s" %$-~&|" in-str? ;

: str=ci ( a1 u1 a2 u2 -- f )
  rot over <> if 2drop drop false exit then
  0 ?do
    over i + c@ uc  over i + c@ uc <> if 2drop unloop false exit then
  loop
  2drop true ;
: str=cs ( a1 u1 a2 u2 -- f ) compare 0= ;

: find-comma ( a u -- n )
  dup 0 ?do over i + c@ 44 = if 2drop i unloop exit then loop nip ;
: trim ( a u -- a' u' )
  begin dup 0> while over c@ spc? while 1 /string repeat then
  begin dup 0> while 2dup + 1- c@ spc? while 1- repeat then ;

\ ---- 文字列を貯める領域 ----
33554432 constant ARENA-SIZE
ARENA-SIZE allocate throw constant arena
variable ar-top
: ar-alloc ( n -- a )
  ar-top @ over + ARENA-SIZE > abort" arena full"
  ar-top @ arena + swap ar-top +! ;
: sdup ( a u -- a' u )
  dup 1+ ar-alloc >r
  swap r@ rot dup >r move
  r> r> swap ;
: hdup ( a u -- a' u )      \ ヒープに写す (解放しない)
  dup 1+ allocate throw >r
  swap r@ rot dup >r move
  r> r> swap ;

\ ---- 大域状態 ----
variable pass          \ 0=なし 1=パス1 2=パス2
variable pass1-iter    \ パス1の反復番号 (0 起点)
variable pc
variable pc-end        \ $.  (その命令の次の番地)
variable pc-start      \ $$
variable in-binlist
variable had-error
variable line-no
variable size-mode
variable in-match
variable padding-v     0 padding-v !
variable align-v       16 align-v !
variable src-name-a    variable src-name-u
variable cur-row
variable force-size

: report? ( -- f ) pass @ 1 > ;

create mbuf 4096 allot
variable mb-u
: mb-reset ( -- ) 0 mb-u ! ;
: mb+ ( a u -- ) dup >r mbuf mb-u @ + swap move r> mb-u +! ;
: mb-n ( n -- ) n>s mb+ ;
: mb-get ( -- a u ) mbuf mb-u @ ;

\ 照合の試行中に出た診断は、採られた候補のぶんだけをあとで流す。
create ddbuf 8192 allot
variable dd-u
create ddbest 8192 allot
variable ddb-u
: dd+ ( a u -- )
  dup dd-u @ + 8191 > if 2drop exit then
  dup >r ddbuf dd-u @ + swap move r> dd-u +! ;
: dd-c ( c -- ) dd-u @ 8191 >= if drop exit then ddbuf dd-u @ + c!  1 dd-u +! ;

\ 同じ行の中で同じ診断を繰り返さない
create seenbuf 16384 allot
variable seen-off
16 constant MAXSEEN
create seen-a MAXSEEN cells allot
create seen-u MAXSEEN cells allot
variable nseen
: seen-reset ( -- ) 0 nseen !  0 seen-off ! ;
: seen? ( a u -- f )
  nseen @ 0 ?do
    2dup i cells seen-a + @ i cells seen-u + @ str=cs if 2drop true unloop exit then
  loop
  2drop false ;
: seen-add { a u }
  nseen @ MAXSEEN >= if exit then
  seen-off @ u + 16383 > if exit then
  a seenbuf seen-off @ + u move
  seenbuf seen-off @ + nseen @ cells seen-a + !
  u nseen @ cells seen-u + !
  u seen-off +!  1 nseen +! ;
: emit-line ( a u -- )
  2dup seen? if 2drop exit then
  2dup seen-add
  etype ecr  true had-error ! ;

create dline 4096 allot
variable dl-u
: dl+ ( a u -- ) dup >r dline dl-u @ + swap move r> dl-u +! ;
: diag ( a u -- )
  report? 0= if 2drop exit then
  0 dl-u !  dl+  s"   [" dl+ src-name-a @ src-name-u @ dl+ s" :" dl+ line-no @ n>s dl+ s" ]" dl+
  in-match @ if
    dline dl-u @ dd+  10 dd-c
  else
    dline dl-u @ emit-line
  then ;
: diag-w ( a u -- )    \ 警告 (had-error にしない)
  in-match @ if 2drop exit then
  report? 0= if 2drop exit then
  etype ecr ;
: dd-snap ( -- ) ddbuf ddbest dd-u @ move  dd-u @ ddb-u ! ;
: dd-replay ( -- )
  report? 0= if exit then
  ddbest ddb-u @ { a u } 0 0 { st k }
  begin k u < while
    a k + c@ 10 = if a st + k st - emit-line  k 1+ to st then
    k 1+ to k
  repeat ;

\ ====================================================================
\ シンボル (.setsym)・.check・変数・ラベルの表
\ ====================================================================

2048 constant MAXSYM
create sym-na MAXSYM cells allot
create sym-nu MAXSYM cells allot
create sym-fin MAXSYM cells allot
create sym-cur MAXSYM cells allot
variable nsym

create ubuf 512 allot
: upper-copy ( a u -- a' u )
  dup 511 > if drop 511 then
  dup >r 0 ?do dup i + c@ uc ubuf i + c! loop drop ubuf r> ;

: sym-find ( a u -- i | -1 )
  upper-copy
  nsym @ 0 ?do
    2dup i cells sym-na + @  i cells sym-nu + @  str=cs if 2drop i unloop exit then
  loop
  2drop -1 ;
: sym-lookup ( a u -- v true | false )
  sym-find dup 0< if drop false exit then
  cells sym-cur + @ true ;
: sym-add ( a u -- i )
  nsym @ MAXSYM >= abort" too many symbols"
  upper-copy sdup
  nsym @ cells sym-nu + !
  nsym @ cells sym-na + !
  nsym @  1 nsym +! ;
: sym-define ( a u v -- )
  >r 2dup sym-find dup 0< if drop sym-add else nip nip then
  r> swap 2dup cells sym-fin + !  cells sym-cur + ! ;
: sym-reset ( -- )
  nsym @ 0 ?do i cells sym-fin + @ i cells sym-cur + ! loop ;

\ .check の表: 変数名 → 許すシンボルの一覧 (大文字のカンマ区切り)
128 constant MAXCHK
create chk-na MAXCHK cells allot
create chk-nu MAXCHK cells allot
create chk-la MAXCHK cells allot     \ 0 なら無効
create chk-lu MAXCHK cells allot
variable nchk
: chk-find ( a u -- i | -1 )
  nchk @ 0 ?do
    2dup i cells chk-na + @  i cells chk-nu + @  str=cs if 2drop i unloop exit then
  loop
  2drop -1 ;
: chk-slot ( a u -- i )
  2dup chk-find dup 0< if
    drop nchk @ MAXCHK >= abort" too many checks"
    sdup nchk @ cells chk-nu + !  nchk @ cells chk-na + !
    nchk @  1 nchk +!
  else nip nip then ;
: chk-set ( na nu la lu -- )
  2>r chk-slot 2r>
  rot dup >r cells chk-lu + !  r> cells chk-la + ! ;
: chk-clear ( na nu -- )
  chk-find dup 0< if drop else cells chk-la + 0 swap ! then ;
: chk-clear-all ( -- ) nchk @ 0 ?do 0 i cells chk-la + ! loop ;
: chk-get ( a u -- la lu true | false )
  chk-find dup 0< if drop false exit then
  dup cells chk-la + @ dup 0= if 2drop false exit then
  swap cells chk-lu + @ true ;

: next-item ( a u -- ra ru ia iu )
  2dup find-comma { a u n }
  a n trim { ia iu }
  n u < if a n 1+ + u n - 1- else a u + 0 then
  ia iu ;
: list-has? { wa wu la lu } 0 0 { ia iu }
  begin lu 0> while
    la lu next-item to iu to ia to lu to la
    wa wu ia iu str=cs if true exit then
  repeat false ;
: list-omit? { la lu } 0 0 { ia iu }
  begin lu 0> while
    la lu next-item to iu to ia to lu to la
    ia iu s\" \"\"" str=cs if true exit then
  repeat false ;

\ パターン変数の表
64 constant MAXVAR
32 constant VNLEN
create var-nm MAXVAR VNLEN * allot
create var-nl MAXVAR cells allot
create var-v MAXVAR cells allot
create var-u MAXVAR cells allot
variable nvar
create bvar-nm MAXVAR VNLEN * allot
create bvar-nl MAXVAR cells allot
create bvar-v MAXVAR cells allot
create bvar-u MAXVAR cells allot
variable bnvar
: var-find ( a u -- i | -1 )
  nvar @ 0 ?do
    2dup i VNLEN * var-nm +  i cells var-nl + @  str=cs if 2drop i unloop exit then
  loop
  2drop -1 ;
: var-new ( a u -- i )
  nvar @ MAXVAR >= abort" too many variables"
  VNLEN 1- min >r
  nvar @ VNLEN * var-nm + r@ move
  r> nvar @ cells var-nl + !
  nvar @  1 nvar +! ;
: var-put ( a u v und -- )
  >r >r 2dup var-find dup 0< if drop var-new else nip nip then
  r> over cells var-v + !
  r> swap cells var-u + ! ;
: var-get ( a u -- v und )
  var-find dup 0< if drop 0 0 exit then
  dup cells var-v + @ swap cells var-u + @ ;
: var-clear ( -- ) 0 nvar ! ;
: var-snap ( -- )
  nvar @ bnvar !
  var-nm bvar-nm MAXVAR VNLEN * move
  var-nl bvar-nl MAXVAR cells move
  var-v bvar-v MAXVAR cells move
  var-u bvar-u MAXVAR cells move ;
: var-restore ( -- )
  bnvar @ nvar !
  bvar-nm var-nm MAXVAR VNLEN * move
  bvar-nl var-nl MAXVAR cells move
  bvar-v var-v MAXVAR cells move
  bvar-u var-u MAXVAR cells move ;

\ ラベル表 (パスをまたいで残す)
4096 constant MAXLAB
create lab-na MAXLAB cells allot
create lab-nu MAXLAB cells allot
create lab-val MAXLAB cells allot
create lab-def MAXLAB cells allot
create lab-prev MAXLAB cells allot
create lab-hp MAXLAB cells allot
create lab-p1 MAXLAB cells allot
variable nlab
: lab-find ( a u -- i | -1 )
  nlab @ 0 ?do
    2dup i cells lab-na + @  i cells lab-nu + @  str=cs if 2drop i unloop exit then
  loop
  2drop -1 ;
: lab-add ( a u -- i )
  nlab @ MAXLAB >= abort" too many labels"
  hdup nlab @ cells lab-nu + !  nlab @ cells lab-na + !
  0 nlab @ cells lab-def + !  0 nlab @ cells lab-hp + !
  nlab @  1 nlab +! ;

\ ====================================================================
\ 式の評価器 (パターン行とアセンブリ行で共通)
\ ====================================================================

variable ex-a  variable ex-u  variable ep
variable patvars?        \ パターン変数を読めるか (binary_list / error_patterns)
variable sup             \ 抑止の深さ (短絡で読み飛ばす側)
variable undef-hit       \ 未定義のラベル・変数を読んだ
variable expr-missing    \ 因子のあるべきところに因子が無かった
variable expr-depth

defer expr

: ch ( off -- c ) ep @ + dup ex-u @ < if ex-a @ + c@ else drop 0 then ;
: cur ( -- c ) 0 ch ;
: adv ( n -- ) ep +! ;
: skipsp ( -- ) begin cur spc? while 1 adv repeat ;
: q? ( a u -- f )
  true -rot 0 ?do
    dup i + c@ uc  i ch uc <> if swap drop false swap then
  loop drop ;

: xerr ( a u -- ) sup @ if 2drop exit then diag ;
: undef! ( -- ) sup @ 0= if true undef-hit ! then ;
: sup+ ( -- ) 1 sup +! ;
: sup- ( -- ) -1 sup +! ;

\ 算術
: ashr ( n k -- n' )
  dup 63 > if drop 0< if -1 else 0 then exit then
  over 0< if >r invert r> rshift invert else rshift then ;
: shl ( n k -- n' ) dup 63 > if 2drop 0 exit then lshift ;
: tdiv ( a b -- q ) >r s>d r> sm/rem swap drop ;
: fldiv ( a b -- q ) >r s>d r> fm/mod swap drop ;
: flmod ( a b -- r ) >r s>d r> fm/mod drop ;
: nbit ( v -- n ) abs 0 swap begin dup while 1 rshift swap 1+ swap repeat drop ;
: divz ( -- ) s"  error - Division by 0 error." xerr ;
: ipow ( x t -- r )
  dup 0< if 2drop s"  error - Negative exponent in ** expression; result set to 0." xerr 0 exit then
  dup 1024 > if 2drop s"  error - Exponent exceeds maximum in ** expression; result set to 0." xerr 0 exit then
  1 swap 0 ?do over * loop nip ;
: sext ( x bits -- r )
  dup 0<= if 2drop 0 exit then
  dup 63 > if drop exit then
  { x bits }
  -1 bits lshift { m }
  x bits 1- ashr 1 and if x m invert and m or else x m invert and then ;

\ 数値
: pdec ( -- x ) 0 begin cur digc? while 10 * cur 48 - + 1 adv repeat ;
: phex ( -- x ) 0 begin cur xdig? while 4 lshift cur hexv + 1 adv repeat ;
: pbin ( -- x ) 0 begin cur dup 48 = swap 49 = or while 1 lshift cur 48 - + 1 adv repeat ;

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
  1 ch 92 <> 1 ch 0<> and 2 ch 39 = and 1 ch 128 < and if 1 ch 3 adv true exit then
  false ;

\ 語の読み取り
: symword ( -- a u )          \ シンボルの語 (swordchars)
  ex-a @ ep @ + 0
  cur digc? 0= cur swc? and if
    begin cur swc? while 1+ 1 adv repeat
  then ;
: labword ( -- a u )          \ ラベルの語 (lwordchars)
  ex-a @ ep @ + 0
  cur 46 = cur digc? 0= cur lwc? and or if
    begin cur lwc? while 1+ 1 adv repeat
  then ;
: varlen ( -- n )             \ パターン変数名の長さ (0 なら変数でない)
  cur lowc? 0= if 0 exit then
  1 begin dup ch dup lowc? swap digc? or over ch 95 = or while 1+ repeat ;
: patvarlen ( -- n )
  varlen dup 0= if exit then
  dup ch lwc? if drop 0 then ;

\ ラベルの値 (get_value 相当)
: label-value ( a u -- v )
  2dup lab-find dup 0>= if
    dup cells lab-def + @ if nip nip cells lab-val + @ exit then
  then
  { a u i }
  pass @ 1 = if
    i 0>= if i cells lab-hp + @ if i cells lab-prev + @ exit then then
    pass1-iter @ 0= if undef! pc @ exit then
  then
  size-mode @ if 0 exit then
  undef!
  sup @ 0= report? and if
    mb-reset s"  error - Label undefined: '" mb+ a u mb+ s" '" mb+ mb-get diag
  then
  0 ;

: pvar-value ( a u -- v )
  2dup var-get { a u v und }
  und if
    in-match @ 0= size-mode @ 0= and report? and sup @ 0= and if
      undef!
      mb-reset s"  error - Label undefined: variable '" mb+ a u mb+ s" ' contains undefined value" mb+
      mb-get diag
    then
  then
  v ;

: assign-var { a u } 0 0 0 { x cu prior }
  undef-hit @ to prior  false undef-hit !
  expr to x
  undef-hit @ to cu
  prior cu or undef-hit !
  sup @ 0= if a u x cu if -1 else 0 then var-put then
  x ;
: patvar-term { n } 0 { a }
  ex-a @ ep @ + to a
  n ch 58 = n 1+ ch 61 = and if
    n 2 + adv  a n assign-var
  else
    n adv a n pvar-value
  then ;

: factor1 ( -- x )
  skipsp
  cur 0= if 0 exit then
  cur [char] ( = if
    1 adv expr
    cur [char] ) = if 1 adv else s"  error - missing closing ')' in expression." xerr then
    skipsp exit
  then
  charlit? if skipsp exit then
  s" $$" q? if 2 adv in-binlist @ if pc-start @ else pc @ then skipsp exit then
  s" $." q? if 2 adv pc-end @ skipsp exit then
  cur [char] # = if
    1 adv symword sym-lookup if skipsp exit then
    s"  error - undefined symbol" xerr 0 skipsp exit
  then
  s" 0b" q? if 2 adv pbin skipsp exit then
  s" 0x" q? if 2 adv phex skipsp exit then
  s" not(" q? if
    4 adv expr skipsp
    cur [char] ) = if 1 adv else s"  error - missing closing ')' in not(...) expression." xerr then
    0= if 1 else 0 then skipsp exit
  then
  cur digc? if pdec skipsp exit then
  patvars? @ if
    patvarlen dup 0> if patvar-term skipsp exit then
    drop
  then
  labword dup 0> if label-value skipsp exit then
  2drop 0 skipsp ;

: b>i ( f -- 1|0 ) 1 and ;
: byte-extract ( x idx -- r )
  dup 0< if 2drop s"  error - negative byte-extract offset in *(expr, expr)." xerr 0 exit then
  dup 1000000 > if drop 1000000 then
  8 * ashr ;

: factor ( -- x )
  skipsp
  cur [char] - = if 1 adv recurse negate skipsp exit then
  cur [char] ~ = if 1 adv recurse invert skipsp exit then
  cur [char] @ = if 1 adv recurse nbit skipsp exit then
  cur [char] * = if
    1 ch [char] ( = if
      2 adv expr
      cur [char] , = if
        1 adv expr
        cur [char] ) = if 1 adv byte-extract
        else s"  error - missing ')' in *(expr, expr) expression." xerr 2drop 0 then
      else s"  error - missing ',' in *(expr, expr) expression." xerr drop 0 then
    else s"  error - expected '(' after '*' in *(expr,expr) expression." xerr 1 adv 0 then
    skipsp exit
  then
  ep @ >r factor1 ep @ r> = if true expr-missing ! then
  skipsp ;

: term0_0 ( -- x ) factor begin s" **" q? while 2 adv factor ipow repeat ;

: term0 ( -- x )
  term0_0
  begin
    cur 42 = 1 ch 42 <> and if 1 adv term0_0 * true else
    s" //" q? if 2 adv term0_0 dup 0= if 2drop divz 0 else fldiv then true else
    cur 47 = if 1 adv term0_0 dup 0= if 2drop divz 0 else tdiv then true else
    cur 37 = if 1 adv term0_0 dup 0= if 2drop divz 0 else flmod then true else
    false
    then then then then
  0= until ;

: term1 ( -- x )
  term0
  begin
    cur 43 = if 1 adv term0 + true else
    cur 45 = if 1 adv term0 - true else
    false
    then then
  0= until ;

: shiftl ( x t -- r )
  dup 0< if 2drop s"  error - negative shift count in << expression." xerr 0 exit then
  dup 65536 > if 2drop s"  error - shift count exceeds maximum in << expression." xerr 0 exit then
  shl ;
: shiftr ( x t -- r )
  dup 0< if 2drop s"  error - negative shift count in >> expression." xerr 0 exit then
  dup 65536 > if 2drop s"  error - shift count exceeds maximum in >> expression." xerr 0 exit then
  ashr ;
: term2 ( -- x )
  term1
  begin
    s" <<" q? if 2 adv term1 shiftl true else
    s" >>" q? if 2 adv term1 shiftr true else
    false
    then then
  0= until ;

: term3 ( -- x )
  term2
  begin cur 38 = 1 ch 38 <> and while 1 adv term2 and repeat ;
: term4 ( -- x )
  term3
  begin cur 124 = 1 ch 124 <> and while 1 adv term3 or repeat ;
: term5 ( -- x )
  term4
  begin cur 94 = while 1 adv term4 xor repeat ;

: sext-op? ( -- f )
  1 begin dup ch spc? while 1+ repeat ch dup digc? swap 40 = or ;
: term6 ( -- x )
  term5
  begin cur 39 = sext-op? and while 1 adv term5 sext repeat ;

: term7 ( -- x )
  term6
  begin
    s" <=" q? if 2 adv term6 <= b>i true else
    cur [char] < = if 1 adv term6 < b>i true else
    s" >=" q? if 2 adv term6 >= b>i true else
    cur [char] > = if 1 adv term6 > b>i true else
    s" ==" q? if 2 adv term6 = b>i true else
    s" !=" q? if 2 adv term6 <> b>i true else
    false
    then then then then then then
  0= until ;

: term9 ( -- x )
  term7
  begin s" &&" q? while
    2 adv
    dup 0= if drop sup+ term7 drop sup- 0
    else drop term7 0<> b>i then
  repeat ;
: term10 ( -- x )
  term9
  begin s" ||" q? while
    2 adv
    dup 0<> if drop sup+ term9 drop sup- 1
    else drop term9 0<> b>i then
  repeat ;

: colon-ternary? ( -- f ) cur [char] : = 1 ch [char] = <> and ;
: term11 ( -- x )
  term10
  cur [char] ? = if
    1 adv skipsp
    0= if
      sup+ recurse drop sup- skipsp
      colon-ternary? if 1 adv skipsp recurse else 0 then
    else
      recurse skipsp
      colon-ternary? if 1 adv skipsp sup+ recurse drop sup- then
    then
  then ;

: expr-top ( -- x ) skipsp term11 ;
' expr-top is expr

: eval-at { a u pos } 0 0 0 { oa ou op }
  ex-a @ to oa  ex-u @ to ou  ep @ to op
  a ex-a !  u ex-u !  pos ep !
  expr ep @
  oa ex-a !  ou ex-u !  op ep ! ;
: eval-fac { a u pos } 0 0 0 { oa ou op }
  ex-a @ to oa  ex-u @ to ou  ep @ to op
  a ex-a !  u ex-u !  pos ep !
  factor ep @
  oa ex-a !  ou ex-u !  op ep ! ;
: pat-eval ( a u pos -- x pos' )
  patvars? @ >r  true patvars? !
  eval-at
  r> patvars? ! ;
: asm-eval ( a u pos -- x pos' )
  patvars? @ >r  false patvars? !
  eval-at
  r> patvars? ! ;

: esc-limit { a u pos stop } 0 { dp }
  0 to dp
  u pos ?do
    a i + c@
    dup stop = dp 0= and if drop i unloop exit then
    dup [char] ( = over [char] [ = or if drop dp 1+ to dp else
      dup [char] ) = swap [char] ] = or if dp 0> if dp 1- to dp then then
    then
  loop
  u ;
: eval-esc { a u pos stop } 0 { lim }
  stop 0= if a u pos asm-eval exit then
  a u pos stop esc-limit to lim
  a lim pos asm-eval ;

\ ====================================================================
\ binary_list の評価 (makeobj) と error_patterns の評価
\ ====================================================================

4096 constant MAXOBJ
create objl MAXOBJ cells allot
variable nobj
: obj+ ( x -- ) nobj @ MAXOBJ >= abort" binary_list too long" objl nobj @ cells + !  1 nobj +! ;

create ebuf 131072 allot
variable eb-u
variable eb-hc
: eb-c ( c -- ) eb-u @ 131071 >= abort" binary_list too long" ebuf eb-u @ + c!  1 eb-u +! ;
: eb-s ( a u -- ) 0 ?do dup i + c@ eb-c loop drop ;

: skip-qstr { a u i0 } 0 { k }
  i0 1+ to k
  begin k u < while
    a k + c@ dup 92 = if drop k 2 + to k else
      34 = if k 1+ exit then
      k 1+ to k
    then
  repeat
  u ;

: at@@[? ( a u i -- f )
  dup 3 + 2 pick > if drop 2drop false exit then
  nip + 3 s" @@[" str=cs ;

defer ep-expand
: ep-scan { a u i0 } 0 0 0 { k dpt cm }
  i0 to k  1 to dpt  -1 to cm
  begin k u < dpt 0> and while
    a k + c@ 34 = if a u k skip-qstr to k else
      a k + c@
      dup [char] [ = if drop dpt 1+ to dpt  k 1+ to k else
      dup [char] ] = if drop dpt 1- to dpt  dpt 0> if k 1+ to k then else
      [char] , = dpt 1 = and cm 0< and if k to cm then
      k 1+ to k
      then then
    then
  repeat
  cm k ;      \ ( comma-pos end-pos )

: ep-rep { a u es cm ep-end } 0 0 0 0 0 0 { cnt ra ru st shc prior }
  undef-hit @ to prior
  false undef-hit !
  a es + cm es - 0 pat-eval drop to cnt
  undef-hit @ if 0 to cnt then
  prior undef-hit @ or undef-hit !
  cnt 16777216 > if s"  error - @@[n,...]: repeat count exceeds maximum." xerr 0 to cnt then
  cnt 0> if
    eb-u @ to st
    eb-hc @ to shc
    a cm 1+ + ep-end cm - 1- ep-expand
    shc eb-hc !
    true eb-hc !
    ebuf st + eb-u @ st - sdup to ru to ra
    st eb-u !
    cnt 0 ?do
      i 0> if 44 eb-c then
      ra ru eb-s
    loop
  then ;

: ep-expand-impl { a u } 0 0 0 0 0 { k es cm en e }
  begin k u < while
    a u k at@@[? if
      k 3 + to es
      a u es ep-scan to en to cm
      cm 0>= cm es >= and if
        a u es cm en ep-rep
        en 1+ to k
      else
        s"  error - @@[...]: missing ',' separating count and pattern." xerr
        64 eb-c 64 eb-c 91 eb-c true eb-hc !
        en to k
      then
    else
      a k + c@ 34 = if
        a u k skip-qstr to e
        a k + e k - eb-s
        true eb-hc !  e to k
      else
        a k + c@ eb-c true eb-hc !  k 1+ to k
      then
    then
  repeat ;
' ep-expand-impl is ep-expand

\ ---- @@[ ] の展開と %% の添字置換 ----
: expand-binlist ( a u -- a' u' empty? )
  0 eb-u !  false eb-hc !
  ep-expand
  ebuf eb-u @ sdup eb-hc @ 0= ;

create pbuf 131072 allot
variable pb-u
: pb-c ( c -- ) pb-u @ 131071 >= abort" binary_list too long" pbuf pb-u @ + c!  1 pb-u +! ;
: pct-replace { a u } 0 0 0 { k cnt e }
  0 pb-u !
  begin k u < while
    a k + c@ 34 = if
      a u k skip-qstr to e
      e k ?do a i + c@ pb-c loop
      e to k
    else
      k 1+ u < a k + c@ 37 = and if
        a k 1+ + c@ 37 = if
          cnt n>s 0 ?do dup i + c@ pb-c loop drop
          cnt 1+ to cnt  k 2 + to k
        else a k 1+ + c@ 48 = if 0 to cnt  k 2 + to k
        else 37 pb-c k 1+ to k then then
      else a k + c@ pb-c k 1+ to k then
    then
  repeat
  pbuf pb-u @ sdup ;

\ ---- makeobj ----
: skip-blanks ( a u i -- i' ) begin 2dup > while 2 pick over + c@ spc? while 1+ repeat then nip nip ;

: makeobj-run { a u } 0 0 0 0 0 { k semi drp x stp }
  begin k u < stp 0= and while
    a k + c@ 44 = if k 1+ to k else
      false to semi  false to drp
      a k + c@ 59 = if
        true to semi  k 1+ to k
        k u < if a k + c@ 59 = if true to drp  k 1+ to k then then
      then
      a u k skip-blanks 
      dup u < if a over + c@ 34 = else false then
      if
        \ テキストテンプレートは未対応: 読み飛ばして終わる
        drop true to stp
      else
        drop
        a u k pat-eval to k to x
        pass @ 1 = if false undef-hit ! then
        drp 0= if semi 0= x 0<> or if x obj+ then then
        k u < if a k + c@ 44 = if k 1+ to k else true to stp then else true to stp then
      then
    then
  repeat ;

: makeobj ( a u -- )
  0 nobj !
  expand-binlist if 2drop exit then
  pct-replace
  undef-hit @ >r  false undef-hit !
  pass @ 1 = force-size @ or size-mode !
  true in-binlist !
  makeobj-run
  false in-binlist !
  false size-mode !
  undef-hit @ r> or undef-hit ! ;

\ ---- エラー表と error_patterns ----
16 constant MAXERR
create err-a MAXERR cells allot
create err-u MAXERR cells allot
: err-set ( a u i -- ) >r sdup  r@ cells err-u + !  r> cells err-a + ! ;
: err-init ( -- )
  MAXERR 0 ?do 0 i cells err-u + !  0 i cells err-a + ! loop
  s" " 0 err-set
  s" Invalid syntax." 1 err-set
  s" Address out of range." 2 err-set
  s" Value out of range." 3 err-set
  s" Register out of range." 5 err-set
  s" Port number out of range." 6 err-set ;

: no-blank? ( a u -- f ) 0 ?do dup i + c@ 32 <> if drop true unloop exit then loop drop false ;

: error-eval { a u } 0 0 0 0 0 0 { k trig cu c t b }
  a u no-blank? 0= if false exit then
  false to trig
  begin k u < while
    a k + c@ 44 = if k 1+ to k else
      k to b
      undef-hit @ >r  false undef-hit !
      a u k pat-eval to k to c
      undef-hit @ to cu
      k u < if a k + c@ 59 = else false then
      if
        a u k 1+ pat-eval to k to t
      else
        a u k pat-eval to k to t
      then
      r> undef-hit @ or undef-hit !
      k b <= if u to k else
        c 0<> cu 0= and report? and if
          s" Line " etype line-no @ .en s"  Error code " etype t .en s"  " etype
          t 0>= t MAXERR < and if
            t cells err-a + @ t cells err-u + @ etype
          then
          s" : " etype ecr
          true to trig  true had-error !
        then
      then
    then
  repeat
  trig ;

\ ====================================================================
\ パターンファイルの読み込み
\ ====================================================================

: s! ( a u addr -- ) >r swap r> 2! ;
: s@ ( addr -- a u ) 2@ swap ;

\ ---- 行の表 (継続行を結んだ形) ----
variable lt-tab  variable lt-n  variable lt-cap
: lt-add ( a u -- )
  lt-n @ lt-cap @ >= abort" too many lines"
  lt-n @ 16 * lt-tab @ + s!  1 lt-n +! ;
: lt@ ( i -- a u ) 16 * lt-tab @ + s@ ;

variable lp  variable le
: rd-line ( -- a u true | false )
  lp @ le @ >= if false exit then
  lp @
  begin lp @ le @ < while
    lp @ c@ dup 10 = swap 13 = or if
      lp @ over -
      lp @ c@ 13 = lp @ 1+ le @ < and if lp @ 1+ c@ 10 = if 1 lp +! then then
      1 lp +!
      true exit
    then
    1 lp +!
  repeat
  lp @ over - true ;
: count-lines ( a u -- n ) 0 -rot bounds ?do i c@ dup 10 = swap 13 = or if 1+ then loop 1+ ;

create pend 262144 allot
variable pend-u
variable pend-open
: pend+ ( a u -- ) pend pend-u @ + swap dup pend-u +! move ;
: ends-bs? ( a u -- f ) dup 0> if + 1- c@ 92 = else 2drop false then ;

: load-lines ( fa fu -- tab n )
  slurp-file
  2dup count-lines dup lt-cap !  16 * allocate throw lt-tab !
  0 lt-n !  0 pend-u !  false pend-open !
  over + le !  lp !
  begin rd-line while
    2dup ends-bs? if
      1- pend+  s" " lt-add  true pend-open !
    else
      pend-u @ if
        pend+ pend pend-u @ sdup lt-add  0 pend-u !
      else lt-add then
      false pend-open !
    then
  repeat
  pend-open @ if
    pend pend-u @ sdup lt-n @ 1- 16 * lt-tab @ + s!  0 pend-u !
  then
  lt-tab @ lt-n @ ;

\ ---- コメント除去 ----
create cbuf 131072 allot
variable cb-u
: cb-c ( c -- ) cb-u @ 131071 >= if drop exit then cbuf cb-u @ + c!  1 cb-u +! ;
: cb-s ( a u -- ) 0 ?do dup i + c@ cb-c loop drop ;

: quoted-span { a u i } 0 0 { c j }
  a i + c@ to c
  c 92 = i 1+ u < and if a i 1+ + c@ 34 = if 2 exit then then
  c 39 = i 2 + u < and if a i 1+ + c@ 34 = a i 2 + + c@ 39 = and if 3 exit then then
  c 34 <> if 0 exit then
  i 1+ to j
  begin j u < while
    a j + c@ 92 = j 1+ u < and if j 2 + to j else
      a j + c@ 34 = if j 1+ i - exit then
      j 1+ to j
    then
  repeat
  0 ;

: at2? ( a u k c1 c2 -- f )      \ a[k]==c1 && a[k+1]==c2
  { a u k c1 c2 }
  k 1+ u < if a k + c@ c1 = a k 1+ + c@ c2 = and else false then ;

: rm-comment { a u inc } 0 0 { k n }
  0 cb-u !
  begin k u < while
    inc if
      a u k 42 47 at2? if false to inc  k 2 + to k else k 1+ to k then
    else
      a u k quoted-span to n
      n 0> if
        a k + n cb-s  k n + to k
      else
        a u k 47 42 at2? if true to inc  k 2 + to k
        else a k + c@ cb-c  k 1+ to k then
      then
    then
  repeat
  cbuf cb-u @ inc ;

create rbuf 131072 allot
variable rb-u
: rb-c ( c -- ) rb-u @ 131071 >= if drop exit then rbuf rb-u @ + c!  1 rb-u +! ;
: ws? ( c -- f ) dup 32 = over 9 = or over 10 = or swap 13 = or ;
: reduce-spaces ( a u -- a' u' )
  0 rb-u !  false { inws } 
  0 ?do
    dup i + c@ dup ws? if
      drop inws 0= if 32 rb-c then  true to inws
    else rb-c  false to inws then
  loop
  drop rbuf rb-u @ ;

\ ---- 行の表: パターン行 ----
30000 constant MAXROWS
10 cells constant ROWSZ
create prows MAXROWS ROWSZ * allot
variable nrows
: row ( i -- a ) ROWSZ * prows + ;
: rf0 ( i -- a u ) row s@ ;
: rf1 ( i -- a u ) row 2 cells + s@ ;
: rf2 ( i -- a u ) row 4 cells + s@ ;
: rkind ( i -- a ) row 6 cells + ;
: raux ( i -- a ) row 7 cells + ;
: raux2 ( i -- a ) row 8 cells + ;
: rgrp ( i -- a ) row 9 cells + ;

create fld-a 8 cells allot
create fld-u 8 cells allot
variable nfld
: fld@ ( i -- a u )
  dup nfld @ < if cells >r fld-a r@ + @  fld-u r> + @ else drop 0 0 then ;

: next-field { a u idx } 0 0 0 0 { st en q f }
  begin idx u < while a idx + c@ spc? while idx 1+ to idx repeat then
  idx u >= if a 0 idx exit then
  idx to st  u to en  u to f
  begin idx u < while
    a u idx quoted-span to q
    q 0> if idx q + to idx else
      a u idx 58 58 at2? if idx to en  idx 2 + to f  u to idx
      else idx 1+ to idx then
    then
  repeat
  a st + en st - -trailing  f ;
: split-fields { a u } 0 { idx }
  0 nfld !
  begin
    a u idx next-field to idx
    nfld @ 6 < if nfld @ cells fld-u + !  nfld @ cells fld-a + !  1 nfld +! else 2drop then
    u idx <=
  until ;

: count-sub { a u } 0 0 { n k }
  begin k 1+ u < while
    a k + 2 s" [[" str=cs if n 1+ to n  k 2 + to k else k 1+ to k then
  repeat
  n ;

create dtmp 128 allot
: known-dir? ( a u -- f )
  dup 100 > if 2drop false exit then
  32 dtmp c!  dtmp 1+ swap dup >r move  32 dtmp r@ 1+ + c!
  s"  .setsym .clearsym .padding .bits .symbolc .vliw .check .clrcheck .reloc .clrreloc .map .free .passthru .eol .textmode .enum .clrenum .error .echo .unordered .elftype .elfmachine .elfclass .elfrela .elfwidth .elfextern .elfdwarf .elfheader .elfsection .elffield .elfpcguess .elfrelax .elfanchor .elfresolve .elfbuiltin .elfextra .elfdiff .elfencode .elfrinfo .elfunit .elflink .elfgroup .elfcfi .elfcfiinit .elfcfireg .elfunaligned "
  dtmp r> 2 + search nip nip ;

: all-blank? ( a u -- f ) no-blank? 0= ;

: unquote { a u } 0 0 { k st }
  begin k u < a k + c@ 34 <> and while k 1+ to k repeat
  k u >= if a 0 exit then
  k 1+ to st  st to k
  begin k u < a k + c@ 34 <> and while k 1+ to k repeat
  a st + k st - ;

: dir-len ( a u -- n )
  begin dup 0> while 2dup + 1- c@ 47 = if nip exit then 1- repeat nip ;

create pathbuf 4096 allot
: join-path ( da du fa fu -- a u )
  dup 0> if over c@ 47 = else false then if 2swap 2drop exit then
  { da du fa fu }
  da pathbuf du move
  fa pathbuf du + fu move
  pathbuf du fu + ;

: starts-open? ( a u -- f )
  begin dup 0> while over c@ spc? while 1 /string repeat then
  dup 2 >= if drop dup c@ 47 = swap 1+ c@ 42 = and else 2drop false then ;

\ ---- 1 行をパターン行として登録 ----
: nonempty-field? ( a u -- f ) all-blank? 0= ;

: add-sym-row { r } 0 0 0 0 { ka ku va vu }
  r rf1 nonempty-field? if r rf1 to ku to ka  r rf2 to vu to va
  else r rf2 to ku to ka  0 to vu  0 to va then
  va vu nonempty-field? if va c@ dup 34 = swap 91 = or if 6 r rkind ! exit then then
  vu 0> va vu nonempty-field? and if
    0 pass !
    va vu 0 pat-eval drop
  else 0 then
  { v }
  ka ku v sym-define
  ka ku sym-find r raux !
  v r raux2 ! ;

: add-check-row { r } 0 0 0 0 { na nu la lu }
  r rf1 nonempty-field? if r rf1 to nu to na  r rf2 trim to lu to la
  else r rf2 trim to nu to na  0 to la  0 to lu then
  la lu upper-copy sdup to lu to la
  na nu chk-slot drop
  la r raux !  lu r raux2 ! ;

: add-row ( -- )
  nrows @ MAXROWS >= abort" too many pattern prows"
  0 fld@
  nfld @ 1 = if 0 0 0 0 else
    nfld @ 2 = if 0 0 1 fld@ else 1 fld@ 2 fld@ then then
  { f0a f0u f1a f1u f2a f2u } 0 0 { r code }
  f0a f0u all-blank? f1a f1u all-blank? and f2a f2u all-blank? and if exit then
  nrows @ row ROWSZ erase
  f0a f0u sdup nrows @ row s!
  f1a f1u sdup nrows @ row 2 cells + s!
  f2a f2u sdup nrows @ row 4 cells + s!
  nrows @ to r
  f0a f0u known-dir? if
    f0a f0u s" .setsym" str=cs if 1 r rkind ! r add-sym-row else
    f0a f0u s" .check" str=cs if 2 r rkind ! r add-check-row else
    f0a f0u s" .clrcheck" str=cs if 3 r rkind ! else
    f0a f0u s" .padding" str=cs if
      4 r rkind !
      0 pass !
      f2a f2u nonempty-field? if f2a f2u 0 pat-eval drop padding-v !
      else f1a f1u nonempty-field? if f1a f1u 0 pat-eval drop padding-v ! then then
    else
    f0a f0u s" .error" str=cs if
      5 r rkind !
      0 pass !
      f1a f1u 0 pat-eval drop to code
      f2a f2u unquote code 0>= code MAXERR < and if code err-set else 2drop then
    else 6 r rkind ! then then then then then
  else
    0 r rkind !
    f0a f0u count-sub r rgrp !
  then
  1 nrows +! ;

variable pat-depth
variable pat-dir-a  variable pat-dir-u
defer read-pattern

: lstrip ( a u -- a' u' ) begin dup 0> while over c@ spc? while 1 /string repeat then ;
: tl@ ( tab i -- a u ) 16 * + s@ ;

: do-include ( a u -- )
  unquote dup 0= if
    2drop s"  error - .INCLUDE directive has no filename." etype ecr true had-error ! exit
  then
  sdup pat-dir-a @ pat-dir-u @ 2swap join-path sdup
  1 pat-depth +!  read-pattern  -1 pat-depth +! ;

: pat-line ( a u -- )
  reduce-spaces { a u }
  a u lstrip { sa su }
  su 8 >= if sa 8 s" .INCLUDE" str=ci else false then
  if sa 8 + su 8 - do-include exit then
  a u split-fields add-row ;

: read-pattern-impl { fa fu } 0 0 0 0 0 0 0 0 0 0 0 { tab n li inc legacy was bare treat rc oda odu }
  pat-dir-a @ to oda  pat-dir-u @ to odu
  fa fa fu dir-len pat-dir-u !  pat-dir-a !
  fa fu load-lines to n to tab
  n 1+ cells allocate throw to rc
  false rc n cells + !
  n 0 ?do
    n 1- i - to li
    tab li tl@ s" */" search nip nip  li 1+ cells rc + @ or  li cells rc + !
  loop
  false to inc  false to legacy
  n 0 ?do
    i to li
    inc to was
    tab li tl@ inc rm-comment to inc
    inc 0= if false to legacy
    else was 0= if
      tab li tl@ starts-open? to bare
      legacy bare and if true to treat
      else
        li 1+ n < if tab li 1+ tl@ starts-open? else false then
        li 1+ cells rc + @ 0= or to treat
      then
      treat if false to inc  bare to legacy else false to legacy then
    then then
    pat-line
  loop
  rc free throw  tab free throw
  oda pat-dir-a !  odu pat-dir-u ! ;
' read-pattern-impl is read-pattern

\ ====================================================================
\ 命令の書式の照合
\ ====================================================================

variable ms-a  variable ms-u        \ ソース行 (lin)
variable mt-a  variable mt-u        \ パターン (括弧処理後)
variable si  variable ti
variable n-expr  variable n-lit  variable n-sym  variable p-alnum
variable s-sp  variable t-sp  variable wbrk  variable ca  variable cb

: sc ( off -- c ) si @ + dup ms-u @ < if ms-a @ + c@ else drop 0 then ;
: tcc ( off -- c ) ti @ + dup mt-u @ < if mt-a @ + c@ else drop 0 then ;
: sskip ( -- ) begin 0 sc spc? while 1 si +! repeat ;
: tskip ( -- ) begin 0 tcc spc? while 1 ti +! repeat ;
: expects-expr? ( off -- f ) begin dup tcc spc? while 1+ repeat tcc 33 = ;

: vname { off } 0 { n }
  off tcc lowc? 0= if 0 exit then
  1 to n
  begin off n + tcc dup lowc? over digc? or swap 95 = or while n 1+ to n repeat
  n ;

: sword-end ( -- n )
  0 sc digc? 0= 0 sc swc? and 0= if 0 exit then
  1 begin dup sc swc? while 1+ repeat ;

: sym-prefix { wa wu } 0 { k }
  wa wu sym-find 0>= if wu exit then
  wu 1- to k
  begin k 0> while
    wa k + c@ corec? 0= if
      wa k sym-find 0>= if k exit then
    then
    k 1- to k
  repeat
  0 ;

variable c-n  variable c-pa  variable c-prev  variable c-wl  variable c-ok
variable c-fl  variable c-la  variable c-lu  variable c-has  variable c-omit

: best-prefix { la lu } 0 0 0 { ia iu best }
  begin lu 0> while
    la lu next-item to iu to ia to lu to la
    iu 0> iu best > and if
      c-prev @ iu + ms-u @ <= if
        ms-a @ c-prev @ + iu upper-copy ia iu str=cs if iu to best then
      then
    then
  repeat
  best ;

: sym-cap ( -- flag )
  0 vname dup c-n !  0= if false exit then
  mt-a @ ti @ + c-pa !
  c-n @ ti +!
  si @ c-prev !
  false p-alnum !
  c-pa @ c-n @ chk-get if true c-has ! c-lu ! c-la ! else false c-has ! 0 c-la ! 0 c-lu ! then
  c-has @ if c-la @ c-lu @ list-omit? else false then c-omit !
  sword-end c-wl !
  ms-a @ c-prev @ + c-wl @ sym-prefix c-fl !
  c-fl @ 0> c-ok !
  c-ok @ c-has @ and if
    ms-a @ c-prev @ + c-fl @ upper-copy c-la @ c-lu @ list-has? 0= if false c-ok ! then
  then
  c-ok @ 0= c-has @ and if
    c-la @ c-lu @ best-prefix dup 0> if
      c-fl !
      ms-a @ c-prev @ + c-fl @ sym-find 0>= c-ok !
    else drop then
  then
  c-ok @ if
    c-prev @ c-fl @ + si !
    ms-a @ c-prev @ + c-fl @ sym-lookup drop   \ ( v )
    c-pa @ c-n @ rot 0 var-put
    1 n-sym +!  true exit
  then
  c-omit @ if
    c-prev @ si !
    c-pa @ c-n @ 0 0 var-put
    1 n-sym +!  true exit
  then
  false ;

: take-stop ( off -- stopchar )
  begin dup tcc spc? while 1+ repeat
  dup tcc 92 = if 1+ dup tcc swap 1+ ti +! else ti +! 0 then ;

: cap-expr { kind } 0 0 0 0 0 0 0 { n na stop cu pr st x }
  0 vname to n
  n 0= if false exit then
  mt-a @ ti @ + to na
  n ti +!
  kind 0= if 0 take-stop to stop then
  undef-hit @ to pr  false undef-hit !  false expr-missing !
  si @ to st
  kind 0= if ms-a @ ms-u @ si @ stop eval-esc else ms-a @ ms-u @ si @ eval-fac then
  si !  to x
  undef-hit @ to cu
  pr cu or undef-hit !
  na n x cu if -1 else 0 then var-put
  expr-missing @ if false exit then
  stop 0<> if 0 sc stop = if 1 si +! then then
  true ;

: step-bs ( -- code )
  1 ti +!
  0 tcc cb @ = ti @ mt-u @ < and 0= if 1 exit then
  0 tcc alnc? p-alnum @ and wbrk @ and if 1 exit then
  0 tcc alnc? { la }
  1 ti +!  1 si +!  1 n-lit +!  la p-alnum !
  0 ;
: step-cap ( -- code )
  ca @ cb @ uc <> if 1 exit then
  p-alnum @ wbrk @ and if 1 exit then
  1 si +!  1 ti +!  1 n-lit +!  true p-alnum !
  0 ;
: step-lit ( -- code )
  ca @ cb @ <> if 1 exit then
  ca @ alnc? p-alnum @ and wbrk @ and if 1 exit then
  1 ti +!  1 si +!  1 n-lit +!  ca @ alnc? p-alnum !
  0 ;
: step-plus ( -- code )
  1 ti +!  1 n-lit +!  false p-alnum !
  0 ;
: step-bang ( -- code )
  1 n-expr +!
  false p-alnum !
  1 ti +!
  0 tcc
  dup 0= if drop 1 exit then
  dup [char] F = over [char] D = or over [char] Q = or if drop 1 exit then
  dup [char] E = over [char] Y = or over [char] S = or if drop 1 exit then
  dup [char] L = if drop 1 ti +! 0 cap-expr if 0 else 1 then exit then
  dup [char] ! = if drop 1 ti +! 1 cap-expr if 0 else 1 then exit then
  drop 0 cap-expr if 0 else 1 then ;
: step-sym ( -- code ) sym-cap if 0 else 1 then ;

: step ( -- code )
  0 sc spc? s-sp !  0 tcc spc? t-sp !
  sskip tskip
  s-sp @ t-sp @ 0= and wbrk !
  0 sc cb !  0 tcc ca !
  ca @ 0= cb @ 0= and if 2 exit then
  ca @ 92 = if step-bs exit then
  ca @ capc? if step-cap exit then
  ca @ 33 = if step-bang exit then
  ca @ lowc? if step-sym exit then
  ca @ 43 = cb @ 45 = and 1 expects-expr? and if step-plus exit then
  step-lit ;

: match1 ( -- flag )
  0 si !  0 ti !  0 n-expr !  0 n-lit !  0 n-sym !  false p-alnum !
  sskip tskip
  begin step dup 0= while drop repeat
  2 = ;

\ ---- [[ ]] の組み合わせ ----
create gop 24 cells allot
create gcl 24 cells allot
create gstk 24 cells allot
create tbuf 8192 allot
variable tb-u
: tb-c ( c -- ) tb-u @ 8191 >= if drop exit then tbuf tb-u @ + c!  1 tb-u +! ;

: find-groups { a u } 0 0 0 0 { k serial sp ser }
  begin k 1+ u < while
    a u k 91 91 at2? if
      serial 1+ to serial
      serial 24 < if
        k gop serial cells + !
        serial gstk sp cells + !  sp 1+ to sp
      then
      k 2 + to k
    else
      a u k 93 93 at2? if
        sp 0> if
          sp 1- to sp  gstk sp cells + @ to ser
          k gcl ser cells + !
        then
        k 2 + to k
      else k 1+ to k then
    then
  repeat ;

: build-text { a u mask cnt } 0 0 { k rm }
  0 tb-u !
  begin k u < while
    false to rm
    cnt 1+ 1 ?do
      mask 1 cnt i - lshift and if
        gop i cells + @ k <= gcl i cells + @ 1+ k >= and if true to rm then
      then
    loop
    rm if k 1+ to k else
      a u k 91 91 at2? if k 2 + to k else
      a u k 93 93 at2? if 32 tb-c k 2 + to k else
      a k + c@ tb-c k 1+ to k then then
    then
  repeat
  tbuf tb-u @ ;

: popcnt ( n -- k ) 0 swap begin dup while dup 1 and rot + swap 1 rshift repeat drop ;

: match-groups { a u cnt } 0 0 { pop mask }
  cnt 20 > if 20 to cnt then
  a u find-groups
  cnt 1+ 0 ?do
    i to pop
    1 cnt lshift 1- to mask
    begin mask 0>= while
      mask popcnt pop = if
        a u mask cnt build-text mt-u ! mt-a !
        var-clear
        match1 if true unloop exit then
      then
      mask 1- to mask
    repeat
  loop
  false ;

: match-row ( row -- flag )
  dup rgrp @ ?dup if
    >r rf0 r> match-groups
  else
    rf0 mt-u ! mt-a !  var-clear
    match1
  then ;

\ ====================================================================
\ ソース 1 行の処理
\ ====================================================================

create nbuf 131072 allot
variable nb-u
: nb-c ( c -- ) nb-u @ 131071 >= if drop exit then nbuf nb-u @ + c!  1 nb-u +! ;
create sbuf 131072 allot
variable sb-u
: sb-c ( c -- ) sb-u @ 131071 >= if drop exit then sbuf sb-u @ + c!  1 sb-u +! ;

\ 文字定数 'c' の終わり (skip_squote_literal)
: skip-squote { a u i } 0 0 0 { j k dg }
  i 1+ to j
  j u < if
    a j + c@ 92 = j 1+ u < and if
      a j 1+ + c@ uc 88 = if
        j 2 + to k
        begin k u < dg 2 < and if a k + c@ xdig? else false then while k 1+ to k dg 1+ to dg repeat
        k u < if a k + c@ 39 = if k 1+ exit then then
      else
        j 2 + u < if a j 2 + + c@ 39 = if j 3 + exit then then
      then
    else
      j 1+ u < if
        a j 1+ + c@ 39 = a j + c@ 128 < and if j 2 + exit then
      then
    then
  then
  i 1+ ;

: normalize-ws { a u } 0 0 0 { k inq inws }
  0 nb-u !
  begin k u < while
    inq if
      a k + c@ 92 = k 1+ u < and if
        a k + c@ nb-c  a k 1+ + c@ nb-c  k 2 + to k
      else
        a k + c@ dup nb-c  34 = if false to inq then
        k 1+ to k
      then
    else
      a k + c@ 34 = if
        true to inq  false to inws  34 nb-c  k 1+ to k
      else
        a k + c@ 39 = if
          a u k skip-squote { j }
          a k + j k - 0 ?do dup i + c@ nb-c loop drop
          false to inws  j to k
        else
          a k + c@ ws? if
            inws 0= if 32 nb-c  true to inws then
          else
            a k + c@ nb-c  false to inws
          then
          k 1+ to k
        then
      then
    then
  repeat
  nbuf nb-u @ ;

: split-comment { a u } 0 0 { k inq }
  0 sb-u !
  begin k u < while
    a k + c@ 92 = inq and k 1+ u < and if
      a k + c@ sb-c  a k 1+ + c@ sb-c  k 2 + to k
    else
      a k + c@ 92 = inq 0= and k 1+ u < and if
        a k 1+ + c@ 59 = if 59 sb-c  k 2 + to k else 92 sb-c  k 1+ to k then
      else
        a k + c@ 34 = if
          inq 0= to inq  34 sb-c  k 1+ to k
        else
          a k + c@ 39 = inq 0= and if
            a u k skip-squote { j }
            a k + j k - 0 ?do dup i + c@ sb-c loop drop
            j to k
          else
            a k + c@ 59 = inq 0= and if u to k
            else a k + c@ sb-c  k 1+ to k then
          then
        then
      then
    then
  repeat
  sbuf sb-u @ -trailing ;

\ ---- 出力バッファ (-b) ----
variable obuf  variable ocap  variable omax
: out-init ( -- )
  1048576 ocap !  ocap @ allocate throw obuf !  0 omax !
  obuf @ ocap @ padding-v @ 255 and fill ;
: out-grow ( need -- )
  dup ocap @ <= if drop exit then
  ocap @ { old }
  begin dup ocap @ > while ocap @ 2* ocap ! repeat drop
  ocap @ 1073741824 > abort" output too large"
  obuf @ ocap @ resize throw obuf !
  obuf @ old + ocap @ old - padding-v @ 255 and fill ;
: outbin ( pos val -- )
  pass @ 2 <> if 2drop exit then
  over 0< if 2drop exit then
  255 and swap dup 1+ out-grow
  dup 1+ omax @ max omax !
  obuf @ + c! ;

\ ---- ラベルの定義 ----
create lab-equ MAXLAB cells allot
64 constant MAXKEYS
create key-a MAXKEYS cells allot
create key-u MAXKEYS cells allot
variable nkeys
variable lab-err-seen

: key-seen? ( a u -- f )
  nkeys @ 0 ?do
    2dup i cells key-a + @ i cells key-u + @ str=cs if 2drop true unloop exit then
  loop
  2drop false ;
: key-add ( a u -- )
  nkeys @ MAXKEYS >= if 2drop exit then
  hdup nkeys @ cells key-u + !  nkeys @ cells key-a + !  1 nkeys +! ;
: fdiag ( a u -- )
  etype s"   [" etype src-name-a @ src-name-u @ etype s" :" etype line-no @ .en s" ]" etype ecr
  true had-error !  true lab-err-seen ! ;
: label-error ( -- )          \ メッセージは mbuf に組み立て済み。同じ原因は 1 回だけ出す
  mb-get key-seen? if exit then
  mb-get key-add
  mb-get fdiag ;

: lab-define ( a u v equ? -- ok )
  { a u v eq } 0 { i }
  a u lab-find to i
  pass @ 2 = if
    i 0< if
      mb-reset s"  error - label '" mb+ a u mb+ s" ' not defined in pass 1." mb+ label-error
      false exit
    then
  else
    i 0>= if i cells lab-def + @ if
      mb-reset s"  error - label '" mb+ a u mb+ s" ' is already defined." mb+ label-error
      false exit
    then then
  then
  a u sym-find 0>= if
    mb-reset s"  error - '" mb+ a u mb+ s" ' is a pattern file symbol." mb+ label-error
    false exit
  then
  i 0< if a u lab-add to i then
  v i cells lab-val + !
  true i cells lab-def + !
  eq if -1 else 0 then i cells lab-equ + !
  true ;

: lab-reset-iter ( -- )
  nlab @ 0 ?do
    i cells lab-def + @ if
      i cells lab-val + @ i cells lab-prev + !  true i cells lab-hp + !
    then
    false i cells lab-def + !
  loop ;
: lab-converged? ( -- f )
  nlab @ 0 ?do
    i cells lab-def + @ if
      i cells lab-hp + @ 0= if false unloop exit then
      i cells lab-val + @ i cells lab-prev + @ <> if false unloop exit then
    else
      i cells lab-hp + @ if false unloop exit then
    then
  loop true ;
: lab-snap ( -- ) nlab @ 0 ?do i cells lab-val + @ i cells lab-p1 + ! loop ;

\ ---- 指令の引数の後ろの余りを検査する ----
: rest-of ( a u idx -- a' u' ) over min /string ;
variable dnm-a  variable dnm-u
: dnm! ( a u -- ) dnm-u ! dnm-a ! ;
: dir-trailing ( a u idx -- stop? )
  rest-of trim { ra ru }
  ru 0= if false exit then
  mb-reset s"  error - " mb+ dnm-a @ dnm-u @ mb+
  s" : unexpected text after the argument: '" mb+ ra ru mb+ s" '." mb+
  mb-get diag true ;

: skipsp-s ( a u -- a' u' ) lstrip ;

\ 引数式を評価して (値 終わりの位置 未定義?) を返す
: eval-arg ( a u -- v idx undef? )
  false undef-hit !
  0 asm-eval undef-hit @ ;

: token ( a u -- ra ru ta tu )
  lstrip { a u } 0 { k }
  begin k u < if a k + c@ 32 <> else false then while k 1+ to k repeat
  a k + u k -  a k ;

: do-equ ( na nu ra ru -- )
  trim { na nu ea eu } 0 0 { v pe }
  mb-reset s" .EQU '" mb+ na nu mb+ s" '" mb+ mb-get sdup dnm!
  false undef-hit !
  pass @ 1 = size-mode !
  ea eu 0 asm-eval to pe to v
  false size-mode !
  undef-hit @ if
    mb-reset s"  error - " mb+ dnm-a @ dnm-u @ mb+ s" : expression contains undefined label." mb+
    mb-get diag
  then
  ea eu pe dir-trailing drop
  na nu v true lab-define drop ;

\ 行頭の label: / label: .equ を処理して、残りの行を返す
: label-proc { a u } 0 0 0 { k nl lend }
  u 0= if a u exit then
  a c@ 46 = a c@ digc? 0= a c@ lwc? and or 0= if a u exit then
  1 to k
  begin k u < if a k + c@ lwc? else false then while k 1+ to k repeat
  k to nl
  k u < if a k + c@ 58 = else false then 0= if a u exit then
  k 1+ u < if a k 1+ + c@ 61 = else false then if a u exit then
  nl 1+ to lend
  a lend + u lend - token { ra ru ta tu }
  ta tu s" .EQU" str=ci if
    a nl ra ru do-equ
    a 0 exit
  then
  a nl pc @ false lab-define 0= if a 0 exit then
  a lend + u lend - ;

\ ---- 指令 ----
: put-byte ( v -- ) pc @ swap outbin  1 pc +! ;

: comma-p? ( a u ep -- f )
  { a u e } e 1+ u < if a e + c@ 44 = a e 1+ + c@ uc 80 = and else false then ;

: dir-org ( a u -- )
  2dup eval-arg { v ep un }
  2dup ep comma-p? { fill }
  ep fill if 2 + then dir-trailing if exit then
  un if s"  error - .ORG argument contains undefined label." diag exit then
  v 0< if
    mb-reset s"  error - .ORG address must be non-negative, got " mb+ v mb-n s" ." mb+ mb-get diag exit
  then
  fill v pc @ > and if
    v pc @ - 0 ?do pc @ i + padding-v @ outbin loop
  then
  v pc ! ;

: align-pad ( -- )
  align-v @ 0> if
    pc @ align-v @ mod dup if align-v @ swap - pc +! else drop then
  then ;

: dir-align ( a u -- )
  dup 0= if 2drop align-pad exit then
  2dup eval-arg { v ep un }
  ep dir-trailing if exit then
  un if s"  error - .ALIGN argument contains undefined label." diag exit then
  v 0<= if
    mb-reset s"  error - .ALIGN requires a positive value, got " mb+ v mb-n s" ." mb+ mb-get diag exit
  then
  v align-v !  align-pad ;

: eval-count { a u } 0 0 0 { v ep un }
  a u eval-arg to un to ep to v
  a u ep dir-trailing if 0 false exit then
  un if
    mb-reset s"  error - " mb+ dnm-a @ dnm-u @ mb+ s"  argument contains undefined label." mb+ mb-get diag
    0 false exit
  then
  v 0< if
    mb-reset s"  error - " mb+ dnm-a @ dnm-u @ mb+ s"  requires a non-negative count, got " mb+ v mb-n s" ." mb+
    mb-get diag 0 false exit
  then
  v true ;
: dir-zero ( a u -- ) eval-count if 0 ?do 0 put-byte loop else drop then ;
: dir-res ( a u mul -- ) >r eval-count if r> * pc +! else r> 2drop then ;

: hex-escape { a u k } 0 0 { v n }
  begin k u < n 2 < and if a k + c@ xdig? else false then while
    v 16 * a k + c@ hexv + to v  k 1+ to k  n 1+ to n
  repeat
  v k n 0> ;

: ascii-str { a u } 0 0 0 { k ok v }
  u 0= if false exit then
  a c@ 34 <> if false exit then
  1 to k  true to ok
  begin ok if k u < if a k + c@ 34 <> else false then else false then while
    a k + c@ 92 = k 1+ u < and if
      a k 1+ + c@
      dup 48 = if drop 0 put-byte k 2 + to k else
      dup [char] t = if drop 9 put-byte k 2 + to k else
      dup [char] n = if drop 10 put-byte k 2 + to k else
      dup [char] r = if drop 13 put-byte k 2 + to k else
      dup 92 = if drop 92 put-byte k 2 + to k else
      dup 34 = if drop 34 put-byte k 2 + to k else
      uc 88 = if
        a u k 2 + hex-escape
        if to k put-byte else
          drop drop s"  error - '\x' escape requires at least one hex digit." diag false to ok
        then
      else 92 put-byte k 1+ to k then
      then then then then then then
    else a k + c@ put-byte k 1+ to k then
  repeat
  ok 0= if false exit then
  k u >= if s"  warning - unterminated string literal in .ASCII/.ASCIZ" diag-w
  else s" .ASCII/.ASCIZ" dnm! a u k 1+ dir-trailing drop then
  true ;

\ ---- 最良パターンの選択 ----
variable best-row  variable b-e  variable b-l  variable b-s  variable best-undef
variable scan-stop

: better? ( -- f )
  best-row @ 0< if true exit then
  n-expr @ b-e @ < if true exit then
  n-expr @ b-e @ > if false exit then
  n-lit @ b-l @ > if true exit then
  n-lit @ b-l @ < if false exit then
  n-sym @ b-s @ < ;

: pattern-try ( r -- )
  dup rf0 nip 0= if drop true scan-stop ! exit then
  var-clear  false undef-hit !  true in-match !  0 dd-u !
  dup match-row
  false in-match !
  if
    better? if
      dup best-row !  n-expr @ b-e !  n-lit @ b-l !  n-sym @ b-s !
      var-snap  undef-hit @ best-undef !  dd-snap
    then
  then
  drop
  false undef-hit ! ;

: check-apply ( r -- )
  dup rf1 nonempty-field? if dup rf1 else dup rf2 then
  rot dup raux @ swap raux2 @ chk-set ;
: clrcheck-apply ( r -- )
  rf2 trim dup 0= if 2drop chk-clear-all else chk-clear then ;

: scan-rows ( -- )
  -1 best-row !  false scan-stop !
  sym-reset  chk-clear-all
  0 { r }
  begin r nrows @ < scan-stop @ 0= and while
    r rkind @
    dup 0= if drop r pattern-try else
    dup 1 = if drop r raux @ r raux2 @ swap cells sym-cur + ! else
    dup 2 = if drop r check-apply else
    dup 3 = if drop r clrcheck-apply else
    drop then then then then
    r 1+ to r
  repeat ;

: emit-objl ( -- )
  nobj @ 0 ?do pc @ i + objl i cells + @ outbin loop
  nobj @ pc +! ;

: finish-line ( -- )
  best-row @ 0< if
    s"  error - Syntax error." diag
    exit
  then
  best-row @ { r }
  var-restore  best-undef @ undef-hit !
  dd-replay
  pc @ pc-start !  pc @ pc-end !
  true force-size !  r rf2 makeobj  false force-size !
  nobj @ pc @ + pc-end !
  best-undef @ undef-hit !
  r rf1 error-eval { trig }
  trig 0= if r rf2 makeobj else 0 nobj ! then
  report? undef-hit @ and if
    s"  error - Undefined label in expression." diag exit
  then
  emit-objl ;

: pattern-line ( a u -- )
  ms-u ! ms-a !
  scan-rows
  finish-line ;

\ ---- ディレクティブ ----
: nop-dir? ( a u -- f )
  2dup s" .section" str=ci if 2drop true exit then
  2dup s" .segment" str=ci if 2drop true exit then
  2dup s" .endsection" str=ci if 2drop true exit then
  2dup s" .endsegment" str=ci if 2drop true exit then
  2dup s" .extern" str=ci if 2drop true exit then
  2dup s" .global" str=ci if 2drop true exit then
  2dup s" .export" str=ci if 2drop true exit then
  2dup s" .globl" str=ci if 2drop true exit then
  2dup s" .type" str=ci if 2drop true exit then
  2dup s" .size" str=ci if 2drop true exit then
  2dup s" .weak" str=ci if 2drop true exit then
  2dup s" .hidden" str=ci if 2drop true exit then
  2dup s" .protected" str=ci if 2drop true exit then
  2dup s" .internal" str=ci if 2drop true exit then
  2dup s" .other" str=ci if 2drop true exit then
  2dup s" .comm" str=ci if 2drop true exit then
  2dup s" .labelc" str=ci if 2drop true exit then
  2dup s" .reloctype" str=ci if 2drop true exit then
  2drop false ;

: ascii-fail ( la lu name-a name-u -- )
  mb-reset s"  error - " mb+ mb+ s" : failed to process string argument: '" mb+ mb+ s" '" mb+ mb-get diag ;

: do-directive ( ta tu la lu -- handled? )
  2>r
  2dup upper-copy sdup dnm!
  2dup s" .org" str=ci if 2drop 2r> dir-org true exit then
  2dup s" .align" str=ci if 2drop 2r> dir-align true exit then
  2dup s" .zero" str=ci if 2drop 2r> dir-zero true exit then
  2dup s" .resb" str=ci if 2drop 2r> 1 dir-res true exit then
  2dup s" .resw" str=ci if 2drop 2r> 2 dir-res true exit then
  2dup s" .resd" str=ci if 2drop 2r> 4 dir-res true exit then
  2dup s" .resq" str=ci if 2drop 2r> 8 dir-res true exit then
  2dup s" .ascii" str=ci if
    2drop 2r> 2dup ascii-str 0= if s" .ASCII" ascii-fail else 2drop then true exit
  then
  2dup s" .asciz" str=ci if
    2drop 2r> 2dup ascii-str if 0 put-byte 2drop
    else
      s"  error - .ASCIZ requires a quoted string." diag
      s" .ASCIZ" ascii-fail
    then
    true exit
  then
  nop-dir? if 2r> 2drop true exit then
  2r> 2drop false ;

: assemble-line ( a u -- )
  normalize-ws split-comment
  dup 0= if 2drop exit then
  label-proc lstrip
  dup 0= if 2drop exit then
  2dup token { ra ru ta tu }
  ra ru lstrip trim { la lu }
  ta tu la lu do-directive if 2drop exit then
  pattern-line ;

: assemble-file { fa fu } 0 0 { tab n }
  fa fu src-name-u ! src-name-a !
  fa fu load-lines to n to tab
  n 0 ?do
    i 1+ line-no !  seen-reset
    ar-top @ { mark }
    tab i tl@ assemble-line
    mark ar-top !
  loop
  tab free throw ;

\ ====================================================================
\ パスの制御と入口
\ ====================================================================

variable outf-a  variable outf-u  variable has-out
variable pat-a   variable pat-u
variable asm-a   variable asm-u

: usage ( -- )
  s" usage: gforth axx.fs <patternfile> <sourcefile> [-b OUTFILE]" etype ecr ;

: flag-opt? ( a u -- f )
  2dup s" -d" str=cs >r  2dup s" -v" str=cs r> or >r  s" -V" str=cs r> or ;

: parse-args ( -- )
  false has-out !  0 pat-u !  0 asm-u !
  begin next-arg dup 0> while
    2dup s" -b" str=cs if
      2drop next-arg dup 0= if 2drop s"  error - -b needs a file name." etype ecr else
        sdup outf-u ! outf-a !  true has-out !
      then
    else
      2dup flag-opt? if
        2drop
      else
        pat-u @ 0= if sdup pat-u ! pat-a !
        else asm-u @ 0= if sdup asm-u ! asm-a !
        else 2drop then then
      then
    then
  repeat
  2drop ;

: n>hex ( n -- a u ) base @ >r hex dup >r abs s>d <# #s r> sign #> r> base ! ;
: lab-drift-count ( -- n )
  0 nlab @ 0 ?do
    i cells lab-equ + @ 0= if
      i cells lab-val + @  i cells lab-p1 + @ <> if 1+ then
    then
  loop ;
: lab-drift-report ( -- )
  lab-drift-count { n }
  s"  error - address mismatch between pass1 and pass2 (" etype n .en
  s"  label(s)); output addresses are UNRELIABLE." etype ecr
  lab-err-seen @ if
    s"          This is a consequence of the label definition error(s) reported above; fix those first." etype ecr
  else had-error @ if
    s"          This is a consequence of the error(s) reported above (a line in error emits nothing, so the addresses after it move); fix those first." etype ecr
  else
    s"          This usually means pass1 relaxation did not fully converge for variable-length forward references." etype ecr
  then then
  0 { shown }
  nlab @ 0 ?do
    i cells lab-equ + @ 0= if
      i cells lab-val + @  i cells lab-p1 + @ <> if
        shown 10 < if
          s"            " etype  i cells lab-na + @ i cells lab-nu + @ etype
          s" : pass1=0x" etype i cells lab-p1 + @ n>hex etype
          s"  pass2=0x" etype i cells lab-val + @ n>hex etype ecr
        then
        shown 1+ to shown
      then
    then
  loop
  shown 10 > if s"            ... and " etype shown 10 - .en s"  more." etype ecr then
  s"          Aborting: no output file written." etype ecr ;

: write-out ( -- )
  omax @ 0= if exit then
  outf-a @ outf-u @ w/o create-file throw { fid }
  obuf @ omax @ fid write-file throw
  fid close-file throw
  s" raw: wrote " etype outf-a @ outf-u @ etype s"  (" etype omax @ .en s"  bytes)" etype ecr ;

: abort-msg ( -- )
  s"  error - one or more errors were reported during assembly; output would be incomplete or wrong." etype ecr
  s"          Aborting: no output file written." etype ecr ;

: run-pass1 ( -- ok )
  0 pass1-iter !
  ar-top @ { mark }
  begin
    1 pass !  0 pc !
    lab-reset-iter
    asm-a @ asm-u @ assemble-file
    mark ar-top !
    pass1-iter @ 0> if lab-converged? if lab-snap true exit then then
    1 pass1-iter +!
    pass1-iter @ 64 > if
      s"  error - Pass1 relaxation did not converge." etype ecr
      false exit
    then
  again ;

: main ( -- )
  err-init
  parse-args
  pat-u @ 0= if usage 1 (bye) then
  pat-a @ pat-u @ file-status nip if
    s"  error - cannot open pattern file '" etype pat-a @ pat-u @ etype s" '" etype ecr 1 (bye)
  then
  0 pass !
  pat-a @ pat-u @ read-pattern
  had-error @ if abort-msg 1 (bye) then
  asm-u @ 0= if
    s"  error - a source file is required (prompt mode is not supported)." etype ecr 1 (bye)
  then
  asm-a @ asm-u @ file-status nip if
    s"  error - cannot open source file '" etype asm-a @ asm-u @ etype s" '" etype ecr 1 (bye)
  then
  out-init
  ar-top @ { amark }
  run-pass1 0= if 1 (bye) then
  2 pass !  0 pc !
  asm-a @ asm-u @ assemble-file
  amark ar-top !
  lab-drift-count 0> if lab-drift-report 1 (bye) then
  had-error @ if abort-msg 1 (bye) then
  has-out @ if write-out then
  0 (bye) ;

main
