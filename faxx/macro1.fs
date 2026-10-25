\ macro1.fs -- マクロ層 (MacroPreprocessor) の前半: 値、スコープ、式、組み込み関数

decimal

\ ---- 領域 (パスごとに捨てる) ----
268435456 constant MM-SIZE
MM-SIZE lazy mm
variable mm-top
: mm-alloc ( n -- a ) 7 + -8 and mm-top @ over + MM-SIZE > abort" macro memory full"
  mm-top @ mm + swap mm-top +! ;
: mm-str ( a u -- a' u ) { a u } u 1+ mm-alloc { d } a d u move  0 d u + c!  d u ;

\ 算術右シフト
: arshift ( n u -- n' ) over 0< if swap invert swap rshift invert else rshift then ;

\ ---- 値 (種別 0 整数 / 1 文字列) ----
: mv-int ( n -- v ) 3 cells mm-alloc { v } 0 v ! v cell+ ! v ;
: mv-str ( a u -- v ) mm-str 3 cells mm-alloc { a u v } 1 v ! a v cell+ ! u v 2 cells + ! v ;
: mv-str? ( v -- f ) @ 1 = ;
: mv-n ( v -- n ) cell+ @ ;
: mv-s ( v -- a u ) cell+ s@ ;
: mv-truth ( v -- f ) dup mv-str? if mv-s nip 0<> else mv-n 0<> then ;
: mv-text ( v -- a u ) dup mv-str? if mv-s else mv-n n>s mm-str then ;

\ ---- 例外 ----
-5001 constant X-MERR
create merr-buf 8192 allot   variable merr-u
: mfail ( -- )                              \ mb に組んだ文言で失敗する
  mb-get dup 8191 min merr-u ! merr-buf swap move  X-MERR throw ;
: mfail-pos ( fa fu ln -- )                 \ 「file:line: 」を mb の先頭に
  mb-reset { fa fu ln } fa fu mb+ s" :" mb+ ln mb-n s" : " mb+ ;

\ ---- マクロ処理系の状態 (ソース用とパターン用の 2 つ) ----
: mpf ( idx -- ) cells constant ;
0 mpf mp.pat      1 mpf mp.funcs    2 mpf mp.declared   3 mpf mp.scopen    4 mpf mp.scopes
5 mpf mp.depth    6 mpf mp.uid      7 mpf mp.incn       8 mpf mp.inca       9 mpf mp.keya
10 mpf mp.keyu    11 mpf mp.enabled 12 mpf mp.hadErr    13 mpf mp.reported  14 mpf mp.out
15 mpf mp.outn    16 mpf mp.outcap  17 mpf mp.ctl       18 mpf mp.retval    19 mpf mp.noeval
20 mpf mp.exprd    21 mpf mp.keyfile
22 cells constant MPSZ
variable mp
256 constant MAX-SCOPES
200 constant MACRO-MAX-DEPTH
1000000 constant MACRO-MAX-ITER
2000000 constant MACRO-MAX-LINES
64 constant MACRO-MAX-INC

: mp-new ( pat? -- inst ) { pat } MPSZ allocate throw { m } m MPSZ erase
  pat m mp.pat + !
  1 om-new m mp.funcs + !  1 om-new m mp.declared + !  1 om-new m mp.reported + !
  MAX-SCOPES cells allocate throw m mp.scopes + !
  MACRO-MAX-INC 2 * cells allocate throw m mp.inca + !
  true m mp.enabled + !
  m ;
false mp-new constant mp-src
true mp-new constant mp-pat
: mp@ ( off -- v ) mp @ + @ ;
: mp! ( v off -- ) mp @ + ! ;
: mp-pat? ( -- f ) mp.pat mp@ ;

: scope-new ( -- om ) 1 om-new ;
: reset-pass-mp ( -- )
  mp @ mp.funcs + @ om-clear   mp @ mp.declared + @ om-clear
  0 mp.scopen mp!  scope-new mp.scopes mp@ !  1 mp.scopen mp!
  0 mp.depth mp!  0 mp.uid mp!  0 mp.incn mp!  0 0 mp.keya mp! 0 mp.keyu mp! ;
: mp-reset-all ( -- )
  0 mp.hadErr mp!  mp @ mp.reported + @ om-clear  reset-pass-mp ;

\ マクロ層の状態は mm の領域を使うので、2 つの処理系が同じ領域を共有する。
\ 領域はパス (あるいはパターンの読み込み) の始まりで巻き戻す。
: mm-reset ( -- ) 0 mm-top ! ;

: scope-top ( -- om ) mp.scopes mp@ mp.scopen mp@ 1- cells + @ ;
: scope-find ( a u -- slot|0 ) { a u }
  mp.scopen mp@ 0 ?do
    a u mp.scopes mp@ mp.scopen mp@ 1- i - cells + @ om-find ?dup if unloop exit then
  loop 0 ;
: scope-set ( a u v -- ) { a u v } a u scope-top om-put v swap ! ;
: assign-var ( a u v -- ) { a u v }
  a u scope-find ?dup if v swap ! else a u v scope-set then ;

: func-find ( a u -- f|0 ) mp @ mp.funcs + @ om-find ?dup if @ else 0 then ;
: declared? ( a u -- f ) mp @ mp.declared + @ om-find 0<> ;
: declare ( a u -- ) mp @ mp.declared + @ om-put drop ;

\ ---- アセンブラ側からラベルを引く (前回の反復の値) ----
variable mlabels-valid
2 om-new constant mlabel-names           \ unused (名前の集合は labels を使う)
4 om-new constant mlabel-vals
variable mlinepcs-n
create mlinepcs-a 1048576 cells allocate throw drop
\ ファイル名 -> 行ごとの PC の配列
2 om-new constant mline-pcs-prev         \ 名前 -> (ptr n)
2 om-new constant mline-pcs-cur
variable cur-line-pcs                    \ 現在の行 PC 配列 (動的)
variable cur-line-pcs-n
variable cur-line-pcs-cap

\ ラベルの値: ( a u -- kind n ) kind 0 無い 1 名前だけ 2 値あり
: asm-label ( a u -- kind n ) { a u }
  mp-pat? if 0 0 exit then
  mlabels-valid @ 0= if 1 0 exit then
  a u mlabel-vals om-find ?dup if @ 2 swap exit then
  a u labels om-find if 1 0 exit then
  0 0 ;

: fmt-pos ( fa fu ln -- ) { fa fu ln } fa fu mb+ s" :" mb+ ln mb-n ;

\ ---- 式の構文解析 ----
variable x-a  variable x-u  variable x-i  variable x-sup
variable x-fa variable x-fu variable x-ln

: xerr-head ( -- ) x-fa @ x-fu @ x-ln @ mfail-pos s" macro expression: " mb+ ;
: xerr-tail ( -- ) s"  in " mb+ x-a @ x-u @ repr1 mb+ mfail ;
: x-err ( a u -- ) xerr-head mb+ xerr-tail ;
: x-ch ( off -- c ) x-i @ + dup x-u @ < if x-a @ + c@ else drop 0 then ;
: x-skip ( -- ) begin 0 x-ch dup 32 = swap 9 = or while 1 x-i +! repeat ;
: x-eat ( a u -- f ) { a u }
  x-skip
  x-i @ u + x-u @ > if false exit then
  x-a @ x-i @ + u a u str=cs 0= if false exit then
  u x-i +! true ;
: x-expect ( a u -- ) 2dup x-eat if 2drop else
  xerr-head s" expected " mb+ 2dup repr1 mb+ 2drop xerr-tail then ;
: x-peek ( -- c ) x-skip 0 x-ch ;
: x-noeval? ( -- f ) x-sup @ 0<> ;

: x-need-int ( v -- n )
  dup mv-str? if
    x-noeval? if drop 0 exit then
    xerr-head s" expected an integer, got the string " mb+ mv-s repr1 mb+ xerr-tail
  then mv-n ;

\ int64 の検査つき演算
: ovf-err ( -- ) xerr-head s" integer overflow (64-bit)" mb+ xerr-tail ;
: i64+ ( a b -- c ) 2dup + { s } 2dup xor 0< 0= >r  over s xor 0< r> and
  if x-noeval? 0= if ovf-err then then 2drop s ;
: i64- ( a b -- c ) 2dup - { s } 2dup xor 0< >r  over s xor 0< r> and
  if x-noeval? 0= if ovf-err then then 2drop s ;
: i64* ( a b -- c ) 2dup m* { lo hi } 2drop
  hi lo 0< if -1 else 0 then <> if x-noeval? 0= if ovf-err then then lo ;
: i64neg ( a -- b ) dup $8000000000000000 = if x-noeval? 0= if ovf-err then then negate ;

: c-div ( a b -- q )
  dup 0= if 2drop 0 exit then
  2dup -1 = swap $8000000000000000 = and if 2drop x-noeval? 0= if ovf-err then 0 exit then
  { a b }
  a 0< if a negate else a then b 0< if b negate else b then >r 0 r> um/mod nip { q }
  a 0>= b 0>= = if q else q negate then ;
: c-mod ( a b -- r ) { a b } a a b c-div b * - ;

defer x-ternary
: x-ident ( -- a u ) x-skip x-i @ { j }
  begin j x-u @ < if x-a @ j + c@ dup alnc? swap 95 = or x-a @ j + c@ 128 < and else false then while j 1+ to j repeat
  j x-i @ = if s" expected a name" x-err then
  x-a @ x-i @ + j x-i @ -  j x-i ! ;

: x-digit ( c -- d|-1 ) dup digc? if 48 - exit then dup 97 >= over 102 <= and if 87 - exit then
  dup 65 >= over 70 <= and if 55 - exit then drop -1 ;
: x-number ( -- v ) x-a @ x-u @ { s n } x-i @ { j } 10 { base }
  j 1+ n < s j + c@ 48 = and if
    s j 1+ + c@ lc { p }
    p 120 = if 16 to base j 2 + to j else
    p 98 = if 2 to base j 2 + to j else
    p 111 = if 8 to base j 2 + to j then then then
  then
  j { st } 0 { v } 0 { nd } false { fin }
  begin j n < fin 0= and while
    s j + c@ { c }
    c 95 = if j 1+ to j else
      c x-digit { d }
      d 0< d base >= or if true to fin else
        v base i64* d i64+ to v
        nd 1+ to nd  j 1+ to j
      then
    then
  repeat
  nd 0= j st = or if s" malformed number" x-err then
  j x-i !  v mv-int ;

: x-string ( q -- a u ) { q }
  x-a @ x-u @ { s n } x-i @ 1+ { j }
  n 1+ mm-alloc { buf } 0 { o }
  begin j n < while
    s j + c@ { c }
    c 92 = j 1+ n < and if
      s j 1+ + c@ { e }
      e case 110 of 10 endof 116 of 9 endof 114 of 13 endof 48 of 0 endof e swap endcase
      buf o + c!  o 1+ to o  j 2 + to j
    else
      c q = if j 1+ x-i !  buf o exit then
      c buf o + c!  o 1+ to o  j 1+ to j
    then
  repeat
  s" unterminated string literal" x-err 0 0 ;

defer m-loc-counter ( -- n )
defer m-call-value ( a u args nargs -- v )
defer m-lookup ( a u -- v )
defer m-defined? ( a u -- f )

create x-args 64 cells allot
: x-primary ( -- v ) x-skip
  x-i @ x-u @ >= if s" unexpected end of expression" x-err then
  0 x-ch { c }
  c 40 = if
    mp.exprd mp@ 1000 >= if s" nesting too deep" x-err then
    mp.exprd mp@ 1+ mp.exprd mp!  1 x-i +!
    x-ternary s" )" x-expect
    mp.exprd mp@ 1- mp.exprd mp!
    exit
  then
  c 34 = if 34 x-string mv-str exit then
  c 39 = if
    39 x-string { a u } u 1 = if a c@ mv-int else a u mv-str then exit
  then
  c 36 = if
    1 x-i +!  0 x-ch 36 = if 1 x-i +! then
    m-loc-counter mv-int exit
  then
  c digc? if x-number exit then
  c 95 = c alnc? c 128 < and or if
    x-ident { na nu }
    na nu s" defined" str=cs if
      s" (" x-expect x-ident { ia iu } s" )" x-expect
      ia iu m-defined? if 1 else 0 then mv-int exit
    then
    x-peek 40 = if
      1 x-i +!  0 { nargs }  64 cells mm-alloc { arr }
      x-peek 41 = if 1 x-i +! else
        begin
          nargs 64 >= if
            xerr-head s" macro call '" mb+ na nu mb+ s" ': too many arguments" mb+ mfail
          then
          x-ternary arr nargs cells + !  nargs 1+ to nargs
          s" ," x-eat if true else s" )" x-expect false then 0=
        until
      then
      x-noeval? if 0 mv-int exit then
      na nu arr nargs m-call-value exit
    then
    x-noeval? if 0 mv-int exit then
    na nu m-lookup exit
  then
  xerr-head s" unexpected character " mb+ x-a @ x-i @ + 1 repr1 mb+ xerr-tail 0 ;

: x-unary ( -- v ) x-skip
  0 x-ch 33 = 1 x-ch 61 <> and if 1 x-i +! recurse mv-truth if 0 else 1 then mv-int exit then
  0 x-ch 126 = if 1 x-i +! recurse x-need-int invert mv-int exit then
  0 x-ch 45 = if 1 x-i +! recurse x-need-int i64neg mv-int exit then
  0 x-ch 43 = if 1 x-i +! recurse exit then
  0 x-ch 64 = if 1 x-i +! recurse x-need-int qn qabs qnbit mv-int exit then
  0 x-ch 42 = 1 x-ch 40 = and if
    2 x-i +!  x-ternary s" ," x-expect x-ternary s" )" x-expect
    x-need-int { nv } x-need-int { xv }
    xv qn nv qn qbyte { r neg }
    neg x-noeval? 0= and if
      xerr-head s" negative byte-extract offset in *(expr, expr)" mb+ mfail
    then
    r q>n mv-int exit
  then
  x-primary ;
defer x-unary-d

: safe-rep-len ( n l -- total ) { n l }
  n 0< if 0 to n then
  n 0= l 0= or if 0 exit then
  n 16777216 l / > if
    x-noeval? if 0 exit then
    xerr-head s" string repetition too large" mb+ xerr-tail
  then
  n l * ;
sb-new constant rep-b
: str-repeat ( a u n -- v ) { a u n }
  n u safe-rep-len { tot }
  rep-b sb-clear  n 0> if n 0 ?do a u rep-b sb+ loop then
  rep-b sb$ mv-str ;
: x-mul ( -- v ) x-unary
  begin x-skip 0 x-ch { c }
    c 42 = if
      1 x-i +!  x-unary { r } { v }
      v mv-str? r mv-str? 0= and if v mv-s r mv-n 0 max str-repeat else
      v mv-str? 0= r mv-str? and if r mv-s v mv-n 0 max str-repeat else
        v x-need-int r x-need-int i64* mv-int
      then then true
    else c 47 = if
      1 x-i +!  x-unary x-need-int { r }
      r 0= x-noeval? 0= and if s" division by zero" x-err then
      x-need-int r c-div mv-int true
    else c 37 = if
      1 x-i +!  x-unary x-need-int { r }
      r 0= x-noeval? 0= and if s" modulo by zero" x-err then
      x-need-int r c-mod mv-int true
    else false then then then
  0= until ;
sb-new constant cat-b
: x-add ( -- v ) x-mul
  begin x-skip 0 x-ch { c }
    c 43 = if
      1 x-i +!  x-mul { r } { v }
      v mv-str? r mv-str? or if
        cat-b sb-clear  v mv-text cat-b sb+  r mv-text cat-b sb+  cat-b sb$ mv-str
      else v mv-n r mv-n i64+ mv-int then true
    else c 45 = if
      1 x-i +!  x-need-int { lv }  x-mul x-need-int { rv }  lv rv i64- mv-int true
    else false then then
  0= until ;
: mshift-count ( v -- n ) x-need-int { n }
  n 0< n 4096 > or if
    x-noeval? 0= if s" shift count out of range" x-err then 0 exit
  then n ;
: x-shift ( -- v ) x-add
  begin x-skip 0 x-ch { c }
    c 60 = 1 x-ch 60 = and if
      2 x-i +!  x-add mshift-count { n } x-need-int { base }
      n 63 > if
        base 0<> x-noeval? 0= and if ovf-err then 0 mv-int
      else
        base n lshift { sh }
        n 0> if sh n arshift base <> x-noeval? 0= and if ovf-err then then
        sh mv-int
      then true
    else c 62 = 1 x-ch 62 = and if
      2 x-i +!  x-add mshift-count { n } x-need-int { rb }
      n 63 > if rb 0< if -1 else 0 then else rb n arshift then mv-int true
    else false then then
  0= until ;
: m-order ( a b or-equal -- f ) { a b oe }
  a mv-str? b mv-str? <> if
    x-noeval? if false exit then
    s" cannot order a string against an integer" x-err
  then
  a mv-str? if
    a mv-s b mv-s compare { c }
    oe if c 0<= else c 0< then
  else
    oe if a mv-n b mv-n <= else a mv-n b mv-n < then
  then ;
: m-equal ( a b -- f ) { a b }
  a mv-str? b mv-str? <> if false exit then
  a mv-str? if a mv-s b mv-s str=cs else a mv-n b mv-n = then ;
: x-rel ( -- v ) x-shift
  begin x-skip
    0 x-ch 60 = 1 x-ch 60 = and if exit then
    0 x-ch 62 = 1 x-ch 62 = and if exit then
    s" <=" x-eat if x-shift true m-order 1 and mv-int true else
    s" >=" x-eat if x-shift { r } r swap true m-order 1 and mv-int true else
    s" <" x-eat if x-shift false m-order 1 and mv-int true else
    s" >" x-eat if x-shift { r2 } r2 swap false m-order 1 and mv-int true else
    false then then then then
  0= until ;
: x-eq ( -- v ) x-rel
  begin
    s" ==" x-eat if x-rel m-equal if 1 else 0 then mv-int true else
    s" !=" x-eat if x-rel m-equal if 0 else 1 then mv-int true else
    false then then
  0= until ;
: x-band ( -- v ) x-eq
  begin x-skip 0 x-ch 38 = 1 x-ch 38 <> and if
      1 x-i +!  x-need-int { lv }  x-eq x-need-int { rv }  lv rv and mv-int true
    else false then
  0= until ;
: x-bxor ( -- v ) x-band
  begin x-skip 0 x-ch 94 = if
      1 x-i +!  x-need-int { lv }  x-band x-need-int { rv }  lv rv xor mv-int true
    else false then
  0= until ;
: x-bor ( -- v ) x-bxor
  begin x-skip 0 x-ch 124 = 1 x-ch 124 <> and if
      1 x-i +!  x-need-int { lv }  x-bxor x-need-int { rv }  lv rv or mv-int true
    else false then
  0= until ;
: sext-tick? ( -- f )                       \ 0 x-ch が ' のとき、符号拡張か
  x-i @ 1+ { j }
  begin j x-u @ < if x-a @ j + c@ dup 32 = swap 9 = or else false then while j 1+ to j repeat
  j x-u @ < if x-a @ j + c@ dup digc? swap 40 = or else false then ;
: x-sext ( -- v ) x-bor
  begin x-skip 0 x-ch 39 = sext-tick? and if
      1 x-i +!  x-bor { t } { v }
      v x-need-int { xv } t x-need-int { tv }
      xv qn tv qn qsext { r warn }
      warn x-noeval? 0= and if
        mb-reset x-fa @ x-fu @ x-ln @ fmt-pos s" : sign-extension bit width " mb+ tv mb-n
        s"  exceeds maximum 256, result set to 0" mb+ mb-get diag-wf
      then
      r q>n mv-int true
    else false then
  0= until ;
: x-land ( -- v ) x-sext
  begin s" &&" x-eat if
      dup mv-truth 0= x-noeval? 0= and { skip }
      skip if 1 x-sup +! then
      x-sext { r }
      skip if -1 x-sup +! then
      { v } skip 0= v mv-truth and r mv-truth and if 1 else 0 then mv-int true
    else false then
  0= until ;
: x-lor ( -- v ) x-land
  begin s" ||" x-eat if
      dup mv-truth x-noeval? 0= and { skip }
      skip if 1 x-sup +! then
      x-land { r }
      skip if -1 x-sup +! then
      { v } skip v mv-truth or r mv-truth or if 1 else 0 then mv-int true
    else false then
  0= until ;
: x-ternary-impl ( -- v ) x-lor { c }
  x-skip 0 x-ch 63 = if
    1 x-i +!
    x-noeval? if 0 else c mv-truth if 1 else 2 then then { taken }
    taken 2 = if 1 x-sup +! then
    x-ternary { a }
    taken 2 = if -1 x-sup +! then
    s" :" x-expect
    taken 1 = if 1 x-sup +! then
    x-ternary { b }
    taken 1 = if -1 x-sup +! then
    taken 2 = if b else a then
  else c then ;
' x-ternary-impl is x-ternary

: m-eval ( a u fa fu ln -- v ) { a u fa fu ln }
  begin u 0> if a c@ dup 32 = swap 9 = or else false then while a 1+ to a u 1- to u repeat
  u 0= if fa fu ln mfail-pos s" empty macro expression" mb+ mfail then
  x-a @ x-u @ x-i @ x-sup @ x-fa @ x-fu @ x-ln @ { sa su si ss sfa sfu sln }
  a x-a ! u x-u ! 0 x-i ! 0 x-sup ! fa x-fa ! fu x-fu ! ln x-ln !
  0 mp.exprd mp!
  x-ternary { v }
  x-skip
  x-i @ x-u @ < if
    xerr-head s" unexpected trailing text " mb+ x-a @ x-i @ + x-u @ x-i @ - repr1 mb+ xerr-tail
  then
  sa x-a ! su x-u ! si x-i ! ss x-sup ! sfa x-fa ! sfu x-fu ! sln x-ln !
  v ;
