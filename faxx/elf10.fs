\ elf10.fs -- ELF オブジェクトの書き出し (1): 道具、行表、セクション

decimal

\ ---- 行表 (-g) ----
variable lm-n  variable lm-cap
variable lm-base
: lm-init ( -- ) 1024 lm-cap ! lm-cap @ 6 * cells allocate throw lm-base ! 0 lm-n ! ;
lm-init
: lm@ ( i -- addr ) 6 * cells lm-base @ + ;
: line-map-add-impl ( -- )
  lm-n @ lm-cap @ >= if lm-cap @ 2* lm-cap ! lm-base @ lm-cap @ 6 * cells resize throw lm-base ! then
  lm-n @ lm@ { e }
  cur-section intern e cell+ ! e !
  pc @ e 2 cells + !
  file@ intern e 4 cells + ! e 3 cells + !
  line-no @ e 5 cells + !
  1 lm-n +! ;
' line-map-add-impl is line-map-add

:noname ( passno -- )
  1 = if ovr-clear export-labels om-clear else ovr-clear rl-reset an-reset 0 lm-n ! then ; is pass-reset-extra

\ ---- バイト列の組み立て ----
variable w-le                                       \ 1 ならリトルエンディアン
variable w-64                                       \ 1 なら ELF64
: bb-new ( -- sb ) sb-new ;
: bb-len ( sb -- n ) sb-len ;
: put-le ( v n sb -- ) { v n sb }
  n 0 ?do v i 8 * rshift 255 and sb sb-c loop ;
: put-be ( v n sb -- ) { v n sb }
  n 0 ?do v n 1- i - 8 * rshift 255 and sb sb-c loop ;
: put ( v n sb -- ) w-le @ if put-le else put-be then ;
: put8 ( v sb -- ) 1 swap put ;
: put16 ( v sb -- ) 2 swap put ;
: put32 ( v sb -- ) 4 swap put ;
: put64 ( v sb -- ) 8 swap put ;
: put-bytes ( a u sb -- ) { a u sb } u 0 ?do a i + c@ sb sb-c loop ;
: put-zero ( n sb -- ) { n sb } n 0 ?do 0 sb sb-c loop ;
: put-cstr ( a u sb -- ) { a u sb } a u sb put-bytes 0 sb sb-c ;
\ ELF のワードサイズ (ELF64 なら 8、ELF32 なら 4)
: put-w ( v sb -- ) w-64 @ if 8 else 4 then swap put ;
: put-w-signed ( v sb -- ) put-w ;
: align-up2 ( x a -- x' ) dup 0<= if drop exit then 1- tuck + swap invert and ;

\ u64 の mask を適用 (ELF32 なら下位 32 bit)
: word-mask-v ( v -- v' ) w-64 @ 0= if 4294967295 and then ;

\ ---- セクション範囲 ----
: sec-ranges-of ( a u -- n ) { a u }                 \ そのセクションの範囲の個数
  0 nranges @ 0 ?do i cells range-na + @ i cells range-nu + @ a u str=cs if 1+ then loop ;

\ その名前の k 番目の範囲 (s l)
: sec-range-k ( a u k -- s l ) { a u k }
  0 { c }
  nranges @ 0 ?do
    i cells range-na + @ i cells range-nu + @ a u str=cs if
      c k = if i cells range-s + @ i cells range-l + @ unloop exit then
      c 1+ to c
    then
  loop 0 0 ;

\ 範囲の並び (範囲がなければ [start,size] が正のとき 1 つ)
: sec-nranges ( a u -- n ) { a u }
  a u sec-ranges-of ?dup if exit then
  a u sections om-find ?dup if cell+ @ 0> if 1 else 0 then else 0 then ;
: sec-range@ ( a u k -- s l ) { a u k }
  a u sec-ranges-of if a u k sec-range-k exit then
  a u sections om-find @ a u sections om-find cell+ @ ;

: addr>woff ( a u wpc -- woff true | false ) { a u w }
  sections om-count 0= if w true exit then
  0 { cum }
  a u sec-nranges 0 ?do
    a u i sec-range@ { rs rl }
    w rs >= w rs rl + <= and if cum w rs - + true unloop exit then
    cum rl + to cum
  loop
  false ;

\ ---- セクションの属性 ----
variable sa-fl  variable sa-ty  variable sa-al  variable sa-es
: section-attrs ( a u -- ) { a u }
  a u supper { ua uu }
  ua uu s" .TEXT" starts? if 6 else
  ua uu s" .DATA" starts? if 3 else
  ua uu s" .RODATA" starts? if 2 else
  ua uu s" .BSS" starts? if 3 else 2 then then then then sa-fl !
  ua uu s" .BSS" starts? if 8 else 1 then sa-ty !
  -1 sa-al !  0 sa-es !
  a u slower d-sec om-find ?dup if
    { dl }
    dl @ sa-fl !
    dl cell+ @ 0>= if dl cell+ @ sa-ty ! then
    dl 2 cells + @ 0>= if dl 2 cells + @ sa-al ! then
    dl 3 cells + @ 0>= if dl 3 cells + @ sa-es ! then
  then ;

\ ---- セクション表 (csecs) ----
4096 constant MAXSEC
create cs-na MAXSEC cells allot   create cs-nu MAXSEC cells allot
create cs-bs MAXSEC cells allot   create cs-data MAXSEC cells allot
create cs-sz MAXSEC cells allot   create cs-fl MAXSEC cells allot
create cs-ty MAXSEC cells allot   create cs-al MAXSEC cells allot
create cs-es MAXSEC cells allot
variable ncs
: cs-name ( i -- a u ) dup cells cs-na + @ swap cells cs-nu + @ ;
: cs-find ( a u -- idx|-1 ) { a u }
  ncs @ 0 ?do i cs-name a u str=cs if i unloop exit then loop -1 ;
: cs-find-ci ( a u -- idx|-1 ) { a u }
  ncs @ 0 ?do i cs-name a u str=ci if i unloop exit then loop -1 ;

\ ワード w0 から n 個を対象のバイト順の列にして sb へ
: extract-words ( w0 n sb -- ) { w0 n sb }
  e-bpw @ { bpw }  bts @ { bt }
  padding-v @ bt 64 < if 1 bt lshift 1- and then { pad }
  n 0 ?do
    w0 i + { pos }
    pos 0>= pos wcap @ < and if pos wset @ + c@ else false then if
      pos cells wbuf @ + @
    else pad then { val }
    bpw 0 ?do
      endian-big @ 0= if val i 8 * rshift 255 and else val bpw 1- i - 8 * rshift 255 and then sb sb-c
    loop
  loop ;
