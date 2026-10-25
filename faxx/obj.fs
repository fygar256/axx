\ obj.fs -- binary_list の評価 (ObjectGenerator) の前半: 出力ワードの列とテキストテンプレート

decimal

8192 constant MAXOBJ
MAXOBJ QB * lazy objl
variable nobj
: obj+ ( q -- ) nobj @ MAXOBJ >= abort" binary_list too long" objl nobj @ QB * + q!  1 nobj +! ;
: obj-q ( i -- q ) QB * objl + ;

\ テキスト出力 (asmtext)
lazy-sb asmtext
lazy-sb asmdisp
variable asmtext-set
: asmtext-clear ( -- ) false asmtext-set !  asmtext sb-clear  asmdisp sb-clear ;

: txt-escaped ( a u sb -- ) { a u sb }                  \ asmtext_escaped
  u 0 ?do
    a i + c@ { c }
    c 10 = if s" \n" sb sb+ else
    c 9 = if s" \t" sb sb+ else
    c 13 = if s" \r" sb sb+ else
    c 92 = if s" \\" sb sb+ else
    c 34 = if s\" \\\"" sb sb+ else
    c sb sb-c
    then then then then then
  loop ;

\ 基数つきの数字だけ (_txt_radix)。基数のプレフィックスなし、小文字
lazy-sb rdx-b
: radix-str ( q radix -- a u ) { q rx }
  q qundef? if s" UNDEF" exit then
  rdx-b sb-clear
  q q-neg? { neg }  neg if q qneg else q then { m }
  m q-zero? if s" 0" exit then
  begin m q-zero? 0= while
    m rx qdivsmall { rm } to m
    rm dup 10 < if 48 + else 87 + then rdx-b sb-c
  repeat
  \ 逆順になっているので並べ替える
  rdx-b sb$ { ra ru }
  ru 2 + ar-alloc { out } 0 { o }
  neg if 45 out c! 1 to o then
  ru 0 ?do ra ru 1- i - + c@ out o + c!  o 1+ to o loop
  out o ;

\ ---- .float (10 進 34 桁、偶数丸め) ----
34 constant TXT-PREC
lazy-sb fl-b
: txt-float ( q -- a u ) { q }
  q qundef? if s" UNDEF" exit then
  q q-neg? { neg }  neg if q qneg else q then q>dec { da du }
  du { n }  du 1- { e10 }  da { dg }
  du TXT-PREC > if
    da TXT-PREC sdup { ta tu }
    da TXT-PREC + c@ 48 - { nxt }
    false { rest } du TXT-PREC 1+ ?do da i + c@ 48 <> if true to rest then loop
    ta tu + 1- c@ 48 - 1 and 0<> { odd }
    nxt 5 > nxt 5 = rest odd or and or { up }
    up if
      tu 1- { k } true { carry }
      begin carry k 0>= and while
        ta k + c@ 57 = if 48 ta k + c! else ta k + c@ 1+ ta k + c! false to carry then
        k 1- to k
      repeat
      carry if 49 ta c! e10 1+ to e10 then
    then
    ta to dg  TXT-PREC to n
  then
  \ 末尾の 0 を落とす
  dg n { ga gn }
  begin gn 1 > if ga gn + 1- c@ 48 = else false then while gn 1- to gn repeat
  fl-b sb-clear
  neg if 45 fl-b sb-c then
  e10 -6 >= e10 TXT-PREC < and if
    e10 gn 1- >= if
      ga gn fl-b sb+  e10 gn 1- - 0 ?do 48 fl-b sb-c loop  s" .0" fl-b sb+
    else e10 0>= if
      ga e10 1+ fl-b sb+  46 fl-b sb-c  ga e10 1+ + gn e10 1+ - fl-b sb+
    else
      s" 0." fl-b sb+  e10 negate 1- 0 ?do 48 fl-b sb-c loop  ga gn fl-b sb+
    then then
  else
    ga c@ fl-b sb-c  46 fl-b sb-c
    gn 1 > if ga 1+ gn 1- fl-b sb+ else 48 fl-b sb-c then
    101 fl-b sb-c  e10 0< if 45 else 43 then fl-b sb-c
    e10 abs dup 10 < if 48 fl-b sb-c then n>s fl-b sb+
  then
  fl-b sb$ sdup ;
