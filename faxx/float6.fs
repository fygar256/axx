\ float6.fs -- !Q の捕捉と flt{} dbl{} qad{} enflt{} endbl{} (axx.py 7050-7190, 4215-4375)

decimal

: q128 ( hi -- q ) q0 dup cell+ rot swap ! ;                 \ 上位 64 ビットだけ
: dbits>q ( bits -- q ) { bits }                              \ 倍精度のビット列を %.17g 経由で binary128 に
  rr-quad
  bits 52 rshift $7ff and $7ff = if
    bits $fffffffffffff and 0<> if
      \ caxx.c は "-nan" を数として読めず long double の経路へ落ち、0.5 のビットになる
      bits 63 rshift 0<> if $3ffe000000000000 q128 else $7fff800000000000 q128 then else
      bits 63 rshift 63 lshift $7fff000000000000 or q128 then
    exit
  then
  ar-mark { mk }
  bits g17-digits 0= if bits 63 rshift 63 lshift q128 mk ar-release exit then
  g17-neg @ g17-dig 17 bn-dec g17-e10 @ 16 - dec-ev ev>q
  mk ar-release ;
: text>q128 ( a u -- q true | false )                          \ decimal_eval_expr
  rr-quad
  ar-mark { mk }
  f128-eval if ev>q true else false then
  mk ar-release ;

: cap-q ( -- ok ) 0 vname-at { n }
  n 0= if false exit then
  mt-a @ ti @ + { na }  n ti +!
  0 var-stopchar { stop }
  na n true vslot { sl }
  si @ { st }
  false expr-missing !
  fdiv0-defer @ fdiv0-seen @ { od os }
  true fdiv0-defer !  false fdiv0-seen !
  ms-a @ ms-u @ si @ stop expr-esc-float { v pos }
  fdiv0-seen @ { d0 }
  od fdiv0-defer !  os fdiv0-seen !
  pos si !
  ncloses @ 0 ?do SUB-CLOSE i cells closes + @ sub-mark loop
  sl st si @ stop cap-text
  ms-a @ st + pos st - { ra ru }
  stop 0<> ru 0> and if ra ru 1- + c@ stop = if ru 1- to ru then then
  ru 4 > if ra 4 s" qad{" compare 0= ra ru 1- + c@ 125 = and if ra 4 + to ra ru 5 - to ru then then
  q0 { r }  d0 { dz }
  v qundef? if q0 to r else
    ru 0> if ra ru text>q128 else false then
    if to r false to dz else
      ra ru s" inf" compare 0= ra ru s" nan" compare 0= or ra ru s" -inf" compare 0= or if
        ra ru s" nan" compare 0= if $7fff800000000000 else
          ra c@ 45 = if $ffff000000000000 else $7fff000000000000 then then q128 to r
      else v @ dbits>q to r then
    then
  then
  dz if s"  error - Division by 0 error." xerr then
  sl r false false vput
  expr-missing @ if false exit then
  stop 0<> if 0 sc stop = if 1 si +! then then
  true ;

: cap-float-impl ( kind -- ok )
  dup 81 = if drop cap-q exit then
  cap-fd ;
' cap-float-impl is cap-float

\ ---- 波括弧 ----
: get-curlb ( -- a u f )
  skipsp cur 123 <> if 0 0 false exit then
  1 adv skipsp
  ep @ { st }
  begin ep @ ex-u @ < if cur 125 <> else false then while 1 adv repeat
  ex-a @ st + ep @ st - { ta tu }
  begin tu 0> if ta tu 1- + c@ dup 32 = over 9 = or over 13 = or over 10 = or swap 0= or else false then while tu 1- to tu repeat
  ep @ ex-u @ >= if
    report? if
      mb-reset s"  error - missing closing '}' in expression: '{" mb+ ta tu mb+ s" '" mb+ mb-get diag-ef
    then
    ex-u @ ep !  0 0 false exit
  then
  1 adv ta tu true ;

: x-label-impl ( a u -- q ) lab-find dup 0= if drop true undef-flag ! q0 exit then
  lab-q dup qundef-derived? if drop true undef-flag ! q0 exit then qcopy ;
' x-label-impl is x-label

: xv>fin ( q flag -- ) ( F: -- r ) xv>f ;
: hex>q ( u -- q ) qun ;

: brace-qad ( a u -- q ) { ta tu }
  ta tu s" nan" compare 0= if $7fff800000000000 q128 exit then
  ta tu s" inf" compare 0= if $7fff000000000000 q128 exit then
  ta tu s" -inf" compare 0= if $ffff000000000000 q128 exit then
  ar-mark { mk }
  q0 { r }
  ta tu text>q128 if to r else
    ta tu xeval if
      xv>f fdup dbl-fin? if dq @ dbits>q to r else fdrop $7fff000000000000 q128 to r then
    else
      mb-reset s"  error - qad{}: cannot evaluate expression '" mb+ ta tu mb+ s" '; using 0." mb+ mb-get xerr
    then
  then
  r cell+ @ 48 rshift $7fff and $7fff = if
    mb-reset s"  error - qad{}: cannot evaluate expression '" mb+ ta tu mb+ s" '; using 0." mb+ mb-get xerr
    q0 to r
  then
  mk ar-release
  r ;

: brace-fd ( a u width -- q ) { ta tu w }
  ta tu s" nan" compare 0= if w 32 = if $7fc00000 else $7ff8000000000000 then qun exit then
  ta tu s" inf" compare 0= if w 32 = if $7f800000 else $7ff0000000000000 then qun exit then
  ta tu s" -inf" compare 0= if w 32 = if $ff800000 else $fff0000000000000 then qun exit then
  ar-mark { mk }
  0 false { bits ok }
  ta tu xeval if
    xv>f fdup dbl-fin? if
      dq w 32 = if f32-of else f64-of then to ok to bits
    else fdrop then
  then
  ok 0= if
    w 32 = if s"  error - flt{}: cannot convert expression to float32; using 0."
    else s"  error - dbl{}: cannot convert expression to float64; using 0." then xerr
    0 to bits
  then
  mk ar-release
  bits qun ;

: brace-enf ( kind -- q ) { kind }
  get-curlb { ta tu f }
  f 0= if q0 exit then
  undef-flag @ { ou }  false undef-flag !
  exp-float @ { pm }  false exp-float !
  ta tu 0 ['] expr-top ev-ctx drop { v }
  pm exp-float !
  undef-flag @ { inner }
  ou inner or undef-flag !
  kind 1 = if s" enflt" else s" endbl" then { na nu }
  inner if
    mb-reset s"  error - " mb+ na nu mb+ s" {}: expression contains undefined label." mb+ mb-get xerr
    q0 to v
  then
  v @ kind 1 = if $ffffffff and fb-buf l! fb-buf sf@ else bits>f then
  pm if dq exit then
  fdup dbl-fin? 0= fdup fabs 255 fpow2 f>= or if
    f-bits g17-text { ga gu }
    mb-reset s"  error - " mb+ na nu mb+ s" {}: the value " mb+ ga gu mb+ s"  cannot be an integer; using 0." mb+ mb-get xerr
    q0 exit
  then
  dq-trunc ;

: brace-eval-impl ( kind -- q true | false ) { kind }
  kind 1 = kind 2 = or if kind brace-enf true exit then
  get-curlb { ta tu f }
  f 0= if q0 true exit then
  kind 0 = if ta tu brace-qad else ta tu kind 3 = if 64 else 32 then brace-fd then
  exp-float @ if qi>dq then
  true ;
' brace-eval-impl is brace-eval
