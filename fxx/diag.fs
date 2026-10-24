\ diag.fs -- 診断の出力。axx.py の AssemblerState.diag と同じ規則。
\
\   diag-text ( a u set-error force -- )
\ 照合の試行中は溜めておき、採られた試行のぶんだけをあとで流す。
\ 同じ行の中で `[file:line]` で終わる同じ診断は 2 度目から出さない。

decimal

variable had-error
variable diag-count
variable in-match
variable pass                      \ 0=対話 1=パス1 2=パス2
variable cur-file-a  variable cur-file-u
variable line-no
variable pend-on
variable pend-sb

: report? ( -- f ) pass @ 2 = pass @ 0= or ;

: file! ( a u -- ) cur-file-u ! cur-file-a ! ;
: file@ ( -- a u ) cur-file-a @ cur-file-u @ ;

\ ---- 同じ行で同じ診断を繰り返さない ----
sb-new constant seen-sb               \ 診断を LF 区切りで並べる
: seen-reset ( -- ) seen-sb sb-clear ;
: seen-has? ( a u -- f ) { a u }
  seen-sb sb$ { sa su }  0 { st }
  su 0 ?do
    sa i + c@ 10 = if
      sa st + i st - a u str=cs if true unloop exit then
      i 1+ to st
    then
  loop false ;
: seen-add ( a u -- ) seen-sb sb+  10 seen-sb sb-c ;

\ 末尾が `[file:ライン]` (後ろに空白・タブは可) か
: has-loc? ( a u -- f ) { a u }
  begin u 0> if a u + 1- c@ spc? else false then while u 1- to u repeat
  u 0= if false exit then
  a u + 1- c@ 93 <> if false exit then
  u 2 - { k }
  begin k 0>= if a k + c@ digc? else false then while k 1- to k repeat
  k u 2 - = if false exit then                    \ 数字が 1 つも無い
  k 0< if false exit then
  a k + c@ 58 <> if false exit then
  k 1- to k
  begin k 0>= if a k + c@ dup 91 <> swap 93 <> and else false then while k 1- to k repeat
  k 0>= if a k + c@ 91 = else false then ;

: starts-diag? ( a u -- f )
  2dup s"  error - " starts? if 2drop true exit then
  s"  warning - " starts? ;

\ 場所を足す (diag_locate)
: diag-locate ( a u -- a' u' ) { a u }
  cur-file-u @ 0= if a u exit then
  a u starts-diag? 0= if a u exit then
  a u 10 has-ch? if a u exit then
  a u has-loc? if a u exit then
  a u s"   [" sconcat file@ sconcat s" :" sconcat line-no @ n>s sconcat s" ]" sconcat ;

: diag-print ( a u -- )
  2dup 10 has-ch? 0= if
    2dup has-loc? if
      2dup seen-has? if 2drop exit then
      2dup seen-add
    then
  then
  etype ecr ;

: diag-text ( a u set-error force -- ) { a u se force }
  1 diag-count +!
  ar-mark { mk }
  force 0= if a u diag-locate to u to a then
  force 0= if
    in-match @ if
      pend-on @ if
        se if s" 1" else s" 0" then pend-sb @ sb+
        a u pend-sb @ sb+  1 pend-sb @ sb-c
      then
      mk ar-release exit
    then
    report? 0= if mk ar-release exit then
  then
  a u diag-print
  se if true had-error ! then
  mk ar-release ;

: diag-e ( a u -- ) true false diag-text ;           \ " error - ..." (had-error を立てる)
: diag-w ( a u -- ) false false diag-text ;          \ " warning - ..."
: diag-ef ( a u -- ) true true diag-text ;           \ force
: diag-wf ( a u -- ) false true diag-text ;

\ 照合の試行の診断の溜め置き
: pend-init ( -- ) sb-new pend-sb ! ;
: pend-begin ( -- ) true pend-on !  pend-sb @ sb-clear ;
: pend-take ( -- a u ) false pend-on !  pend-sb @ sb$ sdup ;
: pend-replay ( a u -- ) { a u }
  report? 0= if exit then
  0 { st }
  u 0 ?do
    a i + c@ 1 = if
      a st + 1+ i st - 1- a st + c@ 49 = { se } diag-print
      se if true had-error ! then
      i 1+ to st
    then
  loop ;
