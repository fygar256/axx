; `**` とシフトのエラーのあとも 0 にして式の残りを読み進める
e 2**-1**2
e (2<<70000<<140)
e 1>>-1>>2
; 定義に失敗したラベル（二重定義・パターンファイルのシンボル）の行は残りも組まない
dup: e 1
dup: e 2
R0: e 3
; .EQU が複数セクションのラベルに触れたら、警告にセクション名を並べる
.section .text
t1: e 1
.section .data
d1: e 2
c1: .equ d1-t1
; 未定義を含む .EQU の値はセクション相対に直さず、未定義のまま後ろへ伝える
.section .data
u1: .equ nosuch+1
u2: .equ u1+2
e u2
; UTF-8 の多バイト文字は文字定数にならない
e 'é'
; 2026-10-14: ソースの行の error / warning には場所 [file:line] が付く。同じ行で場所まで
; 同じ診断は 1 回だけ。.include で開けないときは .include を書いた行の場所
e 1/0+1/0
e nosuch2+nosuch2
 .include "regress_no_such_file.s"
; error_patterns の整数モード: 64 ビットを 1 だけ外れた値、ちょうど 0xffffffffffffffff、
; 浮動小数点モードの割り算（7/2 = 3.5 > 3）、条件の := の値
C64 18446744073709551616
C64 -9223372036854775809
CX 0xffffffffffffffff
CD 7
CA 60
; 2026-10-18: 短絡しない側の見張りは働く（100/10 > 3 でエラー 3）。`[[ ]]` が 20 個を
; 超えるパターンの警告はパターンごとに 1 回、組み合わせの上限で当たらなかった警告も 1 回
CZ 10
oh bbbbbbbbbbbbbbbbbbbbbc
oh bbbbbbbbbbbbbbbbbbbbbc
og bbbbbbbbc
og bbbbbbbbc
; 2026-10-20: flt{} / dbl{} の中身の誤り（Python と同じく読めない綴り・整数だけの演算・
; 0 で割る・有限でない途中の値）。enflt{} / endbl{} の整数にできない値
rc2: .equ flt{nan}
rd2: .equ dbl{1e300}
e dbl{1.2.3}
e dbl{01}
e dbl{1_}
e dbl{~0.5}
e dbl{3&1.5}
e dbl{1<<300}
e dbl{1<2}
e dbl{1e308*10/10}
e dbl{2**-1/0}
e flt{2**128}
e enflt{rc2}
e endbl{rd2}
; !Q でも本当に 0 で割るとエラー
Q 1/(1-1)
