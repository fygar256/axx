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
