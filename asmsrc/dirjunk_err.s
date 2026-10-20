; dirjunk_err.s -- z80.axx で指令の引数の後ろに残った文字を確かめる（5 章）
;
; 2026-10-20 まで、.org .align .zero .resb/.resw/.resd/.resq .ascii/.asciz
; .equ .section は引数の後ろの文字を黙って捨てていた（.ascii "a","b" の "b"、
; .section .data,"aw" の旗、x: .equ 5 junk の junk）。どれもエラーにする。
; 正しい行（下の 4 行）は通る。
;
;   axx z80.axx dirjunk_err.s -b out.bin
        .org    0x10 garbage
        .org    0x20,5
        .align  4 junk
        .align  4,7
        .zero   4 x
        .resb   3,4
        .resw   2 y
        .ascii  "a","b"
        .asciz  "a" x
x1:     .equ    5 junk
x2:     .equ    5,6
        .section .text junk
        .section .data,"aw"
        .org    0x40,P
x3:     .equ    5 + 6
        .ascii  "ok"
        .section .data
