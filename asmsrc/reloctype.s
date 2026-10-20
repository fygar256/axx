; ===================================================================
; reloctype.s -- x86_64.axx で .reloctype（5.5.1 節）を -o で確かめる
;
; .reloctype で選んだ型は、値を見て絶対と PC 相対を選び直す推測にかけない。
; 型を書かない .extern の既定の型（x86-64 は PC32）も上書きする。
; 2026-10-20 まで、上書きした型が推測で元に戻され、.reloctype は効いていなかった。
;
;   axx x86_64.axx reloctype.s -o out.o
; ===================================================================

        .extern ext
        .section .data
lab:
        db      lab
        dw      lab
        dd      lab
        dq      lab
        dd      ext
.reloctype pc8,pc16,pc32,pc64
        db      lab
        dw      lab
        dd      lab
        dq      lab
        dd      ext
.reloctype ,,abs32s
        dd      lab
        dd      ext
