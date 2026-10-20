; ===================================================================
; cfiptr.s -- elfcfi.axx で .cfi_personality / .cfi_lsda の符号化を並べる
;
; 絶対の符号化（0x00・0x02〜0x04・0x0a〜0x0c、0x80 付きも）は絶対のデータ型
; （R_X86_64_16 / 32 / 64）、PC 相対（0x10 付き）は PC 相対の型になる。
; 4 バイトの絶対を PC32 で書いていた誤り（2026-10-20）の回帰。
; `llvm-readelf -r` のリロケーションの型は、同じソースを llvm-mc で組んだものと一致する。
;
;   axx elfcfi.axx cfiptr.s -o out.o
; ===================================================================

        .extern pers
        .extern lsda1
        .section .text
        .global f0
f0:
        .cfi_startproc
        .cfi_personality 0x03, pers
        .cfi_lsda 0x0b, lsda1
        push    rbp
        .cfi_def_cfa_offset 16
        pop     rbp
        ret
        .cfi_endproc

        .global f1
f1:
        .cfi_startproc
        .cfi_personality 0x83, pers
        .cfi_lsda 0x02, lsda1
        push    rbp
        .cfi_def_cfa_offset 16
        pop     rbp
        ret
        .cfi_endproc

        .global f2
f2:
        .cfi_startproc
        .cfi_personality 0x12, pers
        .cfi_lsda 0x1a, lsda1
        push    rbp
        .cfi_def_cfa_offset 16
        pop     rbp
        ret
        .cfi_endproc

        .global f3
f3:
        .cfi_startproc
        .cfi_personality 0x00, pers
        .cfi_lsda 0x9b, lsda1
        push    rbp
        .cfi_def_cfa_offset 16
        pop     rbp
        ret
        .cfi_endproc

        .global f4
f4:
        .cfi_startproc
        .cfi_personality 0x04, pers
        .cfi_lsda 0x0c, lsda1
        push    rbp
        .cfi_def_cfa_offset 16
        pop     rbp
        ret
        .cfi_endproc
