; ===================================================================
; elfcfi.s -- test source for elfcfi.axx (x86-64 CFI, manual 3.7.11)
;
; `llvm-dwarfdump --eh-frame` on the object reads the same rows as on
; the object llvm-mc writes for the same code.
;
;   axx elfcfi.axx elfcfi.s -o out.o
; ===================================================================

        .extern ext
        .global f
        .global g

        .section .text
f:
        .cfi_startproc
        push    rbp
        .cfi_def_cfa_offset 16
        .cfi_offset rbp, -16
        mov     rbp,rsp
        .cfi_def_cfa_register rbp
        push    rbx
        .cfi_offset rbx, -24
        sub     rsp,0x1000
        call    ext
        add     rsp,0x1000
        pop     rbx
        .cfi_restore rbx
        pop     rbp
        .cfi_def_cfa rsp, 8
        ret
        .cfi_endproc

g:
        .cfi_startproc
        .cfi_remember_state
        push    rbx
        .cfi_adjust_cfa_offset 8
        .cfi_rel_offset rbx, 0
        pop     rbx
        .cfi_restore_state
        ret
        .cfi_endproc
