; ===================================================================
; elfpair.s -- test source for elfpair.axx (RISC-V, manual 3.7.10)
;
; What to expect from `readelf -r -g -S`:
;
;   call ext / call foo   R_RISCV_CALL_PLT + R_RISCV_RELAX (.elfextra)
;   dword lend-_start     R_RISCV_ADD32 lend + 0, R_RISCV_SUB32 _start
;   dword ext-_start+4    R_RISCV_ADD32 ext + 4,  R_RISCV_SUB32 _start
;   quad  foo-d0          R_RISCV_ADD64 foo + 0,  R_RISCV_SUB64 d0
;   dword lend-_start+d0-d1+4
;                         ADD32 lend + 4, ADD32 d0, SUB32 _start, SUB32 d1
;   dword -(lend-_start)  R_RISCV_ADD32 _start + 0, R_RISCV_SUB32 lend
;   uleb  lend-_start+300 R_RISCV_SET_ULEB128 lend + 300, SUB_ULEB128 _start
;   adv6  lend-_start     R_RISCV_SET6 lend + 0, R_RISCV_SUB6 _start
;   fn                    .eh_frame: the FDE address by R_RISCV_32_PCREL,
;                         the length and the advances by ADD32/SUB32 on
;                         .Lcfi<n> local symbols
;   .text.foo             in the COMDAT group [foo] (flag G)
;   .meta                 SHF_LINK_ORDER, sh_link = .text (flag L)
;
;   axx elfpair.axx elfpair.s -o out.o
; ===================================================================

        .extern ext
        .global _start
        .global foo

        .section .text
_start:
        call    ext
        call    foo
        ret
lend:

fn:
        .cfi_startproc
        addi    sp,sp,-16
        .cfi_def_cfa_offset 16
        sd      ra,8(sp)
        .cfi_offset ra, -8
        call    ext
        ld      ra,8(sp)
        .cfi_restore ra
        addi    sp,sp,16
        .cfi_def_cfa_offset 0
        ret
        .cfi_endproc

        .section .text.foo
foo:
        ret

        .section .meta
        dword   1

        .section .data
d0:
        dword   lend-_start
        dword   ext-_start+4
        quad    foo-d0
d1:
        dword   lend-_start+d0-d1+4
        dword   -(lend-_start)
        uleb    lend-_start+300
        adv6    lend-_start
