; ===================================================================
; elfpair.s -- test source for elfpair.axx (RISC-V, manual 3.7.10)
;
; What to expect from `readelf -r -g -S`:
;
;   call ext / call foo   R_RISCV_CALL_PLT + R_RISCV_RELAX (.elfextra)
;   dword lend-_start     R_RISCV_ADD32 lend + 0, R_RISCV_SUB32 _start
;   dword ext-_start+4    R_RISCV_ADD32 ext + 4,  R_RISCV_SUB32 _start
;   quad  foo-d0          R_RISCV_ADD64 foo + 0,  R_RISCV_SUB64 d0
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
