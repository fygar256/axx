; ===================================================================
; riscv64_reloc2.s -- data relocations of riscv64.axx under -o
;
; Assemble with -o:  axx riscv64.axx riscv64_reloc2.s -o out.o
;
; Data written as label-$$ is an ADD/SUB pair: the label added and a
; local symbol (.Lanchor<n>) axx places on the field subtracted. A
; label difference across sections, or with an external symbol, is an
; ADD/SUB pair too; one inside a section is a constant. A branch, jump or
; call to a local label of the same section is resolved here with no
; relocation (.elfresolve, .elfencode). The entries are
; those llvm-mc 19 (no relax) writes, and the linked image (ld.lld) is
; identical.
; ===================================================================
        .extern ext
        .section .text
start:
        call    ext
        beq     a0,a1,start
        j       start
        call    start
        ret
        .section .data
dat:
        quad    ext
        quad    ext-$$
        dword   ext-$$
        dword   ext+4
        dword   start-$$
        quad    ext-dat
        dword   ext-dat
        quad    dat2-dat
        dword   start-dat
dat2:
        quad    0
