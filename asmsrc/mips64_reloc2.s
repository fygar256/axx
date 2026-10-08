; ===================================================================
; mips64_reloc2.s -- n64 relocations of la / dla and of PC-relative data
;
; Assemble with -o (mips64.axx, mips64el.axx, mips64r6.axx or
; mips64r6el.axx).
;
; la and dla are the six-word form with R_MIPS_HIGHEST, R_MIPS_HIGHER,
; R_MIPS_HI16 and R_MIPS_LO16, all against the symbol with its addend.
; Data written as label-$$, or as a label minus a label of this
; section, is R_MIPS_PC32, or for 8 bytes the composite R_MIPS_PC32 /
; R_MIPS_64. The words and the relocation entries are those of llvm-mc
; 19 (a local label named by its own symbol), and the image linked with
; ld.lld is the same.
; ===================================================================
        .set noreorder
        .set noat
        .extern ext
        .section .text
start:
        dla     $t0,ext
        dla     $t1,ext+0x123456789
        la      $t2,dat
        la      $t3,dat+0x10
        jr      $ra
        nop
        .section .data
dat:
        dword   ext
        dword   ext-$$
        dword   ext+8-$$
        word    ext-$$
        word    ext-dat
        dword   ext-dat
        dword   start+4-$$
        word    start-$$
        dword   dat2-dat
dat2:
        dword   0
