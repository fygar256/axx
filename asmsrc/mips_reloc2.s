; ===================================================================
; mips_reloc2.s -- o32 relocations of la and of PC-relative data
;
; Assemble with -o (mips.axx, mipsel.axx, mipsr6.axx or mipsr6el.axx).
;
; la is lui + addiu with R_MIPS_HI16 and R_MIPS_LO16, both against the
; symbol; o32 is REL, so the addend goes back into the fields (HI16
; rounded). Data written as label-$$, or as a label minus a label of
; this section, is R_MIPS_PC32. A difference inside a section is a
; constant. The words and the relocation entries are those of llvm-mc
; 19 (a local label named by its own symbol), and the image linked with
; ld.lld is the same.
; ===================================================================
        .set noreorder
        .set noat
        .extern ext
        .section .text
start:
        la      $t0,ext
        la      $t1,ext+0x12348
        la      $t2,dat
        la      $t3,dat+0x10
        lui     $t4,%hi(ext+0x18000)
        addiu   $t4,$t4,%lo(ext+0x18000)
        jr      $ra
        nop
        .section .data
dat:
        word    ext
        word    ext+4
        word    ext-$$
        word    ext+8-$$
        word    start-$$
        word    ext-dat
        word    start-dat
        word    dat2-dat
        half    dat2-dat
dat2:
        word    0
