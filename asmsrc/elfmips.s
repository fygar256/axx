; ===================================================================
; elfmips.s -- test source for elfmips.axx (MIPS32, REL, manual 3.7.10)
;
; The words to expect are those llvm-mc writes for the same code:
;
;   lui   2,%hi(ext)              3c02 0000   R_MIPS_HI16
;   addiu 2,2,%lo(ext)            2442 0000   R_MIPS_LO16
;   lui   3,%hi(ext+0x18000)      3c03 0002   (0x18000 + 0x8000) >> 16
;   addiu 3,3,%lo(ext+0x18000)    2463 8000
;   lw    4,%lo(ext+0x12345)(3)   8c64 2345
;   jal   ext / jal ext+8         0c00 0000 / 0c00 0002   R_MIPS_26
;   word  ext / word ext+4        0000 0000 / 0000 0004   R_MIPS_32
;
;   axx elfmips.axx elfmips.s -o out.o
; ===================================================================

        .extern ext
        .global start

start:
        lui     2,%hi(ext)
        addiu   2,2,%lo(ext)
        lui     3,%hi(ext+0x18000)
        addiu   3,3,%lo(ext+0x18000)
        lw      4,%lo(ext+0x12345)(3)
        jal     ext
        nop
        jal     ext+8
        nop
        jr      31
        nop
        word    ext
        word    ext+4
