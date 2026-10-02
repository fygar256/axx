; ===================================================================
; elfmips64.s -- test source for elfmips64.axx (MIPS64, manual 3.7.10)
;
; Every r_info is laid out by the pattern file's .elfrinfo function;
; `readelf -r` shows the three types of each entry:
;
;   lui    2,%hi(ext)        R_MIPS_HI16/R_MIPS_NONE/R_MIPS_NONE
;   daddiu 2,2,%lo(ext)      R_MIPS_LO16/R_MIPS_NONE/R_MIPS_NONE
;   dword  ext / ext+8       R_MIPS_64/R_MIPS_NONE/R_MIPS_NONE
;   word   ext               R_MIPS_32/R_MIPS_NONE/R_MIPS_NONE
;
;   axx elfmips64.axx elfmips64.s -o out.o
; ===================================================================

        .extern ext
        .global start

        .section .text
start:
        lui     2,%hi(ext)
        daddiu  2,2,%lo(ext)
        jr      31
        nop

        .section .data
        dword   ext
        dword   ext+8
        word    ext
