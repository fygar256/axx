; ===================================================================
; elfrel.s -- test source for elfrel.axx (EM_ARM, REL, manual 3.7.9)
;
; Every relocation below is REL: the addend is written back into the
; instruction field, shifted and biased as the pattern file's
; `.elffield` says. The words to expect are those GNU as and llvm-mc
; write for the same code:
;
;   bl  ext        eb fffffe   R_ARM_CALL         (-8) >> 2
;   bl  ext+16     eb 000002   R_ARM_CALL         (16-8) >> 2
;   b   ext2       ea fffffe   R_ARM_JUMP24
;   movw r0,dat    e300 0000   R_ARM_MOVW_ABS_NC
;   movt r0,dat    e340 0000   R_ARM_MOVT_ABS
;   movw r1,dat+0x12345  e302 1345  (low 16 bits of the addend)
;   movt r1,dat+0x12345  e342 1345
;   dd  dat / dat+4      0 / 4      R_ARM_ABS32
;
;   axx elfrel.axx elfrel.s -o out.o
; ===================================================================

        .extern ext
        .extern ext2
        .extern dat
        .global start

start:
        bl      ext
        bl      ext+16
        b       ext2
        movw    r0,%lo16(dat)
        movt    r0,%hi16(dat)
        movw    r1,%lo16(dat+0x12345)
        movt    r1,%hi16(dat+0x12345)
        bx      lr
        dd      dat
        dd      dat+4
