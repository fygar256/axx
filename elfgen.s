; ===================================================================
; elfgen.s -- test source for elfgen.axx (EM_MSP430, manual 3.7.7)
;
; The machine is not one of the eleven axx knows; every relocation
; type below comes from the pattern file's `.elftype` declarations.
; The expected relocations are
;
;   ext1   R_MSP430_ABS16   2  (.elfextern default, 2-byte field)
;   ext2   R_MSP430_ABS32   1  (.extern ext2::abs32, 4-byte field)
;   start  R_MSP430_PCR16   4  (.reloc::t::pcrel16 in the pattern)
;   start  R_MSP430_ABS16   2  (.elfwidth::2, no type written)
;   start  R_MSP430_ABS8    3  (.elfwidth::1, no type written)
;
;   axx elfgen.axx elfgen.s -o out.o
;   axx elfgen.axx elfgen.s -o out.o -E exp.tsv
; ===================================================================

        .extern ext1                    ; type comes from .elfextern
        .extern ext2::abs32             ; an .elftype name in .extern
        .global start

start:
        call    ext1                    ; .elfextern -> abs16
        jmp     start                   ; .reloc     -> pcrel16
        dw      start                   ; .elfwidth::2 -> abs16
        db      start                   ; .elfwidth::1 -> abs8
        dd      ext2                    ; .extern     -> abs32
        ret
