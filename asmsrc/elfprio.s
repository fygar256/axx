; ===================================================================
; elfprio.s -- test source for elfprio.axx (manual 3.7.8)
;
; Every line below is decided by one of the three ranks:
;
;   start (jmp)  R_MSP430_PCR16  4  the pattern's `.reloc` beats the
;                                   2-byte default
;   ext   (jmp)  R_MSP430_ABS16  2  `.extern ext::abs16` beats the
;                                   pattern's `.reloc`
;   start (dw)   R_MSP430_ABS16  2  the default for a 2-byte field
;   hi    (dw)   R_MSP430_PCR16  4  `.global hi::pcrel16` beats that
;                                   default
;   start (dd)   R_MSP430_ABS32  1  the default for a 4-byte field
;   start (db)   R_MSP430_ABS8   3  the default for a 1-byte field
;
;   axx elfprio.axx elfprio.s -o out.o
;   axx elfprio.axx elfprio.s -o out.o -E exp.tsv
; ===================================================================

        .extern ext::abs16              ; beats the pattern's .reloc
        .global start
        .global hi::pcrel16             ; beats the 2-byte default

start:
        jmp     start                   ; .reloc  -> pcrel16
        jmp     ext                     ; .extern -> abs16
hi:
        dw      start                   ; default -> abs16
        dw      hi                      ; .global -> pcrel16
        dd      start                   ; default -> abs32
        db      start                   ; default -> abs8
        ret
