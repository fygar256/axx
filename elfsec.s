; ===================================================================
; elfsec.s -- test source for elfsec.axx (manual 3.7.7)
;
; The expected section headers are
;
;   .text        PROGBITS  AX   (from the name rule)
;   .vectors     PROGBITS  AX   (.elfsection::.vectors::0x6)
;   .noinit      NOBITS    WA   (.elfsection::.noinit::0x3::8)
;   .note.axx    NOTE      --   (.elfsection::.note.axx::0::7)
;
;   axx elfsec.axx elfsec.s -o out.o
; ===================================================================

        .section .text
        nop
        nop
        .section .vectors
        db      0x12
        db      0x34
        .section .noinit
        db      0
        db      0
        db      0
        db      0
        .section .note.axx
        db      0x41
