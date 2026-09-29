; ===================================================================
; elfsec.s -- test source for elfsec.axx (manual 3.7.7)
;
; The expected section headers are
;
;   .text        PROGBITS  AX   align 16  (from the name rule)
;   .vectors     PROGBITS  AX   align 16  (.elfsection::.vectors::0x6)
;   .noinit      NOBITS    WA   align 16  (.elfsection::.noinit::0x3::8)
;   .note.axx    NOTE      --   align  4  (SHT_NOTE default)
;   .vectors2    PROGBITS  AX   align  2  (.elfsection::.vectors2::0x6::1::2)
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
;       a well-formed ELF note: n_namesz, n_descsz, n_type, then the
;       name and the descriptor. readelf reads this one because the
;       section now carries the word alignment the gABI asks for.
        db      0x04             ; n_namesz = 4 ("axx\0")
        db      0x00
        db      0x00
        db      0x00
        db      0x04             ; n_descsz = 4
        db      0x00
        db      0x00
        db      0x00
        db      0x01             ; n_type = 1
        db      0x00
        db      0x00
        db      0x00
        db      0x61             ; "axx\0"
        db      0x78
        db      0x78
        db      0x00
        db      0xde             ; descriptor
        db      0xad
        db      0xbe
        db      0xef
        .section .vectors2
        db      0x56
        db      0x78
