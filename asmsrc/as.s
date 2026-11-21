; ===================================================================
; as.s -- test source for as.axx (`.as`, manual 3.7.12)
;
;   ld  b,c        41            s has r's 8-bit list
;   ld  a,l        7d
;   add d,e        93            p and q too
;   inc hl         23            r is now BC,DE,HL,SP
;   inc sp         33
;   sub a          97            s keeps the 8-bit list
;   dec de         1b            r = x (BC,DE,HL)
;   jp  hl         c3 02 00      s has no list any more
;   jp  sp         c3 03 00
;   pushm r0-r2    e0 07         n has m's .enum
;   popm  r1/r3    e1 0a
;   call ext       e8 ...        u has t's .reloc (pc32)
;   dd   ext       ...           v has w's .reloc (abs32)
;   dw   ext       ...           t has no .reloc
;
;   axx as.axx as.s -b out.bin
;   axx as.axx as.s -o out.o -m 62
; ===================================================================
        .extern ext
        ld      b,c
        ld      a,l
        add     d,e
        inc     hl
        inc     sp
        sub     a
        dec     de
        jp      hl
        jp      sp
        pushm   r0-r2
        popm    r1/r3
        call    ext
        dd      ext
        dw      ext
        ret
