; ===================================================================
; sparc_reloc2.s -- relocations sparc_reloc.s does not reach
;
; Assemble with -o:  axx sparc.axx sparc_reloc2.s -o out.o
;
; 1. set / setuw / setx of a label take the fixed form llvm-mc writes
;    for a symbol, with R_SPARC_HI22 + LO10 (and HH22 + HM10 for setx)
;    against the symbol (the extra relocations of .reloc, .islabel).
;    A number still takes the shortest form.
; 2. A call or branch to a local label of the same section is resolved
;    here, with no relocation (.elfresolve); a global target keeps its
;    R_SPARC_WDISP30.
; 3. Data written as label-$$, or as a label minus a label of this
;    section, is R_SPARC_DISP8 / 16 / 32 / 64.
; The words and the relocation entries are those of llvm-mc 19 (a local
; label named by its own symbol), and the object links with ld.lld 19.
; ===================================================================
        .extern ext
        .global gfun
        .section .data
dat:
        xword   ext
        xword   ext-$$
        word    ext-$$
        word    ext+8-$$
        word    start-$$
        word    ext-dat
        xword   ext-dat
        word    dat2-dat
        half    ext-$$
        byte    ext-$$
dat2:
        xword   0
        .section .text
start:
        set     ext,%o0
        set     ext+0x1234,%o1
        setuw   dat,%o2
        set     0x12345678,%o3
        set     100,%o4
        setx    ext,%g1,%o4
        setx    dat+8,%g1,%o5
        setx    0x123456789,%g1,%o5
        call    ext
        nop
        call    start
        nop
gfun:
        call    gfun
        nop
        ba      start
        nop
        bne     %icc,start
        nop
        brz     %o0,start
        nop
        fbne    start
        nop
        retl
        nop
