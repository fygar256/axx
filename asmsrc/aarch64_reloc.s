; ===================================================================
; aarch64_reloc.s -- relocations of aarch64.axx under -o
;
; Assemble with:  axx aarch64.axx aarch64_reloc.s -o out.o
; (no -m is needed: aarch64.axx declares EM_AARCH64)
;
; 1. Every instruction relocation against an external symbol: CALL26,
;    JUMP26, CONDBR19, TSTBR14, ADR_PREL_LO21, ADR_PREL_PG_HI21,
;    ADD_ABS_LO12_NC, LDST8/32/64/128_ABS_LO12_NC, LD_PREL_LO19,
;    MOVW_UABS_G*, ADR_GOT_PAGE, LD64_GOT_LO12_NC.
; 2. A branch, adr or literal ldr to a local label of the same section is
;    resolved here with no relocation (.elfresolve; adr through
;    .elfencode). adrp and :lo12: keep theirs, and so does a global target.
; 3. Data: .quad / .word / .hword take ABS64 / ABS32 / ABS16, and a value
;    written as label-$$, or as a label minus a label of this section,
;    takes PREL64 / PREL32 / PREL16.
; The words and the relocation entries are those of llvm-mc 19 (a local
; label named by its own symbol), and the object links with ld.lld 19.
; ===================================================================
        .extern ext
        .global gfun
        .section .data
dat:
        .quad   ext
        .quad   ext+8
        .quad   ext-$$
        .word   ext-$$
        .word   ext+4
        .word   ext+12-$$
        .word   start-$$
        .xword  start+4-$$
        .word   ext-dat
        .quad   ext-dat
        .word   dat2-dat
        .hword  ext-$$
        .hword  ext
        .byte   1
dat2:
        .quad   0
        .section .text
start:
        b       ext
        bl      ext+8
        b.eq    ext
        cbz     x0,ext
        tbz     x1,#3,ext
        adr     x2,ext
        adrp    x3,ext
        add     x3,x3,:lo12:ext
        ldr     x4,[x3,:lo12:ext]
        ldr     w4,[x3,:lo12:ext+8]
        ldrb    w4,[x3,:lo12:ext]
        ldr     q4,[x3,:lo12:ext]
        ldr     x5,ext
        movz    x6,#:abs_g0_nc:ext
        movk    x6,#:abs_g1_nc:ext
        movz    x6,#:abs_g3:ext
        adrp    x7,:got:ext
        ldr     x7,[x7,:got_lo12:ext]
loop1:
        b       loop1
        bl      gfun
        b.ne    loop1
        cbnz    x0,loop1
        tbnz    x1,#3,fwd
        adr     x1,loop1
        ldr     x2,fwd
        adrp    x3,dat
        add     x3,x3,:lo12:dat
fwd:
        nop
gfun:
        bl      gfun
        ret
