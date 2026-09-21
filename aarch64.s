; ===================================================================
; aarch64.s -- test source for aarch64.axx
;
; One or more lines for every instruction group the pattern file
; covers. Every encoding below was compared byte-for-byte against
; llvm-mc -triple=aarch64, and the file assembles to identical bytes
; under both Paxx and Caxx.
;
;   axx aarch64.axx aarch64.s -v
;   axx aarch64.axx aarch64.s -o out.o -m 183
; ===================================================================

; ---- data processing: PC-relative and add/subtract immediate ----
here:
        adr     x0, here
        adrp    x1, here
        add     x0, x1, #5
        add     x0, x1, #5, lsl #12
        add     sp, sp, #16
        adds    w3, w4, #7
        sub     x2, x3, #1
        subs    x2, x3, #1
        cmp     x0, #3
        cmn     w0, #3
        mov     sp, x0
        mov     x0, sp

; ---- logical immediate (the mini-language bitmask encoder) ----
        and     x1, x2, #0xff
        orr     x1, x2, #0x5555555555555555
        eor     w1, w2, #0xf0f0f0f0
        ands    x1, x2, #0xfffffffffffffff0
        tst     w0, #0xff

; ---- move wide, and the MOV alias that chooses among three forms ----
        movz    x0, #0x1234, lsl #16
        movn    w0, #0
        movk    x0, #0xabcd, lsl #32
        mov     x0, #0x1234                     ; MOVZ
        mov     x0, #-1                         ; MOVN
        mov     w0, #0xffff0000                 ; MOVN
        mov     x0, #0x5555555555555555         ; ORR bitmask

; ---- bitfield and extract ----
        sbfm    x0, x1, #3, #7
        ubfx    w0, w1, #4, #8
        sbfiz   x0, x1, #5, #10
        bfi     w0, w1, #2, #6
        bfxil   x0, x1, #1, #20
        ubfiz   x0, x1, #7, #9
        bfc     x0, #4, #8
        asr     x0, x1, #5
        lsr     w0, w1, #3
        lsl     x0, x1, #7
        sxtb    x0, w1
        sxth    w0, w1
        sxtw    x0, w1
        uxtb    w0, w1
        uxth    w0, w1
        extr    x0, x1, x2, #13
        ror     w0, w1, #9

; ---- logical and arithmetic, shifted register ----
        and     x0, x1, x2
        and     x0, x1, x2, lsr #7
        bic     w0, w1, w2, ror #3
        orr     x0, x1, x2, asr #9
        orn     x0, x1, x2
        eor     w0, w1, w2, lsl #1
        eon     x0, x1, x2
        ands    x0, x1, x2, lsl #4
        bics    w0, w1, w2
        mov     x0, x1
        mvn     x0, x1, lsl #2
        tst     x0, x1
        add     x0, x1, x2, lsl #3
        adds    w0, w1, w2, asr #2
        subs    x0, x1, x2, lsr #1
        neg     x0, x1
        negs    w0, w1, lsl #5
        cmn     x0, x1
        cmp     w0, w1, asr #3

; ---- arithmetic, extended register ----
        add     x0, x1, w2, uxtb
        add     x0, x1, w2, sxth #2
        add     x0, x1, x2, uxtx
        adds    x0, x1, w2, uxtw
        sub     sp, sp, x0
        add     sp, sp, x0, lsl #2
        add     x0, sp, x1
        cmp     sp, x0
        add     w0, w1, w2, uxtb
        add     wsp, wsp, w0

; ---- carry, conditional compare, conditional select ----
        adc     x0, x1, x2
        sbcs    w0, w1, w2
        ngc     x0, x1
        ccmp    x0, x1, #5, eq
        ccmn    w0, #3, #7, ne
        csel    x0, x1, x2, ge
        csinc   w0, w1, w2, lt
        csinv   x0, x1, x2, mi
        csneg   w0, w1, w2, vs
        cset    x0, eq
        csetm   w0, ne
        cinc    x0, x1, hi
        cneg    x0, x1, ge

; ---- multiply, divide, shift and bit counting ----
        madd    x0, x1, x2, x3
        msub    w0, w1, w2, w3
        smaddl  x0, w1, w2, x3
        mul     x0, x1, x2
        smull   x0, w1, w2
        umulh   x0, x1, x2
        udiv    x0, x1, x2
        sdiv    w0, w1, w2
        lsl     x0, x1, x2
        ror     w0, w1, w2
        crc32b  w0, w1, w2
        crc32cx w0, w1, x2
        rbit    x0, x1
        rev16   w0, w1
        rev32   x0, x1
        rev     x0, x1
        clz     x0, x1
        cls     w0, w1

; ---- branches ----
        b       here
        bl      here
        b.eq    here
        b.lo    here
        cbz     x0, here
        cbnz    w1, here
        tbz     x0, #40, here
        tbnz    w1, #5, here
        br      x0
        blr     x30
        ret
        ret     x1

; ---- exceptions, hints, barriers ----
        svc     #0
        brk     #0x1234
        hlt     #0
        nop
        yield
        wfe
        sevl
        paciasp
        autiasp
        bti     c
        hint    #17
        clrex
        dsb     sy
        dmb     ishst
        isb
        sb

; ---- system registers and system instructions ----
        msr     daifset, #3
        msr     spsel, #1
        cfinv
        mrs     x0, nzcv
        msr     nzcv, x0
        mrs     x2, midr_el1
        mrs     x3, tpidr_el0
        mrs     x4, cntvct_el0
        mrs     x7, s3_3_c4_c2_0                ; the generic spelling
        msr     s3_0_c15_c13_7, x8
        sys     #3, c7, c5, #1
        sysl    x1, #3, c7, c5, #1
        ic      iallu
        ic      ivau, x0
        dc      zva, x1
        at      s1e1r, x4
        tlbi    vmalle1
        tlbi    vae1is, x5

; ---- loads and stores ----
        ldr     x0, [x1]
        ldr     x0, [x1, #16]
        ldr     x0, [x1, #-8]                   ; falls back to LDUR
        str     x0, [x1, #16]!
        ldr     x0, [x1], #-8
        ldrb    w0, [x1, x2]
        ldrsb   x0, [x1, #3]
        strh    w0, [x1, #2]
        ldrsw   x0, [x1, #4]
        ldr     x0, [x1, x2, lsl #3]
        ldr     x0, [x1, w2, uxtw #3]
        ldr     x0, [x1, w2, sxtw #3]
        ldr     x0, [x1, x2, sxtx]
        ldur    x0, [x1, #-3]
        stur    w0, [x1, #255]
        ldr     x0, here
        ldrsw   x0, here
        str     b0, [x1, #1]
        ldr     h0, [x1, #2]
        str     s0, [x1, #4]
        ldr     d0, [x1, #8]
        str     q0, [x1, #16]
        ldr     q0, [x1, x2, lsl #4]
        stp     x0, x1, [sp, #16]
        ldp     x0, x1, [sp], #16
        stp     w0, w1, [x2, #-8]!
        ldpsw   x0, x1, [x2, #4]
        stp     s0, s1, [x2, #8]
        ldp     d0, d1, [x2, #16]
        stp     q0, q1, [x2, #32]
        stnp    x0, x1, [x2, #8]
        prfm    pldl1keep, [x0, #8]
        prfm    pldl1keep, here

; ---- exclusives, acquire-release, atomics ----
        stxr    w0, x1, [x2]
        stlxrb  w0, w1, [x2]
        ldxr    x0, [x1]
        ldaxrh  w0, [x1]
        stlr    x0, [x1]
        ldar    w0, [x1]
        stxp    w0, x1, x2, [x3]
        ldaxp   w0, w1, [x2]
        cas     x0, x1, [x2]
        casal   w0, w1, [x2]
        ldadd   x0, x1, [x2]
        ldaddal w0, w1, [x2]
        ldclrb  w0, w1, [x2]
        ldsetl  x0, x1, [x2]
        swp     x0, x1, [x2]
        stadd   x0, [x1]
        staddlb w0, [x1]

; ---- scalar floating point ----
        fmov    s0, s1
        fabs    d0, d1
        fneg    s2, s3
        fsqrt   d4, d5
        frintz  d0, d1
        fcvt    s0, d1
        fcvt    d0, s1
        fcvt    h0, s1
        fmul    s0, s1, s2
        fdiv    d0, d1, d2
        fadd    s0, s1, s2
        fsub    d0, d1, d2
        fmaxnm  d0, d1, d2
        fnmul   s0, s1, s2
        fmadd   s0, s1, s2, s3
        fnmsub  d0, d1, d2, d3
        fcmp    s0, s1
        fcmp    s0, #0.0
        fcmpe   d0, d1
        fccmp   s0, s1, #3, eq
        fcsel   d0, d1, d2, le
        fcvtzs  w0, s1
        fcvtzu  w0, d1
        fcvtns  x0, s1
        scvtf   s0, w1
        ucvtf   d0, w1
        fmov    w0, s1
        fmov    s0, w1
        fmov    x0, d1
        fmov    d0, x1
        fmov    s0, #1.0                        ; the 8-bit FP immediate
        fmov    d0, #-0.125
        fmov    s0, #31.0
        fadd    h0, h1, h2
        fmov    h0, #1.0

; ---- fixed-point conversions, RCpc load, compare-and-swap pair ----
        fcvtzs  w0, s1, #4
        fcvtzu  x0, d1, #64
        scvtf   s0, w1, #8
        ucvtf   d0, w1, #31
        ldaprb  w0, [x1]
        ldapr   x0, [x1]
        casp    w0, w1, w2, w3, [x4]
        caspal  x2, x3, x4, x5, [x6]

; ---- forward references resolve through the relaxation loop ----
        b       tail
        adr     x2, tail
        ldr     x4, tail
tail:
        nop
