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

; ---- Advanced SIMD: three same, two-register misc ----
        add     v0.16b, v1.16b, v2.16b
        sub     v0.2d, v1.2d, v2.2d
        sqadd   v0.8h, v1.8h, v2.8h
        umax    v0.4s, v1.4s, v2.4s
        cmgt    v0.2d, v1.2d, v2.2d
        mul     v0.4h, v1.4h, v2.4h
        and     v0.8b, v1.8b, v2.8b
        bsl     v0.16b, v1.16b, v2.16b
        orn     v0.16b, v1.16b, v2.16b
        mov     v0.16b, v1.16b
        fadd    v0.4s, v1.4s, v2.4s
        fmla    v0.2d, v1.2d, v2.2d
        fdiv    v0.8h, v1.8h, v2.8h
        facgt   v0.4s, v1.4s, v2.4s
        sqrdmlah v0.4s, v1.4s, v2.4s
        rev64   v0.4s, v1.4s
        cnt     v0.16b, v1.16b
        not     v0.8b, v1.8b
        rbit    v0.16b, v1.16b
        clz     v0.4s, v1.4s
        abs     v0.2d, v1.2d
        cmeq    v0.8h, v1.8h, #0
        fcmlt   v0.4s, v1.4s, #0
        fabs    v0.2d, v1.2d
        fcvtzs  v0.4h, v1.4h
        scvtf   v0.4s, v1.4s
        frint64x v0.2d, v1.2d

; ---- SIMD widening, narrowing, pairwise, three-different ----
        saddlp  v0.4s, v1.8h
        uadalp  v0.2d, v1.4s
        xtn     v0.8b, v1.8h
        xtn2    v0.16b, v1.8h
        sqxtun  v0.4h, v1.4s
        fcvtn   v0.4h, v1.4s
        fcvtl2  v0.2d, v1.4s
        shll    v0.4s, v1.4h, #16
        smull   v0.4s, v1.4h, v2.4h
        umlal2  v0.2d, v1.4s, v2.4s
        sqdmull v0.4s, v1.4h, v2.4h
        saddw   v0.8h, v1.8h, v2.8b
        raddhn  v0.2s, v1.2d, v2.2d
        pmull   v0.8h, v1.8b, v2.8b
        pmull2  v0.1q, v1.2d, v2.2d

; ---- SIMD across lanes, permute, extract, table ----
        addv    b0, v1.16b
        saddlv  s0, v1.8h
        fmaxnmv s0, v1.4s
        fminv   h0, v1.8h
        zip1    v0.4s, v1.4s, v2.4s
        uzp2    v0.2d, v1.2d, v2.2d
        trn1    v0.8b, v1.8b, v2.8b
        ext     v0.16b, v1.16b, v2.16b, #7
        tbl     v0.8b, {v30.16b}, v2.8b
        tbl     v0.16b, {v30.16b, v31.16b}, v2.16b
        tbx     v0.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v2.16b

; ---- SIMD copy and modified immediate ----
        dup     v0.4s, v1.s[2]
        dup     v0.2d, x1
        dup     b0, v1.b[9]
        smov    x0, v1.h[3]
        umov    w0, v1.s[1]
        ins     v0.d[1], x1
        mov     v0.b[7], v1.b[2]
        movi    v0.16b, #0xab
        movi    v0.4s, #0x12, lsl #16
        movi    v0.4s, #0x12, msl #8
        mvni    v0.8h, #0x34, lsl #8
        orr     v0.4s, #0x56
        bic     v0.8h, #0x78, lsl #8
        movi    v0.2d, #0xff00ff00ff00ff00
        movi    d0, #0xffff0000ffff0000
        fmov    v0.4s, #1.0
        fmov    v0.2d, #-0.125
        fmov    v0.8h, #31.0

; ---- SIMD shift by immediate, by element ----
        sshr    v0.16b, v1.16b, #3
        urshr   v0.2d, v1.2d, #64
        sli     v0.4h, v1.4h, #5
        sqshlu  v0.4s, v1.4s, #31
        shrn2   v0.8h, v1.4s, #16
        sqrshrun v0.2s, v1.2d, #1
        sshll   v0.2d, v1.2s, #7
        uxtl2   v0.8h, v1.16b
        scvtf   v0.4s, v1.4s, #4
        fcvtzu  v0.2d, v1.2d, #64
        mul     v0.8h, v1.8h, v15.h[7]
        mla     v0.4s, v1.4s, v31.s[3]
        fmla    v0.2d, v1.2d, v31.d[1]
        fmulx   v0.4h, v1.4h, v15.h[5]
        smlal2  v0.2d, v1.4s, v31.s[2]
        sqdmull v0.4s, v1.4h, v15.h[1]
        sdot    v0.4s, v1.16b, v31.4b[3]

; ---- SIMD load and store structures ----
        ld1     {v0.16b}, [x1]
        ld1     {v0.8h, v1.8h}, [x1], #32
        st1     {v0.4s, v1.4s, v2.4s}, [x1], x3
        ld2     {v0.2d, v1.2d}, [x1]
        st3     {v0.8b, v1.8b, v2.8b}, [x1], #24
        ld4     {v0.4h, v1.4h, v2.4h, v3.4h}, [x1], x3
        ld1     {v0.b}[15], [x1]
        st2     {v0.s, v1.s}[3], [x1], #8
        ld4     {v0.d, v1.d, v2.d, v3.d}[1], [x1], x3
        ld1r    {v0.4s}, [x1]
        ld3r    {v0.8h, v1.8h, v2.8h}, [x1], #6

; ---- SIMD scalar forms ----
        add     d0, d1, d2
        sqadd   b0, b1, b2
        sqdmulh h0, h1, h2
        facge   s0, s1, s2
        fabd    d0, d1, d2
        sqabs   s0, s1
        cmle    d0, d1, #0
        fcvtzs  h0, h1
        frecpx  s0, s1
        sqxtn   b0, h1
        addp    d0, v1.2d
        faddp   s0, v1.2s
        sshr    d0, d1, #7
        sqshrn  h0, s1, #16
        ucvtf   d0, d1, #32
        sqdmlal s0, h1, h2
        sqdmulh h0, h1, v15.h[6]
        fmla    d0, d1, v31.d[1]

; ---- cryptography, complex arithmetic, matrix multiply ----
        aese    v0.16b, v1.16b
        sha1c   q0, s1, v2.4s
        sha256h2 q0, q1, v2.4s
        sha512su1 v0.2d, v1.2d, v2.2d
        eor3    v0.16b, v1.16b, v2.16b, v3.16b
        xar     v0.2d, v1.2d, v2.2d, #13
        sm3tt1a v0.4s, v1.4s, v2.s[2]
        sm4e    v0.4s, v1.4s
        fcadd   v0.4s, v1.4s, v2.4s, #270
        fcmla   v0.2d, v1.2d, v2.2d, #180
        fcmla   v0.4s, v1.4s, v2.s[1], #90
        fmlal   v0.4s, v1.4h, v2.4h
        fmlsl2  v0.2s, v1.2h, v2.h[5]
        smmla   v0.4s, v1.16b, v2.16b
        usdot   v0.4s, v1.16b, v31.4b[2]
        bfdot   v0.4s, v1.8h, v2.8h
        bfmlalt v0.4s, v1.8h, v2.h[7]
        bfcvtn2 v0.8h, v1.4s

; ---- pointer authentication, memory tagging, MOPS ----
        pacia   x0, x1
        pacia   x0, sp
        autdzb  x0
        xpaci   x0
        braa    x0, x1
        retab
        ldraa   x0, [x1, #8]!
        addg    x0, x1, #16, #3
        irg     x0, x1, x2
        subps   x0, x1, x2
        stg     x0, [x1, #16]!
        st2g    x0, [x1], #16
        ldg     x0, [x1, #-16]
        stgp    x0, x1, [x2, #16]
        cpyfprn [x0]!, [x1]!, x2!
        setgpt  [x0]!, x1!, x2
        ldapursw x0, [x1, #-4]
        stlurh  w0, [x1, #2]
        fjcvtzs w0, d1
        ld64b   x2, [x1]
        rmif    x0, #13, #7
        setf8   w0
        axflag
        chkfeat x16

; ---- relocation modifiers ----
; axx works the symbol out itself instead of leaving the field for a
; linker, so :lo12: and friends come out already filled in. Here they
; all name "here", which sits at address 0, so every slice is zero.
; (:pg_hi21: is supported too but is left out here: GNU as takes that
;  spelling, llvm-mc does not, and this file is compared against both.)
        adrp    x0, here
        add     x0, x0, :lo12:here
        add     x0, x0, #:lo12:here
        add     w1, w1, :lo12:here
        add     sp, sp, :lo12:here
        ldr     x1, [x0, :lo12:here]
        ldr     x1, [x0, #:lo12:here]
        ldrb    w2, [x0, :lo12:here]
        ldrh    w2, [x0, :lo12:here]
        ldrsw   x2, [x0, :lo12:here]
        str     q0, [x0, :lo12:here]
        ldr     d0, [x0, :lo12:here]
        prfm    pldl1keep, [x0, :lo12:here]
        movz    x4, #:abs_g0_nc:here
        movk    x4, #:abs_g1_nc:here
        movk    x4, #:abs_g2_nc:here
        movk    x4, #:abs_g3:here
        movz    x5, :abs_g0:here
        movn    x6, #:abs_g1:here
        movz    w7, #:abs_g0_nc:here
; :got: and :got_lo12: name the GOT slot itself, since axx builds no
; GOT of its own; "here" stands in for the slot below.
        adrp    x8, :got:here
        ldr     x8, [x8, :got_lo12:here]
        adrp    x9, #:got:here
        ldr     x9, [x9, #:got_lo12:here]

; ---- forward references resolve through the relaxation loop ----
        b       tail
        adr     x2, tail
        ldr     x4, tail
tail:
        nop

; ---- SVE ----
        ptrue   p0.s
        ptrue   p1.b, vl8
        whilelt p2.s, x0, x1
        index   z0.s, #0, #1
        index   z1.d, x0, x1
        cntb    x2
        cntw    x3, mul4, mul #3
        incd    z2.d, all, mul #2
        addvl   x4, x4, #-2
        rdvl    x5, #1
        dup     z3.b, w0
        dup     z4.s, z5.s[3]
        dupm    z6.h, #0xf00f
        mov     z7.d, p0/m, z8.d
        add     z9.s, p0/m, z9.s, z10.s
        mul     z11.h, z11.h, z12.h
        sdot    z13.s, z14.b, z15.b
        smmla   z16.s, z17.b, z18.b
        asr     z19.b, p1/m, z19.b, #3
        cmpgt   p3.s, p0/z, z0.s, z1.s
        fadd    z20.d, p0/m, z20.d, #1.0
        fmla    z21.s, p0/m, z22.s, z23.s
        fmul    z24.h, z25.h, z6.h[5]
        fcmla   z27.s, p0/m, z28.s, z29.s, #270
        fcvtzs  z30.d, p0/m, z31.s
        fmov    z0.s, #-2.5
        faddv   s1, p0, z2.s
        saddv   d3, p0, z4.b
        lastb   x6, p0, z5.d
        clasta  z6.h, p0, z6.h, z7.h
        zip1    z8.b, z9.b, z10.b
        punpklo p4.h, p5.b
        movprfx z11.s, p0/m, z12.s
        abs     z11.s, p0/m, z12.s
        ldr     z13, [x7, #3, mul vl]
        str     p6, [x8, #-1, mul vl]
        ld1w    {z14.s}, p0/z, [x9, x10, lsl #2]
        ld1sb   {z15.d}, p0/z, [x11, #-4, mul vl]
        ldnf1h  {z16.h}, p0/z, [x12]
        ldff1d  {z17.d}, p0/z, [x13, x14, lsl #3]
        ld2d    {z18.d, z19.d}, p0/z, [x15, #4, mul vl]
        st4b    {z20.b, z21.b, z22.b, z23.b}, p0, [x16, x17]
        ld1rw   {z24.s}, p0/z, [x18, #12]
        ld1rqd  {z25.d}, p0/z, [x19, #-16]
        ld1d    {z26.d}, p0/z, [x20, z27.d, lsl #3]
        st1w    {z28.s}, p0, [x21, z29.s, sxtw #2]
        ld1sh   {z30.s}, p0/z, [z31.s, #6]
        prfw    pldl1keep, p0, [x22, x23, lsl #2]
        prfd    #5, p0, [z0.d, #16]

; ---- SVE2 ----
        smullb  z1.s, z2.h, z3.h
        addhnt  z4.b, z5.h, z6.h
        sqrshrunb z7.h, z8.s, #5
        srsra   z9.d, z10.d, #17
        saba    z11.b, z12.b, z13.b
        bext    z14.s, z15.s, z16.s
        cadd    z17.h, z17.h, z18.h, #270
        cmla    z19.s, z20.s, z21.s, #90
        cdot    z22.s, z23.b, z4.b[2], #180
        sqrdmlah z25.h, z26.h, z7.h[3]
        smlalt  z27.d, z28.s, z9.s[1]
        fmlalb  z30.s, z31.h, z3.h[6]
        histcnt z0.s, p0/z, z1.s, z2.s
        match   p7.b, p0/z, z3.b, z4.b
        tbx     z5.d, z6.d, z7.d
        xar     z8.s, z8.s, z9.s, #7
        bsl     z10.d, z10.d, z11.d, z12.d
        aese    z13.b, z13.b, z14.b
        rax1    z15.d, z16.d, z17.d
        whilerw p1.d, x24, x25
        ldnt1w  {z18.s}, p0/z, [z19.s, x26]
        stnt1d  {z20.d}, p0, [z21.d, x27]

; ---- SME ----
        smstart
        smstart sm
        smstop  za
        rdsvl   x28, #-3
        addsvl  x29, x28, #2
        addspl  x0, x1, #1
        zero    {za}
        zero    {za0.s, za2.s}
        mova    z1.h, p0/m, za1v.h[w13, 5]
        mova    za3h.s[w14, 2], p0/m, z2.s
        ld1b    {za0h.b[w12, 9]}, p0/z, [x2, x3]
        st1q    {za15v.q[w15, 0]}, p0, [x4]
        ldr     za[w12, 0], [x5]
        str     za[w13, 6], [x6, #6, mul vl]
        addha   za2.s, p0/m, p1/m, z3.s
        addva   za6.d, p0/m, p1/m, z4.d
        smopa   za1.s, p0/m, p1/m, z5.b, z6.b
        usmops  za0.d, p2/m, p3/m, z7.h, z8.h
        fmopa   za2.s, p0/m, p1/m, z9.h, z10.h
        bfmops  za3.s, p0/m, p1/m, z11.h, z12.h
        psel    p2, p3, p4.s[w12, 1]
        revd    z13.q, p0/m, z14.q
        sclamp  z15.b, z16.b, z17.b
        fclamp  z18.d, z19.d, z20.d
        ctermeq x7, x8
