; aarch64_edge.s -- aarch64.axx の範囲の境目の回帰テスト（llvm-mc 19 と照合した値）。どの行も組めて、
; -b の像で比べる。SVE の DUP / MOV の即値は、要素の幅で切った値が符号付きバイト（か、その 256 倍）
        dup     z0.b, #255              ; バイトの要素では -1
        dup     z1.h, #0xff00           ; -1, LSL #8
        dup     z2.h, #32768            ; -128, LSL #8
        dup     z3.s, #-128
        dup     z4.d, #0xffffffffffffff80
        dup     z5.h, #255, lsl #8
        mov     z6.s, #255              ; DUP では表せないのでビットマスク形
        mov     z7.d, #-1
        mul     z8.s, z8.s, #127
        smax    z9.b, z9.b, #-128
        umax    z10.h, z10.h, #255
        add     z11.s, z11.s, #65280
here:   b       here+0x7fffffc
        b.ne    here+4-0x100000         ; 変位 -0x100000（最小）
        adrp    x0, here+0xfffff000
        tbz     x1, #63, here+0x7ffc
