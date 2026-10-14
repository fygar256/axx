; aarch64_err.s -- aarch64.axx の範囲検査の回帰テスト。どの行も範囲外で、エラーになる。
; 4 の倍数でない PC 相対（以前は黙って切り捨て、自分へ飛ぶ符号になった）
        b       $$+2
        bl      $$+6
        b.eq    $$-2
        cbz     x0, $$+1
        tbnz    w0, #1, $$+3
        ldr     x0, $$+2
        prfm    pldl1keep, $$+2
; ADRP は ±4 GiB（以前は黙って回り込んだ）
        adrp    x0, $$+0x100000000
        adrp    x0, $$-0x100001000
; SVE の符号付きバイトの即値（以前は 128..255 を -128..-1 として組んだ）
        dup     z0.s, #255
        dup     z0.d, #128
        dup     z0.s, #65280
        mul     z0.s, z0.s, #255
        smax    z0.h, z0.h, #128
        smin    z0.b, z0.b, #200
        dup     z0.s, #128, lsl #8
