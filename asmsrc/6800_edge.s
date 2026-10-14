; 6800_edge.s -- 6800.axx の範囲の境目の回帰テスト。どの行も組めて、バイト列で比べる。
        .org 0x0100
        LDAA #-0x80             ; 即値は -$80..$FF（以前は負をエラーにしていた）
        LDAA #0xff
        LDX #-1                 ; 16 ビットの即値は -$8000..$FFFF
        CPX #-0x8000
        LDAA 0xff               ; 直接
        LDAA 0x100              ; 拡張
        FCB -1,0xff,-0x80,0
        FDB -1,0xffff
