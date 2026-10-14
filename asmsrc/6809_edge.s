; 6809_edge.s -- 6809.axx の範囲の境目の回帰テスト。どの行も組めて、バイト列で比べる。
dpreg:  .equ 0x12
        .org 0x0100
        LDA #-0x80              ; 即値は -$80..$FF
        LDX #-0x8000            ; 16 ビットの即値は -$8000..$FFFF
        ANDCC #0xff
; < は 16 ビットに収まれば下位バイトを使う。ページ 1 / 2 の命令と STY / STS も同じ
; （以前はこの 8 命令だけ $FF を超えるとエラーだった）
        LDA <0x1234
        LDY <0x1234
        STY <0x1256
        STS <0x12ff
        CMPD <0x1200
        CMPY <0x1201
        LDS <0x1202
        CMPU <0x1203
        CMPS <0x1204
        FCB -1,0xff,-0x80
