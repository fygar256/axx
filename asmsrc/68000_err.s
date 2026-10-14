; 68000_err.s -- 68000.axx の範囲検査の回帰テスト。どの行も範囲外で、エラーになる。
;
;   caxx 68000.axx 68000_err.s -b out.bin
lea $$+40000(PC),A0
lea $$+200(PC,D0.W),A0
movem.l #0x12345,(A0)
btst #300,D0
move.l #0x123456789,D0
move.w (0x123456789).L,D0
bra.w $$+40000
dbra d0,$$+40000
bra.s $$+300
trap #16
moveq #200,d0
link a6,#-40000
stop #0x10000
addq.w #9,d0
move.b #300,d0
move.w #70000,d0
cmpi.b #300,d0
andi #0x10000,sr
andi #0x100,ccr
move.w d0,40000(a1)
move.w d0,200(a1,d1.w)
move.w d0,(0x12345).W
movep.w 40000(a0),d0
ori.w #0x12345,d0
; 2026-10-14: MOVEM の絶対番地 .L と PC 相対の変位（以前は検査が無く黙って切り詰めた）
movem.l (0x100000000).L,d0-d3
movem.w d0/a1,(-2147483649).L
movem.l $$+40000(pc),d0
movem.w $$+200(pc,d1.w),d0
