; z80_err.s -- z80.axx の範囲検査の回帰テスト。どの行も範囲外で、エラーになる。
LD A,0x1234
LD HL,0x12345
LD (0x10000),A
JP 0x10000
CALL NZ,-40000
OUT (0x100),A
IN A,(-1)
LD (IX+200),A
LD (IY+1),300
JR $$+300
DJNZ $$-300
ADD A,300
CP -129
