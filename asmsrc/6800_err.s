; 6800_err.s -- 6800.axx の範囲検査の回帰テスト。どの行も範囲外で、エラーになる。
LDAA #0x1234
LDAA 0x12345
LDX #0x12345
JMP 0x10000
BNE $$+300
LDAA #-0x81
LDAA -1
FCB 0x100
FCB 1,-0x81
