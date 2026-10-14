; 6502_err.s -- 6502.axx の範囲検査の回帰テスト。どの行も範囲外で、エラーになる。
LDA #0x1234
LDA 0x12345
LDA 0x12345,X
JMP 0x10000
BNE $$+300
ASL >0x12345,X
LDA #-0x81
LDA <-1
LDA (-1),Y
STX -1,Y
