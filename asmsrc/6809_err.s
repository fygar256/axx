; 6809_err.s -- 6809.axx の範囲検査の回帰テスト。どの行も範囲外で、エラーになる。
lda #0x1234
lda 0x12345
lbne 0x10000
bne $$+300
lda 70000,x
jmp 0x10000
leax >0x12345,y
lda #-0x81
ldx #-0x8001
andcc #-0x81
ldy <0x10000
ldy <-1
fcb 0x100
