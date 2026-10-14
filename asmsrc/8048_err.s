; 8048_err.s -- 8048.axx の範囲検査の回帰テスト。.org 以外のどの行も範囲外で、エラーになる。
MOV A,#-1000
ADD A,#-129
JMP -5000
        .org 0x00ff
JZ 0x00f0
        .org 0x0100
JZ 0x0900
CPL F2
DB 0x100
MOV A,#0x100
