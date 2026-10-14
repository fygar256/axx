; relaxchain.s -- 前方参照の .equ が 16 段を超えて連なっても組めること（z80.axx）。
; 連鎖は pass 1 の反復ごとに 1 段ずつ決まる。以前は反復の上限 16 で「収束しない」と
; 止まった。いまは前の反復から値の変わったラベルが減っている限り上限に数えない。
; test1 は -b の像と、-d の「何回で収束したか」の行を比べる。
        ld      a,C0
        ld      hl,C0*0x100+C39
        jp      tail
C0:     .equ    C1+1
C1:     .equ    C2+1
C2:     .equ    C3+1
C3:     .equ    C4+1
C4:     .equ    C5+1
C5:     .equ    C6+1
C6:     .equ    C7+1
C7:     .equ    C8+1
C8:     .equ    C9+1
C9:     .equ    C10+1
C10:     .equ    C11+1
C11:     .equ    C12+1
C12:     .equ    C13+1
C13:     .equ    C14+1
C14:     .equ    C15+1
C15:     .equ    C16+1
C16:     .equ    C17+1
C17:     .equ    C18+1
C18:     .equ    C19+1
C19:     .equ    C20+1
C20:     .equ    C21+1
C21:     .equ    C22+1
C22:     .equ    C23+1
C23:     .equ    C24+1
C24:     .equ    C25+1
C25:     .equ    C26+1
C26:     .equ    C27+1
C27:     .equ    C28+1
C28:     .equ    C29+1
C29:     .equ    C30+1
C30:     .equ    C31+1
C31:     .equ    C32+1
C32:     .equ    C33+1
C33:     .equ    C34+1
C34:     .equ    C35+1
C35:     .equ    C36+1
C36:     .equ    C37+1
C37:     .equ    C38+1
C38:     .equ    C39+1
C39:    .equ    1
        .org    C0*2
tail:   nop
