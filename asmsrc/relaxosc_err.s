; relaxosc_err.s -- pass 1 の配置が振動するとき、前方参照の .equ の連鎖で反復が
; 延びても「振動」と報告し、その周期と反復の番号が両実装で同じであること（6502.axx）。
; lda v はゼロページ（2 バイト）と絶対番地（3 バイト）を行き来する: v = 0x102 - 命令長。
        .org    0x100
        lda     v
        lda     D0
w:
v:      .equ    0x204 - w
D0:     .equ    D1+1
D1:     .equ    D2+1
D2:     .equ    D3+1
D3:     .equ    D4+1
D4:     .equ    D5+1
D5:     .equ    D6+1
D6:     .equ    D7+1
D7:     .equ    D8+1
D8:     .equ    D9+1
D9:     .equ    D10+1
D10:     .equ    D11+1
D11:     .equ    D12+1
D12:     .equ    D13+1
D13:     .equ    D14+1
D14:     .equ    D15+1
D15:     .equ    D16+1
D16:     .equ    D17+1
D17:     .equ    D18+1
D18:     .equ    D19+1
D19:     .equ    D20+1
D20:     .equ    D21+1
D21:     .equ    D22+1
D22:     .equ    D23+1
D23:     .equ    D24+1
D24:    .equ    1
