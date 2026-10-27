	.org	0x100
; 行全体がコメントの行も1行として出る
	.section .text
	.global	start
start:
	mvi	c,9		; 命令の後ろのコメント
	lxi	h,msg
	call	0x0005
	jmp	loop
loop:	; ラベルの後ろだけコメント
	mov	a,h
	; 字下げしたコメントだけの行
    mov	a,l
	    nop
	lda	msg+2
	jmp	far_away	; このファイルのどこにも定義のないラベル（!L はエラーにしない）
	lxi	h,ext_buf+2
	jmpc	far_away	; 値は 0 になる
	jmpc	loop		; 値と綴りの両方を使う行のコメント
	xyzzy	foo, bar	; マッチしない行のコメント
	esc	\; エスケープした \; はコメントではない
	nop
	.align	4
tbl:	.dw	loop, 0x1234	; .dw の行もテキストのまま出る
	.db	"ok", 0
buf:	.resb	16		; ディレクティブの行のコメント
msg:	.ascii	"He;llo"	; 文字列の中の ; はデータ
val:	.equ	0x1234		; .equ の行のコメント
	ret
	.endsection
