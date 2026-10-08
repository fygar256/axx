; ELF オブジェクト（-o）では .org で位置を後ろへ戻せない（-b なら戻せる）
.section .text
	nop
	nop
	.org 0
	nop
; 未定義を含む .EQU の値を .zero / .resb / .align / .org に渡したら、未定義の
; ラベルとして報告する（未定義の番兵を数として扱わない）
u: .equ nosuch+1
	.zero u
	.resb u
	.align u
	.org u
