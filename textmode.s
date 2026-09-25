	.org	0x100
	.section .text
	.global	start
start:
	mvi	c,9
	lxi	h,msg
	call	0x0005
	jmp	loop
loop:
	mov	a,h
	lda	msg+2
	jmpc	loop
	xyzzy	foo, bar
	nop
	.align	4
buf:	.resb	16
msg:	.ascii	"Hello"
val:	.equ	0x1234
	ret
	.endsection
