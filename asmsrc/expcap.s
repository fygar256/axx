	mov	b,d
	mov	c , b
	expr	1+2*3
	expr	( 4 + 5 )
	stop	1+1 , 2*2
	fact	(3+4)+1
	flt	1.5
	dbl	-2.25
	qad	3.0
	push	a0-a2,-(sp)
	push	a0/a2,-(sp)
	sel	cx
	jmp	here
here:	ld.b	0x10+1
	ld.w	2
	nest	x2
	nest	y1
	pair	#1+2,3
	opt	5
	opt	5,6
	opt	7
