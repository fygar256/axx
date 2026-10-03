	ld	a,c
	ld	c,a
	ld	c,0x12
	inc	c
	inc	sp
	add	hl,de
	inc	ix
	inc	iy
	push	af
	pop	bc
	jp	c,0x1234
	jp	nc,0x1234
	jp	0x1234
top:	jr	c,top
	jr	nz,top
	jr	top
	ret	c
	ret	nz
	ret
	sig
