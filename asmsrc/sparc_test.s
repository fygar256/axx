; sparc_test.s -- test assemble file for sparc.axx: every pattern row
; of sparc.axx, one source line each (about 2400 lines).
;
; How it was checked (see the header of sparc.axx):
;   - the first part (up to the line "Lf1:" and the nop after it) is
;     byte-for-byte identical to llvm-mc 19
;       llvm-mc -triple=sparcv9 -mattr=+vis,+vis2,+vis3,+hard-quad-float,+hasumacsmac
;     except xmulxhi and bshuffle, where llvm-mc 19 writes the opf
;     0x117 / 0x01c and sparc.axx the 0x116 / 0x04c of the
;     architecture manuals and the GNU opcode table;
;   - the V8 part (std %fq, the coprocessor loads / stores, rd / wr of
;     %psr %wim %tbr) is identical to llvm-mc -triple=sparc;
;   - the last part (the rows llvm-mc 19 does not have: %r names, VIS
;     rows on single precision registers, fpadds / fpsubs, fucmp*8,
;     movxtod / movwtos, the UltraSPARC Architecture 2007 FPop1, the
;     fused multiply-add, rdhpr / wrhpr, allclean ..., cpop1 / cpop2,
;     ldtw / sttw, setuw / setsw, clrx / clruw, iprefetch, the data
;     rows) was checked against encodings written out from the manuals.
; caxx and axx.py give identical output.
;
;   axx sparc.axx sparc_test.s -b out.bin

	add %g1, %g3, %g2
	add %g1, 0, %g2
	add %g1, %lo(0x123456789abcdef0), %g2
	add %g1, %hm(0x123456789abcdef0), %g2
	add %g1, %ulo(0x123456789abcdef0), %g2
	add %g1, %m44(0x123456789abcdef0), %g2
	add %g1, %l44(0x123456789abcdef0), %g2
	add %g1, %lox(0x123456789abcdef0), %g2
	and %g4, %g6, %g5
	and %g4, 1, %g5
	and %g4, %lo(0x123456789abcdef0), %g5
	and %g4, %hm(0x123456789abcdef0), %g5
	and %g4, %ulo(0x123456789abcdef0), %g5
	and %g4, %m44(0x123456789abcdef0), %g5
	and %g4, %l44(0x123456789abcdef0), %g5
	and %g4, %lox(0x123456789abcdef0), %g5
	or %g7, %o1, %o0
	or %g7, -1, %o0
	or %g7, %lo(0x123456789abcdef0), %o0
	or %g7, %hm(0x123456789abcdef0), %o0
	or %g7, %ulo(0x123456789abcdef0), %o0
	or %g7, %m44(0x123456789abcdef0), %o0
	or %g7, %l44(0x123456789abcdef0), %o0
	or %g7, %lox(0x123456789abcdef0), %o0
	xor %o2, %o4, %o3
	xor %o2, 5, %o3
	xor %o2, %lo(0x123456789abcdef0), %o3
	xor %o2, %hm(0x123456789abcdef0), %o3
	xor %o2, %ulo(0x123456789abcdef0), %o3
	xor %o2, %m44(0x123456789abcdef0), %o3
	xor %o2, %l44(0x123456789abcdef0), %o3
	xor %o2, %lox(0x123456789abcdef0), %o3
	sub %o5, %o7, %sp
	sub %o5, 100, %sp
	sub %o5, %lo(0x123456789abcdef0), %sp
	sub %o5, %hm(0x123456789abcdef0), %sp
	sub %o5, %ulo(0x123456789abcdef0), %sp
	sub %o5, %m44(0x123456789abcdef0), %sp
	sub %o5, %l44(0x123456789abcdef0), %sp
	sub %o5, %lox(0x123456789abcdef0), %sp
	andn %l0, %l2, %l1
	andn %l0, -100, %l1
	andn %l0, %lo(0x123456789abcdef0), %l1
	andn %l0, %hm(0x123456789abcdef0), %l1
	andn %l0, %ulo(0x123456789abcdef0), %l1
	andn %l0, %m44(0x123456789abcdef0), %l1
	andn %l0, %l44(0x123456789abcdef0), %l1
	andn %l0, %lox(0x123456789abcdef0), %l1
	orn %l3, %l5, %l4
	orn %l3, 4095, %l4
	orn %l3, %lo(0x123456789abcdef0), %l4
	orn %l3, %hm(0x123456789abcdef0), %l4
	orn %l3, %ulo(0x123456789abcdef0), %l4
	orn %l3, %m44(0x123456789abcdef0), %l4
	orn %l3, %l44(0x123456789abcdef0), %l4
	orn %l3, %lox(0x123456789abcdef0), %l4
	xnor %l6, %i0, %l7
	xnor %l6, -4096, %l7
	xnor %l6, %lo(0x123456789abcdef0), %l7
	xnor %l6, %hm(0x123456789abcdef0), %l7
	xnor %l6, %ulo(0x123456789abcdef0), %l7
	xnor %l6, %m44(0x123456789abcdef0), %l7
	xnor %l6, %l44(0x123456789abcdef0), %l7
	xnor %l6, %lox(0x123456789abcdef0), %l7
	addx %i1, %i3, %i2
	addx %i1, 2047, %i2
	addx %i1, %lo(0x123456789abcdef0), %i2
	addx %i1, %hm(0x123456789abcdef0), %i2
	addx %i1, %ulo(0x123456789abcdef0), %i2
	addx %i1, %m44(0x123456789abcdef0), %i2
	addx %i1, %l44(0x123456789abcdef0), %i2
	addx %i1, %lox(0x123456789abcdef0), %i2
	addc %i4, %fp, %i5
	addc %i4, -2048, %i5
	addc %i4, %lo(0x123456789abcdef0), %i5
	addc %i4, %hm(0x123456789abcdef0), %i5
	addc %i4, %ulo(0x123456789abcdef0), %i5
	addc %i4, %m44(0x123456789abcdef0), %i5
	addc %i4, %l44(0x123456789abcdef0), %i5
	addc %i4, %lox(0x123456789abcdef0), %i5
	mulx %i7, %g2, %g1
	mulx %i7, 291, %g1
	mulx %i7, %lo(0x123456789abcdef0), %g1
	mulx %i7, %hm(0x123456789abcdef0), %g1
	mulx %i7, %ulo(0x123456789abcdef0), %g1
	mulx %i7, %m44(0x123456789abcdef0), %g1
	mulx %i7, %l44(0x123456789abcdef0), %g1
	mulx %i7, %lox(0x123456789abcdef0), %g1
	umul %g3, %g5, %g4
	umul %g3, -2047, %g4
	umul %g3, %lo(0x123456789abcdef0), %g4
	umul %g3, %hm(0x123456789abcdef0), %g4
	umul %g3, %ulo(0x123456789abcdef0), %g4
	umul %g3, %m44(0x123456789abcdef0), %g4
	umul %g3, %l44(0x123456789abcdef0), %g4
	umul %g3, %lox(0x123456789abcdef0), %g4
	smul %g6, %o0, %g7
	smul %g6, 0, %g7
	smul %g6, %lo(0x123456789abcdef0), %g7
	smul %g6, %hm(0x123456789abcdef0), %g7
	smul %g6, %ulo(0x123456789abcdef0), %g7
	smul %g6, %m44(0x123456789abcdef0), %g7
	smul %g6, %l44(0x123456789abcdef0), %g7
	smul %g6, %lox(0x123456789abcdef0), %g7
	subx %o1, %o3, %o2
	subx %o1, 1, %o2
	subx %o1, %lo(0x123456789abcdef0), %o2
	subx %o1, %hm(0x123456789abcdef0), %o2
	subx %o1, %ulo(0x123456789abcdef0), %o2
	subx %o1, %m44(0x123456789abcdef0), %o2
	subx %o1, %l44(0x123456789abcdef0), %o2
	subx %o1, %lox(0x123456789abcdef0), %o2
	subc %o4, %sp, %o5
	subc %o4, -1, %o5
	subc %o4, %lo(0x123456789abcdef0), %o5
	subc %o4, %hm(0x123456789abcdef0), %o5
	subc %o4, %ulo(0x123456789abcdef0), %o5
	subc %o4, %m44(0x123456789abcdef0), %o5
	subc %o4, %l44(0x123456789abcdef0), %o5
	subc %o4, %lox(0x123456789abcdef0), %o5
	udivx %o7, %l1, %l0
	udivx %o7, 5, %l0
	udivx %o7, %lo(0x123456789abcdef0), %l0
	udivx %o7, %hm(0x123456789abcdef0), %l0
	udivx %o7, %ulo(0x123456789abcdef0), %l0
	udivx %o7, %m44(0x123456789abcdef0), %l0
	udivx %o7, %l44(0x123456789abcdef0), %l0
	udivx %o7, %lox(0x123456789abcdef0), %l0
	udiv %l2, %l4, %l3
	udiv %l2, 100, %l3
	udiv %l2, %lo(0x123456789abcdef0), %l3
	udiv %l2, %hm(0x123456789abcdef0), %l3
	udiv %l2, %ulo(0x123456789abcdef0), %l3
	udiv %l2, %m44(0x123456789abcdef0), %l3
	udiv %l2, %l44(0x123456789abcdef0), %l3
	udiv %l2, %lox(0x123456789abcdef0), %l3
	sdiv %l5, %l7, %l6
	sdiv %l5, -100, %l6
	sdiv %l5, %lo(0x123456789abcdef0), %l6
	sdiv %l5, %hm(0x123456789abcdef0), %l6
	sdiv %l5, %ulo(0x123456789abcdef0), %l6
	sdiv %l5, %m44(0x123456789abcdef0), %l6
	sdiv %l5, %l44(0x123456789abcdef0), %l6
	sdiv %l5, %lox(0x123456789abcdef0), %l6
	addcc %i0, %i2, %i1
	addcc %i0, 4095, %i1
	addcc %i0, %lo(0x123456789abcdef0), %i1
	addcc %i0, %hm(0x123456789abcdef0), %i1
	addcc %i0, %ulo(0x123456789abcdef0), %i1
	addcc %i0, %m44(0x123456789abcdef0), %i1
	addcc %i0, %l44(0x123456789abcdef0), %i1
	addcc %i0, %lox(0x123456789abcdef0), %i1
	andcc %i3, %i5, %i4
	andcc %i3, -4096, %i4
	andcc %i3, %lo(0x123456789abcdef0), %i4
	andcc %i3, %hm(0x123456789abcdef0), %i4
	andcc %i3, %ulo(0x123456789abcdef0), %i4
	andcc %i3, %m44(0x123456789abcdef0), %i4
	andcc %i3, %l44(0x123456789abcdef0), %i4
	andcc %i3, %lox(0x123456789abcdef0), %i4
	orcc %fp, %g1, %i7
	orcc %fp, 2047, %i7
	orcc %fp, %lo(0x123456789abcdef0), %i7
	orcc %fp, %hm(0x123456789abcdef0), %i7
	orcc %fp, %ulo(0x123456789abcdef0), %i7
	orcc %fp, %m44(0x123456789abcdef0), %i7
	orcc %fp, %l44(0x123456789abcdef0), %i7
	orcc %fp, %lox(0x123456789abcdef0), %i7
	xorcc %g2, %g4, %g3
	xorcc %g2, -2048, %g3
	xorcc %g2, %lo(0x123456789abcdef0), %g3
	xorcc %g2, %hm(0x123456789abcdef0), %g3
	xorcc %g2, %ulo(0x123456789abcdef0), %g3
	xorcc %g2, %m44(0x123456789abcdef0), %g3
	xorcc %g2, %l44(0x123456789abcdef0), %g3
	xorcc %g2, %lox(0x123456789abcdef0), %g3
	subcc %g5, %g7, %g6
	subcc %g5, 291, %g6
	subcc %g5, %lo(0x123456789abcdef0), %g6
	subcc %g5, %hm(0x123456789abcdef0), %g6
	subcc %g5, %ulo(0x123456789abcdef0), %g6
	subcc %g5, %m44(0x123456789abcdef0), %g6
	subcc %g5, %l44(0x123456789abcdef0), %g6
	subcc %g5, %lox(0x123456789abcdef0), %g6
	andncc %o0, %o2, %o1
	andncc %o0, -2047, %o1
	andncc %o0, %lo(0x123456789abcdef0), %o1
	andncc %o0, %hm(0x123456789abcdef0), %o1
	andncc %o0, %ulo(0x123456789abcdef0), %o1
	andncc %o0, %m44(0x123456789abcdef0), %o1
	andncc %o0, %l44(0x123456789abcdef0), %o1
	andncc %o0, %lox(0x123456789abcdef0), %o1
	orncc %o3, %o5, %o4
	orncc %o3, 0, %o4
	orncc %o3, %lo(0x123456789abcdef0), %o4
	orncc %o3, %hm(0x123456789abcdef0), %o4
	orncc %o3, %ulo(0x123456789abcdef0), %o4
	orncc %o3, %m44(0x123456789abcdef0), %o4
	orncc %o3, %l44(0x123456789abcdef0), %o4
	orncc %o3, %lox(0x123456789abcdef0), %o4
	xnorcc %sp, %l0, %o7
	xnorcc %sp, 1, %o7
	xnorcc %sp, %lo(0x123456789abcdef0), %o7
	xnorcc %sp, %hm(0x123456789abcdef0), %o7
	xnorcc %sp, %ulo(0x123456789abcdef0), %o7
	xnorcc %sp, %m44(0x123456789abcdef0), %o7
	xnorcc %sp, %l44(0x123456789abcdef0), %o7
	xnorcc %sp, %lox(0x123456789abcdef0), %o7
	addxcc %l1, %l3, %l2
	addxcc %l1, -1, %l2
	addxcc %l1, %lo(0x123456789abcdef0), %l2
	addxcc %l1, %hm(0x123456789abcdef0), %l2
	addxcc %l1, %ulo(0x123456789abcdef0), %l2
	addxcc %l1, %m44(0x123456789abcdef0), %l2
	addxcc %l1, %l44(0x123456789abcdef0), %l2
	addxcc %l1, %lox(0x123456789abcdef0), %l2
	addccc %l4, %l6, %l5
	addccc %l4, 5, %l5
	addccc %l4, %lo(0x123456789abcdef0), %l5
	addccc %l4, %hm(0x123456789abcdef0), %l5
	addccc %l4, %ulo(0x123456789abcdef0), %l5
	addccc %l4, %m44(0x123456789abcdef0), %l5
	addccc %l4, %l44(0x123456789abcdef0), %l5
	addccc %l4, %lox(0x123456789abcdef0), %l5
	umulcc %l7, %i1, %i0
	umulcc %l7, 100, %i0
	umulcc %l7, %lo(0x123456789abcdef0), %i0
	umulcc %l7, %hm(0x123456789abcdef0), %i0
	umulcc %l7, %ulo(0x123456789abcdef0), %i0
	umulcc %l7, %m44(0x123456789abcdef0), %i0
	umulcc %l7, %l44(0x123456789abcdef0), %i0
	umulcc %l7, %lox(0x123456789abcdef0), %i0
	smulcc %i2, %i4, %i3
	smulcc %i2, -100, %i3
	smulcc %i2, %lo(0x123456789abcdef0), %i3
	smulcc %i2, %hm(0x123456789abcdef0), %i3
	smulcc %i2, %ulo(0x123456789abcdef0), %i3
	smulcc %i2, %m44(0x123456789abcdef0), %i3
	smulcc %i2, %l44(0x123456789abcdef0), %i3
	smulcc %i2, %lox(0x123456789abcdef0), %i3
	subxcc %i5, %i7, %fp
	subxcc %i5, 4095, %fp
	subxcc %i5, %lo(0x123456789abcdef0), %fp
	subxcc %i5, %hm(0x123456789abcdef0), %fp
	subxcc %i5, %ulo(0x123456789abcdef0), %fp
	subxcc %i5, %m44(0x123456789abcdef0), %fp
	subxcc %i5, %l44(0x123456789abcdef0), %fp
	subxcc %i5, %lox(0x123456789abcdef0), %fp
	subccc %g1, %g3, %g2
	subccc %g1, -4096, %g2
	subccc %g1, %lo(0x123456789abcdef0), %g2
	subccc %g1, %hm(0x123456789abcdef0), %g2
	subccc %g1, %ulo(0x123456789abcdef0), %g2
	subccc %g1, %m44(0x123456789abcdef0), %g2
	subccc %g1, %l44(0x123456789abcdef0), %g2
	subccc %g1, %lox(0x123456789abcdef0), %g2
	udivcc %g4, %g6, %g5
	udivcc %g4, 2047, %g5
	udivcc %g4, %lo(0x123456789abcdef0), %g5
	udivcc %g4, %hm(0x123456789abcdef0), %g5
	udivcc %g4, %ulo(0x123456789abcdef0), %g5
	udivcc %g4, %m44(0x123456789abcdef0), %g5
	udivcc %g4, %l44(0x123456789abcdef0), %g5
	udivcc %g4, %lox(0x123456789abcdef0), %g5
	sdivcc %g7, %o1, %o0
	sdivcc %g7, -2048, %o0
	sdivcc %g7, %lo(0x123456789abcdef0), %o0
	sdivcc %g7, %hm(0x123456789abcdef0), %o0
	sdivcc %g7, %ulo(0x123456789abcdef0), %o0
	sdivcc %g7, %m44(0x123456789abcdef0), %o0
	sdivcc %g7, %l44(0x123456789abcdef0), %o0
	sdivcc %g7, %lox(0x123456789abcdef0), %o0
	taddcc %o2, %o4, %o3
	taddcc %o2, 291, %o3
	taddcc %o2, %lo(0x123456789abcdef0), %o3
	taddcc %o2, %hm(0x123456789abcdef0), %o3
	taddcc %o2, %ulo(0x123456789abcdef0), %o3
	taddcc %o2, %m44(0x123456789abcdef0), %o3
	taddcc %o2, %l44(0x123456789abcdef0), %o3
	taddcc %o2, %lox(0x123456789abcdef0), %o3
	tsubcc %o5, %o7, %sp
	tsubcc %o5, -2047, %sp
	tsubcc %o5, %lo(0x123456789abcdef0), %sp
	tsubcc %o5, %hm(0x123456789abcdef0), %sp
	tsubcc %o5, %ulo(0x123456789abcdef0), %sp
	tsubcc %o5, %m44(0x123456789abcdef0), %sp
	tsubcc %o5, %l44(0x123456789abcdef0), %sp
	tsubcc %o5, %lox(0x123456789abcdef0), %sp
	taddcctv %l0, %l2, %l1
	taddcctv %l0, 0, %l1
	taddcctv %l0, %lo(0x123456789abcdef0), %l1
	taddcctv %l0, %hm(0x123456789abcdef0), %l1
	taddcctv %l0, %ulo(0x123456789abcdef0), %l1
	taddcctv %l0, %m44(0x123456789abcdef0), %l1
	taddcctv %l0, %l44(0x123456789abcdef0), %l1
	taddcctv %l0, %lox(0x123456789abcdef0), %l1
	tsubcctv %l3, %l5, %l4
	tsubcctv %l3, 1, %l4
	tsubcctv %l3, %lo(0x123456789abcdef0), %l4
	tsubcctv %l3, %hm(0x123456789abcdef0), %l4
	tsubcctv %l3, %ulo(0x123456789abcdef0), %l4
	tsubcctv %l3, %m44(0x123456789abcdef0), %l4
	tsubcctv %l3, %l44(0x123456789abcdef0), %l4
	tsubcctv %l3, %lox(0x123456789abcdef0), %l4
	mulscc %l6, %i0, %l7
	mulscc %l6, -1, %l7
	mulscc %l6, %lo(0x123456789abcdef0), %l7
	mulscc %l6, %hm(0x123456789abcdef0), %l7
	mulscc %l6, %ulo(0x123456789abcdef0), %l7
	mulscc %l6, %m44(0x123456789abcdef0), %l7
	mulscc %l6, %l44(0x123456789abcdef0), %l7
	mulscc %l6, %lox(0x123456789abcdef0), %l7
	sdivx %i1, %i3, %i2
	sdivx %i1, 5, %i2
	sdivx %i1, %lo(0x123456789abcdef0), %i2
	sdivx %i1, %hm(0x123456789abcdef0), %i2
	sdivx %i1, %ulo(0x123456789abcdef0), %i2
	sdivx %i1, %m44(0x123456789abcdef0), %i2
	sdivx %i1, %l44(0x123456789abcdef0), %i2
	sdivx %i1, %lox(0x123456789abcdef0), %i2
	save %i4, %fp, %i5
	save %i4, 100, %i5
	save %i4, %lo(0x123456789abcdef0), %i5
	save %i4, %hm(0x123456789abcdef0), %i5
	save %i4, %ulo(0x123456789abcdef0), %i5
	save %i4, %m44(0x123456789abcdef0), %i5
	save %i4, %l44(0x123456789abcdef0), %i5
	save %i4, %lox(0x123456789abcdef0), %i5
	restore %i7, %g2, %g1
	restore %i7, -100, %g1
	restore %i7, %lo(0x123456789abcdef0), %g1
	restore %i7, %hm(0x123456789abcdef0), %g1
	restore %i7, %ulo(0x123456789abcdef0), %g1
	restore %i7, %m44(0x123456789abcdef0), %g1
	restore %i7, %l44(0x123456789abcdef0), %g1
	restore %i7, %lox(0x123456789abcdef0), %g1
	umac %g3, %g5, %g4
	umac %g3, 4095, %g4
	umac %g3, %lo(0x123456789abcdef0), %g4
	umac %g3, %hm(0x123456789abcdef0), %g4
	umac %g3, %ulo(0x123456789abcdef0), %g4
	umac %g3, %m44(0x123456789abcdef0), %g4
	umac %g3, %l44(0x123456789abcdef0), %g4
	umac %g3, %lox(0x123456789abcdef0), %g4
	smac %g6, %o0, %g7
	smac %g6, -4096, %g7
	smac %g6, %lo(0x123456789abcdef0), %g7
	smac %g6, %hm(0x123456789abcdef0), %g7
	smac %g6, %ulo(0x123456789abcdef0), %g7
	smac %g6, %m44(0x123456789abcdef0), %g7
	smac %g6, %l44(0x123456789abcdef0), %g7
	smac %g6, %lox(0x123456789abcdef0), %g7
	save
	restore
	popc %g1, %g2
	sll %o1, %o2, %o3
	sll %o4, 0, %o5
	sll %sp, 1, %o7
	sll %l0, 17, %l1
	sll %l2, 31, %l3
	srl %l4, %l5, %l6
	srl %l7, 0, %i0
	srl %i1, 1, %i2
	srl %i3, 17, %i4
	srl %i5, 31, %fp
	sra %i7, %g1, %g2
	sra %g3, 0, %g4
	sra %g5, 1, %g6
	sra %g7, 17, %o0
	sra %o1, 31, %o2
	sllx %o3, %o4, %o5
	sllx %sp, 0, %o7
	sllx %l0, 1, %l1
	sllx %l2, 31, %l3
	sllx %l4, 32, %l5
	sllx %l6, 63, %l7
	srlx %i0, %i1, %i2
	srlx %i3, 0, %i4
	srlx %i5, 1, %fp
	srlx %i7, 31, %g1
	srlx %g2, 32, %g3
	srlx %g4, 63, %g5
	srax %g6, %g7, %o0
	srax %o1, 0, %o2
	srax %o3, 1, %o4
	srax %o5, 31, %sp
	srax %o7, 32, %l0
	srax %l1, 63, %l2
	sethi 0, %g1
	sethi 0x3fffff, %o2
	sethi 12345, %l3
	sethi %hi(0x123456789abcdef0), %l3
	sethi %hh(0x123456789abcdef0), %l4
	sethi %uhi(0x123456789abcdef0), %l5
	sethi %lm(0x123456789abcdef0), %l6
	sethi %h44(0x123456789abcdef0), %l7
	sethi %hix(0xffffffff12345678), %g4
	xor %g4, %lox(0xffffffff12345678), %g4
	nop
Lb0:
	ba Lb1
	ba,a Lf0
	ba %icc, Lf1
	ba,pt %xcc, Lb0
	ba,pn %icc, Lb0
	ba,a %xcc, Lb0
	ba,a,pt %icc, Lb1
	ba,a,pn %xcc, Lb0
	b Lf0
	b,a Lb0
	b %icc, Lb0
	b,pt %xcc, Lf1
	b,pn %icc, Lf1
	b,a %xcc, Lb0
	b,a,pt %icc, Lf0
	b,a,pn %xcc, Lb0
	bn Lf1
	bn,a Lb0
	bn %icc, Lb0
	bn,pt %xcc, Lf0
	bn,pn %icc, Lb0
	bn,a %xcc, Lf1
	bn,a,pt %icc, Lb0
	bn,a,pn %xcc, Lf0
	bne Lb0
	bne,a Lf0
	bne %icc, Lb1
	bne,pt %xcc, Lf1
	bne,pn %icc, Lf0
	bne,a %xcc, Lb0
	bne,a,pt %icc, Lb1
	bne,a,pn %xcc, Lf0
	bnz Lb0
	bnz,a Lf0
	bnz %icc, Lb1
	bnz,pt %xcc, Lb0
	bnz,pn %icc, Lb0
	bnz,a %xcc, Lb0
	bnz,a,pt %icc, Lf0
	bnz,a,pn %xcc, Lf1
	be Lf1
	be,a Lb1
	be %icc, Lf1
	be,pt %xcc, Lf1
	be,pn %icc, Lb1
	be,a %xcc, Lb1
	be,a,pt %icc, Lf0
	be,a,pn %xcc, Lf0
	bz Lf0
	bz,a Lb0
	bz %icc, Lb1
	bz,pt %xcc, Lf1
	bz,pn %icc, Lb1
	bz,a %xcc, Lf1
	bz,a,pt %icc, Lb1
	bz,a,pn %xcc, Lb0
	bg Lb0
	bg,a Lf1
	bg %icc, Lf0
	bg,pt %xcc, Lb1
	bg,pn %icc, Lf0
	bg,a %xcc, Lf1
	bg,a,pt %icc, Lf1
	bg,a,pn %xcc, Lb0
	ble Lb0
	ble,a Lb1
	ble %icc, Lb1
	ble,pt %xcc, Lb1
	ble,pn %icc, Lf1
	ble,a %xcc, Lf1
	ble,a,pt %icc, Lb0
	ble,a,pn %xcc, Lb0
	bge Lb1
	bge,a Lf1
	bge %icc, Lb0
	bge,pt %xcc, Lb0
	bge,pn %icc, Lb1
	bge,a %xcc, Lf1
	bge,a,pt %icc, Lb1
	bge,a,pn %xcc, Lf1
	bl Lb1
	bl,a Lb0
	bl %icc, Lf1
	bl,pt %xcc, Lb1
	bl,pn %icc, Lf0
	bl,a %xcc, Lb0
	bl,a,pt %icc, Lf1
	bl,a,pn %xcc, Lb0
	bgu Lf0
	bgu,a Lb1
	bgu %icc, Lf0
	bgu,pt %xcc, Lf0
	bgu,pn %icc, Lf1
	bgu,a %xcc, Lf1
	bgu,a,pt %icc, Lf1
	bgu,a,pn %xcc, Lb0
	bleu Lf0
	bleu,a Lf1
	bleu %icc, Lf1
	bleu,pt %xcc, Lb1
	bleu,pn %icc, Lf0
	bleu,a %xcc, Lf1
	bleu,a,pt %icc, Lb1
	bleu,a,pn %xcc, Lf1
	bcc Lb1
	bcc,a Lf1
	bcc %icc, Lf0
	bcc,pt %xcc, Lf0
	bcc,pn %icc, Lb0
	bcc,a %xcc, Lf0
	bcc,a,pt %icc, Lf0
	bcc,a,pn %xcc, Lf0
	bgeu Lf0
	bgeu,a Lb0
	bgeu %icc, Lf1
	bgeu,pt %xcc, Lf0
	bgeu,pn %icc, Lb1
	bgeu,a %xcc, Lb1
	bgeu,a,pt %icc, Lb0
	bgeu,a,pn %xcc, Lf0
	bcs Lf1
	bcs,a Lb1
	bcs %icc, Lb1
	bcs,pt %xcc, Lf0
	bcs,pn %icc, Lb0
	bcs,a %xcc, Lf1
	bcs,a,pt %icc, Lf1
	bcs,a,pn %xcc, Lf1
	blu Lf1
	blu,a Lf1
	blu %icc, Lb0
	blu,pt %xcc, Lf1
	blu,pn %icc, Lf1
	blu,a %xcc, Lb0
	blu,a,pt %icc, Lf0
	blu,a,pn %xcc, Lb0
	bpos Lf0
	bpos,a Lf1
	bpos %icc, Lf0
	bpos,pt %xcc, Lb0
	bpos,pn %icc, Lb1
	bpos,a %xcc, Lb0
	bpos,a,pt %icc, Lb0
	bpos,a,pn %xcc, Lb0
	bneg Lf0
	bneg,a Lb0
	bneg %icc, Lb1
	bneg,pt %xcc, Lb0
	bneg,pn %icc, Lb0
	bneg,a %xcc, Lf0
	bneg,a,pt %icc, Lf1
	bneg,a,pn %xcc, Lf0
	bvc Lb1
	bvc,a Lb1
	bvc %icc, Lb1
	bvc,pt %xcc, Lf1
	bvc,pn %icc, Lb0
	bvc,a %xcc, Lb0
	bvc,a,pt %icc, Lf1
	bvc,a,pn %xcc, Lf1
	bvs Lf1
	bvs,a Lf1
	bvs %icc, Lb1
	bvs,pt %xcc, Lb0
	bvs,pn %icc, Lf0
	bvs,a %xcc, Lb0
	bvs,a,pt %icc, Lb1
	bvs,a,pn %xcc, Lb1
Lb1:
	fba Lf1
	fba,a Lf0
	fba %fcc0, Lb0
	fba,pt %fcc1, Lf0
	fba,pn %fcc2, Lb1
	fba,a %fcc3, Lf0
	fba,a,pt %fcc0, Lb0
	fba,a,pn %fcc1, Lb1
	fbn Lb0
	fbn,a Lb1
	fbn %fcc2, Lb1
	fbn,pt %fcc3, Lf0
	fbn,pn %fcc0, Lb1
	fbn,a %fcc1, Lf0
	fbn,a,pt %fcc2, Lb1
	fbn,a,pn %fcc3, Lf0
	fbu Lf0
	fbu,a Lf0
	fbu %fcc0, Lf1
	fbu,pt %fcc1, Lf0
	fbu,pn %fcc2, Lf0
	fbu,a %fcc3, Lf1
	fbu,a,pt %fcc0, Lb1
	fbu,a,pn %fcc1, Lb0
	fbg Lb0
	fbg,a Lb1
	fbg %fcc2, Lf1
	fbg,pt %fcc3, Lb1
	fbg,pn %fcc0, Lf0
	fbg,a %fcc1, Lb1
	fbg,a,pt %fcc2, Lf1
	fbg,a,pn %fcc3, Lb1
	fbug Lb1
	fbug,a Lb0
	fbug %fcc0, Lf0
	fbug,pt %fcc1, Lb0
	fbug,pn %fcc2, Lf0
	fbug,a %fcc3, Lf1
	fbug,a,pt %fcc0, Lf0
	fbug,a,pn %fcc1, Lb1
	fbl Lf0
	fbl,a Lf1
	fbl %fcc2, Lb0
	fbl,pt %fcc3, Lf1
	fbl,pn %fcc0, Lb1
	fbl,a %fcc1, Lb0
	fbl,a,pt %fcc2, Lb0
	fbl,a,pn %fcc3, Lf1
	fbul Lf0
	fbul,a Lf1
	fbul %fcc0, Lf0
	fbul,pt %fcc1, Lf1
	fbul,pn %fcc2, Lb1
	fbul,a %fcc3, Lb0
	fbul,a,pt %fcc0, Lf1
	fbul,a,pn %fcc1, Lf1
	fblg Lf1
	fblg,a Lb0
	fblg %fcc2, Lf0
	fblg,pt %fcc3, Lf0
	fblg,pn %fcc0, Lf0
	fblg,a %fcc1, Lb0
	fblg,a,pt %fcc2, Lf0
	fblg,a,pn %fcc3, Lf1
	fbne Lf0
	fbne,a Lf1
	fbne %fcc0, Lb1
	fbne,pt %fcc1, Lf0
	fbne,pn %fcc2, Lf0
	fbne,a %fcc3, Lb0
	fbne,a,pt %fcc0, Lb0
	fbne,a,pn %fcc1, Lb0
	fbnz Lf0
	fbnz,a Lf1
	fbnz %fcc2, Lf0
	fbnz,pt %fcc3, Lf0
	fbnz,pn %fcc0, Lb0
	fbnz,a %fcc1, Lb1
	fbnz,a,pt %fcc2, Lf0
	fbnz,a,pn %fcc3, Lb1
	fbe Lf0
	fbe,a Lb1
	fbe %fcc0, Lb1
	fbe,pt %fcc1, Lf1
	fbe,pn %fcc2, Lf0
	fbe,a %fcc3, Lb0
	fbe,a,pt %fcc0, Lb1
	fbe,a,pn %fcc1, Lf1
	fbz Lf1
	fbz,a Lf0
	fbz %fcc2, Lf0
	fbz,pt %fcc3, Lb0
	fbz,pn %fcc0, Lf1
	fbz,a %fcc1, Lf0
	fbz,a,pt %fcc2, Lb0
	fbz,a,pn %fcc3, Lf0
	fbue Lf0
	fbue,a Lf0
	fbue %fcc0, Lf1
	fbue,pt %fcc1, Lb0
	fbue,pn %fcc2, Lb0
	fbue,a %fcc3, Lb1
	fbue,a,pt %fcc0, Lf1
	fbue,a,pn %fcc1, Lb0
	fbge Lb0
	fbge,a Lf0
	fbge %fcc2, Lf0
	fbge,pt %fcc3, Lb1
	fbge,pn %fcc0, Lb0
	fbge,a %fcc1, Lb0
	fbge,a,pt %fcc2, Lf1
	fbge,a,pn %fcc3, Lb0
	fbuge Lb0
	fbuge,a Lf1
	fbuge %fcc0, Lb1
	fbuge,pt %fcc1, Lf0
	fbuge,pn %fcc2, Lb1
	fbuge,a %fcc3, Lf1
	fbuge,a,pt %fcc0, Lf1
	fbuge,a,pn %fcc1, Lf0
	fble Lb1
	fble,a Lf0
	fble %fcc2, Lf1
	fble,pt %fcc3, Lf0
	fble,pn %fcc0, Lf1
	fble,a %fcc1, Lb0
	fble,a,pt %fcc2, Lf1
	fble,a,pn %fcc3, Lf1
	fbule Lb1
	fbule,a Lb0
	fbule %fcc0, Lf0
	fbule,pt %fcc1, Lf1
	fbule,pn %fcc2, Lb0
	fbule,a %fcc3, Lf0
	fbule,a,pt %fcc0, Lb1
	fbule,a,pn %fcc1, Lb0
	fbo Lf0
	fbo,a Lb1
	fbo %fcc2, Lf0
	fbo,pt %fcc3, Lb1
	fbo,pn %fcc0, Lf0
	fbo,a %fcc1, Lf1
	fbo,a,pt %fcc2, Lf0
	fbo,a,pn %fcc3, Lb0
	brz %i0, Lf1
	brz,pt %i1, Lf1
	brz,pn %i2, Lf0
	brz,a %i3, Lf0
	brz,a,pt %i4, Lf0
	brz,a,pn %i5, Lf1
	bre %fp, Lf1
	bre,pt %i7, Lb1
	bre,pn %g1, Lf1
	bre,a %g2, Lf0
	bre,a,pt %g3, Lb1
	bre,a,pn %g4, Lb1
	brlez %g5, Lb0
	brlez,pt %g6, Lb1
	brlez,pn %g7, Lb0
	brlez,a %o0, Lb1
	brlez,a,pt %o1, Lf1
	brlez,a,pn %o2, Lf1
	brlz %o3, Lb0
	brlz,pt %o4, Lf1
	brlz,pn %o5, Lb1
	brlz,a %sp, Lb1
	brlz,a,pt %o7, Lb0
	brlz,a,pn %l0, Lb0
	brnz %l1, Lf0
	brnz,pt %l2, Lb0
	brnz,pn %l3, Lb0
	brnz,a %l4, Lb1
	brnz,a,pt %l5, Lb1
	brnz,a,pn %l6, Lb0
	brne %l7, Lf0
	brne,pt %i0, Lb1
	brne,pn %i1, Lf0
	brne,a %i2, Lf1
	brne,a,pt %i3, Lb1
	brne,a,pn %i4, Lf1
	brgz %i5, Lf0
	brgz,pt %fp, Lf1
	brgz,pn %i7, Lb1
	brgz,a %g1, Lb0
	brgz,a,pt %g2, Lb1
	brgz,a,pn %g3, Lb0
	brgez %g4, Lf0
	brgez,pt %g5, Lf1
	brgez,pn %g6, Lb0
	brgez,a %g7, Lb1
	brgez,a,pt %o0, Lb0
	brgez,a,pn %o1, Lb0
	cba Lb1
	cba,a Lb0
	cbn Lf0
	cbn,a Lb0
	cb3 Lb1
	cb3,a Lb0
	cb2 Lf1
	cb2,a Lb0
	cb23 Lb1
	cb23,a Lf1
	cb1 Lb1
	cb1,a Lf0
	cb13 Lb0
	cb13,a Lf0
	cb12 Lb0
	cb12,a Lf0
	cb123 Lb1
	cb123,a Lb0
	cb0 Lf0
	cb0,a Lf0
	cb03 Lb1
	cb03,a Lb1
	cb02 Lf0
	cb02,a Lb1
	cb023 Lf1
	cb023,a Lf0
	cb01 Lb1
	cb01,a Lb1
	cb013 Lb0
	cb013,a Lb1
	cb012 Lb0
	cb012,a Lb0
	call Lb0
	call Lf1
Lf0:
	call %o2+%o3
	call %o4
	call %o5+2047
	call %sp-152
	call %o7+%lo(0x123456789abcdef0)
	call %l0+%hm(0x123456789abcdef0)
	call %l1+%ulo(0x123456789abcdef0)
	call %l2+%m44(0x123456789abcdef0)
	call %l3+%l44(0x123456789abcdef0)
	call %l4+%lox(0x123456789abcdef0)
	jmpl %l5+%l6, %o7
	jmpl %l7, %o7
	jmpl %i0+-2048, %o7
	jmpl %i1-1553, %o7
	jmpl %i2+%lo(0x123456789abcdef0), %o7
	jmpl %i3+%hm(0x123456789abcdef0), %o7
	jmpl %i4+%ulo(0x123456789abcdef0), %o7
	jmpl %i5+%m44(0x123456789abcdef0), %o7
	jmpl %fp+%l44(0x123456789abcdef0), %o7
	jmpl %i7+%lox(0x123456789abcdef0), %o7
	jmpl 291, %o7
	jmpl %g1+%g2, %g0
	jmpl %g3, %g0
	jmpl %g4+-2047, %g0
	jmpl %g5-3890, %g0
	jmpl %g6+%lo(0x123456789abcdef0), %g0
	jmpl %g7+%hm(0x123456789abcdef0), %g0
	jmpl %o0+%ulo(0x123456789abcdef0), %g0
	jmpl %o1+%m44(0x123456789abcdef0), %g0
	jmpl %o2+%l44(0x123456789abcdef0), %g0
	jmpl %o3+%lox(0x123456789abcdef0), %g0
	jmpl 0, %g0
	jmp %o4+%o5
	jmp %sp
	jmp %o7+1
	jmp %l0-2013
	jmp %l1+%lo(0x123456789abcdef0)
	jmp %l2+%hm(0x123456789abcdef0)
	jmp %l3+%ulo(0x123456789abcdef0)
	jmp %l4+%m44(0x123456789abcdef0)
	jmp %l5+%l44(0x123456789abcdef0)
	jmp %l6+%lox(0x123456789abcdef0)
	jmp -1
	return %l7+%i0
	return %i1
	return %i2+5
	return %i3-3663
	return %i4+%lo(0x123456789abcdef0)
	return %i5+%hm(0x123456789abcdef0)
	return %fp+%ulo(0x123456789abcdef0)
	return %i7+%m44(0x123456789abcdef0)
	return %g1+%l44(0x123456789abcdef0)
	return %g2+%lox(0x123456789abcdef0)
	return 100
	rett %g3+%g4
	rett %g5
	rett %g6+-100
	rett %g7-871
	rett %o0+%lo(0x123456789abcdef0)
	rett %o1+%hm(0x123456789abcdef0)
	rett %o2+%ulo(0x123456789abcdef0)
	rett %o3+%m44(0x123456789abcdef0)
	rett %o4+%l44(0x123456789abcdef0)
	rett %o5+%lox(0x123456789abcdef0)
	rett 4095
	ret
	retl
	ta 110
	ta %sp
	ta %o7 + %l0
	ta %l1 + 126
	ta %icc, 100
	ta %icc, %l2
	ta %icc, %l3 + %l4
	ta %icc, %l5 + 78
	tn 55
	tn %l6
	tn %l7 + %i0
	tn %i1 + 58
	tn %xcc, 87
	tn %xcc, %i2
	tn %xcc, %i3 + %i4
	tn %xcc, %i5 + 50
	tne 35
	tne %fp
	tne %i7 + %g1
	tne %g2 + 103
	tne %icc, 88
	tne %icc, %g3
	tne %icc, %g4 + %g5
	tne %icc, %g6 + 13
	tnz 33
	tnz %g7
	tnz %o0 + %o1
	tnz %o2 + 3
	tnz %xcc, 18
	tnz %xcc, %o3
	tnz %xcc, %o4 + %o5
	tnz %xcc, %sp + 65
	te 110
	te %o7
	te %l0 + %l1
	te %l2 + 41
	te %icc, 14
	te %icc, %l3
	te %icc, %l4 + %l5
	te %icc, %l6 + 21
	tz 97
	tz %l7
	tz %i0 + %i1
	tz %i2 + 72
	tz %xcc, 62
	tz %xcc, %i3
	tz %xcc, %i4 + %i5
	tz %xcc, %fp + 75
	tg 11
	tg %i7
	tg %g1 + %g2
	tg %g3 + 117
	tg %icc, 47
	tg %icc, %g4
	tg %icc, %g5 + %g6
	tg %icc, %g7 + 40
	tle 68
	tle %o0
	tle %o1 + %o2
	tle %o3 + 114
	tle %xcc, 0
	tle %xcc, %o4
	tle %xcc, %o5 + %sp
	tle %xcc, %o7 + 67
	tge 93
	tge %l0
	tge %l1 + %l2
	tge %l3 + 84
	tge %icc, 82
	tge %icc, %l4
	tge %icc, %l5 + %l6
	tge %icc, %l7 + 62
	tl 8
	tl %i0
	tl %i1 + %i2
	tl %i3 + 79
	tl %xcc, 55
	tl %xcc, %i4
	tl %xcc, %i5 + %fp
	tl %xcc, %i7 + 91
	tgu 46
	tgu %g1
	tgu %g2 + %g3
	tgu %g4 + 0
	tgu %icc, 85
	tgu %icc, %g5
	tgu %icc, %g6 + %g7
	tgu %icc, %o0 + 97
	tleu 21
	tleu %o1
	tleu %o2 + %o3
	tleu %o4 + 121
	tleu %xcc, 71
	tleu %xcc, %o5
	tleu %xcc, %sp + %o7
	tleu %xcc, %l0 + 51
	tcc 63
	tcc %l1
	tcc %l2 + %l3
	tcc %l4 + 1
	tcc %icc, 23
	tcc %icc, %l5
	tcc %icc, %l6 + %l7
	tcc %icc, %i0 + 67
	tgeu 22
	tgeu %i1
	tgeu %i2 + %i3
	tgeu %i4 + 36
	tgeu %xcc, 102
	tgeu %xcc, %i5
	tgeu %xcc, %fp + %i7
	tgeu %xcc, %g1 + 10
	tcs 100
	tcs %g2
	tcs %g3 + %g4
	tcs %g5 + 5
	tcs %icc, 76
	tcs %icc, %g6
	tcs %icc, %g7 + %o0
	tcs %icc, %o1 + 77
	tlu 59
	tlu %o2
	tlu %o3 + %o4
	tlu %o5 + 21
	tlu %xcc, 39
	tlu %xcc, %sp
	tlu %xcc, %o7 + %l0
	tlu %xcc, %l1 + 99
	tpos 83
	tpos %l2
	tpos %l3 + %l4
	tpos %l5 + 126
	tpos %icc, 38
	tpos %icc, %l6
	tpos %icc, %l7 + %i0
	tpos %icc, %i1 + 72
	tneg 37
	tneg %i2
	tneg %i3 + %i4
	tneg %i5 + 11
	tneg %xcc, 109
	tneg %xcc, %fp
	tneg %xcc, %i7 + %g1
	tneg %xcc, %g2 + 35
	tvc 4
	tvc %g3
	tvc %g4 + %g5
	tvc %g6 + 58
	tvc %icc, 21
	tvc %icc, %g7
	tvc %icc, %o0 + %o1
	tvc %icc, %o2 + 7
	tvs 10
	tvs %o3
	tvs %o4 + %o5
	tvs %sp + 34
	tvs %xcc, 92
	tvs %xcc, %o7
	tvs %xcc, %l0 + %l1
	tvs %xcc, %l2 + 26
	mova %icc, %l3, %l4
	mova %xcc, 518, %l5
	movn %icc, %l6, %l7
	movn %xcc, 824, %i0
	movne %icc, %i1, %i2
	movne %xcc, -817, %i3
	movnz %icc, %i4, %i5
	movnz %xcc, -947, %fp
	move %icc, %i7, %g1
	move %xcc, -23, %g2
	movz %icc, %g3, %g4
	movz %xcc, 980, %g5
	movg %icc, %g6, %g7
	movg %xcc, 56, %o0
	movle %icc, %o1, %o2
	movle %xcc, -1011, %o3
	movge %icc, %o4, %o5
	movge %xcc, 847, %sp
	movl %icc, %o7, %l0
	movl %xcc, -737, %l1
	movgu %icc, %l2, %l3
	movgu %xcc, -648, %l4
	movleu %icc, %l5, %l6
	movleu %xcc, -754, %l7
	movcc %icc, %i0, %i1
	movcc %xcc, 916, %i2
	movgeu %icc, %i3, %i4
	movgeu %xcc, 8, %i5
	movcs %icc, %fp, %i7
	movcs %xcc, -720, %g1
	movlu %icc, %g2, %g3
	movlu %xcc, 63, %g4
	movpos %icc, %g5, %g6
	movpos %xcc, -63, %g7
	movneg %icc, %o0, %o1
	movneg %xcc, -184, %o2
	movvc %icc, %o3, %o4
	movvc %xcc, -79, %o5
	movvs %icc, %sp, %o7
	movvs %xcc, 861, %l0
	mova %fcc0, %l1, %l2
	mova %fcc1, 999, %l3
	movn %fcc2, %l4, %l5
	movn %fcc3, 542, %l6
	movu %fcc0, %l7, %i0
	movu %fcc1, -710, %i1
	movg %fcc2, %i2, %i3
	movg %fcc3, 938, %i4
	movug %fcc0, %i5, %fp
	movug %fcc1, 152, %i7
	movl %fcc2, %g1, %g2
	movl %fcc3, -833, %g3
	movul %fcc0, %g4, %g5
	movul %fcc1, -212, %g6
	movlg %fcc2, %g7, %o0
	movlg %fcc3, -707, %o1
	movne %fcc0, %o2, %o3
	movne %fcc1, -421, %o4
	movnz %fcc2, %o5, %sp
	movnz %fcc3, 334, %o7
	move %fcc0, %l0, %l1
	move %fcc1, 16, %l2
	movz %fcc2, %l3, %l4
	movz %fcc3, 222, %l5
	movue %fcc0, %l6, %l7
	movue %fcc1, -478, %i0
	movge %fcc2, %i1, %i2
	movge %fcc3, -973, %i3
	movuge %fcc0, %i4, %i5
	movuge %fcc1, 951, %fp
	movle %fcc2, %i7, %g1
	movle %fcc3, -776, %g2
	movule %fcc0, %g3, %g4
	movule %fcc1, 965, %g5
	movo %fcc2, %g6, %g7
	movo %fcc3, 76, %o0
	fmovsa %icc, %f0, %f1
	fmovda %xcc, %f0, %f2
	fmovqa %icc, %f0, %f4
	fmovsn %xcc, %f5, %f9
	fmovdn %icc, %f6, %f10
	fmovqn %xcc, %f12, %f28
	fmovsne %icc, %f14, %f19
	fmovdne %xcc, %f30, %f32
	fmovqne %icc, %f32, %f40
	fmovsnz %xcc, %f23, %f30
	fmovdnz %icc, %f36, %f44
	fmovqnz %xcc, %f52, %f60
	fmovse %icc, %f31, %f2
	fmovde %xcc, %f58, %f62
	fmovqe %icc, %f0, %f4
	fmovsz %xcc, %f0, %f1
	fmovdz %icc, %f0, %f2
	fmovqz %xcc, %f12, %f28
	fmovsg %icc, %f5, %f9
	fmovdg %xcc, %f6, %f10
	fmovqg %icc, %f32, %f40
	fmovsle %xcc, %f14, %f19
	fmovdle %icc, %f30, %f32
	fmovqle %xcc, %f52, %f60
	fmovsge %icc, %f23, %f30
	fmovdge %xcc, %f36, %f44
	fmovqge %icc, %f0, %f4
	fmovsl %xcc, %f31, %f2
	fmovdl %icc, %f58, %f62
	fmovql %xcc, %f12, %f28
	fmovsgu %icc, %f0, %f1
	fmovdgu %xcc, %f0, %f2
	fmovqgu %icc, %f32, %f40
	fmovsleu %xcc, %f5, %f9
	fmovdleu %icc, %f6, %f10
	fmovqleu %xcc, %f52, %f60
	fmovscc %icc, %f14, %f19
	fmovdcc %xcc, %f30, %f32
	fmovqcc %icc, %f0, %f4
	fmovsgeu %xcc, %f23, %f30
	fmovdgeu %icc, %f36, %f44
	fmovqgeu %xcc, %f12, %f28
	fmovscs %icc, %f31, %f2
	fmovdcs %xcc, %f58, %f62
	fmovqcs %icc, %f32, %f40
	fmovslu %xcc, %f0, %f1
	fmovdlu %icc, %f0, %f2
	fmovqlu %xcc, %f52, %f60
	fmovspos %icc, %f5, %f9
	fmovdpos %xcc, %f6, %f10
	fmovqpos %icc, %f0, %f4
	fmovsneg %xcc, %f14, %f19
	fmovdneg %icc, %f30, %f32
	fmovqneg %xcc, %f12, %f28
	fmovsvc %icc, %f23, %f30
	fmovdvc %xcc, %f36, %f44
	fmovqvc %icc, %f32, %f40
	fmovsvs %xcc, %f31, %f2
	fmovdvs %icc, %f58, %f62
	fmovqvs %xcc, %f52, %f60
	fmovsa %fcc0, %f0, %f1
	fmovda %fcc1, %f0, %f2
	fmovqa %fcc2, %f0, %f4
	fmovsn %fcc3, %f5, %f9
	fmovdn %fcc0, %f6, %f10
	fmovqn %fcc1, %f12, %f28
	fmovsu %fcc2, %f14, %f19
	fmovdu %fcc3, %f30, %f32
	fmovqu %fcc0, %f32, %f40
	fmovsg %fcc1, %f23, %f30
	fmovdg %fcc2, %f36, %f44
	fmovqg %fcc3, %f52, %f60
	fmovsug %fcc0, %f31, %f2
	fmovdug %fcc1, %f58, %f62
	fmovqug %fcc2, %f0, %f4
	fmovsl %fcc3, %f0, %f1
	fmovdl %fcc0, %f0, %f2
	fmovql %fcc1, %f12, %f28
	fmovsul %fcc2, %f5, %f9
	fmovdul %fcc3, %f6, %f10
	fmovqul %fcc0, %f32, %f40
	fmovslg %fcc1, %f14, %f19
	fmovdlg %fcc2, %f30, %f32
	fmovqlg %fcc3, %f52, %f60
	fmovsne %fcc0, %f23, %f30
	fmovdne %fcc1, %f36, %f44
	fmovqne %fcc2, %f0, %f4
	fmovsnz %fcc3, %f31, %f2
	fmovdnz %fcc0, %f58, %f62
	fmovqnz %fcc1, %f12, %f28
	fmovse %fcc2, %f0, %f1
	fmovde %fcc3, %f0, %f2
	fmovqe %fcc0, %f32, %f40
	fmovsz %fcc1, %f5, %f9
	fmovdz %fcc2, %f6, %f10
	fmovqz %fcc3, %f52, %f60
	fmovsue %fcc0, %f14, %f19
	fmovdue %fcc1, %f30, %f32
	fmovque %fcc2, %f0, %f4
	fmovsge %fcc3, %f23, %f30
	fmovdge %fcc0, %f36, %f44
	fmovqge %fcc1, %f12, %f28
	fmovsuge %fcc2, %f31, %f2
	fmovduge %fcc3, %f58, %f62
	fmovquge %fcc0, %f32, %f40
	fmovsle %fcc1, %f0, %f1
	fmovdle %fcc2, %f0, %f2
	fmovqle %fcc3, %f52, %f60
	fmovsule %fcc0, %f5, %f9
	fmovdule %fcc1, %f6, %f10
	fmovqule %fcc2, %f0, %f4
	fmovso %fcc3, %f14, %f19
	fmovdo %fcc0, %f30, %f32
	fmovqo %fcc1, %f12, %f28
	movrz %o1, %o2, %o3
	movrz %o4, -309, %o5
	fmovrsz %sp, %f23, %f30
	fmovrdz %o7, %f36, %f44
	fmovrqz %l0, %f32, %f40
	movre %l1, %l2, %l3
	movre %l4, -67, %l5
	fmovrse %l6, %f31, %f2
	fmovrde %l7, %f58, %f62
	fmovrqe %i0, %f52, %f60
	movrlez %i1, %i2, %i3
	movrlez %i4, 490, %i5
	fmovrslez %fp, %f0, %f1
	fmovrdlez %i7, %f0, %f2
	fmovrqlez %g1, %f0, %f4
	movrlz %g2, %g3, %g4
	movrlz %g5, 83, %g6
	fmovrslz %g7, %f5, %f9
	fmovrdlz %o0, %f6, %f10
	fmovrqlz %o1, %f12, %f28
	movrnz %o2, %o3, %o4
	movrnz %o5, 72, %sp
	fmovrsnz %o7, %f14, %f19
	fmovrdnz %l0, %f30, %f32
	fmovrqnz %l1, %f32, %f40
	movrne %l2, %l3, %l4
	movrne %l5, 439, %l6
	fmovrsne %l7, %f23, %f30
	fmovrdne %i0, %f36, %f44
	fmovrqne %i1, %f52, %f60
	movrgz %i2, %i3, %i4
	movrgz %i5, 442, %fp
	fmovrsgz %i7, %f31, %f2
	fmovrdgz %g1, %f58, %f62
	fmovrqgz %g2, %f0, %f4
	movrgez %g3, %g4, %g5
	movrgez %g6, 443, %g7
	fmovrsgez %o0, %f0, %f1
	fmovrdgez %o1, %f0, %f2
	fmovrqgez %o2, %f12, %f28
	ld [%o4+%o5], %o3
	ld [%sp], %o3
	ld [%o7+-4096], %o3
	ld [%l0-971], %o3
	ld [%l1+%lo(0x123456789abcdef0)], %o3
	ld [%l2+%hm(0x123456789abcdef0)], %o3
	ld [%l3+%ulo(0x123456789abcdef0)], %o3
	ld [%l4+%m44(0x123456789abcdef0)], %o3
	ld [%l5+%l44(0x123456789abcdef0)], %o3
	ld [%l6+%lox(0x123456789abcdef0)], %o3
	ld [2047], %o3
	lduw [%i0+%i1], %l7
	lduw [%i2], %l7
	lduw [%i3+-2048], %l7
	lduw [%i4-1633], %l7
	lduw [%i5+%lo(0x123456789abcdef0)], %l7
	lduw [%fp+%hm(0x123456789abcdef0)], %l7
	lduw [%i7+%ulo(0x123456789abcdef0)], %l7
	lduw [%g1+%m44(0x123456789abcdef0)], %l7
	lduw [%g2+%l44(0x123456789abcdef0)], %l7
	lduw [%g3+%lox(0x123456789abcdef0)], %l7
	lduw [291], %l7
	ldub [%g5+%g6], %g4
	ldub [%g7], %g4
	ldub [%o0+-2047], %g4
	ldub [%o1-2554], %g4
	ldub [%o2+%lo(0x123456789abcdef0)], %g4
	ldub [%o3+%hm(0x123456789abcdef0)], %g4
	ldub [%o4+%ulo(0x123456789abcdef0)], %g4
	ldub [%o5+%m44(0x123456789abcdef0)], %g4
	ldub [%sp+%l44(0x123456789abcdef0)], %g4
	ldub [%o7+%lox(0x123456789abcdef0)], %g4
	ldub [0], %g4
	lduh [%l1+%l2], %l0
	lduh [%l3], %l0
	lduh [%l4+1], %l0
	lduh [%l5-704], %l0
	lduh [%l6+%lo(0x123456789abcdef0)], %l0
	lduh [%l7+%hm(0x123456789abcdef0)], %l0
	lduh [%i0+%ulo(0x123456789abcdef0)], %l0
	lduh [%i1+%m44(0x123456789abcdef0)], %l0
	lduh [%i2+%l44(0x123456789abcdef0)], %l0
	lduh [%i3+%lox(0x123456789abcdef0)], %l0
	lduh [-1], %l0
	ldsw [%i5+%fp], %i4
	ldsw [%i7], %i4
	ldsw [%g1+5], %i4
	ldsw [%g2-3875], %i4
	ldsw [%g3+%lo(0x123456789abcdef0)], %i4
	ldsw [%g4+%hm(0x123456789abcdef0)], %i4
	ldsw [%g5+%ulo(0x123456789abcdef0)], %i4
	ldsw [%g6+%m44(0x123456789abcdef0)], %i4
	ldsw [%g7+%l44(0x123456789abcdef0)], %i4
	ldsw [%o0+%lox(0x123456789abcdef0)], %i4
	ldsw [100], %i4
	ldsb [%o2+%o3], %o1
	ldsb [%o4], %o1
	ldsb [%o5+-100], %o1
	ldsb [%sp-144], %o1
	ldsb [%o7+%lo(0x123456789abcdef0)], %o1
	ldsb [%l0+%hm(0x123456789abcdef0)], %o1
	ldsb [%l1+%ulo(0x123456789abcdef0)], %o1
	ldsb [%l2+%m44(0x123456789abcdef0)], %o1
	ldsb [%l3+%l44(0x123456789abcdef0)], %o1
	ldsb [%l4+%lox(0x123456789abcdef0)], %o1
	ldsb [4095], %o1
	ldsh [%l6+%l7], %l5
	ldsh [%i0], %l5
	ldsh [%i1+-4096], %l5
	ldsh [%i2-2373], %l5
	ldsh [%i3+%lo(0x123456789abcdef0)], %l5
	ldsh [%i4+%hm(0x123456789abcdef0)], %l5
	ldsh [%i5+%ulo(0x123456789abcdef0)], %l5
	ldsh [%fp+%m44(0x123456789abcdef0)], %l5
	ldsh [%i7+%l44(0x123456789abcdef0)], %l5
	ldsh [%g1+%lox(0x123456789abcdef0)], %l5
	ldsh [2047], %l5
	ldx [%g3+%g4], %g2
	ldx [%g5], %g2
	ldx [%g6+-2048], %g2
	ldx [%g7-3760], %g2
	ldx [%o0+%lo(0x123456789abcdef0)], %g2
	ldx [%o1+%hm(0x123456789abcdef0)], %g2
	ldx [%o2+%ulo(0x123456789abcdef0)], %g2
	ldx [%o3+%m44(0x123456789abcdef0)], %g2
	ldx [%o4+%l44(0x123456789abcdef0)], %g2
	ldx [%o5+%lox(0x123456789abcdef0)], %g2
	ldx [291], %g2
	ldstub [%o7+%l0], %sp
	ldstub [%l1], %sp
	ldstub [%l2+-2047], %sp
	ldstub [%l3-627], %sp
	ldstub [%l4+%lo(0x123456789abcdef0)], %sp
	ldstub [%l5+%hm(0x123456789abcdef0)], %sp
	ldstub [%l6+%ulo(0x123456789abcdef0)], %sp
	ldstub [%l7+%m44(0x123456789abcdef0)], %sp
	ldstub [%i0+%l44(0x123456789abcdef0)], %sp
	ldstub [%i1+%lox(0x123456789abcdef0)], %sp
	ldstub [0], %sp
	swap [%i3+%i4], %i2
	swap [%i5], %i2
	swap [%fp+1], %i2
	swap [%i7-3682], %i2
	swap [%g1+%lo(0x123456789abcdef0)], %i2
	swap [%g2+%hm(0x123456789abcdef0)], %i2
	swap [%g3+%ulo(0x123456789abcdef0)], %i2
	swap [%g4+%m44(0x123456789abcdef0)], %i2
	swap [%g5+%l44(0x123456789abcdef0)], %i2
	swap [%g6+%lox(0x123456789abcdef0)], %i2
	swap [-1], %i2
	ldd [%g7+%o0], %g0
	ldd [%o1], %g0
	ldd [%o2+5], %g0
	ldd [%o3-2201], %g0
	ldd [%o4+%lo(0x123456789abcdef0)], %g0
	ldd [%o5+%hm(0x123456789abcdef0)], %g0
	ldd [%sp+%ulo(0x123456789abcdef0)], %g0
	ldd [%o7+%m44(0x123456789abcdef0)], %g0
	ldd [%l0+%l44(0x123456789abcdef0)], %g0
	ldd [%l1+%lox(0x123456789abcdef0)], %g0
	ldd [100], %g0
	st %l2, [%l3+%l4]
	st %l2, [%l5]
	st %l2, [%l6+-100]
	st %l2, [%l7-3170]
	st %l2, [%i0+%lo(0x123456789abcdef0)]
	st %l2, [%i1+%hm(0x123456789abcdef0)]
	st %l2, [%i2+%ulo(0x123456789abcdef0)]
	st %l2, [%i3+%m44(0x123456789abcdef0)]
	st %l2, [%i4+%l44(0x123456789abcdef0)]
	st %l2, [%i5+%lox(0x123456789abcdef0)]
	st %l2, [4095]
	stw %fp, [%i7+%g1]
	stw %fp, [%g2]
	stw %fp, [%g3+-4096]
	stw %fp, [%g4-1719]
	stw %fp, [%g5+%lo(0x123456789abcdef0)]
	stw %fp, [%g6+%hm(0x123456789abcdef0)]
	stw %fp, [%g7+%ulo(0x123456789abcdef0)]
	stw %fp, [%o0+%m44(0x123456789abcdef0)]
	stw %fp, [%o1+%l44(0x123456789abcdef0)]
	stw %fp, [%o2+%lox(0x123456789abcdef0)]
	stw %fp, [2047]
	stuw %o3, [%o4+%o5]
	stuw %o3, [%sp]
	stuw %o3, [%o7+-2048]
	stuw %o3, [%l0-1727]
	stuw %o3, [%l1+%lo(0x123456789abcdef0)]
	stuw %o3, [%l2+%hm(0x123456789abcdef0)]
	stuw %o3, [%l3+%ulo(0x123456789abcdef0)]
	stuw %o3, [%l4+%m44(0x123456789abcdef0)]
	stuw %o3, [%l5+%l44(0x123456789abcdef0)]
	stuw %o3, [%l6+%lox(0x123456789abcdef0)]
	stuw %o3, [291]
	stsw %l7, [%i0+%i1]
	stsw %l7, [%i2]
	stsw %l7, [%i3+-2047]
	stsw %l7, [%i4-612]
	stsw %l7, [%i5+%lo(0x123456789abcdef0)]
	stsw %l7, [%fp+%hm(0x123456789abcdef0)]
	stsw %l7, [%i7+%ulo(0x123456789abcdef0)]
	stsw %l7, [%g1+%m44(0x123456789abcdef0)]
	stsw %l7, [%g2+%l44(0x123456789abcdef0)]
	stsw %l7, [%g3+%lox(0x123456789abcdef0)]
	stsw %l7, [0]
	stb %g4, [%g5+%g6]
	stb %g4, [%g7]
	stb %g4, [%o0+1]
	stb %g4, [%o1-740]
	stb %g4, [%o2+%lo(0x123456789abcdef0)]
	stb %g4, [%o3+%hm(0x123456789abcdef0)]
	stb %g4, [%o4+%ulo(0x123456789abcdef0)]
	stb %g4, [%o5+%m44(0x123456789abcdef0)]
	stb %g4, [%sp+%l44(0x123456789abcdef0)]
	stb %g4, [%o7+%lox(0x123456789abcdef0)]
	stb %g4, [-1]
	stub %l0, [%l1+%l2]
	stub %l0, [%l3]
	stub %l0, [%l4+5]
	stub %l0, [%l5-1162]
	stub %l0, [%l6+%lo(0x123456789abcdef0)]
	stub %l0, [%l7+%hm(0x123456789abcdef0)]
	stub %l0, [%i0+%ulo(0x123456789abcdef0)]
	stub %l0, [%i1+%m44(0x123456789abcdef0)]
	stub %l0, [%i2+%l44(0x123456789abcdef0)]
	stub %l0, [%i3+%lox(0x123456789abcdef0)]
	stub %l0, [100]
	stsb %i4, [%i5+%fp]
	stsb %i4, [%i7]
	stsb %i4, [%g1+-100]
	stsb %i4, [%g2-2145]
	stsb %i4, [%g3+%lo(0x123456789abcdef0)]
	stsb %i4, [%g4+%hm(0x123456789abcdef0)]
	stsb %i4, [%g5+%ulo(0x123456789abcdef0)]
	stsb %i4, [%g6+%m44(0x123456789abcdef0)]
	stsb %i4, [%g7+%l44(0x123456789abcdef0)]
	stsb %i4, [%o0+%lox(0x123456789abcdef0)]
	stsb %i4, [4095]
	sth %o1, [%o2+%o3]
	sth %o1, [%o4]
	sth %o1, [%o5+-4096]
	sth %o1, [%sp-2946]
	sth %o1, [%o7+%lo(0x123456789abcdef0)]
	sth %o1, [%l0+%hm(0x123456789abcdef0)]
	sth %o1, [%l1+%ulo(0x123456789abcdef0)]
	sth %o1, [%l2+%m44(0x123456789abcdef0)]
	sth %o1, [%l3+%l44(0x123456789abcdef0)]
	sth %o1, [%l4+%lox(0x123456789abcdef0)]
	sth %o1, [2047]
	stuh %l5, [%l6+%l7]
	stuh %l5, [%i0]
	stuh %l5, [%i1+-2048]
	stuh %l5, [%i2-1087]
	stuh %l5, [%i3+%lo(0x123456789abcdef0)]
	stuh %l5, [%i4+%hm(0x123456789abcdef0)]
	stuh %l5, [%i5+%ulo(0x123456789abcdef0)]
	stuh %l5, [%fp+%m44(0x123456789abcdef0)]
	stuh %l5, [%i7+%l44(0x123456789abcdef0)]
	stuh %l5, [%g1+%lox(0x123456789abcdef0)]
	stuh %l5, [291]
	stsh %g2, [%g3+%g4]
	stsh %g2, [%g5]
	stsh %g2, [%g6+-2047]
	stsh %g2, [%g7-2291]
	stsh %g2, [%o0+%lo(0x123456789abcdef0)]
	stsh %g2, [%o1+%hm(0x123456789abcdef0)]
	stsh %g2, [%o2+%ulo(0x123456789abcdef0)]
	stsh %g2, [%o3+%m44(0x123456789abcdef0)]
	stsh %g2, [%o4+%l44(0x123456789abcdef0)]
	stsh %g2, [%o5+%lox(0x123456789abcdef0)]
	stsh %g2, [0]
	stx %sp, [%o7+%l0]
	stx %sp, [%l1]
	stx %sp, [%l2+1]
	stx %sp, [%l3-924]
	stx %sp, [%l4+%lo(0x123456789abcdef0)]
	stx %sp, [%l5+%hm(0x123456789abcdef0)]
	stx %sp, [%l6+%ulo(0x123456789abcdef0)]
	stx %sp, [%l7+%m44(0x123456789abcdef0)]
	stx %sp, [%i0+%l44(0x123456789abcdef0)]
	stx %sp, [%i1+%lox(0x123456789abcdef0)]
	stx %sp, [-1]
	std %g2, [%i2+%i3]
	std %g2, [%i4]
	std %g2, [%i5+5]
	std %g2, [%fp-2992]
	std %g2, [%i7+%lo(0x123456789abcdef0)]
	std %g2, [%g1+%hm(0x123456789abcdef0)]
	std %g2, [%g2+%ulo(0x123456789abcdef0)]
	std %g2, [%g3+%m44(0x123456789abcdef0)]
	std %g2, [%g4+%l44(0x123456789abcdef0)]
	std %g2, [%g5+%lox(0x123456789abcdef0)]
	std %g2, [100]
	lda [%g7+%o0] #ASI_P, %g6
	lda [%o1] #ASI_P, %g6
	lda [%o2] %asi, %g6
	lda [%o3+-100] %asi, %g6
	lda [4095] %asi, %g6
	lduwa [%o5+%sp] 0x2a, %o4
	lduwa [%o7] 0x2a, %o4
	lduwa [%l0] %asi, %o4
	lduwa [%l1+-4096] %asi, %o4
	lduwa [2047] %asi, %o4
	lduba [%l3+%l4] 0x2a, %l2
	lduba [%l5] 0x2a, %l2
	lduba [%l6] %asi, %l2
	lduba [%l7+-2048] %asi, %l2
	lduba [291] %asi, %l2
	lduha [%i1+%i2] 0x2a, %i0
	lduha [%i3] 0x2a, %i0
	lduha [%i4] %asi, %i0
	lduha [%i5+-2047] %asi, %i0
	lduha [0] %asi, %i0
	ldswa [%i7+%g1] 0x80, %fp
	ldswa [%g2] 0x80, %fp
	ldswa [%g3] %asi, %fp
	ldswa [%g4+1] %asi, %fp
	ldswa [-1] %asi, %fp
	ldsba [%g6+%g7] #ASI_P, %g5
	ldsba [%o0] #ASI_P, %g5
	ldsba [%o1] %asi, %g5
	ldsba [%o2+5] %asi, %g5
	ldsba [100] %asi, %g5
	ldsha [%o4+%o5] 0x80, %o3
	ldsha [%sp] 0x80, %o3
	ldsha [%o7] %asi, %o3
	ldsha [%l0+-100] %asi, %o3
	ldsha [4095] %asi, %o3
	ldxa [%l2+%l3] 0x2a, %l1
	ldxa [%l4] 0x2a, %l1
	ldxa [%l5] %asi, %l1
	ldxa [%l6+-4096] %asi, %l1
	ldxa [2047] %asi, %l1
	ldstuba [%i0+%i1] 255, %l7
	ldstuba [%i2] 255, %l7
	ldstuba [%i3] %asi, %l7
	ldstuba [%i4+-2048] %asi, %l7
	ldstuba [291] %asi, %l7
	swapa [%fp+%i7] 0x2a, %i5
	swapa [%g1] 0x2a, %i5
	swapa [%g2] %asi, %i5
	swapa [%g3+-2047] %asi, %i5
	swapa [0] %asi, %i5
	ldda [%g4+%g5] 0x2a, %g6
	ldda [%g6] 0x2a, %g6
	ldda [%g7] %asi, %g6
	ldda [%o0+1] %asi, %g6
	ldda [-1] %asi, %g6
	sta %o1, [%o2+%o3] #ASI_AIUS
	sta %o1, [%o4] #ASI_AIUS
	sta %o1, [%o5] %asi
	sta %o1, [%sp+5] %asi
	sta %o1, [100] %asi
	stwa %o7, [%l0+%l1] 255
	stwa %o7, [%l2] 255
	stwa %o7, [%l3] %asi
	stwa %o7, [%l4+-100] %asi
	stwa %o7, [4095] %asi
	stuwa %l5, [%l6+%l7] #ASI_P
	stuwa %l5, [%i0] #ASI_P
	stuwa %l5, [%i1] %asi
	stuwa %l5, [%i2+-4096] %asi
	stuwa %l5, [2047] %asi
	stba %i3, [%i4+%i5] 0x2a
	stba %i3, [%fp] 0x2a
	stba %i3, [%i7] %asi
	stba %i3, [%g1+-2048] %asi
	stba %i3, [291] %asi
	stha %g2, [%g3+%g4] #ASI_AIUS
	stha %g2, [%g5] #ASI_AIUS
	stha %g2, [%g6] %asi
	stha %g2, [%g7+-2047] %asi
	stha %g2, [0] %asi
	stxa %o0, [%o1+%o2] 0x2a
	stxa %o0, [%o3] 0x2a
	stxa %o0, [%o4] %asi
	stxa %o0, [%o5+1] %asi
	stxa %o0, [-1] %asi
	stda %o2, [%sp+%o7] #ASI_AIUS
	stda %o2, [%l0] #ASI_AIUS
	stda %o2, [%l1] %asi
	stda %o2, [%l2+5] %asi
	stda %o2, [100] %asi
	clr [%l3+%l4]
	clr [%l5]
	clr [%l6+-100]
	clr [%l7-991]
	clr [%i0+%lo(0x123456789abcdef0)]
	clr [%i1+%hm(0x123456789abcdef0)]
	clr [%i2+%ulo(0x123456789abcdef0)]
	clr [%i3+%m44(0x123456789abcdef0)]
	clr [%i4+%l44(0x123456789abcdef0)]
	clr [%i5+%lox(0x123456789abcdef0)]
	clr [4095]
	clrb [%fp+%i7]
	clrb [%g1]
	clrb [%g2+-4096]
	clrb [%g3-2715]
	clrb [%g4+%lo(0x123456789abcdef0)]
	clrb [%g5+%hm(0x123456789abcdef0)]
	clrb [%g6+%ulo(0x123456789abcdef0)]
	clrb [%g7+%m44(0x123456789abcdef0)]
	clrb [%o0+%l44(0x123456789abcdef0)]
	clrb [%o1+%lox(0x123456789abcdef0)]
	clrb [2047]
	clrh [%o2+%o3]
	clrh [%o4]
	clrh [%o5+-2048]
	clrh [%sp-15]
	clrh [%o7+%lo(0x123456789abcdef0)]
	clrh [%l0+%hm(0x123456789abcdef0)]
	clrh [%l1+%ulo(0x123456789abcdef0)]
	clrh [%l2+%m44(0x123456789abcdef0)]
	clrh [%l3+%l44(0x123456789abcdef0)]
	clrh [%l4+%lox(0x123456789abcdef0)]
	clrh [291]
	ld [%l5+%l6], %f5
	ld [%l7], %f5
	ld [%i0+-2047], %f5
	ld [%i1-2659], %f5
	ld [%i2+%lo(0x123456789abcdef0)], %f5
	ld [%i3+%hm(0x123456789abcdef0)], %f5
	ld [%i4+%ulo(0x123456789abcdef0)], %f5
	ld [%i5+%m44(0x123456789abcdef0)], %f5
	ld [%fp+%l44(0x123456789abcdef0)], %f5
	ld [%i7+%lox(0x123456789abcdef0)], %f5
	ld [0], %f5
	ldd [%g1+%g2], %f6
	ldd [%g3], %f6
	ldd [%g4+1], %f6
	ldd [%g5-2772], %f6
	ldd [%g6+%lo(0x123456789abcdef0)], %f6
	ldd [%g7+%hm(0x123456789abcdef0)], %f6
	ldd [%o0+%ulo(0x123456789abcdef0)], %f6
	ldd [%o1+%m44(0x123456789abcdef0)], %f6
	ldd [%o2+%l44(0x123456789abcdef0)], %f6
	ldd [%o3+%lox(0x123456789abcdef0)], %f6
	ldd [-1], %f6
	ldq [%o4+%o5], %f32
	ldq [%sp], %f32
	ldq [%o7+5], %f32
	ldq [%l0-3263], %f32
	ldq [%l1+%lo(0x123456789abcdef0)], %f32
	ldq [%l2+%hm(0x123456789abcdef0)], %f32
	ldq [%l3+%ulo(0x123456789abcdef0)], %f32
	ldq [%l4+%m44(0x123456789abcdef0)], %f32
	ldq [%l5+%l44(0x123456789abcdef0)], %f32
	ldq [%l6+%lox(0x123456789abcdef0)], %f32
	ldq [100], %f32
	st %f9, [%l7+%i0]
	st %f9, [%i1]
	st %f9, [%i2+-100]
	st %f9, [%i3-984]
	st %f9, [%i4+%lo(0x123456789abcdef0)]
	st %f9, [%i5+%hm(0x123456789abcdef0)]
	st %f9, [%fp+%ulo(0x123456789abcdef0)]
	st %f9, [%i7+%m44(0x123456789abcdef0)]
	st %f9, [%g1+%l44(0x123456789abcdef0)]
	st %f9, [%g2+%lox(0x123456789abcdef0)]
	st %f9, [4095]
	std %f10, [%g3+%g4]
	std %f10, [%g5]
	std %f10, [%g6+-4096]
	std %f10, [%g7-1604]
	std %f10, [%o0+%lo(0x123456789abcdef0)]
	std %f10, [%o1+%hm(0x123456789abcdef0)]
	std %f10, [%o2+%ulo(0x123456789abcdef0)]
	std %f10, [%o3+%m44(0x123456789abcdef0)]
	std %f10, [%o4+%l44(0x123456789abcdef0)]
	std %f10, [%o5+%lox(0x123456789abcdef0)]
	std %f10, [2047]
	stq %f40, [%sp+%o7]
	stq %f40, [%l0]
	stq %f40, [%l1+-2048]
	stq %f40, [%l2-97]
	stq %f40, [%l3+%lo(0x123456789abcdef0)]
	stq %f40, [%l4+%hm(0x123456789abcdef0)]
	stq %f40, [%l5+%ulo(0x123456789abcdef0)]
	stq %f40, [%l6+%m44(0x123456789abcdef0)]
	stq %f40, [%l7+%l44(0x123456789abcdef0)]
	stq %f40, [%i0+%lox(0x123456789abcdef0)]
	stq %f40, [291]
	lda [%i1+%i2] 255, %f14
	lda [%i3] 255, %f14
	lda [%i4] %asi, %f14
	lda [%i5+-2047] %asi, %f14
	lda [0] %asi, %f14
	ldda [%fp+%i7] #ASI_AIUS, %f30
	ldda [%g1] #ASI_AIUS, %f30
	ldda [%g2] %asi, %f30
	ldda [%g3+1] %asi, %f30
	ldda [-1] %asi, %f30
	ldqa [%g4+%g5] #ASI_AIUS, %f52
	ldqa [%g6] #ASI_AIUS, %f52
	ldqa [%g7] %asi, %f52
	ldqa [%o0+5] %asi, %f52
	ldqa [100] %asi, %f52
	sta %f19, [%o1+%o2] #ASI_AIUS
	sta %f19, [%o3] #ASI_AIUS
	sta %f19, [%o4] %asi
	sta %f19, [%o5+-100] %asi
	sta %f19, [4095] %asi
	stda %f32, [%sp+%o7] 0x80
	stda %f32, [%l0] 0x80
	stda %f32, [%l1] %asi
	stda %f32, [%l2+-4096] %asi
	stda %f32, [2047] %asi
	stqa %f60, [%l3+%l4] 0x2a
	stqa %f60, [%l5] 0x2a
	stqa %f60, [%l6] %asi
	stqa %f60, [%l7+-2048] %asi
	stqa %f60, [291] %asi
	ld [%i0+%i1], %fsr
	ld [%i2], %fsr
	ld [%i3+-2047], %fsr
	ld [%i4-3197], %fsr
	ld [%i5+%lo(0x123456789abcdef0)], %fsr
	ld [%fp+%hm(0x123456789abcdef0)], %fsr
	ld [%i7+%ulo(0x123456789abcdef0)], %fsr
	ld [%g1+%m44(0x123456789abcdef0)], %fsr
	ld [%g2+%l44(0x123456789abcdef0)], %fsr
	ld [%g3+%lox(0x123456789abcdef0)], %fsr
	ld [0], %fsr
	ldx [%g4+%g5], %fsr
	ldx [%g6], %fsr
	ldx [%g7+1], %fsr
	ldx [%o0-626], %fsr
	ldx [%o1+%lo(0x123456789abcdef0)], %fsr
	ldx [%o2+%hm(0x123456789abcdef0)], %fsr
	ldx [%o3+%ulo(0x123456789abcdef0)], %fsr
	ldx [%o4+%m44(0x123456789abcdef0)], %fsr
	ldx [%o5+%l44(0x123456789abcdef0)], %fsr
	ldx [%sp+%lox(0x123456789abcdef0)], %fsr
	ldx [-1], %fsr
	st %fsr, [%o7+%l0]
	st %fsr, [%l1]
	st %fsr, [%l2+5]
	st %fsr, [%l3-2955]
	st %fsr, [%l4+%lo(0x123456789abcdef0)]
	st %fsr, [%l5+%hm(0x123456789abcdef0)]
	st %fsr, [%l6+%ulo(0x123456789abcdef0)]
	st %fsr, [%l7+%m44(0x123456789abcdef0)]
	st %fsr, [%i0+%l44(0x123456789abcdef0)]
	st %fsr, [%i1+%lox(0x123456789abcdef0)]
	st %fsr, [100]
	stx %fsr, [%i2+%i3]
	stx %fsr, [%i4]
	stx %fsr, [%i5+-100]
	stx %fsr, [%fp-3507]
	stx %fsr, [%i7+%lo(0x123456789abcdef0)]
	stx %fsr, [%g1+%hm(0x123456789abcdef0)]
	stx %fsr, [%g2+%ulo(0x123456789abcdef0)]
	stx %fsr, [%g3+%m44(0x123456789abcdef0)]
	stx %fsr, [%g4+%l44(0x123456789abcdef0)]
	stx %fsr, [%g5+%lox(0x123456789abcdef0)]
	stx %fsr, [4095]
	prefetch [%g6+%g7], #one_write
	prefetch [%o0], #one_write
	prefetch [%o1+-4096], #one_write
	prefetch [%o2-2255], #one_write
	prefetch [%o3+%lo(0x123456789abcdef0)], #one_write
	prefetch [%o4+%hm(0x123456789abcdef0)], #one_write
	prefetch [%o5+%ulo(0x123456789abcdef0)], #one_write
	prefetch [%sp+%m44(0x123456789abcdef0)], #one_write
	prefetch [%o7+%l44(0x123456789abcdef0)], #one_write
	prefetch [%l0+%lox(0x123456789abcdef0)], #one_write
	prefetch [2047], #one_write
	prefetch [%l1+%l2], 20
	prefetch [%l3], 20
	prefetch [%l4+-2048], 20
	prefetch [%l5-396], 20
	prefetch [%l6+%lo(0x123456789abcdef0)], 20
	prefetch [%l7+%hm(0x123456789abcdef0)], 20
	prefetch [%i0+%ulo(0x123456789abcdef0)], 20
	prefetch [%i1+%m44(0x123456789abcdef0)], 20
	prefetch [%i2+%l44(0x123456789abcdef0)], 20
	prefetch [%i3+%lox(0x123456789abcdef0)], 20
	prefetch [291], 20
	prefetcha [%i4+%i5] #ASI_AIUS, #n_reads
	prefetcha [%fp] #ASI_AIUS, #n_reads
	prefetcha [%i7] %asi, #n_reads
	prefetcha [%g1+-2047] %asi, #n_reads
	prefetcha [0] %asi, #n_reads
	casa [%g2] 0x80, %g3, %g4
	casa [%g5] #ASI_PNF, %g6, %g7
	casa [%o0] %asi, %o1, %o2
	casxa [%o3] 0x80, %o4, %o5
	casxa [%sp] #ASI_PNF, %o7, %l0
	casxa [%l1] %asi, %l2, %l3
	cas [%l4], %l5, %l6
	casl [%l7], %i0, %i1
	casx [%i2], %i3, %i4
	casxl [%i5], %fp, %i7
	fmovs %f23, %f30
	fmovd %f36, %f44
	fmovq %f0, %f4
	fnegs %f31, %f2
	fnegd %f58, %f62
	fnegq %f12, %f28
	fabss %f0, %f1
	fabsd %f0, %f2
	fabsq %f32, %f40
	fsqrts %f5, %f9
	fsqrtd %f6, %f10
	fsqrtq %f52, %f60
	fadds %f14, %f19, %f23
	faddd %f30, %f32, %f36
	faddq %f0, %f4, %f12
	fsubs %f30, %f31, %f2
	fsubd %f44, %f58, %f62
	fsubq %f28, %f32, %f40
	fmuls %f0, %f1, %f5
	fmuld %f0, %f2, %f6
	fmulq %f52, %f60, %f0
	fdivs %f9, %f14, %f19
	fdivd %f10, %f30, %f32
	fdivq %f4, %f12, %f28
	fsmuld %f23, %f30, %f36
	fdmulq %f44, %f58, %f32
	fstox %f31, %f62
	fdtox %f0, %f2
	fqtox %f40, %f6
	fxtos %f10, %f2
	fxtod %f30, %f32
	fxtoq %f36, %f52
	fitos %f0, %f1
	fdtos %f44, %f5
	fqtos %f60, %f9
	fitod %f14, %f58
	fstod %f19, %f62
	fqtod %f0, %f0
	fitoq %f23, %f4
	fstoq %f30, %f12
	fdtoq %f2, %f28
	fstoi %f31, %f2
	fdtoi %f6, %f0
	fqtoi %f32, %f1
	fcmps %fcc2, %f5, %f9
	fcmps %f14, %f19
	fcmpd %fcc3, %f10, %f30
	fcmpd %f32, %f36
	fcmpq %fcc0, %f40, %f52
	fcmpq %f60, %f0
	fcmpes %fcc1, %f23, %f30
	fcmpes %f31, %f2
	fcmped %fcc2, %f44, %f58
	fcmped %f62, %f0
	fcmpeq %fcc3, %f4, %f12
	fcmpeq %f28, %f32
	edge8 %i3, %i4, %i5
	edge8n %fp, %i7, %g1
	edge8l %g2, %g3, %g4
	edge8ln %g5, %g6, %g7
	edge16 %o0, %o1, %o2
	edge16n %o3, %o4, %o5
	edge16l %sp, %o7, %l0
	edge16ln %l1, %l2, %l3
	edge32 %l4, %l5, %l6
	edge32n %l7, %i0, %i1
	edge32l %i2, %i3, %i4
	edge32ln %i5, %fp, %i7
	array8 %g1, %g2, %g3
	addxc %g4, %g5, %g6
	array16 %g7, %o0, %o1
	addxccc %o2, %o3, %o4
	array32 %o5, %sp, %o7
	umulxhi %l0, %l1, %l2
	alignaddr %l3, %l4, %l5
	bmask %l6, %l7, %i0
	alignaddrl %i1, %i2, %i3
	xmulx %i4, %i5, %fp
	xmulxhi %i7, %g1, %g2
	lzcnt %g3, %g4
	cmask8 %g5
	cmask16 %g6
	cmask32 %g7
	fcmple16 %f2, %f6, %o0
	fcmpne16 %f10, %f30, %o1
	fcmple32 %f32, %f36, %o2
	fcmpne32 %f44, %f58, %o3
	fcmpgt16 %f62, %f0, %o4
	fcmpeq16 %f2, %f6, %o5
	fcmpgt32 %f10, %f30, %sp
	fcmpeq32 %f32, %f36, %o7
	fsll16 %f44, %f58, %f62
	fsrl16 %f0, %f2, %f6
	fsll32 %f10, %f30, %f32
	fsrl32 %f36, %f44, %f58
	fslas16 %f62, %f0, %f2
	fsra16 %f6, %f10, %f30
	fslas32 %f32, %f36, %f44
	fsra32 %f58, %f62, %f0
	fmul8sux16 %f2, %f6, %f10
	fmul8ulx16 %f30, %f32, %f36
	fpack32 %f44, %f58, %f62
	pdist %f0, %f2, %f6
	fmean16 %f10, %f30, %f32
	fpadd64 %f36, %f44, %f58
	fchksm16 %f62, %f0, %f2
	faligndata %f6, %f10, %f30
	bshuffle %f32, %f36, %f44
	fpadd16 %f58, %f62, %f0
	fpadd32 %f2, %f6, %f10
	fpsub16 %f30, %f32, %f36
	fpsub32 %f44, %f58, %f62
	fnor %f0, %f2, %f6
	fandnot2 %f10, %f30, %f32
	fandnot1 %f36, %f44, %f58
	fxor %f62, %f0, %f2
	fnand %f6, %f10, %f30
	fand %f32, %f36, %f44
	fxnor %f58, %f62, %f0
	fornot2 %f2, %f6, %f10
	fornot1 %f30, %f32, %f36
	for %f44, %f58, %f62
	fpadd16s %f2, %f30, %f4
	fpadd32s %f30, %f8, %f0
	fpsub16s %f30, %f30, %f20
	fpsub32s %f8, %f12, %f12
	fnors %f0, %f1, %f5
	fandnot2s %f9, %f14, %f19
	fandnot1s %f23, %f30, %f31
	fxors %f2, %f0, %f1
	fnands %f5, %f9, %f14
	fands %f19, %f23, %f30
	fxnors %f31, %f2, %f0
	fornot2s %f1, %f5, %f9
	fornot1s %f14, %f19, %f23
	fors %f30, %f31, %f2
	fnot2 %f0, %f2
	fsrc2 %f6, %f10
	fnot1 %f30, %f32
	fsrc1 %f36, %f44
	fnot2s %f0, %f1
	fsrc2s %f5, %f9
	fnot1s %f14, %f19
	fsrc1s %f23, %f30
	fzero %f58
	fone %f62
	fzeros %f31
	fones %f2
	shutdown
	movdtox %f0, %l0
	flcmpd %fcc0, %f2, %f6
	fmul8x16 %f2, %f20, %f0
	fmul8x16au %f0, %f20, %f8
	fmul8x16al %f8, %f12, %f30
	fmuld8sux16 %f2, %f20, %f30
	fmuld8ulx16 %f4, %f8, %f0
	fpmerge %f12, %f2, %f2
	fexpand %f8, %f8
	fpack16 %f4, %f4
	fpackfix %f4, %f4
	rd %y, %l1
	rd %ccr, %l2
	rd %asi, %l3
	rd %tick, %l4
	rd %pc, %l5
	rd %fprs, %l6
	rd %asr7, %l7
	rd %asr16, %i0
	rd %pcr, %i1
	rd %pic, %i2
	rd %dcr, %i3
	rd %gsr, %i4
	rd %softint, %i5
	rd %tick_cmpr, %fp
	rd %stick, %i7
	rd %sys_tick, %g1
	rd %stick_cmpr, %g2
	rd %asr31, %g3
	wr %g4, %g5, %y
	wr %g6, -100, %y
	wr %g7, %y
	wr %o0, %o1, %ccr
	wr %o2, 4095, %ccr
	wr %o3, %ccr
	wr %o4, %o5, %asi
	wr %sp, -4096, %asi
	wr %o7, %asi
	wr %l0, %l1, %fprs
	wr %l2, 2047, %fprs
	wr %l3, %fprs
	wr %l4, %l5, %asr18
	wr %l6, -2048, %asr18
	wr %l7, %asr18
	wr %i0, %i1, %gsr
	wr %i2, 291, %gsr
	wr %i3, %gsr
	wr %i4, %i5, %set_softint
	wr %fp, -2047, %set_softint
	wr %i7, %set_softint
	wr %g1, %g2, %clear_softint
	wr %g3, 0, %clear_softint
	wr %g4, %clear_softint
	wr %g5, %g6, %softint
	wr %g7, 1, %softint
	wr %o0, %softint
	wr %o1, %o2, %tick_cmpr
	wr %o3, -1, %tick_cmpr
	wr %o4, %tick_cmpr
	wr %o5, %sp, %stick_cmpr
	wr %o7, 5, %stick_cmpr
	wr %l0, %stick_cmpr
	wr %l1, %l2, %asr30
	wr %l3, 100, %asr30
	wr %l4, %asr30
	rdpr %tpc, %l5
	rdpr %tnpc, %l6
	rdpr %tstate, %l7
	rdpr %tt, %i0
	rdpr %tick, %i1
	rdpr %tba, %i2
	rdpr %pstate, %i3
	rdpr %tl, %i4
	rdpr %pil, %i5
	rdpr %cwp, %fp
	rdpr %cansave, %i7
	rdpr %canrestore, %g1
	rdpr %cleanwin, %g2
	rdpr %otherwin, %g3
	rdpr %wstate, %g4
	rdpr %fq, %g5
	rdpr %gl, %g6
	rdpr %ver, %g7
	wrpr %o0, %o1, %tpc
	wrpr %o2, -100, %tpc
	wrpr %o3, %tpc
	wrpr %o4, %o5, %tnpc
	wrpr %sp, 4095, %tnpc
	wrpr %o7, %tnpc
	wrpr %l0, %l1, %tstate
	wrpr %l2, -4096, %tstate
	wrpr %l3, %tstate
	wrpr %l4, %l5, %tt
	wrpr %l6, 2047, %tt
	wrpr %l7, %tt
	wrpr %i0, %i1, %tick
	wrpr %i2, -2048, %tick
	wrpr %i3, %tick
	wrpr %i4, %i5, %tba
	wrpr %fp, 291, %tba
	wrpr %i7, %tba
	wrpr %g1, %g2, %pstate
	wrpr %g3, -2047, %pstate
	wrpr %g4, %pstate
	wrpr %g5, %g6, %tl
	wrpr %g7, 0, %tl
	wrpr %o0, %tl
	wrpr %o1, %o2, %pil
	wrpr %o3, 1, %pil
	wrpr %o4, %pil
	wrpr %o5, %sp, %cwp
	wrpr %o7, -1, %cwp
	wrpr %l0, %cwp
	wrpr %l1, %l2, %cansave
	wrpr %l3, 5, %cansave
	wrpr %l4, %cansave
	wrpr %l5, %l6, %canrestore
	wrpr %l7, 100, %canrestore
	wrpr %i0, %canrestore
	wrpr %i1, %i2, %cleanwin
	wrpr %i3, -100, %cleanwin
	wrpr %i4, %cleanwin
	wrpr %i5, %fp, %otherwin
	wrpr %i7, 4095, %otherwin
	wrpr %g1, %otherwin
	wrpr %g2, %g3, %wstate
	wrpr %g4, -4096, %wstate
	wrpr %g5, %wstate
	wrpr %g6, %g7, %gl
	wrpr %o0, 2047, %gl
	wrpr %o1, %gl
	membar #LoadLoad
	membar #StoreLoad | #LoadLoad
	membar #Sync
	membar #Lookaside | #MemIssue | #StoreStore
	membar #LoadStore
	membar 15
	membar 127
	stbar
	sir 5
	sir -4096
	flush %o2+%o3
	flush %o4
	flush %o5+-2048
	flush %sp-2132
	flush 291
	iflush %o7+%l0
	iflush %l1
	iflush %l2+-2047
	iflush %l3-3328
	iflush 0
	flush
	flushw
	saved
	restored
	done
	retry
	unimp 0
	unimp 0x3fffff
	cmp %g1, %g2
	cmp %g1, 100
	cmp %g1, %lo(0x123456789abcdef0)
	cmp %g1, %hm(0x123456789abcdef0)
	cmp %g1, %ulo(0x123456789abcdef0)
	cmp %g1, %m44(0x123456789abcdef0)
	cmp %g1, %l44(0x123456789abcdef0)
	cmp %g1, %lox(0x123456789abcdef0)
	tst %g3
	mov %g5, %g4
	mov -100, %g4
	mov %lo(0x123456789abcdef0), %g4
	mov %hm(0x123456789abcdef0), %g4
	mov %ulo(0x123456789abcdef0), %g4
	mov %m44(0x123456789abcdef0), %g4
	mov %l44(0x123456789abcdef0), %g4
	mov %lox(0x123456789abcdef0), %g4
	mov %y, %g6
	mov %asr19, %g7
	mov %ccr, %o0
	mov %fprs, %o1
	mov %o2, %y
	mov %o3, %asr19
	mov %o4, %gsr
	clr %o5
	not %sp, %o7
	not %l0
	neg %l1, %l2
	neg %l3
	signx %l4, %l5
	signx %l6
	inc %l7
	inc 4095, %i0
	inc %lo(0x123456789abcdef0), %i1
	inccc %i2
	inccc -4096, %i3
	inccc %lo(0x123456789abcdef0), %i4
	dec %i5
	dec 2047, %fp
	dec %lo(0x123456789abcdef0), %i7
	deccc %g1
	deccc -2048, %g2
	deccc %lo(0x123456789abcdef0), %g3
	btst %g4, %g5
	btst 291, %g6
	bset %g7, %o0
	bset -2047, %o1
	bclr %o2, %o3
	bclr 0, %o4
	btog %o5, %sp
	btog 1, %o7
	set 0, %l0
	set 1, %l1
	set 4095, %l2
	set 4096, %l3
	set 1024, %l4
	set 305419896, %l5
	set 4294963200, %l6
	set 4294967295, %l7
	set -1, %i0
	set -4096, %i1
	set -4097, %i2
	set 2147483648, %i3
	set -2147483647, %i4
	setx 0, %i5, %fp
	setx 5, %i7, %g1
	setx -1, %g2, %g3
	setx -4096, %g4, %g5
	setx 4095, %g6, %g7
	setx 4096, %o0, %o1
	setx 1024, %o2, %o3
	setx 305419896, %o4, %o5
	setx 4294967295, %sp, %o7
	setx 4294967296, %l0, %l1
	setx 1311768467463790320, %l2, %l3
	setx -305419896, %l4, %l5
	setx -4294967296, %l6, %l7
	setx 9223372036854775807, %i0, %i1
	setx -9223372036854775808, %i2, %i3
	setx 18446744073709547520, %i4, %i5
Ld0:
Lf1:
	nop
; V8
	std %fq, [%g1+%g2]
	std %fq, [%g3]
	std %fq, [%g4+1]
	std %fq, [%g5-834]
	std %fq, [%g6+%lo(0x123456789abcdef0)]
	std %fq, [%g7+%hm(0x123456789abcdef0)]
	std %fq, [%o0+%ulo(0x123456789abcdef0)]
	std %fq, [%o1+%m44(0x123456789abcdef0)]
	std %fq, [%o2+%l44(0x123456789abcdef0)]
	std %fq, [%o3+%lox(0x123456789abcdef0)]
	std %fq, [-1]
	ld [%o4+%o5], %c3
	ld [%sp], %c3
	ld [%o7+5], %c3
	ld [%l0-423], %c3
	ld [%l1+%lo(0x123456789abcdef0)], %c3
	ld [%l2+%hm(0x123456789abcdef0)], %c3
	ld [%l3+%ulo(0x123456789abcdef0)], %c3
	ld [%l4+%m44(0x123456789abcdef0)], %c3
	ld [%l5+%l44(0x123456789abcdef0)], %c3
	ld [%l6+%lox(0x123456789abcdef0)], %c3
	ld [100], %c3
	ldd [%l7+%i0], %c4
	ldd [%i1], %c4
	ldd [%i2+-100], %c4
	ldd [%i3-2340], %c4
	ldd [%i4+%lo(0x123456789abcdef0)], %c4
	ldd [%i5+%hm(0x123456789abcdef0)], %c4
	ldd [%fp+%ulo(0x123456789abcdef0)], %c4
	ldd [%i7+%m44(0x123456789abcdef0)], %c4
	ldd [%g1+%l44(0x123456789abcdef0)], %c4
	ldd [%g2+%lox(0x123456789abcdef0)], %c4
	ldd [4095], %c4
	st %c5, [%g3+%g4]
	st %c5, [%g5]
	st %c5, [%g6+-4096]
	st %c5, [%g7-1220]
	st %c5, [%o0+%lo(0x123456789abcdef0)]
	st %c5, [%o1+%hm(0x123456789abcdef0)]
	st %c5, [%o2+%ulo(0x123456789abcdef0)]
	st %c5, [%o3+%m44(0x123456789abcdef0)]
	st %c5, [%o4+%l44(0x123456789abcdef0)]
	st %c5, [%o5+%lox(0x123456789abcdef0)]
	st %c5, [2047]
	std %c6, [%sp+%o7]
	std %c6, [%l0]
	std %c6, [%l1+-2048]
	std %c6, [%l2-2043]
	std %c6, [%l3+%lo(0x123456789abcdef0)]
	std %c6, [%l4+%hm(0x123456789abcdef0)]
	std %c6, [%l5+%ulo(0x123456789abcdef0)]
	std %c6, [%l6+%m44(0x123456789abcdef0)]
	std %c6, [%l7+%l44(0x123456789abcdef0)]
	std %c6, [%i0+%lox(0x123456789abcdef0)]
	std %c6, [291]
	ld [%i1+%i2], %csr
	ld [%i3], %csr
	ld [%i4+-2047], %csr
	ld [%i5-2177], %csr
	ld [%fp+%lo(0x123456789abcdef0)], %csr
	ld [%i7+%hm(0x123456789abcdef0)], %csr
	ld [%g1+%ulo(0x123456789abcdef0)], %csr
	ld [%g2+%m44(0x123456789abcdef0)], %csr
	ld [%g3+%l44(0x123456789abcdef0)], %csr
	ld [%g4+%lox(0x123456789abcdef0)], %csr
	ld [0], %csr
	st %csr, [%g5+%g6]
	st %csr, [%g7]
	st %csr, [%o0+1]
	st %csr, [%o1-3574]
	st %csr, [%o2+%lo(0x123456789abcdef0)]
	st %csr, [%o3+%hm(0x123456789abcdef0)]
	st %csr, [%o4+%ulo(0x123456789abcdef0)]
	st %csr, [%o5+%m44(0x123456789abcdef0)]
	st %csr, [%sp+%l44(0x123456789abcdef0)]
	st %csr, [%o7+%lox(0x123456789abcdef0)]
	st %csr, [-1]
	std %cq, [%l0+%l1]
	std %cq, [%l2]
	std %cq, [%l3+5]
	std %cq, [%l4-2586]
	std %cq, [%l5+%lo(0x123456789abcdef0)]
	std %cq, [%l6+%hm(0x123456789abcdef0)]
	std %cq, [%l7+%ulo(0x123456789abcdef0)]
	std %cq, [%i0+%m44(0x123456789abcdef0)]
	std %cq, [%i1+%l44(0x123456789abcdef0)]
	std %cq, [%i2+%lox(0x123456789abcdef0)]
	std %cq, [100]
	rd %psr, %l4
	wr %l5, %l6, %psr
	wr %l7, 1, %psr
	rd %wim, %i0
	wr %i1, %i2, %wim
	wr %i3, -1, %wim
	rd %tbr, %i4
	wr %i5, %fp, %tbr
	wr %i7, 5, %tbr
; rows llvm-mc 19 does not have
	add %r3, %r17, %r31
	popc 5, %o3
	popc -1, %g1
	fpsub64 %f6, %f10, %f30
	fpsub64 %f34, %f62, %f40
	fpadd16s %f1, %f3, %f31
	fpadd32s %f1, %f3, %f31
	fpsub16s %f1, %f3, %f31
	fpsub32s %f1, %f3, %f31
	fpadds16 %f2, %f40, %f62
	fpadds32 %f2, %f40, %f62
	fpsubs16 %f2, %f40, %f62
	fpsubs32 %f2, %f40, %f62
	fpadds16s %f1, %f2, %f29
	fpadds32s %f1, %f2, %f29
	fpsubs16s %f1, %f2, %f29
	fpsubs32s %f1, %f2, %f29
	fucmple8 %f2, %f44, %o1
	fucmpne8 %f2, %f44, %o1
	fucmpgt8 %f2, %f44, %o1
	fucmpeq8 %f2, %f44, %o1
	xmulxhi %i7, %g1, %g2
	bshuffle %f32, %f36, %f44
	movstouw %f3, %g1
	movstosw %f31, %o2
	movxtod %g5, %f34
	movwtos %l1, %f7
	flcmps %fcc2, %f1, %f3
	pdistn %f2, %f34, %o5
	fexpand %f3, %f34
	fpack16 %f40, %f5
	fpackfix %f42, %f9
	fpmerge %f1, %f3, %f36
	fmul8x16 %f1, %f38, %f40
	fmul8x16au %f1, %f3, %f40
	fmul8x16al %f5, %f7, %f42
	fmuld8sux16 %f9, %f11, %f44
	fmuld8ulx16 %f13, %f15, %f46
	alignaddress %g1, %g2, %g3
	alignaddress_little %g1, %g2, %g3
	siam 0
	siam 7
	fnadds %f1, %f2, %f31
	fnaddd %f2, %f34, %f62
	fnmuls %f1, %f2, %f31
	fnmuld %f2, %f34, %f62
	fhadds %f1, %f2, %f31
	fhaddd %f2, %f34, %f62
	fhsubs %f1, %f2, %f31
	fhsubd %f2, %f34, %f62
	fnhadds %f1, %f2, %f31
	fnhaddd %f2, %f34, %f62
	fnsmuld %f1, %f3, %f34
	fmadds %f1, %f2, %f3, %f4
	fmaddd %f2, %f34, %f62, %f40
	fmsubs %f1, %f2, %f3, %f4
	fmsubd %f2, %f34, %f62, %f40
	fnmsubs %f1, %f2, %f3, %f4
	fnmsubd %f2, %f34, %f62, %f40
	fnmadds %f1, %f2, %f3, %f4
	fnmaddd %f2, %f34, %f62, %f40
	rdhpr %hpstate, %g1
	rdhpr %htstate, %o2
	rdhpr %hintp, %l3
	rdhpr %htba, %i4
	rdhpr %hver, %g5
	rdhpr %hstick_cmpr, %g6
	rdhpr %hsys_tick_cmpr, %g6
	wrhpr %g1, %g2, %hpstate
	wrhpr %g1, 5, %htba
	wrhpr %o3, %hintp
	allclean
	otherw
	normalw
	invalw
	illtrap 0
	illtrap 0x12345
	pwr %g1, %g2, %psr
	pwr %g1, 7, %psr
	cpop1 5, %c1, %c2, %c3
	cpop2 0x1ff, %c31, %c0, %c17
	ldtw [%g1+8], %o2
	sttw %o4, [%g1+%g2]
	ldtwa [%g1+%g2] 0x80, %o2
	sttwa %o4, [%g1] %asi
	stswa %o4, [%g1+%g2] 0x81
	stsba %o4, [%g1+%g2] 0x81
	stuba %o4, [%g1+%g2] 0x81
	stsha %o4, [%g1+%g2] 0x81
	stuha %o4, [%g1+%g2] 0x81
	clrx [%g1+8]
	clrx [%g1+%g2]
	clruw %g1, %g2
	clruw %o3
	setuw 5, %g1
	setuw 0x12345678, %g1
	setsw 5, %g1
	setsw -5, %g1
	setsw -4096, %g1
	setsw 0x12345400, %g1
	setsw 0x12345678, %g1
	setsw -0x12345400, %g1
	setsw -0x12345678, %o2
	iprefetch Lx
Lx: nop
	byte 0x12
	half 0x1234
	word 0x12345678
	xword 0x123456789abcdef0
	nword -1
	single 1.5
	float -2.0
	double 1.5
