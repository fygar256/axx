; sparc_reloc.s -- the relocations of sparc.axx (-o, ELF64 SPARCV9):
; every operand type that can hold a symbol, against an external one.
; The relocation entries (offset, type, symbol, addend) and the bytes
; are those of llvm-mc 19 for the same source, except the two calls /
; branches to the local label loc at the end, which axx makes
; relocations against loc where llvm-mc resolves them itself.
;
;   axx sparc.axx sparc_reloc.s -o out.o

	.extern ext
	call ext
	call ext+16
	ba ext
	ba,a ext+8
	bne %xcc, ext
	fbe ext
	fbe,a,pn %fcc1, ext
	brz %g1, ext
	brgez,a,pn %o2, ext+4
	cba ext
	sethi %hi(ext), %g1
	sethi %hh(ext+0x100), %g1
	sethi %uhi(ext), %g1
	sethi %lm(ext), %g1
	sethi %h44(ext), %g1
	sethi %pc22(ext), %g1
	sethi %got22(ext), %g1
	sethi %tgd_hi22(ext), %g1
	sethi %tldm_hi22(ext), %g1
	sethi %tldo_hix22(ext), %g1
	sethi %tie_hi22(ext), %g1
	sethi %tle_hix22(ext), %g1
	sethi %gdop_hix22(ext), %g1
	add %g1, ext, %g2
	or %g1, %lo(ext+12), %g1
	or %g1, %hm(ext), %g1
	or %g1, %ulo(ext), %g1
	or %g1, %m44(ext), %g1
	or %g1, %l44(ext), %g1
	xor %g1, %lox(ext), %g1
	or %g1, %pc10(ext), %g1
	ld [%l7+%got10(ext)], %g1
	ld [%l7+%got13(ext)], %g1
	add %g1, %tgd_lo10(ext), %g1
	add %g1, %tldm_lo10(ext), %g1
	xor %g1, %tldo_lox10(ext), %g1
	add %g1, %tie_lo10(ext), %g1
	xor %g1, %tle_lox10(ext), %g1
	xor %g1, %gdop_lox10(ext), %g1
	ld [%g1+%lo(ext)], %g2
	ld [%g1+ext], %g2
	stx %g2, [%g1+%lo(ext+4)]
	jmpl %g1+%lo(ext), %g0
	ldd [%g1+%lo(ext)], %f32
	call loc
	nop
loc:
	ba loc
	nop
	.section .data
	WORD ext
	WORD ext+4
	WORD 0
	XWORD ext+8
	HALF 0
	BYTE 0
	BYTE 0
	WORD 0
