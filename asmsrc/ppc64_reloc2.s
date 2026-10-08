; ppc64_reloc2.s -- relocations that ppc64_reloc_test.s does not reach.
; Assemble with -o (ppc64.axx or ppc64le.axx).
;
; 1. DS-form fields (ld, std, lwa, stq, lxsd, lfdp ...) with an addend whose
;    bits 2-3 are set: the field goes out as 0 and only the opcode bits (XO)
;    stay, as GNU as writes it. The DQ forms (lq, lxv, stxv, lxvp, stxvp)
;    keep their low 4 bits (opcode bits, TX).
; 2. Data written as label-$$: R_PPC64_REL64 / REL32 / REL16 with the
;    constant part as the addend (GNU as: .quad / .long / .short ext-.).
;    A label of the same section gives a constant and no relocation.
 .extern ext
 .section .text
code0:
 ld 3,ext+12(1)
 ld 3,ext+4@l(1)
 ldu 3,ext+8(1)
 lwa 3,ext+12(1)
 std 7,ext+12(1)
 stdu 7,ext+4@l(1)
 stq 8,ext+12(1)
 lxsd 1,ext+12(1)
 lxssp 1,ext+8@l(1)
 stxsd 5,ext+4(1)
 stxssp 5,ext+12@l(1)
 lfdp 2,ext+12(1)
 stfdp 4,ext+8@l(1)
 lq 6,ext+32(1)
 lxv 35,ext+48(1)
 stxv 37,ext+16@l(1)
 lxvp 40,ext+64(1)
 stxvp 34,ext+80@l(1)
 ld 4,dat0+12@l(3)
 blr
 .section .data
dat0:
 .quad ext-$$
 .quad ext-$$+8
 .long ext-$$
 .long ext+12-$$
 .short ext-$$
 .short ext-$$-2
 .long code0-$$
 .quad code0+4-$$
 .long dat0-$$
 .quad ext
 .long ext+4
