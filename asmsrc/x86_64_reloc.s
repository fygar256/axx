; x86_64_reloc.s -- relocations of x86_64.axx / x86_64m.axx under -o
;
; Assemble with:  axx x86_64.axx x86_64_reloc.s -o out.o
;             or: axx x86_64m.axx x86_64_reloc.s -o out.o
;
; 1. call / jmp / jcc near (32-bit relative) to an external or .global
;    symbol carry R_X86_64_PLT32, as GNU as and llvm-mc give them; to a
;    local label of the same section they are resolved here with no
;    relocation at all, as GNU as and llvm-mc resolve them.
; 2. The short forms (jcc8, jmp8, loop*, jrcxz) carry R_X86_64_PC8 when
;    not resolved in place; in practice they only ever reach a local
;    label (the 8-bit range cannot address an external symbol), so they
;    are always resolved.
; 3. A RIP-relative operand ([RIP+sym], the ALU instructions, lea, the
;    64-bit mov) carries R_X86_64_PC32 against an external symbol or a
;    label of another section, and is resolved in place against a local
;    label of the same section.
; 4. Plain data (db/dw/dd/dq) carries R_X86_64_8/16/32/64 -- an absolute
;    reference, never resolved in place even for a local label, since an
;    absolute address is not known until the linker places the section.
; 5. The absolute-addressed immediate-store forms (mov byte/word/dword/
;    qword [sym],imm, with no base register and no RIP) carry
;    R_X86_64_32S: the ModRM+SIB (base=none) encoding sign-extends the
;    32-bit displacement, so GNU as and llvm-mc give it the signed type.
; 6. A 32-bit immediate against a symbol carries R_X86_64_32 (mov eax,ext,
;    mov dword [rbx],ext, test eax,ext), or R_X86_64_32S where the CPU
;    sign-extends it to 64 bits (REX.W: movs rax,ext, mov qword [rbx],ext,
;    imul rax,rbx,ext; and push ext). A 32-bit displacement against a
;    symbol ([rbx+ext], [rbx+rcx*4+ext], also in the VEX / EVEX forms)
;    carries R_X86_64_32S. These used to come out as R_X86_64_PC32, the
;    default guess for a 4-byte field.
; 7. ADD / OR / ADC / SBB / AND / SUB / XOR / CMP of a register and an
;    immediate pick the short imm8 form for a small number, and the
;    0x81 /r imm16 / imm32 form for a symbol (as GNU as does), since the
;    linker fills it in: R_X86_64_16 / 32 / 32S at the field after the
;    opcode and ModRM. These used to turn the opcode itself into a
;    relocation. A local label is a symbol here too.
; 8. MOV of a 32 / 16 / 8-bit register to or from [RIP+sym] carries
;    R_X86_64_PC32, like the 64-bit form.
;
; The relocation entries (type, addend) match llvm-mc 19 wherever both
; can express the same thing; llvm-mc auto-relaxes the generic "jmp" /
; "jcc" mnemonics to a short encoding when it can, where axx's jmp/jcc
; and jmp8/jcc8 are two separate, always-fixed-length mnemonics (no
; relaxation, as throughout axx), so the exact bytes then differ only in
; instruction length, not in relocation type or addend. Linked with
; ld.lld, the two give the same running program.
;
        .extern ext
        .global gfn
        .section .text
start:
        call    ext
        jmp     ext
        je      ext
        call    gfn
        jmp     gfn
        call    start
        jmp     start
        je      start
        jrcxz   start
        loop    start
        adc     eax,[RIP+ext]
        lea     rax,[RIP+ext]
        mov     rax,[RIP+ext]
        lea     rax,[RIP+start]
        mov     byte [ext],1
        mov     word [ext],1
        mov     dword [ext],1
        mov     qword [ext],1
        mov     eax,ext
        mov     r9d,ext+4
        mov     dword [rbx],ext
        mov     dword [rbx+8]b,ext
        mov     qword [rbx],ext
        movs    rax,ext
        push    ext
        test    eax,ext
        imul    rax,rbx,ext
        mov     eax,[rbx+ext]
        mov     rax,[rbx+rcx*4+ext]
        mov     [rbx+ext],ecx
        lea     rax,[rbx+ext]
        vmovaps xmm1,[rbx+ext]
        vaddps256 ymm1,ymm2,[rbx+rcx*2+ext]
        vmovaps512 zmm1,[rbx+ext]
        mov     ax,ext
        mov     al,ext
        add     eax,ext
        sub     r9d,ext+8
        cmp     rax,ext
        and     r15,ext-4
        or      cx,ext
        xor     ebx,start
        add     ecx,5
        mov     eax,[RIP+ext]
        mov     [RIP+ext],r9d
        mov     ax,[RIP+ext]
        mov     sil,[RIP+ext]
        mov     [RIP+ext],r15b
gfn:
        ret
        .section .data
dat:
        db      ext
        dw      ext
        dd      ext
        dq      ext
        dd      start
