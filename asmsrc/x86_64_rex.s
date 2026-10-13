; x86_64_rex.s -- REX prefixes of x86_64.axx / x86_64m.axx for R8-R15
;
; Assemble with:  axx x86_64.axx x86_64_rex.s -b out.bin
;             or: axx x86_64m.axx x86_64_rex.s -b out.bin
;
; Every line below was compared against llvm-mc 19 by disassembling the
; bytes axx writes (llvm-mc --disassemble -triple=x86_64). These forms
; used to lose a REX bit, or set the wrong one, so a register numbered 8
; or above silently became its low counterpart (R10D -> EDX, R15 -> RDI):
;
; 1. [disp+index] with the displacement written first (SIB, no base):
;    the register operand needs REX.R and the index REX.X.
; 2. MOV to and from CR0-CR4 and DR0-DR7: the general register sits in
;    the r/m field and needs REX.B.
; 3. VMREAD r/m64,r64 and VMWRITE r64,r/m64.
; 4. PEXTRB / PEXTRD / PEXTRQ: the XMM register is in the reg field and
;    the general register in r/m (the bits were the wrong way round);
;    the same for MOVDG / MOVQG (MOVD / MOVQ from XMM to a general
;    register).
;
; LOOP / LOOPE / LOOPZ / LOOPNE / LOOPNZ / JRCXZ now report "Value out of
; range" when the target is beyond the 8-bit displacement, as JMP8 and
; Jcc8 do; they used to keep only the low byte of the distance.
;
; The immediates are range checked: an 8-bit one takes -128..255 (-128..127
; when it is sign-extended, as in ADD8 / IMUL8 / PUSH8), a 16-bit one
; -32768..65535, a 32-bit one -2**31..2**32-1 (-2**31..2**31-1 when it is
; sign-extended to 64 bits). AH / CH / DH / BH cannot be used where the
; instruction has a REX prefix; that is "Register out of range" now, where
; it used to become SPL / BPL / SIL / DIL. The lines at the end are the
; boundary values that still assemble; x86_64_err.s holds the ones that
; must be refused.
;
; The three-operand IMUL with an immediate has its 32-bit and 16-bit forms
; (it had only the 64-bit one), and MOV to and from [RIP+label] its 32 /
; 16 / 8-bit ones; both are at the very end.
        mov     r11b,[5+r11]
        mov     dil,[-1+r13]
        mov     [-128+r14],r14b
        mov     [5+r8],bpl
        mov     al,[5+rcx]
        mov     [5+rcx],ah
        mov     r10d,[4660+rax]
        mov     [5+r13],r13d
        mov     eax,[4+rbx]
        mov     qword r11,[4660+r10]
        mov     qword rax,[8+rcx]
        lea     r9,[16+r12]
        lea     rax,[16+rcx]
        mov     cr0,r11
        mov     r14,cr0
        mov     cr3,r15
        mov     cr4,rax
        mov     dr7,r14
        mov     r8,dr1
        mov     rdx,dr6
        vmread  rbx,r15
        vmread  r9,rax
        vmwrite r15,rbx
        vmwrite rax,r9
        pextrb  r9,xmm2,1
        pextrd  r13,xmm3,2
        pextrd  rax,xmm12,3
        pextrq  rax,xmm8,1
        pextrq  r8,xmm0,1
        movdg   rax,xmm8
        movdg   r9,xmm1
        movqg   rsi,xmm11
        movqg   r14,xmm3
back:
        loop    back
        loopne  back
        jrcxz   fwd
fwd:
        nop
        add al,255
        add al,-128
        add8 ax,127
        add8 ax,-128
        shl eax,255
        mov ax,65535
        mov ax,-32768
        mov eax,4294967295
        mov eax,-2147483648
        movs rax,2147483647
        movs rax,-2147483648
        ret 65535
        enter 65535,255
        mov ah,bl
        mov ah,[rbx]
        add ah,5
        mov [rcx+rdx*2],bh
        imul    eax,ebx,100000
        imul    r9d,r10d,-5000
        imul8   ecx,r12d,-3
        imul    eax,[rbx],7000
        imul    r11d,[r13+16]b,300
        imul    edx,[rsp+r9*4],70000
        imul8   esi,[rbp+rcx*8+1000],5
        imul    ax,bx,1000
        imul    r8w,r15w,-30000
        imul8   cx,dx,100
        imul    si,[r14+rax*2-8]b,4000
        imul8   r12w,[rdi],-128
here:
        mov     eax,[rip+here]
        mov     [rip+here],r9d
        mov     ax,[rip+here]
        mov     [rip+here],r12w
        mov     cl,[rip+here]
        mov     sil,[rip+here]
        mov     [rip+here],r15b
        mov     [rip+here],ah
