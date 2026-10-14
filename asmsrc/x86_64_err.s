; x86_64_err.s -- lines x86_64.axx / x86_64m.axx must refuse
;
; Assemble with:  axx x86_64.axx x86_64_err.s -b out.bin
;             or: axx x86_64m.axx x86_64_err.s -b out.bin
;
; Every line is an error, so no output file is written; test1 compares
; the diagnostics on standard error. An immediate beyond its field
; ("Value out of range": 8-bit -128..255, or -128..127 when sign-extended;
; 16-bit -32768..65535; 32-bit -2**31..2**32-1, or -2**31..2**31-1 when
; sign-extended to 64 bits), and AH / CH / DH / BH where the instruction
; needs a REX prefix ("Register out of range"; it used to become SPL /
; BPL / SIL / DIL without a word). The boundary values that are accepted
; are at the end of x86_64_rex.s.
        add al,256
        add al,-129
        add8 ax,128
        add8 ax,-129
        shl eax,256
        mov ax,65536
        mov ax,-32769
        mov eax,4294967296
        mov eax,-2147483649
        movs rax,2147483648
        ret 65536
        enter 65536,1
        mov ah,r8b
        mov ah,sil
        mov ah,[r8]
        mov [rcx+r9*2],bh
        add ch,[r12+5]b
; 2026-10-14: 以前は黙って回り込ませていたもの（push は符号拡張で別の値になる）
        push    2147483648
        push    4294967295
        mov     rax, 18446744073709551616
        mov     rax, -9223372036854775809
        lea     rax, [rbx+0x100000000]
        lea     rax, [rbx-0x80000001]
        mov     dword [rcx+r8*4+0x100000000], 1
; 2026-10-14: 倍率は 1/2/4/8 だけ（以前は *3 を *2、*16 を *1 などとして黙って組んだ）、
; 基底の無い [disp+index] の変位、movabs の番地、データ定義の範囲
        lea     rax, [rbx+rcx*3]
        lea     rax, [rbx+rcx*16]
        mov     eax, [rbx+rcx*0+8]
        inc     byte [0x100000000+rcx]
        movabs  al, 18446744073709551616
        db      256
        dw      -32769
        dd      4294967296
        dq      -9223372036854775809
