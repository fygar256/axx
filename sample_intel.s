start:
        mov rax, rbx
        mov eax, 4
        mov edi, 1
        mov rsi, offset msg
        mov r8d, r15d
        mov al, bh
        mov cx, 0x1234
        add rsp, 16
        sub rsp, 8*4
        xor eax, eax
        and r12, 0xff
        or  qword ptr [rdi], 5
        cmp dword ptr [rbp-8], 10
        test al, al
        mov rax, [rbp+16]
        mov rax, qword ptr [rbp-24]
        mov [rbx], rcx
        mov [rbx+rcx*8+32], rdx
        mov rdx, [rbx+rcx*4-4]
        mov eax, [rsi+rdi]
        mov eax, [rsi+rdi+8]
        mov rax, [rcx*8+table]
        mov rax, [rip+msg]
        mov rax, [msg]
        mov byte ptr [rdi+rcx], 0x41
        mov word ptr [rdi], 7
        lea rax, [rbx+rcx*2+start]
        lea rsi, [rip+msg]
        inc rax
        dec dword ptr [rbx]
        neg r9
        not byte ptr [rsi+1]
        mul rcx
        idiv qword ptr [rbp-8]
        imul rax, rbx
        imul eax, [rbx+4], 10
        imul rcx, rdx, 3
        shl rax, 4
        shr ebx, cl
        sar rdx
        rol qword ptr [rdi], 1
        movzx eax, byte ptr [rsi]
        movzx eax, bl
        movsx rax, word ptr [rbx+2]
        movsx rcx, dl
        movsxd rax, ecx
        movsxd rdx, dword ptr [rsi+8]
        cmove rax, rbx
        cmovne ecx, dword ptr [rdi]
        sete al
        setg byte ptr [rbx]
        push rbp
        push 10
        push qword ptr [rbx+8]
        pop rbp
        call func
        call rax
        call qword ptr [rbx+16]
        jmp start
        jmp qword ptr [rax*8+table]
        jne start
        jz  func
        jge start
lp1:
        loop lp1
        cqo
        cdq
        cdqe
        rep movsb
        rep stosq
        int 0x80
        syscall
func:
        push rbp
        mov rbp, rsp
        leave
        ret
        ret 8
table:
        dq start, func
        dd 1, 2, 3
        dw 0xffff
        db 1, 2, 3, 4, 5
msg:
        db 0x68, 0x69, 10
