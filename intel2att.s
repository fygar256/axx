# ===================================================================
# intel2att.s -- intel2att.axx の試験ソース（x86-64 Intel 記法）
#
# caxx intel2att.axx intel2att.s -V > att.s
# paxx intel2att.axx intel2att.s -V > att.s
#
# 翻訳結果はそのまま GNU as に通る AT&T 記法になる:
# caxx intel2att.axx intel2att.s -V | as --64 -o att.o -
#
# `#` で始まる行、ラベル、`.` で始まる擬似命令は
# .textmode の素通しでそのまま出る。
# ===================================================================

        .text
        .globl  main

# -------------------------------------------------------------------
# オペランドを取らない命令。綴りが変わるものを含む
# (cqo->cqto, cdq->cltd, cdqe->cltq, cwde->cwtl, stosd->stosl ...)
# -------------------------------------------------------------------
main:
        nop
        cqo
        cdq
        cdqe
        cwde
        cbw
        cwd
        clc
        stc
        cmc
        cld
        std
        pushfq
        popfq
        movsb
        stosq
        lodsd
        cmpsw
        scasd
        rep movsb
        repne scasb

# -------------------------------------------------------------------
# 2 オペランド: レジスタ同士（64 / 32 / 16 / 8 ビット）
# -------------------------------------------------------------------
        mov     rax, rbx
        add     r14, r15
        sub     eax, ecx
        adc     r8d, r9d
        sbb     ax, cx
        and     r10w, r11w
        or      al, bl
        xor     r12b, r13b
        cmp     spl, dil
        test    ah, bh
        xchg    rdx, rsi
        xadd    ecx, edx
        cmpxchg rsi, rdi
        bt      rax, rcx
        bts     eax, ecx
        btr     ax, cx
        btc     rbx, rdx
        bsf     rax, rbx
        bsr     eax, ebx
        popcnt  rax, rbx
        lzcnt   eax, ebx
        tzcnt   ax, bx

# -------------------------------------------------------------------
# 2 オペランド: 即値と OFFSET
# -------------------------------------------------------------------
        mov     rax, 1
        mov     eax, 0x1234
        mov     ax, 40
        mov     al, 0x7f
        add     rsp, 8*4
        sub     rsp, size_of_frame
        and     r12, 0xff
        mov     rsi, offset msg
        mov     rdi, msg

# -------------------------------------------------------------------
# メモリ参照: intel2att.axx が持つ 28 通りの形をすべて通す
# -------------------------------------------------------------------
        mov     rax, [rbx]
        mov     rax, [rbx+8]
        mov     rax, [rbx-8]
        mov     rax, [rbx+rcx*1]
        mov     rax, [rbx+rcx*2]
        mov     rax, [rbx+rcx*4]
        mov     rax, [rbx+rcx*8]
        mov     rax, [rbx+rcx*1+16]
        mov     rax, [rbx+rcx*2+16]
        mov     rax, [rbx+rcx*4+16]
        mov     rax, [rbx+rcx*8+16]
        mov     rax, [rbx+rcx*1-16]
        mov     rax, [rbx+rcx*2-16]
        mov     rax, [rbx+rcx*4-16]
        mov     rax, [rbx+rcx*8-16]
        mov     rax, [rcx*1+table]
        mov     rax, [rcx*2+table]
        mov     rax, [rcx*4+table]
        mov     rax, [rcx*8+table]
        mov     rax, [rcx*1]
        mov     rax, [rcx*2]
        mov     rax, [rcx*4]
        mov     rax, [rcx*8]
        mov     rax, [rbx+rcx]
        mov     rax, [rbx+rcx+16]
        mov     rax, [rbx+rcx-16]
        mov     rax, [rip+msg]
        mov     rax, [msg]

# -------------------------------------------------------------------
# メモリへの書き込みと、サイズ指定の 3 通りの書き方
# -------------------------------------------------------------------
        mov     [rbx], rcx
        mov     [rbx+rcx*8+32], rdx
        mov     qword ptr [rbp-24], rax
        mov     rax, qword ptr [rbp-24]
        mov     rax, qword [rbp-24]
        mov     dword ptr [rbx], eax
        mov     eax, dword [rbx]
        mov     word ptr [rbx], ax
        mov     byte ptr [rbx], al
        mov     qword ptr [rdi], 5
        mov     dword ptr [rbp-8], 10
        mov     word ptr [rdi], 7
        mov     byte ptr [rdi+rcx], 0x41
        cmp     dword ptr [rbp-8], 10
        or      qword ptr [rdi], 5

# -------------------------------------------------------------------
# 1 オペランド
# -------------------------------------------------------------------
        inc     rax
        dec     ecx
        neg     ax
        not     al
        mul     rcx
        div     ebx
        idiv    qword ptr [rbp-8]
        imul    dword ptr [rbx]
        inc     qword ptr [rbx+8]
        dec     byte ptr [rsi]

# -------------------------------------------------------------------
# シフトとローテート
# -------------------------------------------------------------------
        shl     rax, 4
        shr     ebx, cl
        sal     ax, 1
        sar     rdx
        rol     al, 3
        ror     qword ptr [rdi], 1
        rcl     dword ptr [rbx], cl
        rcr     byte ptr [rsi]

# -------------------------------------------------------------------
# LEA と IMUL の 2・3 オペランド形
# -------------------------------------------------------------------
        lea     rax, [rbx+rcx*2+table]
        lea     rsi, [rip+msg]
        lea     ecx, [rbx+4]
        lea     ax, [rbx]
        imul    rax, rbx
        imul    ecx, edx
        imul    rcx, rdx, 3
        imul    eax, dword ptr [rbx+4], 10
        imul    rax, qword ptr [rbx]

# -------------------------------------------------------------------
# ゼロ拡張・符号拡張
# -------------------------------------------------------------------
        movzx   ax, bl
        movzx   eax, bl
        movzx   rax, bl
        movzx   eax, bx
        movzx   rax, bx
        movzx   eax, byte ptr [rsi]
        movzx   rax, word ptr [rsi]
        movsx   ax, bl
        movsx   eax, bl
        movsx   rax, bl
        movsx   eax, bx
        movsx   rax, word ptr [rbx+2]
        movsxd  rax, ecx
        movsxd  rdx, dword ptr [rsi+8]

# -------------------------------------------------------------------
# CMOVcc と SETcc
# -------------------------------------------------------------------
        cmove   rax, rbx
        cmovne  ecx, edx
        cmovl   ax, bx
        cmovge  rax, qword ptr [rdi]
        sete    al
        setne   bl
        setg    byte ptr [rbx]
        setbe   r12b

# -------------------------------------------------------------------
# スタックと分岐
# -------------------------------------------------------------------
        push    rbp
        push    r12
        push    ax
        push    10
        push    offset msg
        push    qword ptr [rbx+8]
        pop     qword ptr [rbx+8]
        pop     ax
        pop     r12
        pop     rbp
        call    func
        call    rax
        call    qword ptr [rbx+16]
        jmp     done
        jmp     rdx
        jmp     qword ptr [rax*8+table]
        je      done
        jne     done
        jb      done
        jae     done
        jl      done
        jge     done
        jbe     done
        ja      done
        js      done
        jns     done
        jp      done
        jnp     done
        jo      done
        jno     done
loop1:
        loop    loop1
        loope   loop1
        jrcxz   loop1
        jecxz   loop1

# -------------------------------------------------------------------
# 即値を取る RET / INT
# -------------------------------------------------------------------
func:
        push    rbp
        mov     rbp, rsp
        leave
        ret
        ret     8
        int     0x80
        syscall
done:
        ret

# -------------------------------------------------------------------
# データ定義。式とラベルは書いたままの綴りで残る
# -------------------------------------------------------------------
table:
        dq      main
        dq      main, func, done
        dd      1, 2, 3, 4
        dw      0xffff, 0
        db      1, 2, 3, 4, 5, 6, 7, 8
msg:
        db      0x68, 0x69, 10
size_of_frame:
        dq      8*4+16
