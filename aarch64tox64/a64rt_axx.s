; a64rt_axx.s -- a64tox64_axx.axx で翻訳したプログラムのランタイム（axx 記法）
;
;   caxx x86_64.axx a64rt_axx.s --osabi Linux -o a64rt.o
;
;   * x86 のレジスタに入りきらない AArch64 レジスタの置き場所
;     （x6 x7 x9-x18 x24-x28。各 8 バイト）
;   * __a64_svc: AArch64 Linux のシステムコール番号（rax）を x86_64 の番号に
;     引き直して syscall する。引数は rdi rsi rdx rcx r8 r9（= x0-x5）。
;     戻り値は rdi（= x0）。rax と rcx は保存する。表にない番号は -ENOSYS。
.global __a64_svc,__a64_x6,__a64_x7,__a64_x9,__a64_x10,__a64_x11,__a64_x12,__a64_x13,__a64_x14,__a64_x15,__a64_x16,__a64_x17,__a64_x18,__a64_x24,__a64_x25,__a64_x26,__a64_x27,__a64_x28

.section .text
__a64_svc:
        push    rcx
        push    rax
        lea     r11, [RIP+__a64_svctab]
__a64_svc_find:
        movsx   r10, [r11+1]            ; 上位バイトで符号を見る
        cmp     r10, -1
        je      __a64_svc_nosys
        mov     r10w, [r11]
        movzx   r10d, r10w
        cmp     r10, rax
        je      __a64_svc_call
        add     r11, 4
        jmp     __a64_svc_find
__a64_svc_call:
        mov     r10w, [r11+2]
        movzx   eax, r10w
        mov     r10, rcx
        syscall
        mov     rdi, rax
        jmp     __a64_svc_done
__a64_svc_nosys:
        mov     rdi, -38                ; -ENOSYS
__a64_svc_done:
        pop     rax
        pop     rcx
        ret
.endsection

.section .rodata
; AArch64（asm-generic）の番号, x86_64 の番号（各 2 バイト）。0xffff で終わる
__a64_svctab:
        DW 17
        DW 79                  ; getcwd
        DW 23
        DW 32                  ; dup
        DW 24
        DW 292                  ; dup3
        DW 25
        DW 72                  ; fcntl
        DW 29
        DW 16                  ; ioctl
        DW 34
        DW 258                  ; mkdirat
        DW 35
        DW 263                  ; unlinkat
        DW 37
        DW 265                  ; linkat
        DW 38
        DW 264                  ; renameat
        DW 46
        DW 77                  ; ftruncate
        DW 48
        DW 269                  ; faccessat
        DW 49
        DW 80                  ; chdir
        DW 56
        DW 257                  ; openat
        DW 57
        DW 3                  ; close
        DW 59
        DW 293                  ; pipe2
        DW 61
        DW 217                  ; getdents64
        DW 62
        DW 8                  ; lseek
        DW 63
        DW 0                  ; read
        DW 64
        DW 1                  ; write
        DW 65
        DW 19                  ; readv
        DW 66
        DW 20                  ; writev
        DW 67
        DW 17                  ; pread64
        DW 68
        DW 18                  ; pwrite64
        DW 78
        DW 267                  ; readlinkat
        DW 79
        DW 262                  ; newfstatat
        DW 80
        DW 5                  ; fstat
        DW 93
        DW 60                  ; exit
        DW 94
        DW 231                  ; exit_group
        DW 96
        DW 218                  ; set_tid_address
        DW 98
        DW 202                  ; futex
        DW 101
        DW 35                  ; nanosleep
        DW 113
        DW 228                  ; clock_gettime
        DW 124
        DW 24                  ; sched_yield
        DW 129
        DW 62                  ; kill
        DW 134
        DW 13                  ; rt_sigaction
        DW 135
        DW 14                  ; rt_sigprocmask
        DW 160
        DW 63                  ; uname
        DW 169
        DW 96                  ; gettimeofday
        DW 172
        DW 39                  ; getpid
        DW 173
        DW 110                  ; getppid
        DW 174
        DW 102                  ; getuid
        DW 175
        DW 107                  ; geteuid
        DW 176
        DW 104                  ; getgid
        DW 177
        DW 108                  ; getegid
        DW 178
        DW 186                  ; gettid
        DW 214
        DW 12                  ; brk
        DW 215
        DW 11                  ; munmap
        DW 221
        DW 59                  ; execve
        DW 222
        DW 9                  ; mmap
        DW 226
        DW 10                  ; mprotect
        DW 260
        DW 61                  ; wait4
        DW 278
        DW 318                  ; getrandom
        DW 0xffff
        DW 0xffff
.endsection

.section .bss
.align 8
__a64_x6: .resb 8
__a64_x7: .resb 8
__a64_x9: .resb 8
__a64_x10: .resb 8
__a64_x11: .resb 8
__a64_x12: .resb 8
__a64_x13: .resb 8
__a64_x14: .resb 8
__a64_x15: .resb 8
__a64_x16: .resb 8
__a64_x17: .resb 8
__a64_x18: .resb 8
__a64_x24: .resb 8
__a64_x25: .resb 8
__a64_x26: .resb 8
__a64_x27: .resb 8
__a64_x28: .resb 8
.endsection
