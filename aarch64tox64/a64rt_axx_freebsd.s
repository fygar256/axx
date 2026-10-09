; a64rt_axx_freebsd.s -- a64tox64_axx.axx で翻訳したプログラムの
;                        FreeBSD/amd64 用ランタイム（axx 記法）
;
;   caxx x86_64.axx a64rt_axx_freebsd.s --osabi FreeBSD -o a64rt.o
;   ld -static -e __a64_start prog.o a64rt.o -o prog
;
;   * __a64_start: プロセスの入口。FreeBSD/amd64 のカーネルは argc の場所を
;     rdi で渡し、rsp はそこから 16 バイト境界合わせのために 8 バイトずらす
;     （exec_setregs の tf_rsp = ((stack - 8) & ~0xF) + 8）。翻訳元の
;     AArch64/Linux コードは入口で [sp] を argc として読むので、rsp を rdi に
;     合わせてから _start へ飛ぶ。Linux は rsp が argc を指すのでこれは要らず、
;     a64rt_axx.s には無い。
;   * x86 のレジスタに入りきらない AArch64 レジスタの置き場所
;     （x6 x7 x9-x18 x24-x28。各 8 バイト）
;   * __a64_svc: AArch64 Linux のシステムコール番号（rax）を FreeBSD/amd64 の
;     番号に引き直して syscall する。引数は rdi rsi rdx rcx r8 r9（= x0-x5）。
;     FreeBSD の syscall は第 4 引数を r10 で渡すので rcx を r10 に移す。
;
;   エラーの約束の違い:
;     Linux は負の戻り値（-errno）でエラーを知らせる。FreeBSD はキャリー
;     フラグ（CF）を立て、rax に errno を返す。翻訳元の AArch64/Linux コードは
;     「x0 < 0 ならエラー」で判定するので、__a64_svc は FreeBSD の CF 方式を
;     Linux の負値方式に直してから返す（CF が立っていたら rax を負にする）。
;     戻り値は rdi（= x0）。rax と rcx は呼び出し側で保存される前提ではないので
;     退避する。表にない番号は -ENOSYS。
.extern _start
.global __a64_start,__a64_svc,__a64_x6,__a64_x7,__a64_x9,__a64_x10,__a64_x11,__a64_x12,__a64_x13,__a64_x14,__a64_x15,__a64_x16,__a64_x17,__a64_x18,__a64_x24,__a64_x25,__a64_x26,__a64_x27,__a64_x28

.section .text
__a64_start:
        mov     rsp, rdi                ; rsp を argc に合わせる
        jmp     _start
__a64_svc:
        push    rcx
        push    rax
        lea     r11, [RIP+__a64_svctab]
__a64_svc_find:
        movsx   r10, [r11+1]            ; 上位バイトで終端 0xffff を見る
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
        mov     r10, rcx                ; FreeBSD の第 4 引数は r10
        syscall
        jnc     __a64_svc_ok            ; CF=0 なら成功、rax が戻り値
        neg     rax                     ; CF=1 なら rax=errno を -errno に
__a64_svc_ok:
        mov     rdi, rax
        jmp     __a64_svc_done
__a64_svc_nosys:
        mov     rdi, -78                ; -ENOSYS (FreeBSD の ENOSYS は 78)
__a64_svc_done:
        pop     rax
        pop     rcx
        ret
.endsection

.section .rodata
; AArch64（asm-generic）の番号, FreeBSD/amd64 の番号（各 2 バイト）。0xffff で終わる
__a64_svctab:
        DW 17
        DW 326              ; getcwd      __getcwd
        DW 23
        DW 41               ; dup
        DW 24
        DW 90               ; dup2        (AArch64 dup3; flags ignored)
        DW 25
        DW 92               ; fcntl
        DW 29
        DW 54               ; ioctl
        DW 34
        DW 496              ; mkdirat
        DW 35
        DW 503              ; unlinkat
        DW 37
        DW 495              ; linkat
        DW 38
        DW 501              ; renameat
        DW 46
        DW 480              ; ftruncate   (FreeBSD: off_t in rsi)
        DW 48
        DW 490              ; faccessat
        DW 49
        DW 12               ; chdir
        DW 56
        DW 499              ; openat
        DW 57
        DW 6                ; close
        DW 59
        DW 542              ; pipe2
        DW 61
        DW 272              ; getdirentries (getdents64; layout differs)
        DW 62
        DW 478              ; lseek
        DW 63
        DW 3                ; read
        DW 64
        DW 4                ; write
        DW 65
        DW 120              ; readv
        DW 66
        DW 121              ; writev
        DW 67
        DW 475              ; pread
        DW 68
        DW 476              ; pwrite
        DW 78
        DW 513              ; readlinkat
        DW 79
        DW 552              ; fstatat
        DW 80
        DW 551              ; fstat
        DW 93
        DW 1                ; exit
        DW 94
        DW 431              ; exit_group  (FreeBSD thr_exit; approx)
        DW 98
        DW 487              ; _umtx_op    (futex; different ABI)
        DW 101
        DW 240              ; nanosleep
        DW 113
        DW 232              ; clock_gettime
        DW 124
        DW 331              ; sched_yield
        DW 129
        DW 37               ; kill
        DW 134
        DW 416              ; sigaction   (rt_sigaction; different ABI)
        DW 135
        DW 340              ; sigprocmask (rt_sigprocmask; different ABI)
        DW 160
        DW 164              ; uname
        DW 169
        DW 116              ; gettimeofday
        DW 172
        DW 20               ; getpid
        DW 173
        DW 39               ; getppid
        DW 174
        DW 24               ; getuid
        DW 175
        DW 25               ; geteuid
        DW 176
        DW 47               ; getgid
        DW 177
        DW 43               ; getegid
        DW 178
        DW 432              ; thr_self    (gettid; returns via arg)
        DW 214
        DW 17               ; brk
        DW 215
        DW 73               ; munmap
        DW 221
        DW 59               ; execve
        DW 222
        DW 477              ; mmap
        DW 226
        DW 74               ; mprotect
        DW 260
        DW 7                ; wait4
        DW 278
        DW 563              ; getrandom
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
