; axx test example hello world.
; for x86_64 FreeBSD
;
; assemble:
; axx.py hello.axx hello.s -o hello.o
; ld hello.o -o hello
; % hello
; hello, world
;
.export _hello,_start,len
section .text
_start:
_hello:
        mov     eax, 4      ; sys_write (04)
        mov     edi, 1      ; stdout    (01)
        mov     edx,len     ; length    (13)
        movabs  rsi,msg     ; address
        syscall
        mov     edi, 0      ; return 0
        mov     eax, 1
        syscall
msg:     .ascii      "hello, world\n"
len:     .equ     $$ - msg
endsection

