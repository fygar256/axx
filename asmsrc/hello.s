; axx test example hello world.
; for x86_64 FreeBSD
;
; assemble:
; axx.py hello.axx hello.s -o hello.o
; ld hello.o -o hello
; % hello
; hello, world
;
.export _hello,_hello2,len
.section .text
_hello:
_hello2:
        mov     eax, 4      ; sys_write (04)
        mov     edi, 1      ; stdout    (01)
        mov     edx,len     ; length    (13)
        mov     rsi,msg     ; address
        syscall
        ret
msg:     .ascii      "hello, world\n"
len:     .equ     $$ - msg
.endsection

