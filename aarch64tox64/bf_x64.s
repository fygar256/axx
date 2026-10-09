; a64ext.s -- a64tox64_axx.axx の出力の先頭に付ける（ランタイムの名前の宣言）
.extern __a64_svc,__a64_x6,__a64_x7,__a64_x9,__a64_x10,__a64_x11,__a64_x12,__a64_x13,__a64_x14,__a64_x15,__a64_x16,__a64_x17,__a64_x18,__a64_x24,__a64_x25,__a64_x26,__a64_x27,__a64_x28
; Brainfuck interpreter
; Android AArch64 / Linux
; axx syntax
;
; build, via a linker:
; axx.py aarch64.axx bf_aarch64.s -m 183 -o bf.o
; ld.lld -static -e _start -o bf bf.o
;
; build, without one:
; axx.py aarch64.axx bf_aarch64.s -b bf.bin
;
; The flat image is .text, .rodata, then .bss at the end; wrap it in an ELF with
; one RWX PT_LOAD at any 4KB-aligned address, p_filesz = image size,
; p_memsz = p_filesz + TAPE_SIZE + PROG_SIZE. The code is position independent
; (every branch is relative, every data reference is an adrp/:lo12: pair).
;
; Usage:
; ./bf program.bf
;
; AArch64 Linux syscall ABI:
; x0-x5 = arguments
; x8 = syscall number
; svc #0
;
; Android uses openat(AT_FDCWD, path, O_RDONLY, 0), not the old x86_64 open syscall.
TAPE_SIZE: .equ 65536
PROG_SIZE: .equ 1048576
SYS_read: .equ 63
SYS_write: .equ 64
SYS_close: .equ 57
SYS_openat: .equ 56
SYS_exit: .equ 93
AT_FDCWD: .equ -100
.global _start
.section .text
_start:
    ; At Linux process entry, SP points at argc/argv.
    mov rbx, [rsp] ; argc
    cmp rbx, 2
    jge _open_file
    ; write(2, usage, usage_len)
    mov rax, SYS_write
    mov rdi, 2
    lea rsi, [RIP+usage]
     ; :lo12:usage (adrp で計算済み)
    mov rdx, usage_len
    call __a64_svc
    jmp _exit_error
_open_file:
    ; argv[1] is at sp + 16.
    mov rsi, [rsp+16]
    ; openat(AT_FDCWD, argv[1], O_RDONLY, 0)
    mov rax, SYS_openat
    mov rdi, AT_FDCWD
    mov rdx, 0 ; O_RDONLY
    mov rcx, 0
    call __a64_svc
    cmp rdi, 0
    jl _exit_error
    mov r12, rdi ; fd
    ; read(fd, prog_buf, PROG_SIZE) until EOF or the buffer is full.
    ; One read() is not enough: on a pipe or a FIFO it can return short.
    lea r11, [RIP+prog_buf]
	mov [RIP+__a64_x25], r11
    ;
	 ; :lo12:prog_buf (adrp で計算済み)
    mov r13, 0 ; bytes read so far
_read_loop:
    mov rdx, PROG_SIZE
    ;
	sub rdx, r13 ; room left
    test rdx, rdx
	jz _read_done
    mov rax, SYS_read
    mov rdi, r12
    mov r11, [RIP+__a64_x25]
	add r11, r13
	mov rsi, r11
    call __a64_svc
    cmp rdi, 0
    jl _exit_error
    je _read_done ; EOF
    ;
	add r13, rdi
    jmp _read_loop
_read_done: ; x21 = program length
    ; close(fd)
    mov rax, SYS_close
    mov rdi, r12
    call __a64_svc
    ; x22 = instruction pointer
    ; x23 = tape index
    mov r14, 0
    mov r15, 0
main_loop:
    cmp r14, r13
    jge _exit_ok
    ; Load prog_buf[x22] into w24 (low byte).
    lea r11, [RIP+prog_buf]
	mov [RIP+__a64_x25], r11
    ;
	 ; :lo12:prog_buf (adrp で計算済み)
    mov r11, [RIP+__a64_x25]
	movzx r10, [r11+r14*1]
	mov [RIP+__a64_x24], r10
    mov r11, [RIP+__a64_x24]
	cmp r11d, '>'
    je op_inc_ptr
    mov r11, [RIP+__a64_x24]
	cmp r11d, '<'
    je op_dec_ptr
    mov r11, [RIP+__a64_x24]
	cmp r11d, '+'
    je op_inc_val
    mov r11, [RIP+__a64_x24]
	cmp r11d, '-'
    je op_dec_val
    mov r11, [RIP+__a64_x24]
	cmp r11d, '.'
    je op_output
    mov r11, [RIP+__a64_x24]
	cmp r11d, ','
    je op_input
    mov r11, [RIP+__a64_x24]
	cmp r11d, '['
    je op_loop_start
    mov r11, [RIP+__a64_x24]
	cmp r11d, ']'
    je op_loop_end
    jmp next
op_inc_ptr:
    ;
	add r15, 1
    ;
	mov r10, TAPE_SIZE-1
	and r15, r10 ; wrap; tape is adjacent to prog_buf
    jmp next
op_dec_ptr:
    ;
	sub r15, 1
    ;
	mov r10, TAPE_SIZE-1
	and r15, r10 ; wrap; below tape is read-only .rodata
    jmp next
op_inc_val:
    lea r11, [RIP+tape]
	mov [RIP+__a64_x25], r11
    ;
	 ; :lo12:tape (adrp で計算済み)
    mov r11, [RIP+__a64_x25]
	add r11, r15
	mov [RIP+__a64_x25], r11
    mov r11, [RIP+__a64_x25]
	movzx r10, [r11]
	mov [RIP+__a64_x24], r10
    mov r11, [RIP+__a64_x24]
	add r11d, 1
	mov [RIP+__a64_x24], r11
    mov r11, [RIP+__a64_x25]
	mov r10, [RIP+__a64_x24]
	mov [r11], r10b
    jmp next
op_dec_val:
    lea r11, [RIP+tape]
	mov [RIP+__a64_x25], r11
    ;
	 ; :lo12:tape (adrp で計算済み)
    mov r11, [RIP+__a64_x25]
	add r11, r15
	mov [RIP+__a64_x25], r11
    mov r11, [RIP+__a64_x25]
	movzx r10, [r11]
	mov [RIP+__a64_x24], r10
    mov r11, [RIP+__a64_x24]
	sub r11d, 1
	mov [RIP+__a64_x24], r11
    mov r11, [RIP+__a64_x25]
	mov r10, [RIP+__a64_x24]
	mov [r11], r10b
    jmp next
op_output:
    ; write(1, &tape[x23], 1)
    lea rsi, [RIP+tape]
     ; :lo12:tape (adrp で計算済み)
    ;
	add rsi, r15
    mov rdi, 1
    mov rdx, 1
    mov rax, SYS_write
    call __a64_svc
    jmp next
op_input:
    ; read(0, &tape[x23], 1)
    lea rsi, [RIP+tape]
     ; :lo12:tape (adrp で計算済み)
    ;
	add rsi, r15
    mov rdi, 0
    mov rdx, 1
    mov rax, SYS_read
    call __a64_svc
    cmp rdi, 0
    jle _exit_ok
    jmp next
op_loop_start:
    ; '[': if current cell != 0, continue.
    lea r11, [RIP+tape]
	mov [RIP+__a64_x25], r11
    ;
	 ; :lo12:tape (adrp で計算済み)
    mov r11, [RIP+__a64_x25]
	add r11, r15
	mov [RIP+__a64_x25], r11
    mov r11, [RIP+__a64_x25]
	movzx r10, [r11]
	mov [RIP+__a64_x24], r10
    mov r11, [RIP+__a64_x24]
	test r11d, r11d
	jnz next
    ; Forward scan for matching ']'.
    mov r11, 1
	mov [RIP+__a64_x26], r11 ; nesting depth
scan_forward:
    ;
	add r14, 1
    cmp r14, r13
    jge _exit_ok
    lea r11, [RIP+prog_buf]
	mov [RIP+__a64_x25], r11
    ;
	 ; :lo12:prog_buf (adrp で計算済み)
    mov r11, [RIP+__a64_x25]
	movzx r10, [r11+r14*1]
	mov [RIP+__a64_x24], r10
    mov r11, [RIP+__a64_x24]
	cmp r11d, '['
    je forward_deeper
    mov r11, [RIP+__a64_x24]
	cmp r11d, ']'
    je forward_shallower
    jmp scan_forward
forward_deeper:
    mov r11, [RIP+__a64_x26]
	add r11, 1
	mov [RIP+__a64_x26], r11
    jmp scan_forward
forward_shallower:
    mov r11, [RIP+__a64_x26]
	sub r11, 1
	mov [RIP+__a64_x26], r11
    mov r11, [RIP+__a64_x26]
	test r11, r11
	jnz scan_forward
    jmp next
op_loop_end:
    ; ']': if current cell == 0, continue.
    lea r11, [RIP+tape]
	mov [RIP+__a64_x25], r11
    ;
	 ; :lo12:tape (adrp で計算済み)
    mov r11, [RIP+__a64_x25]
	add r11, r15
	mov [RIP+__a64_x25], r11
    mov r11, [RIP+__a64_x25]
	movzx r10, [r11]
	mov [RIP+__a64_x24], r10
    mov r11, [RIP+__a64_x24]
	test r11d, r11d
	jz next
    ; Backward scan for matching '['.
    mov r11, 1
	mov [RIP+__a64_x26], r11 ; nesting depth
scan_backward:
    cmp r14, 0
    jle _exit_ok
    ;
	sub r14, 1
    lea r11, [RIP+prog_buf]
	mov [RIP+__a64_x25], r11
    ;
	 ; :lo12:prog_buf (adrp で計算済み)
    mov r11, [RIP+__a64_x25]
	movzx r10, [r11+r14*1]
	mov [RIP+__a64_x24], r10
    mov r11, [RIP+__a64_x24]
	cmp r11d, ']'
    je backward_deeper
    mov r11, [RIP+__a64_x24]
	cmp r11d, '['
    je backward_shallower
    jmp scan_backward
backward_deeper:
    mov r11, [RIP+__a64_x26]
	add r11, 1
	mov [RIP+__a64_x26], r11
    jmp scan_backward
backward_shallower:
    mov r11, [RIP+__a64_x26]
	sub r11, 1
	mov [RIP+__a64_x26], r11
    mov r11, [RIP+__a64_x26]
	test r11, r11
	jnz scan_backward
    jmp next
next:
    ;
	add r14, 1
    jmp main_loop
_exit_error:
    mov rax, SYS_exit
    mov rdi, 1
    call __a64_svc
    jmp $$
_exit_ok:
    mov rax, SYS_exit
    mov rdi, 0
    call __a64_svc
    jmp $$
.section .rodata
usage:
    .ascii "Usage: bf <file>\n"
usage_len: .equ $$ - usage
.section .bss
.align 4
tape:
    .resb TAPE_SIZE
prog_buf:
    .resb PROG_SIZE
