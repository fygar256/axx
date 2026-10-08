; Brainfuck interpreter
; RISC-V 64 / FreeBSD (qemu-riscv64 bsd-user, or FreeBSD/riscv64)
; axx syntax; the FreeBSD version of bf_riscv64.s (which is for Linux)
;
; build:
;   axx --osabi freebsd riscv64full.axx bf_riscv64_freebsd.s -o bf.o
;   ld.lld -m elf64lriscv -static -e _start -o bf bf.o
; ld.lld writes OS/ABI "System V" for RISC-V (even ld.lld 19 on FreeBSD/amd64),
; so brand it by hand (the FreeBSD kernel needs the brand; qemu does not):
;   brandelf -t FreeBSD bf          or      elfedit --output-osabi FreeBSD bf
; bf_riscv64.sh does all of this.
;
; run:
;   qemu-riscv64-static ./bf program.bf
;
; What differs from the Linux file:
;   - the syscall number goes in t0 (not a7), the arguments in a0-a5;
;   - the numbers are FreeBSD's: exit 1, read 3, write 4, close 6, openat 499;
;   - a failed syscall sets t0 = 1 and returns the errno in a0 (a0 is not
;     negative), so the error test is `bnez t0`, right after the ecall;
;   - at process entry a0 points at argc, argv[0], argv[1] ... (sp is the
;     same place, after alignment); the code reads them through a0.
; Run with mandelbrot.bf under qemu-riscv64 11.0.2 (bsd-user) on
; FreeBSD/amd64; qemu-riscv64-static 3.1.0 runs it too.
;
; The addresses of the data are formed with auipc + %pcrel_hi / %pcrel_lo
; pairs (the macro `la` below), so the object carries R_RISCV_PCREL_HI20 /
; R_RISCV_PCREL_LO12_I relocations and the code is position independent.
; A flat image (-b) is not supported: %pcrel_lo needs the linker.
;
; registers:
;   s0 argument block  s1 argc            s2 fd
;   s3 program length  s4 instruction ptr s5 tape index
;   s6 current char    s7 scratch address s8 nesting depth

TAPE_SIZE:  .equ 65536
PROG_SIZE:  .equ 1048576

SYS_exit:   .equ 1
SYS_read:   .equ 3
SYS_write:  .equ 4
SYS_close:  .equ 6
SYS_openat: .equ 499
AT_FDCWD:   .equ -100

; la reg,sym : reg = address of sym, pc-relative, with relocations
!def la(r, sym) {
L!{__id__}:
    auipc !{r},%pcrel_hi(!{sym})
    addi  !{r},!{r},%pcrel_lo(L!{__id__})
}

.global _start
.section .text

_start:
    ; At process entry a0 points at argc, then argv[0], argv[1] ...
    mv   s0,a0
    ld   s1,0(s0)                 ; argc
    li   t0,2
    bge  s1,t0,_open_file

    ; write(2, usage, usage_len)
    li   t0,SYS_write
    li   a0,2
    !la("a1", "usage")
    li   a2,usage_len
    ecall
    j    _exit_error

_open_file:
    ; argv[1] is at s0 + 16.
    ld   a1,16(s0)

    ; openat(AT_FDCWD, argv[1], O_RDONLY, 0)
    li   t0,SYS_openat
    li   a0,AT_FDCWD
    li   a2,0                     ; O_RDONLY
    li   a3,0
    ecall
    bnez t0,_exit_error
    mv   s2,a0                    ; fd

    ; read(fd, prog_buf, PROG_SIZE) until EOF or the buffer is full.
    ; One read() is not enough: on a pipe or a FIFO it can return short.
    li   s3,0                     ; bytes read so far
_read_loop:
    li   a2,PROG_SIZE
    sub  a2,a2,s3                 ; room left
    beqz a2,_read_done
    li   t0,SYS_read
    mv   a0,s2
    !la("a1", "prog_buf")
    add  a1,a1,s3
    ecall
    bnez t0,_exit_error
    beqz a0,_read_done            ; EOF
    add  s3,s3,a0
    j    _read_loop
_read_done:                       ; s3 = program length

    ; close(fd)
    li   t0,SYS_close
    mv   a0,s2
    ecall

    ; s4 = instruction pointer
    ; s5 = tape index
    li   s4,0
    li   s5,0

main_loop:
    bge  s4,s3,_exit_ok

    ; Load prog_buf[s4] into s6 (low byte).
    !la("s7", "prog_buf")
    add  s7,s7,s4
    lbu  s6,0(s7)

    li   t0,'>'
    beq  s6,t0,op_inc_ptr
    li   t0,'<'
    beq  s6,t0,op_dec_ptr
    li   t0,'+'
    beq  s6,t0,op_inc_val
    li   t0,'-'
    beq  s6,t0,op_dec_val
    li   t0,'.'
    beq  s6,t0,op_output
    li   t0,','
    beq  s6,t0,op_input
    li   t0,'['
    beq  s6,t0,op_loop_start
    li   t0,']'
    beq  s6,t0,op_loop_end
    j    next

op_inc_ptr:
    addi s5,s5,1
    li   t0,TAPE_SIZE-1
    and  s5,s5,t0                 ; wrap; tape is adjacent to prog_buf
    j    next

op_dec_ptr:
    addi s5,s5,-1
    li   t0,TAPE_SIZE-1
    and  s5,s5,t0                 ; wrap; below tape is read-only .rodata
    j    next

op_inc_val:
    !la("s7", "tape")
    add  s7,s7,s5
    lbu  s6,0(s7)
    addi s6,s6,1
    sb   s6,0(s7)
    j    next

op_dec_val:
    !la("s7", "tape")
    add  s7,s7,s5
    lbu  s6,0(s7)
    addi s6,s6,-1
    sb   s6,0(s7)
    j    next

op_output:
    ; write(1, &tape[s5], 1)
    !la("a1", "tape")
    add  a1,a1,s5
    li   a0,1
    li   a2,1
    li   t0,SYS_write
    ecall
    j    next

op_input:
    ; read(0, &tape[s5], 1)
    !la("a1", "tape")
    add  a1,a1,s5
    li   a0,0
    li   a2,1
    li   t0,SYS_read
    ecall
    bnez t0,_exit_ok
    beqz a0,_exit_ok
    j    next

op_loop_start:
    ; '[': if current cell != 0, continue.
    !la("s7", "tape")
    add  s7,s7,s5
    lbu  s6,0(s7)
    bnez s6,next

    ; Forward scan for matching ']'.
    li   s8,1                     ; nesting depth
scan_forward:
    addi s4,s4,1
    bge  s4,s3,_exit_ok

    !la("s7", "prog_buf")
    add  s7,s7,s4
    lbu  s6,0(s7)

    li   t0,'['
    beq  s6,t0,forward_deeper
    li   t0,']'
    beq  s6,t0,forward_shallower
    j    scan_forward

forward_deeper:
    addi s8,s8,1
    j    scan_forward

forward_shallower:
    addi s8,s8,-1
    bnez s8,scan_forward
    j    next

op_loop_end:
    ; ']': if current cell == 0, continue.
    !la("s7", "tape")
    add  s7,s7,s5
    lbu  s6,0(s7)
    beqz s6,next

    ; Backward scan for matching '['.
    li   s8,1                     ; nesting depth
scan_backward:
    blez s4,_exit_ok
    addi s4,s4,-1

    !la("s7", "prog_buf")
    add  s7,s7,s4
    lbu  s6,0(s7)

    li   t0,']'
    beq  s6,t0,backward_deeper
    li   t0,'['
    beq  s6,t0,backward_shallower
    j    scan_backward

backward_deeper:
    addi s8,s8,1
    j    scan_backward

backward_shallower:
    addi s8,s8,-1
    bnez s8,scan_backward
    j    next

next:
    addi s4,s4,1
    j    main_loop

_exit_error:
    li   t0,SYS_exit
    li   a0,1
    ecall
    j    $$

_exit_ok:
    li   t0,SYS_exit
    li   a0,0
    ecall
    j    $$

.section .rodata
usage:
    .ascii "Usage: bf <file>\n"
usage_len:  .equ    $$ - usage

.section .bss
.align 4
tape:
    .resb TAPE_SIZE
prog_buf:
    .resb PROG_SIZE
