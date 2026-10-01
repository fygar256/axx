; Brainfuck interpreter
; RISC-V 64 / Linux (qemu-riscv64 user mode, or any riscv64 Linux)
; axx syntax; a port of bf_aarch64.s
;
; build:
;   axx riscv64full.axx bf_riscv64.s -o bf.o
;   ld.lld -m elf64lriscv -static -e _start -o bf bf.o     (or GNU ld)
;
; run:
;   qemu-riscv64 ./bf program.bf
;
; The addresses of the data are formed with auipc + %pcrel_hi / %pcrel_lo
; pairs (the macro `la` below), so the object carries R_RISCV_PCREL_HI20 /
; R_RISCV_PCREL_LO12_I relocations and the code is position independent.
; riscv64full.axx's own `la` pseudo-instruction is not used: it works out
; the offset itself and is exact only inside one section (see its header).
; A flat image (-b) is therefore not supported: %pcrel_lo needs the linker.
;
; RISC-V Linux syscall ABI (the generic table, same numbers as AArch64):
;   a0-a5 = arguments, a7 = syscall number, ecall; the result is in a0.
;
; registers:
;   s1 argc            s2 fd              s3 program length
;   s4 instruction ptr s5 tape index      s6 current char
;   s7 scratch address s8 nesting depth

TAPE_SIZE:  .equ 65536
PROG_SIZE:  .equ 1048576

SYS_read:   .equ 63
SYS_write:  .equ 64
SYS_close:  .equ 57
SYS_openat: .equ 56
SYS_exit:   .equ 93
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
    ; At Linux process entry, sp points at argc, then argv[0], argv[1] ...
    ld   s1,0(sp)                 ; argc
    li   t0,2
    bge  s1,t0,_open_file

    ; write(2, usage, usage_len)
    li   a7,SYS_write
    li   a0,2
    !la("a1", "usage")
    li   a2,usage_len
    ecall
    j    _exit_error

_open_file:
    ; argv[1] is at sp + 16.
    ld   a1,16(sp)

    ; openat(AT_FDCWD, argv[1], O_RDONLY, 0)
    li   a7,SYS_openat
    li   a0,AT_FDCWD
    li   a2,0                     ; O_RDONLY
    li   a3,0
    ecall
    bltz a0,_exit_error
    mv   s2,a0                    ; fd

    ; read(fd, prog_buf, PROG_SIZE) until EOF or the buffer is full.
    ; One read() is not enough: on a pipe or a FIFO it can return short.
    li   s3,0                     ; bytes read so far
_read_loop:
    li   a2,PROG_SIZE
    sub  a2,a2,s3                 ; room left
    beqz a2,_read_done
    li   a7,SYS_read
    mv   a0,s2
    !la("a1", "prog_buf")
    add  a1,a1,s3
    ecall
    bltz a0,_exit_error
    beqz a0,_read_done            ; EOF
    add  s3,s3,a0
    j    _read_loop
_read_done:                       ; s3 = program length

    ; close(fd)
    li   a7,SYS_close
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
    li   a7,SYS_write
    ecall
    j    next

op_input:
    ; read(0, &tape[s5], 1)
    !la("a1", "tape")
    add  a1,a1,s5
    li   a0,0
    li   a2,1
    li   a7,SYS_read
    ecall
    blez a0,_exit_ok
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
    li   a7,SYS_exit
    li   a0,1
    ecall
    j    $$

_exit_ok:
    li   a7,SYS_exit
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
