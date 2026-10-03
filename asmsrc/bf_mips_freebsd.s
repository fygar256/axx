; Brainfuck interpreter
; MIPS32 o32 / FreeBSD (qemu-mips bsd-user, or FreeBSD/mips)
; axx syntax; the FreeBSD version of bf_mips.s (which is for Linux)
;
; build:
;   axx --osabi freebsd mips.axx bf_mips_freebsd.s -o bf.o      ; big-endian
;   axx --osabi freebsd mipsel.axx bf_mips_freebsd.s -o bf.o    ; little-endian
;   ld.lld -static -o bf bf.o
; ld.lld copies the OS/ABI of the object, so the executable is branded
; FreeBSD. With a linker that writes "System V", brand it by hand:
;   elfedit --output-osabi FreeBSD bf
;
; run:
;   qemu-mips-static ./bf program.bf        ; qemu-mipsel-static for -EL
;
; What differs from the Linux file:
;   - the numbers are FreeBSD's: exit 1, read 3, write 4, close 6,
;     openat 499 (the Linux o32 numbers are 4000 higher);
;   - open is done with openat(AT_FDCWD, ...);
;   - at process entry a0 points at argc, argv[0], argv[1] ... (sp is the
;     same place, rounded down for alignment); the code reads them
;     through a0.
; The rest is the same: the number goes in v0, the arguments in a0-a3,
; and a failed syscall sets a3 != 0 and returns the errno in v0.
;
; The kernel preserves s0-s7 across syscall, so all interpreter state lives
; there and survives every syscall:
;   s0 = argv           s1 = fd                 s2 = program length
;   s3 = instruction pointer                    s4 = tape index
;   s5 = current byte   s6 = scratch pointer    s7 = loop nesting depth
; t0 / t1 are only used between syscalls.
;
; Every delay slot is written out (axx, like GNU as under .set noreorder,
; puts nothing there on its own): a nop, or an instruction that is harmless
; on both paths.
;
; Addresses are formed with lui/addiu (%hi and %lo), so the image must run
; at the address it was linked for.

    .set noreorder
    .set noat

TAPE_SIZE:  .equ 65536
PROG_SIZE:  .equ 1048576

SYS_exit:   .equ 1
SYS_read:   .equ 3
SYS_write:  .equ 4
SYS_close:  .equ 6
SYS_openat: .equ 499
AT_FDCWD:   .equ -100

; __start is the default entry of ld.lld (and GNU ld) on MIPS; _start is
; kept for -e _start.
.global __start
.global _start
.section .text

__start:
_start:
    lw $t0,0($a0)                 ; argc
    addiu $s0,$a0,4               ; argv
    slti $t1,$t0,2
    beqz $t1,_open_file
    nop

    ; write(2, usage, usage_len)
    lui $a1,%hi(usage)
    addiu $a1,$a1,%lo(usage)
    li $v0,SYS_write
    li $a0,2
    li $a2,usage_len
    syscall
    b _exit_error
    nop

_open_file:
    ; openat(AT_FDCWD, argv[1], O_RDONLY, 0)
    lw $a1,4($s0)                 ; argv[1]
    li $v0,SYS_openat
    li $a0,AT_FDCWD
    li $a2,0                      ; O_RDONLY
    li $a3,0                      ; mode
    syscall
    bnez $a3,_exit_error
    nop
    move $s1,$v0                  ; fd

    ; read(fd, prog_buf, PROG_SIZE) until EOF or the buffer is full.
    ; One read() is not enough: on a pipe or a FIFO it can return short.
    lui $s6,%hi(prog_buf)
    addiu $s6,$s6,%lo(prog_buf)
    li $s2,0                      ; bytes read so far
_read_loop:
    lui $a2,PROG_SIZE>>16
    subu $a2,$a2,$s2              ; room left
    beqz $a2,_read_done
    nop
    li $v0,SYS_read
    move $a0,$s1
    addu $a1,$s6,$s2
    syscall
    bnez $a3,_exit_error
    nop
    beqz $v0,_read_done           ; EOF
    nop
    b _read_loop
    addu $s2,$s2,$v0              ; (delay slot)
_read_done:                       ; s2 = program length

    ; close(fd)
    li $v0,SYS_close
    move $a0,$s1
    syscall

    ; s3 = instruction pointer
    ; s4 = tape index
    li $s3,0
    li $s4,0

main_loop:
    sltu $t0,$s3,$s2
    beqz $t0,_exit_ok
    nop

    ; Load prog_buf[s3] into s5 (zero extended byte).
    lui $s6,%hi(prog_buf)
    addiu $s6,$s6,%lo(prog_buf)
    addu $s6,$s6,$s3
    lbu $s5,0($s6)

    li $t0,'>'
    beq $s5,$t0,op_inc_ptr
    li $t0,'<'                    ; (delay slot) next character
    beq $s5,$t0,op_dec_ptr
    li $t0,'+'
    beq $s5,$t0,op_inc_val
    li $t0,'-'
    beq $s5,$t0,op_dec_val
    li $t0,'.'
    beq $s5,$t0,op_output
    li $t0,','
    beq $s5,$t0,op_input
    li $t0,'['
    beq $s5,$t0,op_loop_start
    li $t0,']'
    beq $s5,$t0,op_loop_end
    nop
    b next
    nop

op_inc_ptr:
    addiu $s4,$s4,1
    b next
    andi $s4,$s4,TAPE_SIZE-1      ; (delay slot) wrap; tape is adjacent to prog_buf

op_dec_ptr:
    addiu $s4,$s4,-1
    b next
    andi $s4,$s4,TAPE_SIZE-1      ; (delay slot) wrap; below tape is .rodata

op_inc_val:
    lui $s6,%hi(tape)
    addiu $s6,$s6,%lo(tape)
    addu $s6,$s6,$s4
    lbu $s5,0($s6)
    addiu $s5,$s5,1
    b next
    sb $s5,0($s6)                 ; (delay slot)

op_dec_val:
    lui $s6,%hi(tape)
    addiu $s6,$s6,%lo(tape)
    addu $s6,$s6,$s4
    lbu $s5,0($s6)
    addiu $s5,$s5,-1
    b next
    sb $s5,0($s6)                 ; (delay slot)

op_output:
    ; write(1, &tape[s4], 1)
    lui $a1,%hi(tape)
    addiu $a1,$a1,%lo(tape)
    addu $a1,$a1,$s4
    li $v0,SYS_write
    li $a0,1
    li $a2,1
    syscall
    b next
    nop

op_input:
    ; read(0, &tape[s4], 1)
    lui $a1,%hi(tape)
    addiu $a1,$a1,%lo(tape)
    addu $a1,$a1,$s4
    li $v0,SYS_read
    li $a0,0
    li $a2,1
    syscall
    bnez $a3,_exit_ok
    nop
    blez $v0,_exit_ok
    nop
    b next
    nop

op_loop_start:
    ; '[': if current cell != 0, continue.
    lui $s6,%hi(tape)
    addiu $s6,$s6,%lo(tape)
    addu $s6,$s6,$s4
    lbu $s5,0($s6)
    bnez $s5,next
    nop

    ; Forward scan for matching ']'.
    li $s7,1                      ; nesting depth
scan_forward:
    addiu $s3,$s3,1
    sltu $t0,$s3,$s2
    beqz $t0,_exit_ok
    nop

    lui $s6,%hi(prog_buf)
    addiu $s6,$s6,%lo(prog_buf)
    addu $s6,$s6,$s3
    lbu $s5,0($s6)

    li $t0,'['
    beq $s5,$t0,forward_deeper
    li $t0,']'                    ; (delay slot)
    beq $s5,$t0,forward_shallower
    nop
    b scan_forward
    nop

forward_deeper:
    b scan_forward
    addiu $s7,$s7,1               ; (delay slot)

forward_shallower:
    addiu $s7,$s7,-1
    bnez $s7,scan_forward
    nop
    b next
    nop

op_loop_end:
    ; ']': if current cell == 0, continue.
    lui $s6,%hi(tape)
    addiu $s6,$s6,%lo(tape)
    addu $s6,$s6,$s4
    lbu $s5,0($s6)
    beqz $s5,next
    nop

    ; Backward scan for matching '['.
    li $s7,1                      ; nesting depth
scan_backward:
    blez $s3,_exit_ok
    nop
    addiu $s3,$s3,-1

    lui $s6,%hi(prog_buf)
    addiu $s6,$s6,%lo(prog_buf)
    addu $s6,$s6,$s3
    lbu $s5,0($s6)

    li $t0,']'
    beq $s5,$t0,backward_deeper
    li $t0,'['                    ; (delay slot)
    beq $s5,$t0,backward_shallower
    nop
    b scan_backward
    nop

backward_deeper:
    b scan_backward
    addiu $s7,$s7,1               ; (delay slot)

backward_shallower:
    addiu $s7,$s7,-1
    bnez $s7,scan_backward
    nop
    b next
    nop

next:
    b main_loop
    addiu $s3,$s3,1               ; (delay slot)

_exit_error:
    li $v0,SYS_exit
    li $a0,1
    syscall
    b $$
    nop

_exit_ok:
    li $v0,SYS_exit
    li $a0,0
    syscall
    b $$
    nop

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
