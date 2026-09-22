; Brainfuck interpreter
; Android AArch64 / Linux
; GNU as syntax
;
; build on Android/Termux:
;   clang --target=aarch64-linux-android -nostdlib -static -Wl,-e,_start -o bf bf_aarch64.s
;
; Usage:
;   ./bf program.bf
;
; AArch64 Linux syscall ABI:
;   x0-x5 = arguments
;   x8    = syscall number
;   svc #0
;
; Android uses openat(AT_FDCWD, path, O_RDONLY, 0), not the old x86_64 open syscall.

TAPE_SIZE:  .equ 65536
PROG_SIZE:  .equ 1048576

SYS_read:   .equ 63
SYS_write:  .equ 64
SYS_close:  .equ 57
SYS_openat: .equ 56
SYS_exit:   .equ 93
AT_FDCWD:   .equ -100

.global _start
.section .text

_start:
    ; At Linux process entry, SP points at argc/argv.
    ldr x19, [sp]                 ; argc
    cmp x19, #2
    b.ge _open_file

    ; write(2, usage, usage_len)
    mov x8, #SYS_write
    mov x0, #2
    adrp x1, usage
    add  x1, x1, :lo12:usage
    mov x2, #usage_len
    svc #0
    b _exit_error

_open_file:
    ; argv[1] is at sp + 16.
    ldr x1, [sp, #16]

    ; openat(AT_FDCWD, argv[1], O_RDONLY, 0)
    mov x8, #SYS_openat
    mov x0, #AT_FDCWD
    mov x2, #0                    ; O_RDONLY
    mov x3, #0
    svc #0
    cmp x0, #0
    b.lt _exit_error
    mov x20, x0                   ; fd

    ; read(fd, prog_buf, PROG_SIZE)
    mov x8, #SYS_read
    mov x0, x20
    adrp x1, prog_buf
    add  x1, x1, :lo12:prog_buf
    mov x2, #PROG_SIZE
    svc #0
    cmp x0, #0
    b.lt _exit_error
    mov x21, x0                   ; program length

    ; close(fd)
    mov x8, #SYS_close
    mov x0, x20
    svc #0

    ; x22 = instruction pointer
    ; x23 = tape index
    mov x22, #0
    mov x23, #0

main_loop:
    cmp x22, x21
    b.ge _exit_ok

    ; Load prog_buf[x22] into w24 (low byte).
    adrp x25, prog_buf
    add  x25, x25, :lo12:prog_buf
    ldrb w24, [x25, x22]

    cmp w24, #'>'
    b.eq op_inc_ptr
    cmp w24, #'<'
    b.eq op_dec_ptr
    cmp w24, #'+'
    b.eq op_inc_val
    cmp w24, #'-'
    b.eq op_dec_val
    cmp w24, #'.'
    b.eq op_output
    cmp w24, #','
    b.eq op_input
    cmp w24, #'['
    b.eq op_loop_start
    cmp w24, #']'
    b.eq op_loop_end
    b next

op_inc_ptr:
    add x23, x23, #1
    b next

op_dec_ptr:
    sub x23, x23, #1
    b next

op_inc_val:
    adrp x25, tape
    add  x25, x25, :lo12:tape
    add  x25, x25, x23
    ldrb w24, [x25]
    add  w24, w24, #1
    strb w24, [x25]
    b next

op_dec_val:
    adrp x25, tape
    add  x25, x25, :lo12:tape
    add  x25, x25, x23
    ldrb w24, [x25]
    sub  w24, w24, #1
    strb w24, [x25]
    b next

op_output:
    ; write(1, &tape[x23], 1)
    adrp x1, tape
    add  x1, x1, :lo12:tape
    add  x1, x1, x23
    mov x0, #1
    mov x2, #1
    mov x8, #SYS_write
    svc #0
    b next

op_input:
    ; read(0, &tape[x23], 1)
    adrp x1, tape
    add  x1, x1, :lo12:tape
    add  x1, x1, x23
    mov x0, #0
    mov x2, #1
    mov x8, #SYS_read
    svc #0
    cmp x0, #0
    b.le _exit_ok
    b next

op_loop_start:
    ; '[': if current cell != 0, continue.
    adrp x25, tape
    add  x25, x25, :lo12:tape
    add  x25, x25, x23
    ldrb w24, [x25]
    cbnz w24, next

    ; Forward scan for matching ']'.
    mov x26, #1                   ; nesting depth
scan_forward:
    add x22, x22, #1
    cmp x22, x21
    b.ge _exit_ok

    adrp x25, prog_buf
    add  x25, x25, :lo12:prog_buf
    ldrb w24, [x25, x22]

    cmp w24, #'['
    b.eq forward_deeper
    cmp w24, #']'
    b.eq forward_shallower
    b scan_forward

forward_deeper:
    add x26, x26, #1
    b scan_forward

forward_shallower:
    sub x26, x26, #1
    cbnz x26, scan_forward
    b next

op_loop_end:
    ; ']': if current cell == 0, continue.
    adrp x25, tape
    add  x25, x25, :lo12:tape
    add  x25, x25, x23
    ldrb w24, [x25]
    cbz w24, next

    ; Backward scan for matching '['.
    mov x26, #1                   ; nesting depth
scan_backward:
    cmp x22, #0
    b.le _exit_ok
    sub x22, x22, #1

    adrp x25, prog_buf
    add  x25, x25, :lo12:prog_buf
    ldrb w24, [x25, x22]

    cmp w24, #']'
    b.eq backward_deeper
    cmp w24, #'['
    b.eq backward_shallower
    b scan_backward

backward_deeper:
    add x26, x26, #1
    b scan_backward

backward_shallower:
    sub x26, x26, #1
    cbnz x26, scan_backward
    b next

next:
    add x22, x22, #1
    b main_loop

_exit_error:
    mov x8, #SYS_exit
    mov x0, #1
    svc #0
    b $$

_exit_ok:
    mov x8, #SYS_exit
    mov x0, #0
    svc #0
    b $$

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
