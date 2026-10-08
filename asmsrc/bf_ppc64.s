; Brainfuck interpreter
; Linux / PowerPC64 big-endian (ELFv1)
; axx syntax
;
; Port of bf_aarch64.s.
;
; build, via a linker:
;   axx.py ppc64.axx bf_ppc64.s -o bf.o
;   ld.lld -static -e _start -o bf bf.o
;
; run:
;   ./bf program.bf
;   qemu-ppc64-static ./bf program.bf      ; on a non-PowerPC host
;
; PowerPC64 Linux syscall ABI:
;   r0     = syscall number
;   r3-r8  = arguments
;   sc
;   r3     = result.  An error is flagged by CR0.SO, not by a negative r3,
;            so every call site tests it with bso / bns.  This is the one
;            structural difference from the AArch64 original, which could
;            just compare x0 against 0.
;
; At process entry of a static executable the stack holds argc and argv:
;   0(r1) = argc,  8(r1) = argv[0],  16(r1) = argv[1] ...
; The registers r3 = argc, r4 = argv, r5 = envp of the PowerPC ELF ABI are
; set by the dynamic linker, not by the kernel (nor by qemu-ppc64), so a
; static program has to read the stack; glibc's static start-up does the
; same.  No stack frame is set up here because nothing in this program
; calls anything.
;
; The kernel preserves r14-r31 across sc, so all interpreter state lives
; there and survives every syscall:
;   r14 = argv          r15 = fd                r16 = program length
;   r17 = instruction pointer                   r18 = tape index
;   r19 = current byte  r20 = scratch pointer   r21 = loop nesting depth
;
; PowerPC64 Linux keeps the legacy open syscall, so the openat(AT_FDCWD, ...)
; that the AArch64 version needs is not required here.
;
; Addresses are formed with lis/addi (@ha and @l), which is absolute, not
; position independent: under -o the linker resolves R_PPC64_ADDR16_HA and
; R_PPC64_ADDR16_LO, and the image must run at the address it was linked for.
; The AArch64 original was position independent because adrp is PC-relative;
; the PowerPC equivalent would need Power10 prefixed pcrel instructions.

TAPE_SIZE:  .equ 65536
PROG_SIZE:  .equ 1048576

SYS_exit:   .equ 1
SYS_read:   .equ 3
SYS_write:  .equ 4
SYS_open:   .equ 5
SYS_close:  .equ 6

.global _start
.section .text

_start:
    ld 3,0(1)                     ; argc
    addi 14,1,8                   ; argv
    cmpdi 3,2
    bge _open_file

    ; write(2, usage, usage_len)
    lis 4,usage@ha
    addi 4,4,usage@l
    li 0,SYS_write
    li 3,2
    li 5,usage_len
    sc
    b _exit_error

_open_file:
    ; open(argv[1], O_RDONLY, 0)
    ld 3,8(14)                    ; argv[1]
    li 0,SYS_open
    li 4,0                        ; O_RDONLY
    li 5,0                        ; mode
    sc
    bso _exit_error
    mr 15,3                       ; fd

    ; read(fd, prog_buf, PROG_SIZE) until EOF or the buffer is full.
    ; One read() is not enough: on a pipe or a FIFO it can return short.
    lis 20,prog_buf@ha
    addi 20,20,prog_buf@l
    li 16,0                       ; bytes read so far
_read_loop:
    lis 5,PROG_SIZE>>16
    sub 5,5,16                    ; room left
    cmpdi 5,0
    beq _read_done
    li 0,SYS_read
    mr 3,15
    add 4,20,16
    sc
    bso _exit_error
    cmpdi 3,0
    beq _read_done                ; EOF
    add 16,16,3
    b _read_loop
_read_done:                       ; r16 = program length

    ; close(fd)
    li 0,SYS_close
    mr 3,15
    sc

    ; r17 = instruction pointer
    ; r18 = tape index
    li 17,0
    li 18,0

main_loop:
    cmpd 17,16
    bge _exit_ok

    ; Load prog_buf[r17] into r19 (zero extended byte).
    lis 20,prog_buf@ha
    addi 20,20,prog_buf@l
    lbzx 19,20,17

    cmpwi 19,'>'
    beq op_inc_ptr
    cmpwi 19,'<'
    beq op_dec_ptr
    cmpwi 19,'+'
    beq op_inc_val
    cmpwi 19,'-'
    beq op_dec_val
    cmpwi 19,'.'
    beq op_output
    cmpwi 19,','
    beq op_input
    cmpwi 19,'['
    beq op_loop_start
    cmpwi 19,']'
    beq op_loop_end
    b next

op_inc_ptr:
    addi 18,18,1
    andi. 18,18,TAPE_SIZE-1       ; wrap; tape is adjacent to prog_buf
    b next

op_dec_ptr:
    subi 18,18,1
    andi. 18,18,TAPE_SIZE-1       ; wrap; below tape is read-only .rodata
    b next

op_inc_val:
    lis 20,tape@ha
    addi 20,20,tape@l
    add 20,20,18
    lbz 19,0(20)
    addi 19,19,1
    stb 19,0(20)
    b next

op_dec_val:
    lis 20,tape@ha
    addi 20,20,tape@l
    add 20,20,18
    lbz 19,0(20)
    subi 19,19,1
    stb 19,0(20)
    b next

op_output:
    ; write(1, &tape[r18], 1)
    lis 4,tape@ha
    addi 4,4,tape@l
    add 4,4,18
    li 0,SYS_write
    li 3,1
    li 5,1
    sc
    b next

op_input:
    ; read(0, &tape[r18], 1)
    lis 4,tape@ha
    addi 4,4,tape@l
    add 4,4,18
    li 0,SYS_read
    li 3,0
    li 5,1
    sc
    bso _exit_ok
    cmpdi 3,0
    ble _exit_ok
    b next

op_loop_start:
    ; '[': if current cell != 0, continue.
    lis 20,tape@ha
    addi 20,20,tape@l
    add 20,20,18
    lbz 19,0(20)
    cmpwi 19,0
    bne next

    ; Forward scan for matching ']'.
    li 21,1                       ; nesting depth
scan_forward:
    addi 17,17,1
    cmpd 17,16
    bge _exit_ok

    lis 20,prog_buf@ha
    addi 20,20,prog_buf@l
    lbzx 19,20,17

    cmpwi 19,'['
    beq forward_deeper
    cmpwi 19,']'
    beq forward_shallower
    b scan_forward

forward_deeper:
    addi 21,21,1
    b scan_forward

forward_shallower:
    subi 21,21,1
    cmpdi 21,0
    bne scan_forward
    b next

op_loop_end:
    ; ']': if current cell == 0, continue.
    lis 20,tape@ha
    addi 20,20,tape@l
    add 20,20,18
    lbz 19,0(20)
    cmpwi 19,0
    beq next

    ; Backward scan for matching '['.
    li 21,1                       ; nesting depth
scan_backward:
    cmpdi 17,0
    ble _exit_ok
    subi 17,17,1

    lis 20,prog_buf@ha
    addi 20,20,prog_buf@l
    lbzx 19,20,17

    cmpwi 19,']'
    beq backward_deeper
    cmpwi 19,'['
    beq backward_shallower
    b scan_backward

backward_deeper:
    addi 21,21,1
    b scan_backward

backward_shallower:
    subi 21,21,1
    cmpdi 21,0
    bne scan_backward
    b next

next:
    addi 17,17,1
    b main_loop

_exit_error:
    li 0,SYS_exit
    li 3,1
    sc
    b $$

_exit_ok:
    li 0,SYS_exit
    li 3,0
    sc
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
