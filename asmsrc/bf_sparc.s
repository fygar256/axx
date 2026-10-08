; Brainfuck interpreter
; SPARC V9 (64-bit) / FreeBSD or Linux
; sparc.axx syntax -- the SPARC port of bfi.s, with the macro layer
;
; build:
;   Set OS below to "freebsd" or "linux".
;
;   axx sparc.axx bf_sparc.s -o bf.o --osabi FreeBSD && ld.lld -o bf bf.o
;   axx sparc.axx bf_sparc.s -o bf.o --osabi Linux   && ld.lld -o bf bf.o
;
; run:
;   qemu-sparc64-static ./bf program.bf      (FreeBSD: qemu bsd-user)
;   qemu-sparc64 ./bf program.bf             (Linux: qemu linux-user)
;
; What differs between the two systems:
;   - the system call trap: ta %xcc, 0x41 on FreeBSD, ta %xcc, 0x6d
;     (the 64-bit Linux trap) on Linux. The numbers used here are the
;     same on both (exit 1, read 3, write 4, open 5, close 6): the
;     number goes in %g1, the arguments in %o0-%o5, the result comes
;     back in %o0, and a failed call sets the carry in %xcc;
;   - at process entry FreeBSD passes in %o0 a pointer to argc,
;     argv[0], argv[1] ...; Linux puts them on the stack above the
;     16-word register save area, at %sp + 2047 (the V9 stack bias) +
;     128.
; The FreeBSD build was run under qemu-sparc64-static (bsd-user) with
; mandelbrot.bf. The Linux build was run under the Linux qemu-sparc64
; (linux-user, on FreeBSD's Linuxulator). bfsh/bf_sparc_freebsd.sh and
; bfsh/bf_sparc_linux.sh do the build and the run.
;
; The branch targets are defined as `name: .equ $$` (the address as a
; constant) instead of `name:`. axx makes every branch to a label a
; relocation (R_SPARC_WDISP22 / WDISP19 / WDISP16), and ld.lld 19 does
; not handle those three types; with a constant target the
; displacement is computed by axx and the object carries only
; R_SPARC_HI22 / LO10 for prog_buf, tape and usage. With a linker that
; has the branch types (GNU ld), plain labels work as well.
;
; Every branch and call has a delay slot (sparc.axx fills nothing on
; its own). Most delay slots here hold a nop; where one holds an
; instruction the comment says so. The addresses of prog_buf and tape
; are formed once with sethi %hi / or %lo (R_SPARC_HI22 / LO10) and
; kept in registers.
;
; registers:
;   %l0 argument block   %l1 fd             %l2 program length
;   %l3 instruction ptr  %l4 tape index     %l5 prog_buf
;   %l6 tape             %l7 nesting depth  %g2 current op
;   %g3 cell value       %g1 system call number

; ===========================================================
; build settings
; ===========================================================
!set OS        = "freebsd"      ; "freebsd" or "linux"
!set TAPE_SIZE = 65536
!set PROG_SIZE = 1048576

!echo "bf_sparc.s: OS=" + OS + " tape=" + str(TAPE_SIZE) + " prog=" + str(PROG_SIZE)

.global _start

; --- system calls ---
!if OS == "freebsd" !then {
SYS_TRAP:  .equ  0x41
} !elif OS == "linux" !then {
SYS_TRAP:  .equ  0x6d
} !else {
    !error "unknown OS: " + OS + " (use \"freebsd\" or \"linux\")"
}
SYS_EXIT:  .equ  1
SYS_READ:  .equ  3
SYS_WRITE: .equ  4
SYS_OPEN:  .equ  5
SYS_CLOSE: .equ  6

; ===========================================================
; macros
; ===========================================================

; system call number nr; the arguments are already in %o0-%o2
!def syscall(nr) {
    mov  !{nr}, %g1
    ta   %xcc, SYS_TRAP
}

; exit(code)
!def sysexit(code) {
    mov  !{code}, %o0
    !syscall("SYS_EXIT")
}

; reg = the address of sym
!def la(sym, reg) {
    sethi %hi(!{sym}), !{reg}
    or   !{reg}, %lo(!{sym}), !{reg}
}

; one entry of the dispatch table
!def case(ch, target) {
    cmp  %g2, '!{ch}'
    be   %icc, !{target}
    nop
}

; to the next op: the branch back to main_loop with the increment of
; the instruction pointer in its delay slot (the "jmp next" of bfi.s)
!def go_next() {
    ba   main_loop
    inc  %l3                   ; delay slot: ip + 1
}

; %o1 = &tape[%l4], %o2 = 1 (the common setup of read / write)
!def tape_ptr_1byte() {
    add  %l6, %l4, %o1
    mov  1, %o2
}

; The scan for the matching bracket.
;   forward=1: step %l3 forward, inc_ch deepens, dec_ch makes it shallower
;   forward=0: step %l3 backward, the same
; The labels are made unique with __id__, as in bfi.s.
!def bracket_scan(forward, inc_ch, dec_ch) {
    mov  1, %l7                ; nesting depth
scan!{__id__}: .equ $$
!if forward !then {
    inc  %l3
    cmp  %l3, %l2
    bge  %xcc, exit
    nop
} !else {
    brlez %l3, exit
    nop
    dec  %l3
}
    ldub [%l5+%l3], %g2
    cmp  %g2, '!{inc_ch}'
    be,a %icc, scan!{__id__}
    inc  %l7                   ; delay slot, annulled unless taken: depth + 1
    cmp  %g2, '!{dec_ch}'
    bne  %icc, scan!{__id__}
    nop
    deccc %l7                  ; depth - 1
    bne  %xcc, scan!{__id__}
    nop
    ba   next
    nop
}

; ===========================================================
.section .text

_start:
!if OS == "freebsd" !then {
    mov  %o0, %l0              ; %o0 -> argc, argv[0], argv[1], ...
} !else {
    add  %sp, 2047+128, %l0    ; argc is above the register save area
}
    ldx  [%l0], %g2            ; argc
    cmp  %g2, 2
    bge  %xcc, _open_file
    nop

    ; too few arguments: print the usage on stderr and exit
    mov  2, %o0
    !la("usage", "%o1")
    mov  usage_len, %o2
    !syscall("SYS_WRITE")
    !sysexit(1)

_open_file: .equ $$
    ldx  [%l0+16], %o0         ; argv[1] = the file name
    clr  %o1                   ; O_RDONLY = 0
    clr  %o2
    !syscall("SYS_OPEN")
    bcs,pn %xcc, exit_error
    nop
    mov  %o0, %l1              ; %l1 = fd

    ; read the file into prog_buf until EOF or the buffer is full (one
    ; read() may return short on a pipe or a FIFO)
    !la("prog_buf", "%l5")
    !la("tape", "%l6")
    clr  %l2                   ; bytes read so far
read_loop: .equ $$
    set  !{PROG_SIZE}, %o2     ; the same constant as the buffer
    sub  %o2, %l2, %o2         ; room left
    brz,pn %o2, read_done
    nop
    mov  %l1, %o0
    add  %l5, %l2, %o1
    !syscall("SYS_READ")
    bcs,pn %xcc, exit_error
    nop
    brz,pn %o0, read_done      ; EOF
    nop
    ba   read_loop
    add  %l2, %o0, %l2         ; delay slot: count the bytes
read_done: .equ $$                     ; %l2 = program length

    mov  %l1, %o0
    !syscall("SYS_CLOSE")

    ; initialise
    clr  %l3                   ; instruction pointer = 0
    clr  %l4                   ; tape index = 0

main_loop: .equ $$
    cmp  %l3, %l2
    bge  %xcc, exit
    nop

    ; the current BF op
    ldub [%l5+%l3], %g2

!case(">", "op_inc_ptr")
!case("<", "op_dec_ptr")
!case("+", "op_inc_val")
!case("-", "op_dec_val")
!case(".", "op_output")
!case(",", "op_input")
!case("[", "op_loop_start")
!case("]", "op_loop_end")

next: .equ $$
    !go_next()

; ===== the Brainfuck ops =====

op_inc_ptr: .equ $$
    inc  %l4                   ; > : tape pointer + 1
    !go_next()

op_dec_ptr: .equ $$
    dec  %l4                   ; < : tape pointer - 1
    !go_next()

op_inc_val: .equ $$
    ldub [%l6+%l4], %g3        ; + : the current cell + 1
    inc  %g3
    stb  %g3, [%l6+%l4]
    !go_next()

op_dec_val: .equ $$
    ldub [%l6+%l4], %g3        ; - : the current cell - 1
    dec  %g3
    stb  %g3, [%l6+%l4]
    !go_next()

op_output: .equ $$
    ; . : write(1, &tape[%l4], 1)
    mov  1, %o0
    !tape_ptr_1byte()
    !syscall("SYS_WRITE")
    !go_next()

op_input: .equ $$
    ; , : read(0, &tape[%l4], 1)
    clr  %o0
    !tape_ptr_1byte()
    !syscall("SYS_READ")
    bcs,pn %xcc, exit          ; error
    nop
    brz,pn %o0, exit           ; EOF
    nop
    !go_next()

op_loop_start: .equ $$
    ; [ : if the current cell is 0, go past the matching ']'
    ldub [%l6+%l4], %g3
    brnz %g3, next
    nop
!bracket_scan(1, "[", "]")

op_loop_end: .equ $$
    ; ] : if the current cell is not 0, go back past the matching '['
    ldub [%l6+%l4], %g3
    brz  %g3, next
    nop
!bracket_scan(0, "]", "[")

exit_error: .equ $$
!sysexit(1)

exit: .equ $$
!sysexit(0)

.section .data
usage:     .ascii "Usage: bf <file>\n"
usage_len: .equ $$ - usage
.endsection

.section .bss
.align 8
tape:     .resb !{TAPE_SIZE}
prog_buf: .resb !{PROG_SIZE}
.endsection
