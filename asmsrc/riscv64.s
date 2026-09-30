; ===================================================================
; riscv64.s -- test source for riscv64.axx
;
; It prints "hello, RISC-V" twice and exits, and on the way it uses
; every relocation type riscv64.axx declares, so the object shows the
; whole set:
;
;   R_RISCV_CALL_PLT      call writeout
;   R_RISCV_HI20          lui  a1,%hi(msg)
;   R_RISCV_LO12_I        addi a1,a1,%lo(msg)
;   R_RISCV_LO12_S        sd   a5,%lo(saved)(a4)
;   R_RISCV_BRANCH        beq  s2,zero,done
;   R_RISCV_JAL           j    loop
;   R_RISCV_PCREL_HI20    auipc a5,%pcrel_hi(msgptr)
;   R_RISCV_PCREL_LO12_I  ld    a5,%pcrel_lo(pcref)(a5)
;   R_RISCV_64            quad  msg
;   R_RISCV_32            dword msg
;
; The pc-relative pair follows the psABI rule: the LO12 relocation
; names the label on the auipc, not the symbol being addressed, which
; is what tells the linker where to take the page base from.
;
;   axx riscv64.axx riscv64.s -o out.o
;   ld -m elf64lriscv -o out out.o
;   qemu-riscv64 out
;
; The two ecalls use the FreeBSD riscv64 syscall ABI: the number goes
; in t0 (SYS_write 4, SYS_exit 1), the arguments in a0 onwards. On
; Linux the number goes in a7 instead (__NR_write 64, __NR_exit 93);
; only those two `li` lines change.
; ===================================================================

        .global _start
        .type   _start::func
        .global writeout
        .type   writeout::func
        .global msg
        .type   msg::object
        .size   msg::14
        .global msgptr
        .type   msgptr::object
        .size   msgptr::8

        .section .text
_start:
        call    writeout                ; -> R_RISCV_CALL_PLT
        li      a0,0
        li      t0,1                    ; SYS_exit
        ecall
_start_end:
        .size   _start::_start_end-_start

writeout:
        li      s2,2                    ; print it twice
loop:
        li      a0,1                    ; fd = stdout
        lui     a1,%hi(msg)             ; -> R_RISCV_HI20
        addi    a1,a1,%lo(msg)          ; -> R_RISCV_LO12_I
        li      a2,14
        li      t0,4                    ; SYS_write
        ecall
        addi    s2,s2,-1
        beq     s2,zero,done            ; -> R_RISCV_BRANCH
        j       loop                    ; -> R_RISCV_JAL
done:
;       read msgptr through a pc-relative pair, then store it back
pcref:
        auipc   a5,%pcrel_hi(msgptr)    ; -> R_RISCV_PCREL_HI20
        ld      a5,%pcrel_lo(pcref)(a5) ; -> R_RISCV_PCREL_LO12_I
        lui     a4,%hi(saved)
        sd      a5,%lo(saved)(a4)       ; -> R_RISCV_LO12_S
        ret
writeout_end:
        .size   writeout::writeout_end-writeout

        .section .rodata
msg:
        .ascii  "hello, RISC-V"
        db      10

        .section .data
msgptr:
        quad    msg                     ; -> R_RISCV_64
msgref:
        dword   msg                     ; -> R_RISCV_32
saved:
        quad    0
