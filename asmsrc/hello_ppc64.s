; hello.s -- Hello, world! for Linux on PowerPC64 (axx, ppc64.axx / ppc64le.axx)
; PowerPC Linux system calls: r0 = number, r3.. = arguments, then sc.
        .global _start
_start:
        bl      print           ; R_PPC64_REL24
        li      0,1             ; exit(0)
        li      3,0
        sc

print:
        li      0,4             ; write(1, msg, len)
        li      3,1
        lis     4,msg@ha        ; R_PPC64_ADDR16_HA
        addi    4,4,msg@l       ; R_PPC64_ADDR16_LO
        li      5,14
        sc
        blr

msg:
        .ascii  "Hello, world!\n"
