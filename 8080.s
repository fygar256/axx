; ============================================================
;  8080.s -- 8080.axx demo, CP/M-style "hello, world" plus a
;  walkthrough of every 8080 addressing mode the pattern file
;  supports (data transfer, arithmetic, logical, branch, stack,
;  and I/O groups).
;
;  assemble:
;    axx.py 8080.axx 8080.s -b 8080.bin
;    caxx   8080.axx 8080.s -b 8080.bin
;
;  On a real (or emulated) CP/M system this .bin, loaded at
;  0x100 as a .com file, prints "HELLO, 8080 WORLD!" via the
;  BDOS console-string call and returns to CP/M.
; ============================================================

BDOS:   .equ    0x0005          ; CP/M BDOS entry point
CONOUT: .equ    2                ; BDOS function: console char out
PRINT:  .equ    9                ; BDOS function: print $-terminated string

        .org    0x100

start:
        LXI     SP,stack         ; set up a private stack
        LXI     D,greeting
        MVI     C,PRINT
        CALL    BDOS

        CALL    demo             ; exercise every addressing mode
        RET                      ; return to CP/M (warm boot)

; ------------------------------------------------------------
;  demo -- touches every instruction group in 8080.axx
; ------------------------------------------------------------
demo:
        ; --- immediate load / register-to-register move ---
        MVI     A,0x41           ; A <- 'A'
        MOV     B,A
        MOV     C,B
        MVI     D,0x00
        MVI     E,0x10

        ; --- register-pair immediate load, INX/DCX/DAD ---
        LXI     H,buffer
        LXI     B,0x0004
        DAD     B                ; HL += BC
        INX     H
        DCX     H

        ; --- memory access through M (i.e. via H:L) ---
        MVI     M,0x2a           ; buffer[0] <- '*'
        MOV     A,M
        INR     M
        DCR     M

        ; --- LDAX/STAX (BC/DE indirect, A only) ---
        LXI     B,buffer
        MOV     A,C
        STAX    B                ; *BC <- A
        LDAX    B                ; A <- *BC

        ; --- direct addressing ---
        STA     total
        LDA     total
        SHLD    hlsave
        LHLD    hlsave

        ; --- 8-bit arithmetic, register/memory/immediate forms ---
        MVI     A,0x10
        ADD     B
        ADC     C
        SUB     D
        SBB     E
        ADI     0x05
        ACI     0x01
        SUI     0x02
        SBI     0x01

        ; --- logical ops, register/memory/immediate forms ---
        ANA     B
        XRA     C
        ORA     D
        ANI     0x0f
        XRI     0xff
        ORI     0x80
        CMP     E
        CPI     0x80

        ; --- rotates, flags, decimal adjust ---
        RLC
        RRC
        RAL
        RAR
        DAA
        CMA
        CMC
        STC

        ; --- classic 8080 delay loop: DCR + JNZ ---
        MVI     B,0x05
wait:
        DCR     B
        JNZ     wait

        ; --- conditional call/return exercised for real ---
        CPI     0x00
        CZ      zero_case
        JMP     skip_zero
zero_case:
        MVI     A,0xff
        RET
skip_zero:

        ; --- stack: PUSH/POP for all four pairs, incl. PSW ---
        PUSH    B
        PUSH    D
        PUSH    H
        PUSH    PSW
        POP     PSW
        POP     H
        POP     D
        POP     B

        XCHG                     ; swap DE/HL
        XTHL                     ; swap HL with top of stack
        SPHL                     ; SP <- HL

        ; --- port I/O and interrupt control (bare-metal only;
        ;     harmless as encoded bytes under CP/M) ---
        MVI     A,0x00
        OUT     0x01
        IN      0x01
        DI
        EI

        RET

; ------------------------------------------------------------
;  data
; ------------------------------------------------------------
greeting:
        .ascii  "HELLO, 8080 WORLD!\r\n$"
buffer: .equ    0x0200
total:  .equ    buffer + 0x40
hlsave: .equ    0x0202

        .org    0x0300
stack:                           ; grows down from here
