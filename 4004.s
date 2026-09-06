;=============================================================
;  4004.s -- 4004.axx demo. The Intel 4004 (1971) was the first
;  commercial microprocessor, designed for the Busicom 141-PF
;  calculator; this program leans into that heritage with a
;  small multi-digit decimal adder, while touching every
;  instruction group 4004.axx supports.
;
;  assemble:
;    axx.py 4004.axx 4004.s -b 4004.bin
;    caxx   4004.axx 4004.s -b 4004.bin
;
;  DATA RAM chip 0, register 0 holds the first 4-digit decimal
;  addend (least-significant digit first), register 1 holds the
;  second addend; ADD16 leaves the 4-digit decimal sum in
;  register 1, one BCD digit per DATA RAM character.
;=============================================================

        .org    0x000

start:
        NOP                     ; classic first byte of a 4004 ROM
        LDM     0
        DCL                     ; select DATA RAM bank 0 (the reset default,
                                 ; but DCL is shown explicitly for the demo)

        JMS     ADD16           ; add the two 4-digit numbers below
        WRR                     ; show register 1's low sum digit on
                                 ; whichever ROM port SRC last selected

        LDM     5
        XCH     4               ; register 4 <- 5, a tiny busy-loop counter
delay:
        ISZ     4,delay         ; same-page 8-bit branch; loops until R4 = 0

        JUN     next_page       ; JUN's operand is a full 12-bit address,
                                 ; so it may (and here does) cross a page

; ------------------------------------------------------------
;  ADD16 -- add two 4-digit (16-bit) decimal numbers held in
;  DATA RAM chip 0, registers 0 and 1 (least-significant BCD
;  digit first in character 0). The sum replaces register 1.
;  Register pair 4P (registers 8,9) walks the digit count;
;  register pairs 0P/1P address the two RAM registers via SRC.
; ------------------------------------------------------------
ADD16:
        FIM     0P,0            ; 0P -> RAM chip 0, register 0
        FIM     1P,0x10         ; 1P -> RAM chip 0, register 1
        CLB                     ; ACC = 0, carry = 0
        XCH     8               ; digit counter (register 8) = 0

digit_loop:
        SRC     0P
        RDM                     ; ACC <- addend-1 digit
        SRC     1P
        ADM                     ; ACC <- ACC + addend-2 digit + carry
        DAA                     ; keep the result in BCD
        WRM                     ; store the sum digit back into register 1

        INC     5               ; next character of register 0
        INC     7               ; next character of register 1
        ISZ     8,digit_loop    ; loop for all 4 digits

        BBL     0               ; return, ACC (return data) = 0

        .org    0x100
next_page:
        JCN     0,next_page     ; condition 0 never jumps -- demo of the
                                 ; generic JCN form; always falls through
        JNZ     next_page       ; named single-bit alias for JCN 12,addr;
                                 ; taken only if ADD16's last digit was
                                 ; nonzero
loop_forever:
        JUN     loop_forever    ; the real halt: an unconditional loop
