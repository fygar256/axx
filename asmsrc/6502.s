; ---------------------------------------------------------------
; 6502.axx demo -- prints "HELLO, WORLD!" to the C64 screen buffer
; and shows every addressing mode the pattern file supports.
;
;   axx.py 6502.axx 6502_demo.s -b demo.bin -v
;
; Numbers use axx expression syntax: 0xc000, not $c000.
; ---------------------------------------------------------------

SCREEN: .equ 0x0400          ; C64 screen RAM
PTRLO:  .equ 0xfb            ; zero-page pointer, low
PTRHI:  .equ 0xfc            ; zero-page pointer, high

        .org 0xc000

start:
        LDA #(msg&0xff)      ; low byte of msg
        STA PTRLO            ; zero page   -- chosen automatically
        LDA #((msg>>8)&0xff) ; high byte of msg
        STA PTRHI
        LDY #0x00

loop:
        LDA (PTRLO),Y        ; (indirect),Y
        BEQ done             ; relative branch, forward
        SEC
        SBC #0x40            ; PETSCII -> screen code
        STA SCREEN,Y         ; absolute,Y  (SCREEN > 0xff)
        INY
        CPY #0x28
        BNE loop             ; relative branch, backward

done:
        LDX #0x00
clr:
        LDA #0x20
        STA >SCREEN,X        ; forced absolute,X
        INX
        CPX #0x10
        BNE clr

; --- a tour of the remaining addressing modes ---
modes:
        ASL A                ; accumulator
        LSR                  ; accumulator, implicit operand
        ROL 0x10             ; zero page
        ROR 0x10,X           ; zero page,X
        INC 0x1234           ; absolute
        DEC 0x1234,X         ; absolute,X
        LDX 0x10,Y           ; zero page,Y
        LDX 0x1234,Y         ; absolute,Y
        ORA (0x20,X)         ; (indirect,X)
        BIT 0x10             ; zero page
        JMP (vector)         ; indirect
        JSR sub
        NOP
        BRK

sub:    PHA
        TXA
        TAY
        PLA
        RTS

vector: .equ 0xfffc
msg:    .ascii "HELLO, WORLD!"
        .zero 1
