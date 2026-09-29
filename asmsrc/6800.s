; ---------------------------------------------------------------
; 6800.axx demo -- copies a short message into a RAM buffer while
; accumulating a checksum, then shows a cross-section of the other
; addressing modes the pattern file supports.
;
;   axx.py 6800.axx 6800.s -b demo.bin -v
;
; Numbers use axx expression syntax: 0x1000, not $1000.
;
; The MC6800 has a single index register, so the classic idiom for
; walking two pointers at once (a source and a destination) is to
; keep both in direct-page scratch cells and reload X from whichever
; one is needed, saving it back with STX after use.
; ---------------------------------------------------------------

SRCPTR: .equ 0x80          ; direct-page scratch: source pointer (2 bytes)
DSTPTR: .equ 0x82          ; direct-page scratch: dest pointer   (2 bytes)
BUFFER: .equ 0x90          ; direct-page destination buffer
CKSUM:  .equ 0xA0          ; direct-page checksum byte
MSGLEN: .equ 13

        .org 0x1000

start:
        LDS #0x8000         ; immediate 16-bit -- set up the stack pointer
        LDAA #0x00
        STAA CKSUM           ; direct

        LDX #msg             ; extended-valued immediate 16-bit
        STX SRCPTR            ; direct
        LDX #BUFFER
        STX DSTPTR
        LDAB #MSGLEN          ; loop counter kept in B (idiomatic on a
                               ; CPU with no direct-page DEC/INC... see below)
copyloop:
        LDX SRCPTR
        LDAA ,X                ; indexed, offset 0
        ADDA CKSUM              ; direct
        STAA CKSUM
        INX
        STX SRCPTR

        LDX DSTPTR
        STAA 0,X                ; indexed, offset 0 (explicit form)
        INX
        STX DSTPTR

        DECB                     ; inherent -- NEG/COM/.../DEC/INC have no
        BNE copyloop              ; direct-page form on real MC6800 hardware,
                                    ; so a memory byte counter would need
                                    ; DEC >CKSUM (forced extended) instead

        LDAA CKSUM
        CMPA #0x00
        BEQ empty                  ; relative, forward (not taken here)
        BSR announce                ; relative subroutine call
        JMP forever

announce:
        PSHA                        ; save A around the call
        LDAB #0x07                   ; bell character, just to touch LDAB #
        TBA                            ; B -> A
        PULA                            ; demonstrate PSHA/PULA pairing
        RTS

empty:
        SWI

forever:
        BRA forever

; --- a short tour of the remaining addressing modes ---
modes:
        LDAA <BUFFER            ; forced direct
        LDAA >BUFFER             ; forced extended (3 bytes even though
                                   ; BUFFER fits in a direct-page address)
        LDX 0x1234                 ; extended (auto: value > 0xff)
        CPX #0x2000                  ; 16-bit immediate compare
        BLO below                     ; alias for BCS
        ASLA                            ; accumulator shift
        ROLA
        LSL >0x1234                      ; forced extended memory shift
        NEG BUFFER,X                       ; indexed read-modify-write
        JSR subr
below:
        NOP

subr:   RTS

table:  FCB 0x01,0x02,0x03,0xFF
vector: FDB start,forever
pad:    RMB 4

msg:    .ascii "HELLO, 6800!!"
