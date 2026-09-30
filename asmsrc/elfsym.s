; ===================================================================
; elfsym.s -- test source for elfsym.axx
;
; The ELF symbol attributes (manual 5.6.1). The expected symbol table
; is
;
;   func       GLOBAL FUNC     .text   size 12  st_other 0x60
;   altentry   WEAK   FUNC     .text   size 0
;   helper     LOCAL  FUNC     .text   size 0   INTERNAL
;   func_end   LOCAL  NOTYPE   .text   size 0
;   datum      GLOBAL OBJECT   .data   size 4   PROTECTED
;   printf     GLOBAL NOTYPE   UND     (a plain external reference)
;   maybe      WEAK   NOTYPE   UND     (a weak reference)
;   sharedbuf  GLOBAL OBJECT   COM     size 64  value 8 (the alignment)
;
; and the expected relocations in .text are
;
;   printf     R_MN10300_32   (.elfextern default, 4-byte field)
;   datum      R_MN10300_24   (.elfwidth::3 -- not a power of two)
;   datum      R_MN10300_16   (.elfwidth::2)
;   datum      R_MN10300_8    (.elfwidth::1)
;   sharedbuf  R_MN10300_32   (a common symbol)
;   maybe      R_MN10300_32   (a weak reference)
;
;   axx elfsym.axx elfsym.s -o out.o
; ===================================================================

;       declarations first, so that pass 1 already knows every name
        .extern printf                  ; an ordinary external symbol
        .weak   maybe                   ; a weak reference: undefined is ok
        .comm   sharedbuf::64::8        ; 64 words, aligned to 8 bytes

        .global func
        .type   func::func              ; STT_FUNC
        .other  func::0x60              ; st_other written out as a byte

        .weak   altentry                ; a weak definition
        .type   altentry::func

        .type   helper::func            ; local, so it stays out of the
        .internal helper                ; global part of the symbol table

        .global datum
        .type   datum::object           ; STT_OBJECT
        .size   datum::4
        .protected datum

        .section .text
func:
altentry:
        nop
        dd      printf                  ; .elfextern -> abs32
        dt      datum                   ; .elfwidth::3 -> abs24
        dw      datum                   ; .elfwidth::2 -> abs16
        db      datum                   ; .elfwidth::1 -> abs8
        ret
func_end:
        .size   func::func_end-func     ; the size of what was just emitted

helper:
        nop
        ret

        .section .data
datum:
        dd      sharedbuf               ; a reference to the common symbol
        dd      maybe                   ; a reference to the weak symbol

        .section .rodata.str1.1
        .asciz  "axx"
