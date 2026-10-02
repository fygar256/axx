; ===================================================================
; elfword.s -- test source for elfword.axx (16-bit words, manual 3.7.10)
;
; With .elfunit::word the addends and symbol values are word counts:
;
;   j   f+3      offset 2   jmp12  f + 3
;   j   mid      offset 4   jmp12  mid + 0
;   dw  mid+1    offset 6   abs16  mid + 1
;   dd  f+5      offset 8   abs32  f + 5
;   mid          st_value 1 (the second word)
;
;   axx elfword.axx elfword.s -o out.o
; ===================================================================

        .extern f
        .global start
        .global mid

start:
        nop
mid:
        j       f+3
        j       mid
        dw      mid+1
        dd      f+5
