; ===================================================================
; as_unord.s -- test source for as_unord.axx (`.as` in .unordered)
;
;   ld  b,c        41
;   ld  a,e        7b
;   jp  c,0x1234   da 34 12     C is the carry condition for k
;   jp  nz,0x10    c2 10 00
; ===================================================================
        ld      b,c
        ld      a,e
        jp      c,0x1234
        jp      nz,0x10
