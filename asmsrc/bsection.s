; bsection.s -- branches in a section that is not the first, under -b
;
; Assemble with:  axx x86_64.axx bsection.s -b out.bin
;
; With -b the sections are laid out one after another in a flat image,
; and a branch is counted between the real addresses: here .text comes
; after two bytes of .data, and is entered again after more data. (axx
; once counted $$ from the start of the section inside a binary_list
; while the label held its address in the image, and these branches
; came out two or three bytes off.)
        .section .data
        db      1
        db      2
        .section .text
        nop
loopa:
        nop
        jmp     loopa
        call    loopa
        .section .data
        db      3
        .section .text
        jmp     loopa
        call    loopb
loopb:
        ret
