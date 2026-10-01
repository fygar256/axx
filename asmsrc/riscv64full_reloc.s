; ===================================================================
; riscv64full_reloc.s -- relocation test for riscv64full.axx
;
; Every instruction-field relocation the pattern file declares, against
; an external symbol, so the object shows the whole set:
;
;   R_RISCV_CALL_PLT      call / tail ext
;   R_RISCV_HI20          lui   a0,%hi(ext)
;   R_RISCV_LO12_I        addi / load / jalr with %lo(ext)
;   R_RISCV_LO12_S        store with %lo(ext)
;   R_RISCV_BRANCH        beq ... ext
;   R_RISCV_JAL           j / jal ext
;   R_RISCV_RVC_BRANCH    c.beqz / c.bnez ext
;   R_RISCV_RVC_JUMP      c.j ext
;   R_RISCV_GOT_HI20      auipc a0,%got_pcrel_hi(ext)
;   R_RISCV_TLS_GOT_HI20  auipc a0,%tls_ie_pcrel_hi(ext)
;   R_RISCV_TLS_GD_HI20   auipc a0,%tls_gd_pcrel_hi(ext)
;   R_RISCV_TPREL_HI20    lui   a0,%tprel_hi(ext)
;   R_RISCV_TPREL_LO12_I  / _S   %tprel_lo(ext)
;   R_RISCV_PCREL_HI20    auipc a0,%pcrel_hi(ext)
;   R_RISCV_PCREL_LO12_I  / _S   %pcrel_lo(label)
;   R_RISCV_64            quad  ext
;   R_RISCV_32            dword ext
;
; The pc-relative pair follows the psABI rule: the LO12 relocation
; names the label on the auipc, not the symbol being addressed.
;
;   axx riscv64full.axx riscv64full_reloc.s -o out.o
;   readelf -r out.o
;
; llvm-mc 18 gives the same entries (offset, type, symbol, addend) for
; every one of them, with `.option norvc`, except for the branches to an
; external symbol (beq ..., c.j, c.beqz, c.bnez): LLVM relaxes those
; into an inverted branch and a jal, where GNU as, like this pattern
; file, writes R_RISCV_BRANCH, R_RISCV_RVC_JUMP and R_RISCV_RVC_BRANCH.
; A program made of the same kinds of lines (the TLS ones need a TLS
; section to link) and linked with ld.lld gives an image identical to
; the one llvm-mc's object gives.
; ===================================================================

        .global _start
        .extern ext1
        .extern ext2
        .extern tlsvar
        .section .text
_start:
        call    ext1                    ; -> R_RISCV_CALL_PLT
        tail    ext2
        lui     a0,%hi(ext1)            ; -> R_RISCV_HI20
        addi    a0,a0,%lo(ext1)         ; -> R_RISCV_LO12_I
        lui     a0,%hi(ext1+16)
        addi    a1,a0,%lo(ext1+16)
        lw      a2,%lo(ext1)(a0)
        ld      a2,%lo(ext2)(a0)
        sw      a2,%lo(ext1)(a0)        ; -> R_RISCV_LO12_S
        sd      a2,%lo(ext2+4)(a0)
        flw     fa0,%lo(ext1)(a0)
        fsd     fa0,%lo(ext1)(a0)
        jalr    ra,%lo(ext1)(a0)
        andi    a0,a0,%lo(ext1)
        beq     a0,a1,ext1              ; -> R_RISCV_BRANCH
        bne     a0,a1,ext2
        bgtu    a0,a1,ext2
        beqz    a0,ext1
        j       ext1                    ; -> R_RISCV_JAL
        jal     ext2
        jal     a0,ext2
        c.j     ext1                    ; -> R_RISCV_RVC_JUMP
        c.beqz  a0,ext1                 ; -> R_RISCV_RVC_BRANCH
        c.bnez  s1,ext2
        auipc   a0,%got_pcrel_hi(ext1)          ; -> R_RISCV_GOT_HI20
        auipc   a0,%tls_ie_pcrel_hi(tlsvar)     ; -> R_RISCV_TLS_GOT_HI20
        auipc   a0,%tls_gd_pcrel_hi(tlsvar)     ; -> R_RISCV_TLS_GD_HI20
        lui     a0,%tprel_hi(tlsvar)            ; -> R_RISCV_TPREL_HI20
        addi    a0,a0,%tprel_lo(tlsvar)         ; -> R_RISCV_TPREL_LO12_I
        lw      a0,%tprel_lo(tlsvar)(a1)
        sw      a0,%tprel_lo(tlsvar)(a1)        ; -> R_RISCV_TPREL_LO12_S
        ld      a0,%tprel_lo(tlsvar)(a1)
        sd      a0,%tprel_lo(tlsvar)(a1)
pc1:    auipc   a0,%pcrel_hi(ext1)              ; -> R_RISCV_PCREL_HI20
        addi    a0,a0,%pcrel_lo(pc1)            ; -> R_RISCV_PCREL_LO12_I
pc2:    auipc   a0,%pcrel_hi(ext2+4)
        ld      a0,%pcrel_lo(pc2)(a0)
pc3:    auipc   a0,%pcrel_hi(ext1)
        sd      a0,%pcrel_lo(pc3)(a0)           ; -> R_RISCV_PCREL_LO12_S

        .section .data
        quad    ext1                    ; -> R_RISCV_64
        quad    ext2+8
        dword   ext1                    ; -> R_RISCV_32
        dword   ext2+12
