; ===================================================================
; riscv64full_reloc2.s -- relocations riscv64full_reloc.s does not reach
;
; Assemble with -o:  axx riscv64full.axx riscv64full_reloc2.s -o out.o
;
; 1. la / lla and the global load / store forms against an external
;    symbol and a symbol of another section: R_RISCV_PCREL_HI20 on the
;    auipc and R_RISCV_PCREL_LO12_I / _S on the second instruction,
;    against a local symbol (.Lanchor<n>) axx places on the auipc.
; 2. Data written as label-$$: an ADD/SUB pair, the label added and a
;    local symbol on the field subtracted.
; 3. Label differences: across sections (or with an external symbol)
;    an ADD/SUB pair; inside one section a constant.
;
; The relocation entries are those llvm-mc 19 (no relax) writes, apart
; from the name of the local symbol (.Lanchor<n> for .Lpcrel_hi<n> /
; .L0), and the linked image (ld.lld) is identical.
; ===================================================================
        .extern ext
        .section .text
start:
        la      a0,ext
        lla     a1,ext+8
        la      a2,dat
        lb      a3,ext
        lw      a3,ext+4
        ld      a4,dat+8
        lwu     a5,ext
        sb      a3,ext,t0
        sw      a3,ext+4,t0
        sd      a4,dat+16,t1
        flw     fa0,ext,t0
        fld     fa1,dat,t1
        fsw     fa0,ext,t2
        fsd     fa1,dat+8,t2
        ret
        .section .data
dat:
        quad    ext
        quad    ext-$$
        quad    ext-$$+8
        dword   ext-$$
        dword   ext+12-$$
        dword   start-$$
        quad    start+4-$$
        quad    ext-dat
        dword   ext-dat
        dword   start-dat
        dword   dat2-dat
        quad    dat2-dat
        dword   dat-$$
dat2:
        quad    0
