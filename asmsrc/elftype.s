; ===================================================================
; elftype.s -- test source for elftype.axx (x86-64, -m 62)
;
; Every relocation below is typed by a name that `.elftype` defined in
; the pattern file, in each of the three places a type name can be
; written. The expected relocations are
;
;   ext1  R_X86_64_GOTPCRELX     41 (.reloc / .extern)
;   ext2  R_X86_64_REX_GOTPCRELX 42 (.reloc / .extern)
;   here  R_X86_64_TPOFF32       23 (.reloc / .global)
;   plain R_X86_64_REX_GOTPCRELX 42 (.global alone -- no .reloc)
;
;   axx elftype.axx elftype.s -o out.o -m 62
;   axx elftype.axx elftype.s -o out.o -m 62 -E exp.tsv
; ===================================================================

        .extern ext1::gotpcrelx         ; an .elftype name in .extern
        .extern ext2::REXGOTPCRELX      ; the name is case-insensitive
        .global here::tpoff32           ; an .elftype name in .global
        .global plain::rexgotpcrelx

here:
        callx   ext1                    ; .reloc::t::GotPcRelX
        movx    ext2                    ; .reloc::t::rexgotpcrelx
plain:
        tpoff   here                    ; .reloc::t::tpoff32
        dd      plain                   ; no .reloc: .global decides
        ret
