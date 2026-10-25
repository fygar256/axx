\ elfmach.fs -- 組み込みの ELF マシン表 (axx.py の _ELF_MACHINE_RAW から機械的に生成)

decimal

\ 基盤の語: 現在の表 (mt-*) へ書き込む。b-named は ( name-a name-u rt width -- )
: base-3 ( -- )
  s" i386" b-name  1 b-class  0 b-rela
  4 2 b-wg
  2 20 b-wg
  1 22 b-wg
  2 b-pc
  4 b-pc
  13 b-pc
  21 b-pc
  23 b-pc
  2 b-ext  1 b-dwarf  0 b-pcg
  s" abs32" 1 4 b-named
  s" pc32" 2 4 b-named
  s" rel32" 2 4 b-named
  s" got32" 3 4 b-named
  s" plt32" 4 4 b-named
  s" gotoff" 9 4 b-named
  s" gotpc" 10 4 b-named
  s" abs16" 20 2 b-named
  s" pc16" 21 2 b-named
  s" abs8" 22 1 b-named
  s" pc8" 23 1 b-named
;
: base-4 ( -- )
  s" m68k" b-name  1 b-class  1 b-rela
  4 4 b-wg
  2 2 b-wg
  1 3 b-wg
  4 b-pc
  5 b-pc
  6 b-pc
  4 b-ext  1 b-dwarf  1 b-pcg
  s" abs32" 1 4 b-named
  s" abs16" 2 2 b-named
  s" abs8" 3 1 b-named
  s" pc32" 4 4 b-named
  s" rel32" 4 4 b-named
  s" pc16" 5 2 b-named
  s" pc8" 6 1 b-named
;
: base-20 ( -- )
  s" PowerPC" b-name  1 b-class  1 b-rela
  4 26 b-wg
  2 4 b-wg
  10 b-pc
  26 b-pc
  26 b-ext  1 b-dwarf  0 b-pcg
  s" abs32" 1 4 b-named
  s" abs16" 3 2 b-named
  s" abs16lo" 4 2 b-named
  s" abs16hi" 5 2 b-named
  s" abs16ha" 6 2 b-named
  s" pc32" 26 4 b-named
  s" rel32" 26 4 b-named
  s" pc24" 10 4 b-named
  s" rel24" 10 4 b-named
;
: base-21 ( -- )
  s" PowerPC64" b-name  2 b-class  1 b-rela
  8 38 b-wg
  4 26 b-wg
  2 4 b-wg
  10 b-pc
  26 b-pc
  44 b-pc
  26 b-ext  38 b-dwarf  0 b-pcg
  s" abs64" 38 8 b-named
  s" abs32" 1 4 b-named
  s" abs16" 3 2 b-named
  s" abs16lo" 4 2 b-named
  s" abs16hi" 5 2 b-named
  s" abs16ha" 6 2 b-named
  s" pc64" 44 8 b-named
  s" rel64" 44 8 b-named
  s" pc32" 26 4 b-named
  s" rel32" 26 4 b-named
  s" pc24" 10 4 b-named
  s" rel24" 10 4 b-named
;
: base-22 ( -- )
  s" s390x" b-name  2 b-class  1 b-rela
  8 22 b-wg
  4 5 b-wg
  2 3 b-wg
  1 1 b-wg
  5 b-pc
  16 b-pc
  23 b-pc
  5 b-ext  22 b-dwarf  0 b-pcg
  s" abs64" 22 8 b-named
  s" abs32" 4 4 b-named
  s" abs16" 3 2 b-named
  s" abs8" 1 1 b-named
  s" pc64" 23 8 b-named
  s" pc32" 5 4 b-named
  s" rel32" 5 4 b-named
  s" pc16" 16 2 b-named
;
: base-40 ( -- )
  s" ARM" b-name  1 b-class  0 b-rela
  4 3 b-wg
  2 5 b-wg
  1 8 b-wg
  1 b-pc
  3 b-pc
  3 b-ext  2 b-dwarf  0 b-pcg
  s" abs32" 2 4 b-named
  s" pc24" 1 4 b-named
  s" pc32" 3 4 b-named
  s" rel32" 3 4 b-named
  s" abs16" 5 2 b-named
  s" abs12" 6 4 b-named
  s" abs8" 8 1 b-named
;
: base-42 ( -- )
  s" SuperH" b-name  1 b-class  1 b-rela
  4 2 b-wg
  2 b-pc
  2 b-ext  1 b-dwarf  0 b-pcg
  s" abs32" 1 4 b-named
  s" pc32" 2 4 b-named
  s" rel32" 2 4 b-named
;
: base-43 ( -- )
  s" SPARCV9" b-name  2 b-class  1 b-rela
  8 32 b-wg
  4 6 b-wg
  2 2 b-wg
  1 1 b-wg
  4 b-pc
  5 b-pc
  6 b-pc
  46 b-pc
  6 b-ext  32 b-dwarf  0 b-pcg
  s" abs64" 32 8 b-named
  s" abs32" 3 4 b-named
  s" abs16" 2 2 b-named
  s" abs8" 1 1 b-named
  s" pc64" 46 8 b-named
  s" rel64" 46 8 b-named
  s" pc32" 6 4 b-named
  s" rel32" 6 4 b-named
  s" pc16" 5 2 b-named
  s" pc8" 4 1 b-named
;
: base-62 ( -- )
  s" x86-64" b-name  2 b-class  1 b-rela
  8 1 b-wg
  4 2 b-wg
  2 12 b-wg
  1 14 b-wg
  2 b-pc
  4 b-pc
  9 b-pc
  13 b-pc
  15 b-pc
  24 b-pc
  2 b-ext  1 b-dwarf  0 b-pcg
  s" abs64" 1 8 b-named
  s" abs32" 10 4 b-named
  s" abs32s" 11 4 b-named
  s" abs16" 12 2 b-named
  s" abs8" 14 1 b-named
  s" pc32" 2 4 b-named
  s" rel32" 2 4 b-named
  s" plt32" 4 4 b-named
  s" pc16" 13 2 b-named
  s" pc8" 15 1 b-named
  s" pc64" 24 8 b-named
  s" got32" 3 4 b-named
  s" gotpcrel" 9 4 b-named
  s" got64" 27 8 b-named
;
: base-183 ( -- )
  s" AArch64" b-name  2 b-class  1 b-rela
  8 257 b-wg
  4 261 b-wg
  2 262 b-wg
  260 b-pc
  261 b-pc
  262 b-pc
  261 b-ext  257 b-dwarf  0 b-pcg
  s" abs64" 257 8 b-named
  s" abs32" 258 4 b-named
  s" abs16" 259 2 b-named
  s" pc64" 260 8 b-named
  s" rel64" 260 8 b-named
  s" pc32" 261 4 b-named
  s" rel32" 261 4 b-named
  s" pc16" 262 2 b-named
  s" rel16" 262 2 b-named
  s" movw_uabs_g0" 263 4 b-named
  s" movw_uabs_g0_nc" 264 4 b-named
  s" movw_uabs_g1" 265 4 b-named
  s" movw_uabs_g1_nc" 266 4 b-named
  s" movw_uabs_g2" 267 4 b-named
  s" movw_uabs_g2_nc" 268 4 b-named
  s" movw_uabs_g3" 269 4 b-named
  s" movw_prel_g0" 287 4 b-named
  s" movw_prel_g0_nc" 288 4 b-named
  s" movw_prel_g1" 289 4 b-named
  s" movw_prel_g1_nc" 290 4 b-named
  s" movw_prel_g2" 291 4 b-named
  s" movw_prel_g2_nc" 292 4 b-named
  s" movw_prel_g3" 293 4 b-named
  s" ld_prel_lo19" 273 4 b-named
  s" adr_prel_lo21" 274 4 b-named
  s" adr_prel_pg_hi21" 275 4 b-named
  s" adrp" 275 4 b-named
  s" adr_prel_pg_hi21_nc" 276 4 b-named
  s" add_abs_lo12_nc" 277 4 b-named
  s" ldst8_abs_lo12_nc" 278 4 b-named
  s" tstbr14" 279 4 b-named
  s" condbr19" 280 4 b-named
  s" jump26" 282 4 b-named
  s" call26" 283 4 b-named
  s" ldst16_abs_lo12_nc" 284 4 b-named
  s" ldst32_abs_lo12_nc" 285 4 b-named
  s" ldst64_abs_lo12_nc" 286 4 b-named
  s" ldst128_abs_lo12_nc" 299 4 b-named
  s" got_ld_prel19" 309 4 b-named
  s" got_page" 311 4 b-named
  s" adr_got_page" 311 4 b-named
  s" got_lo12" 312 4 b-named
  s" ld64_got_lo12_nc" 312 4 b-named
  s" ld64_gotpage_lo15" 313 4 b-named
  263 2097120 0 0 0 b-field
  264 2097120 0 0 0 b-field
  265 2097120 0 0 0 b-field
  266 2097120 0 0 0 b-field
  267 2097120 0 0 0 b-field
  268 2097120 0 0 0 b-field
  269 2097120 0 0 0 b-field
  287 2097120 0 0 0 b-field
  288 2097120 0 0 0 b-field
  289 2097120 0 0 0 b-field
  290 2097120 0 0 0 b-field
  291 2097120 0 0 0 b-field
  292 2097120 0 0 0 b-field
  293 2097120 0 0 0 b-field
  274 1627389920 0 0 0 b-field
  275 1627389920 0 0 0 b-field
  276 1627389920 0 0 0 b-field
  277 4193280 0 0 0 b-field
  278 4193280 0 0 0 b-field
  273 16777184 0 0 0 b-field
  279 524256 0 0 0 b-field
  280 16777184 0 0 0 b-field
  282 67108863 0 0 0 b-field
  283 67108863 0 0 0 b-field
  284 4193280 0 0 0 b-field
  285 4193280 0 0 0 b-field
  286 4193280 0 0 0 b-field
  299 4193280 0 0 0 b-field
  309 16777184 0 0 0 b-field
  311 1627389920 0 0 0 b-field
  312 4193280 0 0 0 b-field
  313 4193280 0 0 0 b-field
;
: base-243 ( -- )
  s" RISC-V" b-name  2 b-class  1 b-rela
  8 2 b-wg
  4 1 b-wg
  2 34 b-wg
  1 33 b-wg
  1 b-ext  2 b-dwarf  0 b-pcg
  s" abs64" 2 8 b-named
  s" abs32" 1 4 b-named
  s" abs16" 34 2 b-named
  s" abs8" 33 1 b-named
;
: base-known? ( m -- f )  case
  3 of true endof
  4 of true endof
  20 of true endof
  21 of true endof
  22 of true endof
  40 of true endof
  42 of true endof
  43 of true endof
  62 of true endof
  183 of true endof
  243 of true endof
  false swap endcase ;
: base-load ( m -- )  case
  3 of base-3 endof
  4 of base-4 endof
  20 of base-20 endof
  21 of base-21 endof
  22 of base-22 endof
  40 of base-40 endof
  42 of base-42 endof
  43 of base-43 endof
  62 of base-62 endof
  183 of base-183 endof
  243 of base-243 endof
  endcase ;
: base-list ( -- ) 
  s" 3 (i386)" b-known+
  s" 4 (m68k)" b-known+
  s" 20 (PowerPC)" b-known+
  s" 21 (PowerPC64)" b-known+
  s" 22 (s390x)" b-known+
  s" 40 (ARM)" b-known+
  s" 42 (SuperH)" b-known+
  s" 43 (SPARCV9)" b-known+
  s" 62 (x86-64)" b-known+
  s" 183 (AArch64)" b-known+
  s" 243 (RISC-V)" b-known+
;
