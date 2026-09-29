# Generalizing the ELF output

axx's ELF object output (`-o`) has been widened from the eleven machines in the
built-in table to **any `e_machine`**. The relocation types, the ELF class,
RELA/REL and the ELF header fields can all be declared in the pattern file, and
so can **instruction-field types** — types whose value sits in bit fields of an
instruction word — with `.elffield`, for any machine.

The work is in both implementations, `axx.py` (Paxx) and `caxx.c` (Caxx), and
their output is byte-identical.

---

## 1. What changed

Until now `-o` only served the eleven machines axx carries relocation numbering
for — i386(3), m68k(4), PowerPC(20), PowerPC64(21), s390x(22), ARM(40),
SuperH(42), SPARCV9(43), x86-64(62), AArch64(183) and RISC-V(243). An `-m` with
any other number stopped with an error, on the grounds that stopping beats
mislabelling every relocation in the file with a guessed type number.

That judgement was right, but stopping was the only road available. So the
missing road is now there: a way to **not guess**. The type numbers, the field
widths and the PC-relativeness are all written by the person who does know the
machine — the author of the pattern file.

This follows on from `.elftype` (naming a relocation type yourself). Where
`.elftype` settled "name → type number", these declarations settle **where each
type is used** and **how the ELF is put together**.

---

## 2. The declarations (pattern file)

| Declaration | What it sets |
|---|---|
| `.elfmachine::<number>[::<name>]` | the `e_machine` number (and the name used in diagnostics) |
| `.elfclass::<32>` / `<64>` | the ELF class (ELF32 / ELF64) |
| `.elfrela::<1>` / `<0>` | RELA (1, also `rela`) or REL (0, `rel`) |
| `.elftype::<name>::<number>[::<width>[::<pc-relative>]]` | a relocation type (width and PC-relative fields are new) |
| `.elfwidth::<bytes>::<type>` | the default type for a reference of that width |
| `.elfextern::<type>` | the default type for `.extern` with no type name |
| `.elfdwarf::<type>` | the absolute type the `-g` DWARF output uses |
| `.elfheader::<field>::<value>` | a field of the ELF header |
| `.elfsection::<name>::<sh_flags>[::<sh_type>[::<align>]]` | the attributes of a section header |
| `.elffield::<type>::<mask>[::<offset>]` | an instruction-field type (which bits of the instruction hold the value) |

Rules they share:

- Every declaration is a difference **laid over** the built-in table selected
  with `-m`. On a machine that is in the table, only what you write is
  replaced — adding a single type name to x86-64, or only an `e_flags`, works
  just as well.
- Wherever `<type>` is written, an `.elftype` name, a built-in name, or a type
  number (decimal or `0x` hex) is accepted. Names are matched without regard to
  case.
- The declarations may be written anywhere. Like `.elftype`, they are all
  collected once the pattern file has been read, so a declaration below its
  first use still resolves.
- The width of `.elfwidth` is 1, 2, 4 or 8.

### 2.1 The `.elftype` extension

```
.elftype::abs16::2::2          /* type 2, a 2-byte field              */
.elftype::pcrel16::4::2::1     /* type 4, 2 bytes, PC-relative        */
```

The fourth field is the width in bytes of the field this type rewrites. The
addend is computed from that width, so on a machine with no built-in table,
write the width for any type that `.elfwidth` or `.elfextern` will reach. The
fifth field, when it is not 0, marks the type as PC-relative, which puts it on
the side that adds the instruction address to the addend. Both may be left out.

### 2.2 The fields `.elfheader` writes

| Field | ELF header field | Default | Range |
|---|---|---|---|
| `type` | `e_type` | 1 (`ET_REL`) | 0-0xFFFF |
| `flags` | `e_flags` | 0 | 0-0xFFFFFFFF |
| `version` | `e_version` | 1 (`EV_CURRENT`) | 0-0xFFFFFFFF |
| `entry` | `e_entry` | 0 | 0-0x7FFFFFFFFFFFFFFF |
| `osabi` | `e_ident[EI_OSABI]` | the `--osabi` value | 0-0xFF |
| `abiversion` | `e_ident[EI_ABIVERSION]` | 0 | 0-0xFF |

This is what machine-specific `e_flags` (the ARM EABI version, the RISC-V ABI
marks) are written with. A field you do not write keeps its default. The values
are constant expressions.

### 2.3 `.elfsection` — the attributes of a section header

A section's `sh_flags` and `sh_type` used to come from its name alone (`.text`
executable, `.data` and `.bss` writable, `.rodata` and anything else allocated
only, and `SHT_NOBITS` for `.bss` alone). A section the name rule does not know
came out as an allocated `SHT_PROGBITS`, with no way to change it.

```
.elfsection::.vectors::0x6           /* ALLOC+EXECINSTR, type left alone */
.elfsection::.noinit::0x3::8         /* ALLOC+WRITE, SHT_NOBITS          */
.elfsection::.note.axx::0::7         /* no flags, SHT_NOTE, align 4      */
.elfsection::.vectors2::0x6::1::2    /* alignment written out: 2         */
```

A machine's own vector table, an uninitialised region that is not called
`.bss`, a note section — this is what writes those. The section name is matched
without regard to case, as a whole name. With no `sh_type` written, the type
stays the one the name rule gives. A section made `SHT_NOBITS` carries only its
`sh_size`; its contents are not written to the file. The fourth field is
`sh_addralign`. It must be 0 or a power of two (the ELF requirement); anything
else is diagnosed and the declaration ignored.

**The default alignment.** A section with no alignment written gets 16, except
`SHT_NOTE` (7), which gets 4. A note's `sh_addralign` has to be 4 or 8, and at
16 binutils reports `Corrupt note: alignment 16, expecting 4 or 8` and cannot
read the contents. It is 4 rather than 8 even for ELF64 because a note's
`n_namesz` / `n_descsz` padding follows the alignment, and real notes such as
`.note.gnu.build-id` are written with 4 in ELF64 too. A note that needs 8
(`.note.gnu.property`) says 8 in this field.

The bundled `elfsec.axx` / `elfsec.s` are a worked example.

### 2.4 `.elffield` — instruction-field types

```
.elffield::<type>::<mask>[::<offset>]
```

A data reference holds its value as a plain integer across consecutive bytes, so
the addend is "emitted bytes - label value". A branch or address-forming
instruction instead packs the value, often scaled, into scattered bit fields of
the instruction word, and the addend cannot be read back out of the bytes.

AArch64 has types of this kind (`call26`, `adrp`, the `:lo12:` types, ...) in a
built-in table. Other machines had none, so typing a row with `.reloc` did not
give a correct relocation. `.elffield` supplies that table for any machine from
the pattern file. A row typed with `.reloc::<variable>::<type>` for a type
declared this way

- carries the addend "operand value - label value" (`bl ext+8` gives 8);
- has its instruction field written as 0, for the linker to fill in (RELA, the
  shape GNU as produces);
- leaves the range and alignment checks on that operand to the linker under
  `-o`.

The fields:

- `<mask>` is the set of bits the linker writes, within the bytes of the type's
  width (from `.elftype` or the machine's name table) read as an integer in the
  target byte order. A field split over two instruction words is one 64-bit
  mask.
- `<offset>` (default 0) is where the field starts, in bytes from the first word
  the row emits for that operand; `r_offset` points there. A 16-bit field in the
  low half of a 32-bit word is at 2 big-endian and at 0 little-endian.
- The type may be an `.elftype` name, a built-in name or a number. Writing the
  same type again replaces the earlier declaration.

```
.elftype::rel24::10::4::1
.elftype::addr16_ha::6::2
.elffield::rel24::0x03fffffc            /* PowerPC64 bl: the LI field       */
.elffield::addr16_ha::0xffff::2         /* the low halfword, big-endian     */
.elffield::pcrel34::0x0003ffff0000ffff  /* 18 prefix bits + 16 suffix bits  */

.reloc::t::rel24
BL !t :: .call w4(0x48000001|((t-$$)&0x3fffffc))
.clrreloc::t
```

On a machine whose offsets or masks depend on the byte order, writing the
`.elffield` lines in the wrapper that sets the byte order keeps a single
instruction-set file (section 7, PowerPC64, is built that way).

---

## 3. How this relates to `-m` and `-f`

| | Written | Not written |
|---|---|---|
| `-m` | that number is the target (it beats `.elfmachine`) | `.elfmachine`, failing that 62 (x86-64) |
| `-f` | that ELF class | `.elfclass`, failing that the machine's conventional class |

`-m` wins, so one pattern file can be used for more than one `e_machine`.

The default of `-f` has changed. It used to be 64 always, so choosing a 32-bit
machine produced ELF64 together with a "`-f` forced ELF64" warning. Now `-m 3`
(i386) quietly produces ELF32. An explicit `-f 32` / `-f 64` behaves exactly as
before, including honoring a combination that is not conventional for the
machine (`-m 62 -f 32`, the real x32 ABI layout) with a warning.

---

## 4. When a declaration is missing

The rule throughout is **never quietly write a broken `.o`**.

- A reference whose type cannot be determined gets no relocation entry, rather
  than a guessed type number. `-d` lists the places that were skipped.
- Writing `-o` with an `-m` outside the built-in table warns about exactly this.
- A type name in `.elfwidth` / `.elfextern` / `.elfdwarf` / `.elffield` that does not resolve
  is reported once, after the declarations have all been collected, so that a
  misspelling is not silently skipped.
- The `-g` DWARF sections are written only when the absolute type is known, from
  `.elfdwarf` or the built-in table.

The width guess does one more thing. When the type it guessed is PC-relative but
the field turns out to hold the label's absolute value, the type is replaced by
the absolute type of the same width. The replacement is found by scanning the
effective table from the top for a type of that width that is not PC-relative —
no machine number and no type number is built in. On the eleven built-in
machines `abs64` / `abs32` / `abs16` / `abs8` head their tables, so the type
found is the one that was used before, and a machine declared in a pattern file
resolves it in `.elftype` declaration order.

---

## 5. A worked example — EM_MSP430 (105)

The whole description of a machine axx has no built-in table for:

```
.bits::8

.elfmachine::105::MSP430
.elfclass::32
.elfrela::1

.elftype::abs32::1::4
.elftype::abs16::2::2
.elftype::pcrel16::4::2::1
.elftype::abs8::3::1

.elfwidth::4::abs32
.elfwidth::2::abs16
.elfwidth::1::abs8
.elfextern::abs16
.elfdwarf::abs32

.elfheader::flags::0x2a
.elfheader::abiversion::1

CALL !t :: 0xb0,0x12,t,t>>8
.reloc::t::pcrel16
JMP !t :: 0x00,0x3c,t,t>>8
.clrreloc::t
DB !t :: t
DW !t :: t,t>>8
DD !t :: t,t>>8,t>>16,t>>24
```

The source side is written as usual:

```
        .extern ext1                    ; type comes from .elfextern
        .extern ext2::abs32             ; an .elftype name
        .global start
start:
        call    ext1
        jmp     start
        dw      start
        db      start
        dd      ext2
```

`axx elfgen.axx elfgen.s -o out.o`, read back with `readelf -r`:

```
Relocation section '.rela.text' at offset 0x58 contains 5 entries:
 Offset     Info    Type            Sym.Value  Sym. Name + Addend
00000002  00000202 R_MSP430_ABS16    00000000   ext1 + 0
00000006  00000404 R_MSP430_PCR16    00000000   start + 6
00000008  00000402 R_MSP430_ABS16    00000000   start + 0
0000000a  00000403 R_MSP430_ABS8     00000000   start + 0
0000000b  00000301 R_MSP430_ABS32    00000000   ext2 + 0
```

and the header, as declared:

```
  Class:        ELF32
  ABI Version:  1
  Machine:      Texas Instruments msp430 microcontroller
  Flags:        0x2a
```

---

## 6. The relocation type priority

The type of one reference can be decided in three places. Strongest first:

| Rank | Decided in | Written as |
|---|---|---|
| high | the source file | `::<type>` on `.extern` / `.global` / `.EQU` / an import TSV, and `.reloctype` |
| middle | the pattern file | `.reloc::<variable>::<type>` |
| low | the default | guessed from the width of the field (`.elfwidth`, the machine's table) |

That is **default < pattern file < source file**: the source has the last word.

Only a type the source **wrote** counts as "the source file". A `.extern ext`
with no type name gets the default type of `.elfextern` (or the machine's
table), but that does not override a type `.reloc` gave: `bl ext` still comes
out with the `.reloc` type (`REL24` on PowerPC64), and the default is used only
for references no `.reloc` covers, such as data.

The pattern file says which type the field of that instruction normally carries;
the source says which type this one symbol takes. When both speak about the same
reference, the source wins. Where `.reloc` has said "the value sits in a bit
field of the instruction word", that knowledge and the way the addend is
computed stay as they are; only the type number is replaced.

```
.reloc::t::pcrel16              /* the pattern: this field is PC relative */
JMP !t :: 0x00,0x3c,t,t>>8
.clrreloc::t
```

```
        .extern ext::abs16      ; a symbol the source typed
        .global start
start:
        jmp     start           ->  R_MSP430_PCR16   start + 2
        jmp     ext             ->  R_MSP430_ABS16   ext + 0
        dw      start           ->  R_MSP430_ABS16   start + 0
```

One caution. In a pattern file that types with `.reloc` the instructions which
refer to one symbol under two types — the AArch64 `adrp` / `add` pair — do not
write `::<type>` on that symbol in the source: both instructions would then take
that one type. A type that belongs to the operand position belongs in the
pattern file alone.

The bundled `elfprio.axx` / `elfprio.s` are a worked example.

---

## 7. A worked example — PowerPC64 (21)

This one lays declarations over a machine that is in the built-in table. The
bundled `patfile/ppc64.axx` (big-endian, ELFv1) and `patfile/ppc64le.axx`
(little-endian, ELFv2) are wrappers that hold only the byte order and the ELF
description, then include the instruction set `ppc64_isa.axx`.

- `.elftype` declares the types of the 64-bit PowerPC ELF ABI with their names,
  numbers, widths and PC-relativeness, and `.elffield` gives the
  instruction-field ones their fields (`REL24`, `ADDR24`, `REL14`, `ADDR14`, the
  `ADDR16` family, `ADDR16_DS` / `_LO_DS`, `D34`, `PCREL34`). The offset of a
  16-bit field is 2 big-endian and 0 little-endian.
- Data uses `ADDR16` / `ADDR32` / `ADDR64` through `.elfwidth`, and a `.extern`
  with no type name `.elfextern::addr64`.
- `.elfsection` aligns `.text` to 64 bytes, so that the guarantee that no
  prefixed instruction crosses a 64-byte boundary survives the link. The ELFv1
  `.opd` (function descriptors) is writable data aligned to 8, and a type `toc`
  (`R_PPC64_TOC`) is provided for its TOC word.
- The little-endian wrapper sets `.elfheader::flags::2` (ELFv2).
- In the instruction set, every row with an operand that can hold a symbol is
  enclosed in `.reloc` / `.clrreloc`.

```
        .extern ext
        .global start
start:
        bl      ext+8
        addis   3,2,msg@ha
        addi    3,3,msg@l
        ld      4,msg@l(3)
        pld     5,ext@pcrel
msg:
        .quad   ext
```

`axx patfile/ppc64le.axx ex.s -o ex.o`, as `readelf -r` shows it:

```
 Offset           Type                  Sym. Name + Addend
0000000000000000  R_PPC64_REL24         ext + 8
0000000000000004  R_PPC64_ADDR16_HA     msg + 0
0000000000000008  R_PPC64_ADDR16_LO     msg + 0
000000000000000c  R_PPC64_ADDR16_LO_DS  msg + 0
0000000000000010  R_PPC64_PCREL34       ext + 0
0000000000000018  R_PPC64_ADDR64        ext + 0
```

With `ppc64.axx` (big-endian) the three 16-bit fields are at `0x6`, `0xa` and
`0xe`; the rest is the same. The instruction fields are written as 0 and the
addend goes in the RELA entry.

Checked against GNU as 2.42: for every row that refers to an external symbol, in
both byte orders, the relocations (offset, type, symbol, addend) match and the
output linked with GNU ld is identical. With ld.lld 18 the result is the same
too, apart from the rows whose types ld.lld does not implement (`ADDR24` /
`ADDR14`, `ADDR16_HIGHA`, `D34`). ld.lld handles only ELFv2 on PowerPC64, so for
big-endian write the ELFv2 form, without `.opd`.
