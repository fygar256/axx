# Generalizing the ELF output

axx's ELF object output (`-o`) has been widened from the eleven machines in the
built-in table to **any `e_machine`**. The relocation types, the ELF class,
RELA/REL and the ELF header fields can all be declared in the pattern file.

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
- A type name in `.elfwidth` / `.elfextern` / `.elfdwarf` that does not resolve
  is reported once, after the declarations have all been collected, so that a
  misspelling is not silently skipped.
- The `-g` DWARF sections are written only when the absolute type is known, from
  `.elfdwarf` or the built-in table.

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
