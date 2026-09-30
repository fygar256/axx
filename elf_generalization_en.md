# Generalizing the ELF output

axx's ELF object output (`-o`) has been widened from the eleven machines in the
built-in table to **any CPU**. The goal is to write a linkable relocatable
object (`.o`) for any CPU, and that has two halves.

- **The machine-dependent half** — the relocation types, the ELF class,
  RELA/REL, the ELF header fields and the section header attributes. These are
  declared in the pattern file (section 2). So are **instruction-field types** —
  types whose value sits in bit fields of an instruction word — with
  `.elffield`, for any machine.
- **The machine-independent half** — the type, size, binding and visibility of
  each symbol. These fields have the same shape on every machine, but a linker
  acts on them, so an object whose symbol table is all defaults is not linkable.
  These are declared in the source (section 3).

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

A complete machine description is still not an object a linker will take. Every
symbol came out as `STT_NOTYPE`, size 0, visibility `STV_DEFAULT`, so an ARM /
AArch64 linker — which reads `STT_FUNC` to decide where a veneer is needed —
could not find a function entry, `--gc-sections` had no size to keep a symbol
by, and there was no way to write a weak symbol at all. The symbol table can
carry machine-specific meaning too: the PowerPC64 ELFv2 local-entry offset lives
in bits 5-7 of `st_other`. Filling those fields in from the source is the other
half of this work (section 3).

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
| `.elfsection::<name>::<sh_flags>[::<sh_type>[::<align>[::<entsize>]]]` | the attributes of a section header |
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
- The width of `.elfwidth` is any of 1 to 8. Widths that are not powers of two
  are accepted because on a machine whose word is not 8 bits (`.bits`) the width
  of a reference is a multiple of the bytes per word: a three-word reference on a
  12-bit machine is 6 bytes. Even on an 8-bit machine some ISAs have a 3-byte
  field (`R_MN10300_24`, for one).

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
.elfsection::.rodata.str1.1::0x32::1::1::1
                                     /* ALLOC+MERGE+STRINGS, entsize 1   */
```

A machine's own vector table, an uninitialised region that is not called
`.bss`, a note section, a string table the linker handles element by element —
this is what writes those. The section name is matched
without regard to case, as a whole name. With no `sh_type` written, the type
stays the one the name rule gives. A section made `SHT_NOBITS` carries only its
`sh_size`; its contents are not written to the file. The fourth field is
`sh_addralign`. It must be 0 or a power of two (the ELF requirement); anything
else is diagnosed and the declaration ignored.

The fifth field is `sh_entsize` — the size in bytes of one element, for a section
that is an array of fixed-size elements. It is 0 (no fixed-size element) when not
written. A section with `SHF_MERGE` (0x10) set requires a non-zero value, since
the linker cannot fold duplicates without knowing how wide an element is; for a
string table (`SHF_MERGE|SHF_STRINGS`, 0x30) it is 1.

There is no field for `sh_link` or `sh_info`. In a relocatable object the only
sections where those two mean anything are `.rela.*` and `.symtab`, both of which
axx builds itself and fills with the right section numbers.

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
instruction-set file (section 8, PowerPC64, is built that way).

---

## 3. The declarations (source file) — the symbol table attributes

Besides a name and an address, the symbol table `-o` writes carries a **type, a
size, a binding and a visibility**. All four have the same shape on every
machine, so they do not belong in the machine description (section 2). A linker
nonetheless acts on them.

- No ARM / AArch64 veneer is built for a symbol that is not `STT_FUNC`, so a call
  too far to reach becomes a link error.
- A symbol of size 0 gives `--gc-sections` no extent to keep, so it cannot be
  kept.
- Without a weak binding (`STB_WEAK`) there is no way to build the library-side
  object whose default implementation another definition may override.
- Without `SHN_COMMON` symbols the ordinary idiom — declaring the same variable
  in several objects and letting the linker fold them into one — cannot be
  written.
- The high bits of `st_other` carry machine-specific meaning: the PowerPC64
  ELFv2 local-entry offset is in bits 5-7.

So there are now declarations that fill the symbol table fields in from the
source. They are source directives, following axx's division of labour: the
pattern file describes the machine, the source describes the program.

| Declaration | What it sets |
|---|---|
| `.type <name>::<kind>` | the type field of `st_info` (`STT_*`) |
| `.size <name>::<expr>` | `st_size` |
| `.weak <name>` | makes the binding `STB_WEAK` |
| `.hidden <name>` / `.protected <name>` / `.internal <name>` | the visibility in `st_other` (`STV_*`) |
| `.other <name>::<value>` | the `st_other` byte itself |
| `.comm <name>::<size>[::<align>]` | an `SHN_COMMON` symbol |

Rules they share:

- Each takes a comma-separated list: `name1::…, name2::…`. The `::` after a name
  is the same separator as in `.extern name::type`.
- A declaration may be written anywhere, though as with `.extern` it is safest
  before the references. The attributes affect the output only, so no address
  moves.
- A symbol with no declaration is written as before: `STT_NOTYPE`, size 0,
  visibility `STV_DEFAULT`.

### 3.1 The kinds `.type` takes

Either a name or a number (0-15). Names are matched without regard to case.

| Kind | `STT_*` | Where it is used |
|---|---|---|
| `notype` | 0 | says nothing about the type (the default) |
| `object` | 1 | data |
| `func` (`function`) | 2 | the entry point of a function |
| `section` | 3 | a section symbol |
| `file` | 4 | a file-name symbol |
| `common` | 5 | a common symbol |
| `tls` (`tls_object`) | 6 | thread-local data |
| `gnu_ifunc` (`ifunc`) | 10 | a GNU indirect function |

### 3.2 `.size` — the value is a word count

Like a label's value it is multiplied by the bytes per word before it goes into
`st_size`. On an 8-bit machine (the `.bits` default) the multiplier is 1, so the
number goes in as written. The usual form is the difference against a label
placed at the end of the function.

```
func:
        ...
func_end:
        .size   func::func_end-func
```

### 3.3 `.weak` — it passes the name out

If the name is defined in this file, it is exported exactly as `.global` does,
with only the binding weakened. A name not yet known is registered exactly as an
`.extern` with no type name — which is why writing `.weak maybe` alone gives a
weak reference, one that becomes 0 if it is never resolved.

A symbol declared `.weak` always lands in the global part of the symbol table. It
has to: ELF does not allow a local symbol to be weak.

### 3.4 `.other` — it replaces the whole byte

The low 2 bits are the visibility (`STV_*`), the high 6 are machine-specific. A
visibility declaration such as `.hidden` rewrites only the low 2 bits, so writing
a visibility after `.other` keeps the high bits; written the other way round,
`.other` overwrites the visibility.

### 3.5 `.comm` — common symbols

Writes an `SHN_COMMON` symbol. The linker creates the storage, so this object
holds none itself. `st_value` becomes the alignment (in bytes, 1 if not written,
and 0 or a power of two) and `st_size` the size (the word count times the bytes
per word). The type is made `STT_OBJECT` unless `.type` says otherwise, as in GNU
as. The name is registered as an external symbol just as `.extern` does, so it
can be referenced directly and relocations are emitted against that name.

### 3.6 A worked example

The declarations are ordinary source lines (the machine is described the way
section 6 describes one; the bundled `elfsym.axx` describes EM_MN10300(89)).

```
        .extern printf                  ; an ordinary external reference
        .weak   maybe                   ; a weak reference: undefined is ok
        .comm   sharedbuf::64::8        ; 64 words, aligned to 8 bytes

        .global func
        .type   func::func
        .other  func::0x60              ; st_other written out as a byte

        .weak   altentry                ; a weak definition
        .type   altentry::func

        .type   helper::func            ; stays local: not in the global part
        .internal helper

        .global datum
        .type   datum::object
        .size   datum::4
        .protected datum

        .section .text
func:
altentry:
        nop
        dd      printf
        dt      datum                   ; a 3-byte field -> R_MN10300_24
        dw      datum
        db      datum
        ret
func_end:
        .size   func::func_end-func

helper:
        nop
        ret

        .section .data
datum:
        dd      sharedbuf
        dd      maybe
```

Under `readelf -s`:

```
   Num:    Value  Size Type    Bind   Vis      Ndx Name
     0: 00000000     0 NOTYPE  LOCAL  DEFAULT  UND
     1: 00000000     0 SECTION LOCAL  DEFAULT    1 .text
     2: 00000000     0 SECTION LOCAL  DEFAULT    2 .data
     3: 0000000c     0 NOTYPE  LOCAL  DEFAULT    1 func_end
     4: 0000000c     0 FUNC    LOCAL  INTERNAL    1 helper
     5: 00000000     0 NOTYPE  WEAK   DEFAULT  UND maybe
     6: 00000000     0 NOTYPE  GLOBAL DEFAULT  UND printf
     7: 00000008    64 OBJECT  GLOBAL DEFAULT  COM sharedbuf
     8: 00000000     0 FUNC    WEAK   DEFAULT    1 altentry
     9: 00000000     4 OBJECT  GLOBAL PROTECTED    2 datum
    10: 00000000    12 FUNC    GLOBAL DEFAULT [<other>: 60]     1 func
```

`func` is `STT_FUNC` with size 12 and the `st_other` byte written as 0x60;
`altentry` is a weak definition at the same address; `helper` stays local and
`STV_INTERNAL`; `sharedbuf` is `SHN_COMMON` (`Ndx COM`) with `st_value` the
alignment 8 and `st_size` 64; `maybe` is a weak reference left undefined.

The bundled `elfsym.axx` / `elfsym.s` are the worked example in the tree. Its
machine is EM_MN10300(89), which is not in the built-in table, and it also shows
the field width that is not a power of two (`.elfwidth::3` → `R_MN10300_24`) and
the section element size (the fifth field of `.elfsection`).

This was checked against a real linker. An object using the same declarations for
x86-64 passes through GNU ld's `-r` with its types, sizes, weak bindings,
visibilities and common symbols intact, and a full link gives the common symbol a
real address and resolves the relocations against it.

---

## 4. How this relates to `-m` and `-f`

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

## 5. When a declaration is missing

The rule throughout is **never quietly write a broken `.o`**.

- A reference whose type cannot be determined gets no relocation entry, rather
  than a guessed type number. `-d` lists the places that were skipped.
- Writing `-o` with an `-m` outside the built-in table warns about exactly this.
- A type name in `.elfwidth` / `.elfextern` / `.elfdwarf` / `.elffield` that does not resolve
  is reported once, after the declarations have all been collected, so that a
  misspelling is not silently skipped.
- The `-g` DWARF sections are written only when the absolute type is known, from
  `.elfdwarf` or the built-in table.
- An ELF32 `r_info` has only an 8-bit type field. `.elftype` accepts numbers up
  to 2147483647, so a type above 255 declared for ELF32 would be truncated — and
  a truncated number **becomes a different type**, which a linker applies wrongly
  with no diagnostic of its own. Each such type is reported once (and so is a
  symbol index that does not fit the 24-bit field).

The width guess does one more thing. When the type it guessed is PC-relative but
the field turns out to hold the label's absolute value, the type is replaced by
the absolute type of the same width. The replacement is found by scanning the
effective table from the top for a type of that width that is not PC-relative —
no machine number and no type number is built in. On the eleven built-in
machines `abs64` / `abs32` / `abs16` / `abs8` head their tables, so the type
found is the one that was used before, and a machine declared in a pattern file
resolves it in `.elftype` declaration order.

---

## 6. A worked example — EM_MSP430 (105)

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

## 7. The relocation type priority

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

## 8. A worked example — PowerPC64 (21)

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
