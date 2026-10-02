# Generalizing the ELF output — how axx's `-o` works

axx's `-o` writes a linkable relocatable object (an `ET_REL` `.o`) for **any
CPU**. What it takes to build the ELF falls into two parts, written in two
places.

- **What depends on the machine** — the relocation types, the ELF class,
  RELA/REL, the ELF header fields, the section header attributes, the shape of
  fields inside instruction words, paired and companion relocations, the layout
  of `r_info`, the unit of addends, section groups, the CIE fields of the CFI.
  These are declared in the **pattern file** (section 2).
- **What depends on the program** — the type, size, binding and visibility of
  each symbol, common symbols, and each function's CFI (`.cfi_*`). These are
  declared in the **source file** (sections 3 and 2.14).

axx carries built-in tables for eleven machines, but a table is nothing more
than pattern-file declarations written in advance. The code that writes the ELF
has no branch on the machine number, and every entry of a table can be written
as a declaration (section 5).

Both implementations, `axx.py` (Paxx) and `caxx.c` (Caxx), write the same ELF
byte for byte from the same input.

---

## 1. How it works

The ELF of `-o` is built in five stages.

### 1.1 Building the machine description

The built-in table of the `-m` number (failing that `.elfmachine`, failing that
62) is the base, and the pattern file's `.elf*` declarations are laid over it to
make the *effective table*.

- A declared type wins over a table type of the same name; types not in the
  table are added.
- With `.elfbuiltin::0` the base is an empty table and only the declarations
  remain.
- Type names in declarations are kept as spelled until the pattern file has been
  read, and resolved to numbers when the effective table is built. That is why a
  declaration may come after its use.
- The effective table is cached under the key (machine number, declaration
  generation). Every new declaration advances the generation, so a stale table
  never survives.

What the effective table holds:

| Entry | Contents | Declaration |
|---|---|---|
| name | the machine name used in diagnostics | `.elfmachine` |
| class | ELF32 / ELF64 | `.elfclass` |
| RELA / REL | where addends go | `.elfrela` |
| types | name → number, number → field width, the set of PC-relative types | `.elftype` |
| width guess | field width → default type | `.elfwidth` |
| external default | the type of `.extern` with no type name | `.elfextern` |
| DWARF type | the absolute type of `-g` | `.elfdwarf` |
| PC-relative guess | whether an absolute type may become PC-relative | `.elfpcguess` |
| instruction fields | type → (mask, offset, shift, bias) | `.elffield` |
| write-back functions | type → function name (REL) | `.elfencode` |
| companions | type → [(companion type, keeps the symbol)] | `.elfextra` |
| label sums and differences | width → (add type, subtract type), type → (add type, subtract type) | `.elfdiff` |
| `r_info` function | function name | `.elfrinfo` |
| unit | byte / word | `.elfunit` |
| CFI | the CIE fields, initial instructions, register names | `.elfcfi`, `.elfcfiinit`, `.elfcfireg` |

### 1.2 Tracking references

While pass 2 assembles a line, axx records which output word came from which
label.

- When a pattern variable (`!t` and the like) captures a source operand, the
  labels its expression referenced are bound to the variable: one label is that
  label; two or more labels with `.elfdiff` declared are a candidate sum and
  difference of labels; anything else is *ambiguous*.
- A candidate is settled by reading each label's sign from the captured text. If
  the expression is made of labels, numbers, `+`, `-` and parentheses, and every
  label's coefficient is +1 or -1, it is a sum and difference; otherwise it is
  ambiguous. A `-` before parentheses negates what is inside. A single label with
  a negative sign is a sum and difference of one subtracted term when `.elfdiff`
  is declared, and ambiguous otherwise.
- When a `binary_list` element uses the variable, the label is recorded at that
  output word. A variable under `.reloc::<variable>::<type>` also records the type
  and "operand value - label value" (the instruction-field hint).
- Everything a failed matching attempt recorded is rolled back.

At the end of the line, consecutive words pointing at the same label become one
field. A word on which different labels overlap is dropped as ambiguous.

### 1.3 Choosing the type

Each field's type is decided in this order (strongest first).

| Rank | Where | How |
|---|---|---|
| strong | source file | `::<type name>` on `.extern` / `.global` / `.EQU` / an imported TSV, `.reloctype` |
| middle | pattern file | `.reloc::<variable>::<type name>` |
| weak | default | the guess from the field's byte width (`.elfwidth`, the effective table) |

- The default type of an `.extern ext` written without a type name
  (`.elfextern`) does not count as "the source file": it does not override the
  type `.reloc` gives, and applies only to references with no `.reloc` (data and
  the like).
- When the source's type wins over `.reloc`'s, what `.reloc` says about the value
  sitting in a bit field of the instruction, and how its addend is found, still
  holds; only the type number changes.
- If the type guessed from the width is PC-relative but the field holds the
  label's own value, it is swapped for the absolute type of the same width.
  Conversely, on a machine with `.elfpcguess::1`, a guessed absolute type whose
  field does not hold the label's value is swapped for the PC-relative type of
  the same width. The replacement is the first type of the effective table, in
  declaration order, with the same width and the opposite PC-relativity.
- A field whose type cannot be decided gets no relocation (`-d` reports it).

### 1.4 Finding the addend

The addend is found in words and then converted to the unit of `.elfunit`
(times the bytes per word for `byte`, unchanged for `word`).

| Kind of field | Addend | The field itself (RELA) |
|---|---|---|
| data, absolute type | field value - label value | the field value |
| data, PC-relative type | field value - label value + field position (from the section start) | the field value |
| instruction field (a `.elffield` type) | operand value - label value + bias | the mask bits zeroed |
| label sum and difference (`.elfdiff`, width) | the first add type: the constant part; the rest: 0 | 0 |
| label sum and difference (`.elfdiff`, type) | the same (the constant part is operand value - the sum and difference) | the mask bits zeroed with `.elffield`, else the assembled value |

A field value is the field's words read as one integer in the target byte order
and sign-extended at the field's width.

### 1.5 Writing it out

Sections, the symbol table, relocations and (with `-g`) DWARF are built and
written.

- **Sections** — `.elfsection` wins over the name rules (`.text` executable,
  `.data` and `.bss` writable, `.bss` `SHT_NOBITS`, the rest allocated only).
  `sh_link` / `sh_info` come from `.elflink`. The position in the file follows
  `sh_addralign` (with 16 as the floor).
- **Section groups** — `.elfgroup` groups come first in the section header table
  (before their members); the members and their relocation sections get
  `SHF_GROUP`.
- **Symbol table** — section symbols, local symbols, external references, then
  exported symbols. Values are positions from the section start, in the unit of
  `.elfunit`. Type, size, binding and visibility come from the source's
  declarations (section 3).
- **Relocations** — each entry is followed by its `.elfextra` companions at the
  same offset. Under RELA the addend goes in the entry. Under REL it is written
  back into the field: by the `.elfencode` function, failing that by the mask
  and shift of `.elffield`, failing that as an integer of the field's width.
  When several entries share an offset, only the first writes back.
- **`r_info`** — the `.elfrinfo` function, or else the ELF default
  (`(symbol << 32) | type` for ELF64, `(symbol << 8) | type` for ELF32).
- **DWARF** — `.debug_info` / `.debug_abbrev` / `.debug_line` and their
  relocations (the `.elfdwarf` type; `r_info` by the same rule).
- **CFI** — an `.eh_frame` and `.rela.eh_frame` from the source's `.cfi_*`
  (section 2.14). On a relaxing machine the local symbols `.Lcfi<n>` the table
  uses follow the local symbols.
- **Section count** — when a section's index is `SHN_LORESERVE` (0xff00) or
  above, `e_shnum` / `e_shstrndx` go in section header 0 and the symbols' section
  indices in `.symtab_shndx` (`SHT_SYMTAB_SHNDX`), `st_shndx` being `SHN_XINDEX`.
  There is no limit on the number of sections.

---

## 2. Declarations (pattern file)

| Declaration | What it sets |
|---|---|
| `.elfmachine::<number>[::<name>]` | the `e_machine` number (and the name used in diagnostics) |
| `.elfclass::<32>` / `<64>` | the ELF class |
| `.elfrela::<1>` / `<0>` | RELA (1, `rela`) or REL (0, `rel`) |
| `.elftype::<name>::<number>[::<width>[::<pc-relative>]]` | a relocation type |
| `.elfwidth::<bytes>::<type>` | the default type for a reference of that width |
| `.elfextern::<type>` | the default type for `.extern` with no type name |
| `.elfdwarf::<type>` | the absolute type the `-g` DWARF output uses |
| `.elfpcguess::<0>` / `<1>` | whether a width-guessed absolute type may become PC-relative |
| `.elfheader::<field>::<value>` | a field of the ELF header |
| `.elfsection::<name>::<sh_flags>[::<sh_type>[::<align>[::<entsize>]]]` | the attributes of a section header |
| `.elflink::<section>::<sh_link>[::<sh_info>]` | the `sh_link` / `sh_info` of a section |
| `.elfgroup::<name>::<signature>::<flags>::<member>[,...]` | a section group |
| `.elffield::<type>::<mask>[::<offset>[::<shift>[::<bias>]]]` | an instruction-field type |
| `.elfencode::<type>::<function>` | the function that writes a REL addend back |
| `.elfextra::<type>::<companion>[::<symbol>]` | a relocation added at the same offset |
| `.elfdiff::<width or type>::<add type>::<subtract type>` | sums and differences of labels as add/subtract relocations |
| `.elfrinfo::<function>` | the function that lays out `r_info` |
| `.elfunit::<byte>` / `<word>` | the unit of addends and symbol values |
| `.elfbuiltin::<0>` / `<1>` | whether the built-in table is the base |
| `.elfcfi::<RA column>::<code align>::<data align>[::<padding>]` | the CIE fields of the CFI |
| `.elfcfiinit::<instruction>` | an initial instruction of the CIE |
| `.elfcfireg::<name>::<DWARF number>` | a register name for the CFI directives |

Common rules:

- Every declaration is a difference *laid over* the built-in table selected with
  `-m` (except under `.elfbuiltin::0`). On a machine that is in the table, only
  what you write is replaced.
- Wherever `<type>` is written, an `.elftype` name, a built-in name, or a type
  number (decimal or `0x` hex) may be used. Names are case-insensitive.
- Declarations may go anywhere; they are gathered once the pattern file has been
  read.
- Numeric fields may be constant expressions.

### 2.1 `.elftype` — relocation types

```
.elftype::abs16::2::2          /* type 2, a 2-byte field            */
.elftype::pcrel16::4::2::1     /* type 4, 2 bytes, PC-relative      */
```

The fourth field is the byte width (1-8) of the field the type rewrites; the
fifth, if not 0, marks the type PC-relative. The addend calculation needs the
width, so give it for types `.elfwidth` or `.elfextern` select and for
instruction-field types. Numbers run from 1 to 2147483647. A composite type
(three types in one entry, as on MIPS64) is a number with the three bytes packed
in (section 2.12).

### 2.2 `.elfwidth` / `.elfextern` / `.elfdwarf`

`.elfwidth` takes any byte width from 1 to 8: on a machine whose words are not
8 bits (`.bits`) a reference is a multiple of the bytes per word, and some 8-bit
ISAs have 3-byte fields (`R_MN10300_24`). A type of 0 means "this width has no
type", and such references get no relocation.

### 2.3 `.elfheader` — ELF header fields

| Field | ELF header field | Default | Range |
|---|---|---|---|
| `type` | `e_type` | 1 (`ET_REL`) | 0-0xFFFF |
| `flags` | `e_flags` | 0 | 0-0xFFFFFFFF |
| `version` | `e_version` | 1 (`EV_CURRENT`) | 0-0xFFFFFFFF |
| `entry` | `e_entry` | 0 | 0-0x7FFFFFFFFFFFFFFF |
| `osabi` | `e_ident[EI_OSABI]` | the `--osabi` value | 0-0xFF |
| `abiversion` | `e_ident[EI_ABIVERSION]` | 0 | 0-0xFF |

These carry the machine-specific `e_flags` (the ARM EABI version, the RISC-V ABI
bits, the MIPS ISA and so on).

### 2.4 `.elfsection` — section header attributes

```
.elfsection::.vectors::0x6           /* ALLOC+EXECINSTR, type left as is */
.elfsection::.noinit::0x3::8         /* ALLOC+WRITE, SHT_NOBITS          */
.elfsection::.note.axx::0::7         /* no flags, SHT_NOTE, aligned 4    */
.elfsection::.vectors2::0x6::1::2    /* alignment written out: 2         */
.elfsection::.rodata.str1.1::0x32::1::1::1
                                     /* ALLOC+MERGE+STRINGS, entsize 1   */
```

- Section names match whole and case-insensitively.
- Without an `sh_type` the name rules stand. An `SHT_NOBITS` (8) section has only
  `sh_size` and no contents in the file.
- The fourth field is `sh_addralign`, 0 or a power of two. Without it the
  alignment is 16, except 4 for `SHT_NOTE` (7): a note's padding follows its
  alignment and binutils reads only 4 or 8; write 8 for a note that needs it.
- The fifth field is `sh_entsize`. An `SHF_MERGE` (0x10) section requires it so
  that the linker knows the element width (1 for a string table).

### 2.5 `.elflink` — `sh_link` and `sh_info`

```
.elfsection::.meta::0x82               /* ALLOC+LINK_ORDER  */
.elflink::.meta::.text                 /* sh_link -> .text  */
```

A value is a section name (an output section, a `.rela.*` / `.rel.*`, `.symtab`,
`.strtab`, `.shstrtab` or a `-g` DWARF section, case-insensitive) or a number
(decimal or `0x` hex). A name that is not found is written as 0, with a warning.
axx fills in the `sh_link` / `sh_info` of `.rela.*` and `.symtab` itself.

### 2.6 `.elfgroup` — section groups

```
.elfsection::.text.foo::0x6
.elfgroup::.group::foo::1::.text.foo   /* COMDAT, signature foo */
```

- `<name>` is the group section's name and `<signature>` the name of the
  signature symbol. A signature that is not in the symbol table but is a
  section's name uses that section's symbol.
- `<flags>` is the first word of the group's contents (1 is `GRP_COMDAT`).
- Members get `SHF_GROUP` (0x200), and their relocation sections join the group.
- Group sections come first in the section header table (the gABI wants a group
  before its members).
- A member that is not in the output is skipped with a warning; a group with no
  member left is not written.

### 2.7 `.elffield` — instruction-field types

```
.elffield::<type>::<mask>[::<offset>[::<shift>[::<bias>]]]
```

Declares that `<type>` packs its value into bit fields of an instruction word
rather than into plain consecutive bytes. A row typed with
`.reloc::<variable>::<type>` then

- carries the addend "operand value - label value + bias" (`bl ext+8` gives 8);
- under RELA, has its instruction field written as 0, for the linker to fill in
  (the shape GNU as produces);
- under REL, has the addend shifted right by `<shift>` bits and put back into the
  field, filling the set bits of the mask from the bottom up; the bits outside
  the mask (the rest of the instruction) are kept;
- leaves the range and alignment checks on that operand to the linker.

The fields:

- `<mask>` is the set of bits the linker writes, within the type's width of words
  read as an integer in the target byte order. A field split over two
  instruction words is one 64-bit mask (RISC-V's `R_RISCV_CALL_PLT` is
  `0xfff00000fffff000`).
- `<offset>` (default 0) is where the field starts, in bytes from the first word
  the row emits for that operand; `r_offset` points there.
- `<shift>` (default 0, 0-63) is how far REL shifts the addend right before
  writing it back (2 for a field counted in words).
- `<bias>` (default 0) is a constant added to the addend: how far ahead of the
  instruction the PC points. It is -8 for an ARM branch.
- Because the mask is filled from the bottom up, a type whose field reorders the
  bits of the value is written back under REL with `.elfencode` (section 2.8).

```
.elftype::rel24::10::4::1
.elffield::rel24::0x03fffffc            /* PowerPC64 bl: the LI field */

.reloc::t::rel24
BL !t :: .call w4(0x48000001|((t-$$)&0x3fffffc))
.clrreloc::t
```

The built-in AArch64 table holds `call26`, `adrp`, the `:lo12:` types and the
like in this form.

### 2.8 `.elfencode` — write-back functions

```
.elfencode::<type>::<function>
```

Under REL, the type's addend is written back into its field by a mini-language
function. The function gets (the field's value, the addend) and returns the new
field. The field's value is the type's width of words read as an integer in the
target byte order; the addend may be negative. Fields that need rounding, fields
with reordered bits, fields whose bits are functions of other bits (Thumb's
J1/J2) can all be written this way. It does the write-back even when `.elffield`
is declared too, and is not called under RELA.

```
.elfencode::hi16::hi16enc
.func hi16enc(f, a)
.return (f & 0xffff0000) | (((a + 0x8000) >> 16) & 0xffff)
.endfunc
```

### 2.9 `.elfextra` — companion relocations

```
.elfextra::<type>::<companion>[::<symbol>]
```

Every relocation of `<type>` is followed at the same offset by `<companion>`
with addend 0. With `<symbol>` 0 (the default) its symbol index is 0; with 1 it
is the same symbol. RISC-V's `R_RISCV_RELAX` is one.

### 2.10 `.elfdiff` — sums and differences of labels

```
.elfdiff::<width>::<add type>::<subtract type>
.elfdiff::<type>::<add type>::<subtract type>
```

A field whose value is labels added and subtracted (`a-b`, `a-b+c-d+4`,
`-(a-b)`, `a-(b-c)` and so on) gets `<add type>` against each added label and
`<subtract type>` against each subtracted label at the same offset. The add types
come first; the constant part goes in the addend of the first add type (or,
negated, of the first subtract type when no label is added).

- With a width in the first field, a data field of that width is meant. Under
  RELA the field is written as 0, because these types add to and subtract from
  what is in it.
- With a type name in the first field, a field `.reloc` gives that type is meant.
  Its position and width follow the type's `.elffield`; without one, the field is
  the words the reference emitted, and their assembled value is kept (for a field
  such as a ULEB128, which a linker rewrites in place, keeping its length).
- On a machine whose linker shrinks code, even a difference within one section
  needs the relocations. A sum and difference of a width with no declaration gets
  no relocation.

### 2.11 `.elfunit` — the unit

| Value | Addends | `st_value` / `st_size` |
|---|---|---|
| `byte` (default) | bytes | bytes |
| `word` | words | words |

`r_offset` and `sh_size` are always bytes. On a machine with 8-bit words the two
give the same values.

### 2.12 `.elfrinfo` — the layout of `r_info`

```
.elfrinfo::<function>
```

The function gets (symbol index, type number) and returns `r_info`. It lays out
the relocations of the `-g` DWARF sections too. MIPS64 puts the type in the top
byte:

```
.elfrinfo::rinfo64
.func rinfo64(sym, t)
.return sym | (((t >> 16) & 0xff) << 40) | (((t >> 8) & 0xff) << 48) | ((t & 0xff) << 56)
.endfunc
```

The functions of `.elfencode` and `.elfrinfo` take two arguments and return a
number; anything else is an error.

### 2.13 `.elfpcguess` / `.elfbuiltin`

`.elfpcguess::1` turns on the absolute-to-PC-relative swap of section 1.3 (the
built-in m68k table sets it). `.elfbuiltin::0` builds the description from the
pattern file's declarations alone, with no built-in table as the base.

### 2.14 CFI — `.elfcfi` / `.elfcfiinit` / `.elfcfireg` and `.cfi_*`

An `.eh_frame` is built from the source's `.cfi_*` directives (written as for GNU
as). What depends on the machine is declared in the pattern file.

```
.elfcfi::16::1::-8                     /* RA column, code align, data align */
.elfcfiinit::def_cfa rsp, 8            /* CIE initial instructions, in order */
.elfcfiinit::offset rip, -8
.elfcfireg::rsp::7                     /* register name -> DWARF number    */
.elfcfireg::rip::16
```

- The fourth field is the unit CIEs and FDEs are padded to (default: the pointer
  size).
- A CIE has the augmentation `zR` (`P` with `.cfi_personality`, `L` with
  `.cfi_lsda`, `S` with `.cfi_signal_frame`), and an FDE address is encoded
  `DW_EH_PE_pcrel|sdata4`, written with the first 4-byte PC-relative data type
  (not an instruction-field type) of the effective table, in declaration order.
  Functions with the same settings share a CIE.
- An advance takes the smallest of the 6-bit, 1-, 2- and 4-byte forms that fits,
  and every instruction takes the form GNU as and llvm-mc use.
- With `.elfdiff::4` declared (a relaxing machine), the function length and the
  advances are written with its add and subtract types, on local symbols
  `.Lcfi<n>`. The code alignment factor must then be 1.
- Directives the source may use: `startproc [simple]`, `endproc`, `def_cfa`,
  `def_cfa_offset`, `def_cfa_register`, `adjust_cfa_offset`, `offset`,
  `rel_offset`, `val_offset`, `restore`, `undefined`, `same_value`, `register`,
  `remember_state`, `restore_state`, `return_column`, `signal_frame`,
  `window_save`, `negate_ra_state`, `escape`, `personality`, `lsda`, and
  `sections` (ignored).

---

## 3. Declarations (source file) — symbol table attributes

The type, size, binding and visibility of a symbol are fields of the same shape
on every machine and belong to the program, so they are written in the source.
A linker acts on them:

- an ARM / AArch64 linker builds no veneer for a symbol that is not `STT_FUNC`;
- `--gc-sections` cannot place a symbol of size 0;
- a weak symbol (`STB_WEAK`) lets a library provide a default that can be
  overridden;
- an `SHN_COMMON` symbol lets the linker merge the same variable from several
  objects;
- the high bits of `st_other` carry machine-specific meaning (bits 5-7 hold the
  PowerPC64 ELFv2 local entry offset).

| Declaration | What it sets |
|---|---|
| `.type <name>::<kind>` | the type field of `st_info` (`STT_*`) |
| `.size <name>::<expr>` | `st_size` |
| `.weak <name>` | binding `STB_WEAK` |
| `.hidden <name>` / `.protected <name>` / `.internal <name>` | the visibility in `st_other` (`STV_*`) |
| `.other <name>::<value>` | the whole `st_other` byte |
| `.comm <name>::<size>[::<align>]` | an `SHN_COMMON` symbol |

- Each takes a comma-separated list, `name1::…, name2::…`.
- An undeclared symbol is `STT_NOTYPE`, size 0, visibility `STV_DEFAULT`.

**`.type` kinds.** By name or by number (0-15).

| Kind | `STT_*` | Used for |
|---|---|---|
| `notype` | 0 | no type (the default) |
| `object` | 1 | data |
| `func` (`function`) | 2 | a function entry |
| `section` | 3 | a section symbol |
| `file` | 4 | a file-name symbol |
| `common` | 5 | a common symbol |
| `tls` (`tls_object`) | 6 | thread-local data |
| `gnu_ifunc` (`ifunc`) | 10 | a GNU indirect function |

**`.size`.** The value is in words; under `.elfunit::byte` it is multiplied by
the bytes per word for `st_size`. It is usually written as the difference to a
label at the end of the function (`.size func::func_end-func`).

**`.weak`.** A name defined in this file is exported like `.global` with only the
binding weakened. An undefined name is registered exactly like an `.extern`
without a type name, so `.weak maybe` alone is a reference that resolves to 0 if
nothing defines it. A weak symbol always goes on the global side (ELF does not
allow a weak local).

**`.other`.** The low 2 bits are the visibility, the high 6 bits machine-specific.
A visibility declaration rewrites only the low 2 bits, so writing it after
`.other` keeps the high bits.

**`.comm`.** `st_value` is the alignment (in bytes, default 1) and `st_size` the
size. The type is `STT_OBJECT` unless `.type` says otherwise. The name is
registered as an external symbol, and references to it get relocations.

The bundled `elfsym.axx` / `elfsym.s` (EM_MN10300) are a worked example.

---

## 4. `-m` / `-f`

| | Given | Not given |
|---|---|---|
| `-m` | that number is the target (over `.elfmachine`) | `.elfmachine`, failing that 62 (x86-64) |
| `-f` | that ELF class | `.elfclass`, failing that the effective table's class (ELF64 for a machine with no table) |

Because `-m` wins, one pattern file can be reused under another `e_machine`
number. An unconventional combination (`-m 62 -f 32`, the x32 ABI layout) is
honored with a warning.

---

## 5. Built-in tables and `--elfdesc`

The machines with a built-in table are i386 (3), m68k (4), PowerPC (20),
PowerPC64 (21), s390x (22), ARM (40), SuperH (42), SPARCV9 (43), x86-64 (62),
AArch64 (183) and RISC-V (243). A table's entries are exactly the entries of the
effective table of section 1.1, all of which can be declared. The AArch64
instruction fields are held in the form of `.elffield`, and the m68k guess in
the form of `.elfpcguess`.

`--elfdesc` prints the description in effect (the `-m` machine's table with the
declarations laid over it) to standard output as a run of declarations headed by
`.elfbuiltin::0`, and stops.

```
$ axx test.axx -m 4 --elfdesc
.elfbuiltin::0
.elfmachine::4::m68k
.elfclass::32
.elfrela::1
.elftype::abs32::1::4
.elftype::abs16::2::2
.elftype::abs8::3::1
.elftype::pc32::4::4::1
.elftype::rel32::4::4::1
.elftype::pc16::5::2::1
.elftype::pc8::6::1::1
.elfwidth::1::abs8
.elfwidth::2::abs16
.elfwidth::4::pc32
.elfextern::pc32
.elfdwarf::abs32
.elfpcguess::1
.elfunit::byte
```

Pasting this into a pattern file (or including it) gives the same ELF with no
built-in table. The functions `.elfencode` / `.elfrinfo` name are not printed,
so use the output with the pattern file that defines them. For all eleven
built-in machines, the AArch64, PowerPC64 (both byte orders) and RISC-V
instruction sets and the bundled ELF pattern files, the output through
`--elfdesc` has been checked to match the original byte for byte.

---

## 6. When declarations are missing

The policy is **never to write a broken `.o` silently**.

- A reference whose type cannot be decided, and a label difference of a width
  with no declaration, get no relocation (`-d` reports them).
- `-o` with an `-m` number that has no built-in table gives a warning.
- A type name in a declaration that cannot be resolved is warned about once,
  when the declarations are complete.
- An `.elfencode` / `.elfrinfo` function that does not exist, takes a different
  number of arguments or returns no number is an error.
- For CFI, a directive outside `.cfi_startproc`, a function left open, an offset
  the data alignment factor does not divide, a `restore_state` with no
  `remember_state`, an unknown symbol or encoding, and a pattern file with no
  `.elfcfi` are errors.
- `-g` DWARF is written only when an absolute type is known.
- The default ELF32 `r_info` has an 8-bit type field. A type number above 255
  would turn into another type, so it is warned about once per type (and so is a
  symbol index that does not fit 24 bits). No warning is given when `.elfrinfo`
  lays out `r_info`.

---

## 7. Scope

axx writes relocatable objects (`ET_REL`). Inside a `binary_list`, a label of
the same section and `$$` are filled in relative to the section start (the
linker decides where the section goes). An executable (`ET_EXEC`) or a shared
library (`ET_DYN`) would need every relocation resolved by its type's formula
and program headers or dynamic-linking tables built — the linker's job. A raw
image at fixed addresses is what `-b` writes.

---

## 8. Examples

### 8.1 EM_MSP430 (105) — a machine with no table

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

CALL !t :: 0xb0,0x12,t,t>>8
.reloc::t::pcrel16
JMP !t :: 0x00,0x3c,t,t>>8
.clrreloc::t
DB !t :: t
DW !t :: t,t>>8
DD !t :: t,t>>8,t>>16,t>>24
```

```
        .extern ext1                    ; type from .elfextern
        .extern ext2::abs32             ; an .elftype name
        .global start
start:
        call    ext1                    ->  R_MSP430_ABS16   ext1 + 0
        jmp     start                   ->  R_MSP430_PCR16   start + 6
        dw      start                   ->  R_MSP430_ABS16   start + 0
        db      start                   ->  R_MSP430_ABS8    start + 0
        dd      ext2                    ->  R_MSP430_ABS32   ext2 + 0
```

These are the bundled `elfgen.axx` / `elfgen.s`. The type priority is shown by
`elfprio.axx` / `elfprio.s`.

### 8.2 PowerPC64 (21) — declarations over a table

`ppc64.axx` (big-endian, ELFv1) and `ppc64le.axx` (little-endian, ELFv2) are
wrappers holding only the byte order and the ELF description; they include the
instruction set, `ppc64_isa.axx`. The 64-bit PowerPC ELF ABI types are declared
with `.elftype` and the instruction fields (`REL24`, `REL14`, the `ADDR16` family,
`ADDR16_DS`, `D34`, `PCREL34` and so on) with `.elffield`. A 16-bit field is at
offset 2 big-endian and 0 little-endian. `.text` is 64-byte aligned through
`.elfsection`.

```
bl      ext+8           ->  R_PPC64_REL24         ext + 8
addis   3,2,msg@ha      ->  R_PPC64_ADDR16_HA     msg + 0
addi    3,3,msg@l       ->  R_PPC64_ADDR16_LO     msg + 0
ld      4,msg@l(3)      ->  R_PPC64_ADDR16_LO_DS  msg + 0
pld     5,ext@pcrel     ->  R_PPC64_PCREL34       ext + 0
.quad   ext             ->  R_PPC64_ADDR64        ext + 0
```

The relocations and the linked result match GNU as 2.42.

### 8.3 ARM (40) — no table, REL instruction fields

`elfrel.axx` describes ARM under `.elfbuiltin::0` and writes REL instruction
fields back with the shift and bias of `.elffield`.

```
.elffield::call::0x00ffffff::0::2::-8  /* imm24, in words, PC+8 */
.elffield::movw_abs_nc::0x000f0fff     /* imm4:imm12            */
```

```
bl   ext                   ->  eb fffffe   R_ARM_CALL         ((0 - 8) >> 2)
bl   ext+16                ->  eb 000002   R_ARM_CALL         ((16 - 8) >> 2)
movw r1,%lo16(dat+0x12345) ->  e302 1345   R_ARM_MOVW_ABS_NC
```

The words and relocations match llvm-mc's, and so does the result of linking
with `ld.lld -m armelf`.

### 8.4 RISC-V (243) — instruction fields, companions, differences, groups

`riscv64.axx` targets a machine whose built-in table holds only data types: it
declares `CALL_PLT`, `BRANCH`, `JAL`, `HI20`, `LO12_I`/`_S` and the `PCREL` pair
with `.elftype` and `.elffield`, and writes a `.o` that links with
`ld -m elf64lriscv`. RISC-V has no 8- or 16-bit absolute type, so
`.elfwidth::1::0` and `.elfwidth::2::0` make those widths typeless.

`elfpair.axx` includes it and adds what linker relaxation needs.

```
.elfextra::call::relax
.elfdiff::4::add32::sub32
.elfdiff::8::add64::sub64
.elfgroup::.group::foo::1::.text.foo
.elfsection::.meta::0x82
.elflink::.meta::.text
```

```
call  ext                ->  R_RISCV_CALL_PLT ext + 0, R_RISCV_RELAX
dword lend-_start        ->  R_RISCV_ADD32 lend + 0,   R_RISCV_SUB32 _start + 0
dword ext-_start+4       ->  R_RISCV_ADD32 ext + 4,    R_RISCV_SUB32 _start + 0
quad  foo-d0             ->  R_RISCV_ADD64 foo + 0,    R_RISCV_SUB64 d0 + 0
dword lend-_start+d0-d1+4 -> ADD32 lend + 4, ADD32 d0, SUB32 _start, SUB32 d1
dword -(lend-_start)     ->  R_RISCV_ADD32 _start + 0, R_RISCV_SUB32 lend + 0
uleb  lend-_start+300    ->  R_RISCV_SET_ULEB128 lend + 300, R_RISCV_SUB_ULEB128 _start
adv6  lend-_start        ->  R_RISCV_SET6 lend + 0,    R_RISCV_SUB6 _start
```

The relocations, the COMDAT group and the `SHF_LINK_ORDER` section header match
llvm-mc's. After `ld.lld`'s relaxation shrinks each `call` into a `jal`, every
difference still comes out right (the ULEB128 keeps its length, the 6-bit field
its high bits).

The same file declares CFI too (`.elfcfi::1::1::-8`, `R_RISCV_32_PCREL`); with
`.elfdiff::4` declared, the function length and the advances are written as
ADD32/SUB32 on `.Lcfi<n>`. After linking, the rows sit where they do in
llvm-mc's object linked the same way.

### 8.5 MIPS (8) — a write-back function and `r_info`

`elfmips.axx` (MIPS32, REL) writes `R_MIPS_26` and `R_MIPS_LO16` back through
`.elffield`, and `R_MIPS_HI16` through an `.elfencode` function
(`(addend + 0x8000) >> 16`).

```
lui   3,%hi(ext+0x18000)    ->  3c03 0002   R_MIPS_HI16
addiu 3,3,%lo(ext+0x18000)  ->  2463 8000   R_MIPS_LO16
jal   ext+8                 ->  0c00 0002   R_MIPS_26
```

The words and relocations match llvm-mc's, and the `.text` linked with `ld.lld`
matches byte for byte.

`elfmips64.axx` (MIPS64 n64, little-endian) puts the type in the top byte of
`r_info` with `.elfrinfo`; `readelf -r` reads each entry as
`R_MIPS_64/R_MIPS_NONE/R_MIPS_NONE` and so on, as it does for llvm-mc's object.

### 8.6 x86-64 — CFI

`elfcfi.axx` holds a few x86-64 instructions and declares CFI.

```
f:
        .cfi_startproc
        push    rbp
        .cfi_def_cfa_offset 16
        .cfi_offset rbp, -16
        mov     rbp,rsp
        .cfi_def_cfa_register rbp
        ...
        ret
        .cfi_endproc
```

The rows `llvm-dwarfdump --eh-frame` reads (`0x1: CFA=RSP+16: RBP=[CFA-16],
RIP=[CFA-8]` and so on) match llvm-mc's, and with padding 4 the `.eh_frame`
matches byte for byte. AArch64 (`R_AARCH64_PREL32`) matches too.

### 8.7 A machine with 16-bit words — the unit

`elfword.axx` is a toy machine with `.bits::16`; `.elfunit::word` makes the
addends and symbol values word counts.

```
j   f+3      ->  jmp12  f + 3      (f + 6 under byte)
dw  mid+1    ->  abs16  mid + 1    (mid + 2 under byte)
mid          st_value 1            (2 under byte)
```

---

## 9. Implementation map

The functions of the two implementations follow the same rules and name each
other.

| Stage | axx.py | caxx.c |
|---|---|---|
| effective table | `elf_machine_table()` | `elf_machine_effective()`, `elf_field_effective()` |
| instruction-field description | `insn_reloc_field_decl()` | `insn_reloc_field_decl()` |
| bit write-back | `_field_deposit()` | `field_deposit()` |
| label sums and differences | `_elf_v2l_second()`, `_elf_v2l_finish()`, `_elf_diff_resolve()` | `label_get_value()`, `elf_v2l_finish()`, `elf_diff_resolve()` |
| calling a function | `_elf_call_func()` | `elf_call_func()` |
| `r_info` | `_elf_r_info()` | `weo_rinfo()` |
| recording CFI | `cfi_processing()` | `adir_cfi()` |
| CFI instructions | `_cfi_op_bytes()` | `cfi_op_bytes()` |
| `.eh_frame` | `_build_eh_frame()`, `_cfi_points()` | `build_eh_frame()`, `cfi_points()` |
| writing | `write_elf_obj()` | `write_elf_obj()` |
| `--elfdesc` | `elf_desc_text()` | `elf_desc_print()` |
| declaration checks | `check_elfdecls()` | `check_elfdecls()` |
