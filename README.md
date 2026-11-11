# axx — a general assembler: one line in, an assembler for any CPU

axx is a general assembler: write one text file, and you have an assembler for any instruction set.

```
RET :: 0xc3
```

That single line is a complete assembler for the x86\_64 `RET` instruction. Stack up lines of the same shape, `instruction syntax :: error conditions :: output`, and you get an assembler for real CPUs, from the Intel 4004 to x86\_64 with AVX-512 and AArch64 with SVE/SME2. No C++, no Scheme, no code-generation step.

- Author: fygar256 (Taisuke Maekawa)
- License: MIT
- Repository: [github.com/fygar256/axx](https://github.com/fygar256/axx)
- Name: **A**rbitrary e**X**tended **X** assembler

axx is *general* in the sense of one mechanism common to every target. It turns an assembler from a program written per ISA into data that describes the ISA.

## Quick start

```sh
git clone https://github.com/fygar256/axx.git
cd axx
make                                                   # builds caxx, paxx and axx
./axx patfile/z80.axx asmsrc/z80.s -v                  # Z80 listing
./axx patfile/x86_64.axx asmsrc/hello.s -o out.o       # x86_64 ELF object
./axx patfile/8080toz80.axx asmsrc/hello8080.s -V      # 8080 -> Z80 translation
./bfsh/bf_x86_64_linux.sh run                          # draw the Mandelbrot set in Brainfuck
```

The command line is `axx <pattern file> <source> [options]`. The main options:

| Option | Output |
| --- | --- |
| `-b FILE` | flat binary image |
| `-o FILE` | ELF32/64 relocatable object (`-f 32` / `-f 64`, `-m` for the machine number) |
| `-g` | DWARF line information in the object |
| `-v` | listing of addresses, source lines and output bytes |
| `-V` | text output, for the translators (`.textmode`) |
| `-e` / `-E` / `-i` | export / import label tables (TSV) |

`axx -h` prints the full list; `Technical_Manual.md` describes every option.

## What makes axx different

### One line per instruction, transcribed straight from the manual

Syntax, range checks and output fit on a single line. An 8048 example:

```
ADD A,R!n :: n>7;5 :: n|0x68
```

`add a,r1` emits 0x69, and an out-of-range register number reports error 5. Pattern files look almost like the instruction tables in a datasheet, so they are easy to read and easy to fix.

### Free-form syntax with no tokenizer

axx matches character by character, so the pattern author defines the grammar. Classic forms like `MOV A,B` work, and so do assignment-style instructions like `r1 = r2 + r3` and ARM64 notation such as `{v0.4s}`, with no special handling. `.symbolc` / `.labelc` declare which characters may form identifiers, so MIPS names like `$v0` work as they are.

### Matching that does not depend on order

Among all matching patterns, axx picks the most specific one by a specificity score. Special cases need not come first, so pattern files of tens of thousands of lines stay easy to grow. With `.unordered`, directive order becomes free as well.

### Three layers: declarative safety plus computing power

- **Macro layer** (`!def` / `!if` / `!while`): generates patterns or source before loading.
- **Pattern layer**: the declarative core. It is not Turing-complete, so matching always terminates.
- **Mini language** (`.func` / `.call`): computes the encodings that no expression can write, called by name.

With the mini language, the whole AArch64 logical-immediate instruction group fits in 86 pattern lines.

### Linkable ELF from code that knows no machine

`-o` emits ELF32/64 relocatable objects that go straight to GNU ld or ld.lld. `-g` adds DWARF, and `.cfi_*` builds `.eh_frame`. The ELF writer has no per-machine branches: relocation types, REL/RELA, bit fields inside instruction words and the layout of `r_info` are all declared in the pattern file. Even the built-in tables for 11 machines are declarations written in advance.

### A translator between assembly languages

Put string templates in the output field and declare `.textmode`, and a pattern file becomes a source-to-source translator. Bundled examples:

- `8080toz80.axx`: Intel 8080 source into Z80 notation
- `intel2att.axx`: x86-64 Intel syntax into AT&T syntax (60 lines expand to 3,437 patterns)
- `a64tox64_axx.axx`: AArch64 assembly into x86\_64, all the way to an executable with axx alone

### VLIW, EPIC and any word size

The `.vliw` declaration handles VLIW machines, including Itanium-style EPIC. Word sizes from 1 to 64 bits are set with `.bits::12` and the like, covering bit-slice and 4-bit machines. Floating-point immediates from half to quad precision use `!F` / `!D` / `!Q`.

### A formal foundation

`axxsemantics` formalizes axx in denotational semantics: a meaning function from source through matching, environment and binary to object, with relaxation placed as a fixed point over label environments.

## Supported ISAs

`patfile/` ships 61 pattern files. The major ISAs are checked byte for byte against external reference assemblers, and their ELF output links directly.

| ISA | Coverage | Checked against / links with |
| --- | --- | --- |
| x86\_64 | x86\_64-v3, segments, AVX/AVX2, BMI1/2, x87, EVEX/AVX-512 | VEX/EVEX per llvm-mc 19; links with ld |
| AArch64 | All of A64, Advanced SIMD, crypto, SVE/SVE2, SME/SME2 | llvm-mc 19 / ld.lld 19 |
| PowerPC64 | Power ISA v3.1 (POWER10), BE/LE, VMX, VSX, MMA, prefixed instructions | GNU as, GNU ld |
| RISC-V | All of RV64: I/M/A/F/D/Q/Zfh/C, bit manipulation, scalar crypto, H, V 1.0 | llvm-mc, `ld -m elf64lriscv` |
| MIPS | MIPS I to MIPS64 Release 6, BE/LE, o32/n64, DSP, MSA and other extensions | GNU as / llvm-mc, GNU ld |
| SPARC | V7/V8/V9, VIS 1–3, UA2005/2007, LEON | llvm-mc, ld.lld |
| Legacy | 68000, 6809, 6800, 6502, Z80, 8080, 8051, 8048, 4004 | capstone, objdump, MAME, ucsim; edge-case and error tests |
| Special | VLIW, Itanium-style EPIC, a Brainfuck virtual CPU | Cross-checked between the implementations |

Pattern files for ARM (A32/T32), RV32 and 32-bit PowerPC are still to be written. The format is fully documented, so anyone can start one.

## Three implementations, one specification

axx has three independent implementations that produce byte-identical output for the same input.

| Implementation | Source | Size | Notes |
| --- | --- | --- | --- |
| Paxx (Python) | `axx.py` | 17,509 lines | The reference implementation; new features land here first |
| Caxx (C) | `caxx.c` | 24,025 lines | Fast: the x86\_64 hello world against about 24,000 patterns in about 0.1 s |
| Faxx (Forth) | `faxx.fs`, `faxxsrc/` (69 files) | 15,051 lines | Runs on gforth, or compiles to an executable with ccforth |

The C and Forth versions carry their own 256-bit integer type, so expressions and the mini language wrap around exactly as the Python version does.

Faxx runs from the top of the repository:

```sh
gforth faxx.fs patfile/z80.axx asmsrc/z80.s -b z80.bin   # under gforth
make faxx                                                # or build ./faxx with ccforth
./faxx patfile/z80.axx asmsrc/z80.s -b z80.bin
```

`build_ccforth.sh` does the build; it needs [ccforth](https://github.com/ncw/ccforth) and a C compiler.

### Testing

`test1` assembles every pattern file / source pair with caxx and paxx, 218 runs on each side, and compares the results with `cmp`. Besides the `-b` images it compares ELF objects (`-o`, ELF64 and ELF32), DWARF (`-g`), listings (`-v`), translated text (`-V`) and the diagnostics on standard error, including the `_err.s` files of lines a pattern file must refuse and the `_edge.s` files of lines at the edges of the ranges.

The two implementations are also checked against each other by differential fuzzing; the disagreements found that way are kept in `regress.axx` and `regress*.s`.

## Demos

| Command | Result |
| --- | --- |
| `caxx patfile/x86_64.axx asmsrc/hello.s -o out.o` | `ELF 64-bit LSB relocatable, x86-64`; paxx and faxx write the same bytes |
| `bfsh/bf_x86_64_linux.sh run` | A Brainfuck interpreter built with axx draws `mandelbrot.bf` |
| `aarch64tox64/testrun.sh` | AArch64 source translated to x86\_64 by axx, assembled by axx, linked with ld, and it draws `mandelbrot.bf` |
| `caxx patfile/intel2att.axx asmsrc/intel2att.s -V \| as --64` | The translated AT&T text passes GNU as unchanged |
| `caxx patfile/8080toz80.axx asmsrc/hello8080.s -V` | A CP/M hello world in Z80 notation, labels, comments and indentation kept |
| `caxx patfile/z80.axx asmsrc/z80.s -v` | A listing of addresses, source lines and output bytes |

`bfsh/` has a script per CPU and OS (x86\_64, AArch64, PowerPC64, MIPS, RISC-V, SPARC on Linux and FreeBSD), so `mandelbrot.bf` runs under qemu as well.

## How axx differs from related tools

axx keeps a declarative ISA description and a declarative description of linkable ELF together in one file.

| Tool | How you describe a target | Object output | Best suited for |
| --- | --- | --- | --- |
| **axx** | Free-form pattern files only | ELF32/64 generated from declarations, DWARF, CFI | Bringing historical, homebrew or unusual ISAs to a real OS from a description you can read end to end |
| customasm | Declarative rules (Rust) | Dump formats such as binary, hexdump, intelhex | Homebrew CPUs targeting ROMs or emulators |
| LLVM MC | TableGen plus substantial hand-written C++ | ELF, COFF, Mach-O, wasm | Production toolchains for mainstream architectures |
| CGEN | Instruction semantics in Scheme | Generates parts of binutils | Embedded ports of GNU binutils/GDB |

LLVM's AsmMatcher needed dedicated handling for Hexagon's mnemonic-less `r0 = r1` syntax. Because axx matches character by character from the start, syntax like this is natural to write.

## Repository layout

| Path | Contents |
| --- | --- |
| `axx.py`, `caxx.c`, `faxx.fs`, `faxxsrc/` | the three implementations |
| `patfile/` | pattern files (`*.axx`) |
| `asmsrc/` | assembly sources and test files (`*.s`, `*.tsv`) |
| `bfsh/` | build and run scripts for the Brainfuck interpreters |
| `aarch64tox64/` | the AArch64 → x86\_64 port of the Brainfuck interpreter |
| `test1` | the cross-check of the implementations |
| `makefile`, `build_ccforth.sh` | build rules |

`FILE_DESCRIPTION` describes every file.

## Documentation

| Topic | English | Japanese |
| --- | --- | --- |
| Technical manual (full reference) | `Technical_Manual.md` | `Technical_Manual_ja.md` |
| Introduction paper | `axx_introduction_paper_en.md` | `axx_introduction_paper.md` |
| ELF generalization | `elf_generalization_en.md` | `elf_generalization.md` |
| Macro layer reference | `macro_en.md` | `MACRO.md` |
| Mini language reference | `mini_en.md` | `MINI.md` |
| Writing pattern files with AI | `axx_ai_pattern_guide_en.md` | `axx_ai_pattern_guide_ja.md` |
| Introductory article | — | `axx_promo.md`, [Qiita](https://qiita.com/fygar256/items/1d06fb757ac422796e31) |
| Denotational semantics | — | `axxsemantics` |
| File list | `FILE_DESCRIPTION` | — |
| Man page | `axx.1.gz` | — |

## History

The idea, the name and a prototype in C were born in 1986, while the author was a university student working part-time at Tokyo Denshi Sekkei. The original listing resurfaced 38 years later, and axx was rewritten in Python and released in April 2024.

In those 38 years VLIW, EPIC, word sizes other than 8 bits and scalable vector extensions all appeared, and axx handles every one of them without changing its core design. The first commit landed on 4 April 2024; the C version joined in February 2026 and the Forth version in October 2026, and development continues.

## Who axx is for

- Anyone who wants an assembler that emits real ELF for a favorite vintage CPU or a homebrew one
- OS and bootloader hobbyists building a toolchain for an unusual target
- Anyone who wants to translate or port between assembly languages with declarations alone
- People interested in what an assembler fundamentally is
- Anyone writing pattern files for large ISAs with AI help: the declarative, mechanical format is a good fit (see `axx_ai_pattern_guide_en.md`)

## Contributing

Pattern files for ARM (A32/T32), RV32 and 32-bit PowerPC, plus structured macros and optimization, are areas where contributions are warmly welcome. Come help widen the world that starts with one line, `RET :: 0xc3`.
