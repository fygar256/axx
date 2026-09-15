---
title: Generalized assembler 'axx General Assembler'
tags: Terminal Python general assembler
author: fygar256
slide: false
---

# axx — An assembler conceived in 1986, dormant for 38 years

## The 30-second version

axx aims to let you build an assembler for **any instruction set** from a single declarative text file — no C++, no Scheme, no code generation step.

```
RET :: 0xc3
```

That one line is a complete assembler for the x86_64 `RET` instruction. Stack up lines in the same shape (`instruction syntax :: error conditions :: output bytes`) and you get an assembler for anything from the Intel 4004 to x86_64 with AVX-512.

- GitHub: https://github.com/fygar256/axx
- Author: fygar256 (Taisuke Maekawa)
- License: MIT

## Why it exists

The idea, the name, and a prototype written in C already existed in 1986, when the author was a university student working part-time at Tokyo Denshi Sekkei. The original listing resurfaced 38 years later and was rewritten in Python and released in 2024.

That gap wasn't just dormancy — it doubled as a validation period. VLIW, EPIC, processors whose word size isn't 8 bits: all of these appeared during those 38 years, and the core idea still held up when it was finally implemented. axx supports all of them.

## What's actually been verified

Not marketing copy — things you can reproduce yourself in a few minutes.

**Two independent implementations agree byte-for-byte.** axx ships a Python implementation (`axx.py`, nicknamed Paxx, 8,226 lines) and a C implementation (`caxx.c`, nicknamed Caxx, 11,221 lines). The bundled `test1` script assembles 14 pattern/source pairs — from the 4004 to x86_64 to a Brainfuck virtual CPU — with both implementations and `cmp`s the results. Run it and you get `test all passed`. This isn't a claim; it's reproducible in five minutes from a fresh clone.

**It produces real ELF objects.**

```sh
axx x86_64.axx hello.s -o out.o
file out.o
# => out.o: ELF 64-bit LSB relocatable, x86-64, version 1 (SYSV), not stripped
```

`-o` emits an ELF32/64 relocatable object for FreeBSD or Linux that you can hand straight to `ld`, with optional DWARF debug info. None of the comparable tools in this space do this (more on that below).

**The grammar itself is free-form.** axx has no tokenizer; it matches character by character. That means it isn't limited to the conventional "mnemonic plus operands" shape — a register-transfer style instruction like `r1 = r2 + r3` is just as legal a pattern as `MOV A,B`. This isn't incidental: LLVM's assembler-generation machinery (TableGen/AsmMatcher) explicitly assumes mnemonic-led syntax, and had to be specially patched to handle Hexagon's mnemonic-less `r0 = r1` transfer syntax. axx never had that assumption baked in to begin with.

**A macro layer keeps large ISAs maintainable.** The full x86_64 pattern set (through AVX-512/EVEX) is 23,923 lines written flat. The macro-based version is 5,787 lines — a quarter of the size — and expands back to an identical, byte-for-byte matching pattern set at load time. Runtime cost of matching against ~24,000 patterns is still sub-second in the C implementation.

## What's covered today

Bundled and working: **x86_64** (x86_64-v3: segment addressing, AVX/AVX2, BMI1/BMI2, x87, EVEX/AVX-512), **Motorola 6809 / 68000 / 6800**, **MOS 6502**, **Zilog Z80**, **Intel 8080 / 8051 / 8048 / 4004**.

ARM, AArch64, RISC-V, PowerPC, MIPS and SPARC don't have pattern files yet. That's not a design limitation — it's a labor constraint: the author doesn't currently have real hardware or emulators to validate against, and doing it solo is more than one person wants to take on. The pattern-file format itself is fully documented and, within the "instructions map one-to-one onto machine code" boundary the design deliberately enforces (a Turing-incomplete core guarantees pattern matching terminates), there's nothing architecture-specific stopping someone from writing one.

## How it compares

**customasm** (Rust, actively maintained) shares the same core idea — describe an ISA declaratively, get an assembler for it — but customasm output formats (binary, hexdump, intelhex, and similar dump formats) stop short of anything like ELF; there's no relocatable-object output at all. If you're building a toy VM or an FPGA CPU, customasm is the better fit. If you need something that links into a real OS binary, axx is the one that does that.

**LLVM MC** is the production-grade backend actually used by clang and rustc, with object-format support (ELF, COFF, Mach-O, wasm) and target coverage that axx doesn't come close to. But TableGen alone rarely suffices for a real target — most non-trivial backends carry thousands of lines of hand-written C++ alongside the declarative description. If you need a mainstream architecture in production today, use LLVM. If you want a historical or unusual ISA running from a single file you can actually read end to end, that's axx's territory.

**CGEN** is a Scheme-based CPU description language used to generate parts of GNU binutils/GDB for a handful of embedded architectures. It describes instruction *semantics* (in an RTL-like form) rather than matching surface text patterns, which puts it in a different category from axx or customasm.

## Who this is for

- Anyone who wants a real, linkable ELF object out of an assembler for an old CPU (or a homebrew one)
- OS/bootloader hobbyists who need a toolchain component for an unusual target
- People interested in assembler design as a subject in its own right
- Anyone writing a pattern file for a large ISA — it's mechanical and declarative enough that AI-assisted generation works well for it

## Try it

```sh
git clone https://github.com/fygar256/axx.git
cd axx
make                              # builds and installs caxx, paxx, axx, and the man page
axx z80.axx z80.s -v              # assemble the Z80 sample, print the listing
axx x86_64.axx hello.s -o out.o   # assemble x86_64 hello-world into an ELF object
```

Pattern files for ARM, RISC-V, PowerPC, MIPS and SPARC don't exist yet. Getting there — including real hardware/emulator validation — is more than one person can reasonably do alone. If you're interested in taking on one of those, that's where help would matter most.

---

*Every verification claim in this document (byte-identical dual implementations, actual ELF object generation, the line-count comparison) was checked by cloning, building, and running the repository directly.*


## 3 Acknowledgements

My thanks to my mentor Junichi Hamada and to Tokyo Denshi Sekkei, who gave me
the problems and the hints; to the University of Electro-Communications; to Pacific
Software Development; to the computer scientists and engineers; to Qiita, IEEE, 
The Alan Turing Institute; and to some unforgettable people. I received a passing 
grade from Emeritus Professor Kameda of the Information Processing Society of Japan.
Thank you very much.

## 4 Mascot

<img alt="axxgirl" width="200px" height="200px" src="https://github.com/fygar256/axx/blob/main/axxgirl.png">
