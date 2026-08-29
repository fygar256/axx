---
title: Generalized assembler 'axx General Assembler'
tags: Terminal Python general assembler
author: fygar256
slide: false
---

A C version is also available, named Caxx. Caxx is much faster than Paxx.

caxx compile:

`gcc caxx.c -o caxx -lm -O2`

`-lm` is required, as the expression evaluator uses the math library.
Alternatively, `make` builds and installs both implementations at once.

Paxx is the reference implementation. Due to Paxx version upgrades, updates to caxx may be delayed. The two are intended to produce identical output for the same input, and the bundled pattern files and test sources are the material used to check that.

# Test environment

FreeBSD,Linux terminal

# Original article in Japanese

Qiita: https://qiita.com/fygar256/items/1d06fb757ac422796e31

# Relocatable ELF creation of axx

GitHub: https://github.com/fygar256/axx_relocatable_elf_generation

# Demonstration of brainfuck interpreter that assembled by axx (with macro)

https://github.com/fygar256/brainfuck_interpreter_for_axx_on_freebsd_of_x86_64

# Pattern files for practical use

x86_64.axx, x86_64m.axx, 68000.axx, z80.axx, 8080.axx, 8048.axx, 6502.axx, 6800.axx, 6809.axx, and 4004.axx are for practical use.

https://github.com/fygar256/x86_64_pattern_file_for_axx

the other pattern files are for tests.

The bundled files and their matching test sources are:

| Pattern file (.axx) | Size | Approx. pattern count (`::` lines) | Matching source (.s) | Description / Notes |
|---------------------|------|------------------------------------|----------------------|---------------------|
| **x86_64.axx** | 3.9 MB | ~23,923 | **hello.s** | x86_64-v3 (segment addressing, AVX/AVX2, BMI1/BMI2, x87, EVEX/AVX-512). Large practical pattern set. README explicitly states that `x86_64.axx` uses `hello.s` |
| **x86_64m.axx** | 935 KB | ~5,787 | **hello.s** (or macro-enabled sources) | x86_64-v3 with macros. Also used in demos such as the Brainfuck interpreter |
| **6809.axx** | 125 KB | ~1,950 | **6809.s** | Motorola 6809 |
| **68000.axx** | 41 KB | ~378 | **68000.s** | Motorola 68000 (present in the repository; not listed in the older FILE_DESCRIPTION) |
| **6502.axx** | 15 KB | ~192 | **6502.s** | MOS 6502 |
| **z80.axx** | 7.5 KB | ~283 | **z80.s** | Zilog Z80 |
| **8048.axx** | 6.4 KB | ~95 | **8048.s** | Intel 8048 |
| **8080.axx** | 6.0 KB | ~113 | **8080.s** | Intel 8080 |
| **4004.axx** | 5.4 KB | ~53 | **4004.s** | Intel 4004 |
| **test.axx** | 1.1 KB | ~40 | **test.s** | Test-only pattern file containing fragments of several ISAs |
| **itanium.axx** | 281 B | ~12 | **vliw.s** | Itanium (EPIC) sketch. Incomplete; no accompanying test source |
| **vliw.axx** | 178 B | ~9 | **vliw.s** | Non-EPIC VLIW (test only) |
| **bf.axx** | 128 B | ~9 | **bf.s** | Brainfuck virtual CPU (hello-world style test) |



Note that `x86_64.axx` uses the source `hello.s`, not a file named
`x86_64.s`.

# GENERAL ASSEMBLER 'axx.py'

Since it's written in Python, the nickname is Paxx. axx is an abbreviation for "Arbitrary eXtended X(cross) assembler." The name also comes from superimposing an X — representing an unknown CPU — onto "ASM."

The core ideas, the name "AXX," and a prototype written in C already existed back in 1986—conceived during my university days while working part-time at Tokyo Denshi Sekkei—but it wasn't until 2024, after rediscovering the original program listing 38 years later and rewriting it in Python, that I finally released the functional code as it exists today. The `instruction` in the axx pattern file is the meta-language for all imperative assembly languages. Although it's a DSL, it doesn't really have a defined grammar; it's a free syntax language (pattern language) where you create your own grammar by combining string literals, symbols, and expressions.

All imperative assembly languages, except for EPIC/VLIW which have meta-level complexity in machine code, can essentially be reduced to a simple structure: `instruction :: error_patterns :: binary_list`. Further simplification by omitting error checking results in `instruction::binary_list`. Here, axx's binary_list includes complex expression calculations, alignment, and the `;` prefix modifier (which prevents binary output if 0) for practical purposes, but these are unnecessary in the minimal model. An instruction is a combination of (string literals, symbols replaceable by integer values, integer expressions, integer factors, and floating-point expressions). This allows processing of any imperative assembly language. However, the binary generation function isn't universal, limiting compatible processors; however, any processor where instructions and machine code are a one-to-one mapping can be processed. axx can also process Itanium-type EPIC and vliw processors through later extensions.

It extracts the essential commonalities of the von Neumann architecture, metamodels the instruction set architecture (ISA), and formalizes it using pattern matching.


# Text

axx.py is a general assembler that generalizes assembly language. It can process almost any processor architecture. A pattern file (processor description file) is required to process individual processor architectures. While you can define free-form instructions, creating a pattern file according to the target processor's assembly language allows it to process that processor's assembly language, albeit with slightly different notation. Essentially, it's just a grammatical rule for instructions and binary generation based on it. axx targets not only virtual CPUs but also "abstracted real CPUs." Converting the specifications of a real processor into a pattern file allows for direct assembly. In that sense, creating pattern files for large ISAs is well-suited to AI, considering the human effort involved. Creating pattern files for large ISAs is time-consuming, but once created, the ISA is complete and can be reused. For a small ISA, using axx allows you to have AI quickly generate the pattern file and complete the assembler. Since the axx pattern file itself lacks an explicit structure, it is well-suited for unstructured assembly code; however, you can also use the `.check` directive to express structured operations—such as `MOVabc r,s` involving the Cartesian product of a=[a1, a2, a3], b=[b1, b2, b3], and c=[c1, c2, c3]. Notation such as `movem d1 d2 d4` can also be expressed using the `.check` directive and the syntax `MOVEM [[ a [[ b [[ c [[ d ]]]]]]]]`. axx operates at a lower level than LLVM, CGen, or customasm.

This is not a "general-purpose assembler" in the sense of being "widely usable." It's a "general assembler" in the sense of being "common to everything." The `binary_list` only has five control structures: assignment, ternary operators, the `;` modifier, alignment, and `@@[]`. While ordinary general assemblers have `mnemonic operand definitions` alongside pattern definitions, axx's pattern definitions are arranged as `instruction :: error_pattern :: binary_list`, allowing for flexible instruction patterns. Therefore, notations like `r1 = r2 + r3` are possible, making it usable not only for assembly language but also as a general-purpose binary generator. The pattern file is Turing incomplete. Because of this Turing incompleteness, it's not suitable for processors with extremely complex architectures. Processor architectures can become infinitely complex if one chooses to make them so. If it were Turing complete, it could follow suit, but axx.py is Turing incomplete, and therefore not a "universal assembler." The reason it's currently Turing incomplete is that if it were Turing complete, the DSL would become a "program." In other words, it's also for the sake of guaranteeing cessation of pattern matching. However, this does not apply to the macro layer.

It cannot handle very specialized processors. For example, it cannot describe the ISAs of the following processors other than general-purpose processors:

Processor - Reason

Mill CPU - Belt architecture

ZISC - No instructions

Thinking Machines - Massively parallel

The execution platform is also independent of specific systems. It ignores `chr(13)` at the end of lines in DOS files. It should work on any system that runs Python.

axx does not support features such as the optimizations found in specialized assemblers, or high-level macros that translate structured or functional assembly constructs into imperative assembly. However, it does include standard macro capabilities. Since the basic functionality is present, you can adapt it for more advanced use cases.

Because pattern files and source files are separated, it's possible to generate machine code for a different processor from the source code of one instruction set, provided you don't consider the effort involved in coding. It's also possible to generate machine code for different processors from a common language. 

axx reads assembler pattern data from the first argument and assembles the source file specified in the second argument based on that data. During this process, the pattern data is matched against the assembly lines one by one, and the `binary_list` of any matching pattern is output to the result. While the definition of directives within the pattern file is order-dependent, the patterns themselves are not. If the second argument is omitted, the source input is read from the terminal (standard input).

The result is output as text to standard output if the -v option is present; a binary file is written to the current directory if an argument is specified with the -b option; and an ELF64 object file is produced if the -o option is used. The -e option outputs labels specified via .export—along with section/segment information—to a file in TSV format.

In `axx`, lines input from assembly language source files or standard input are called assembly lines.

# Explanation

## Install and Execution (Assemble) on Unix.

```
# Install
git clone https://github.com/fygar256/axx.git
cd axx
chmod +x axx.py
sudo cp axx.py /usr/bin/axx
# Execution (Assemble)
axx patternfile.axx [source.s] [-b outfile.bin] [-e expfile.tsv] [-i impfile.tsv] [-o object.o]
```

The bundled `makefile` builds and installs both implementations in one step
(it installs `caxx`, `paxx`, `axx` and the man page, and uses `sudo`):

```
make
```

patternfile.axx --- Pattern file
source.s --- Assembly source
outfile.bin --- Raw binary output file
expfile.tsv --- Section label information export file
impfile.tsv --- Section label information import file
object.o ---- ELF relocatable object file

Currently, object file output supports both ELF64 and ELF32 relocatable objects (see `-f`, below). ELF class (32/64-bit) is selected independently of the target machine (`-m`) via `-f`, and defaults to ELF64.

Relocatable object output works on FreeBSD and Linux (see `--osabi`). It is not limited to x86_64: `-m` currently has relocation-numbering support for i386, M68K, PowerPC, PowerPC64, s390x, ARM, SuperH, SPARCV9, x86-64, AArch64, and RISC-V, and `-f` selects ELF32 or ELF64 independently of the chosen machine (defaulting to ELF64, with a warning if the combination is non-conventional for that machine). `-g`/`--gen-debug` DWARF output currently requires ELF64.

Usage:

```
usage: axx [-h] [--osabi ELF_OSABI] [-b OUTFILE] [-e EXPORT_TSV]
           [-E EXPORT_ELF_TSV] [-i IMPORT_TSV] [-o OBJ_FILE] [-f {32,64}]
           [-m MACHINE] [-v] [-d] [-g] [--no-macro] [-P [FILE]] [-p [FILE]]
           patternfile [sourcefile]

axx general assembler programmed and designed by Taisuke Maekawa

positional arguments:
  patternfile           Pattern definition file (.axx)
  sourcefile            Assembly source file (.s). Omit for interactive mode.

options:
  -h, --help            show this help message and exit
  --osabi ELF_OSABI     ELF OSABI value (default: FreeBSD; FreeBSD/Linux, case-insensitive)
  -b OUTFILE            Output binary file
  -e EXPORT_TSV         Export labels to TSV file (plain format)
  -E EXPORT_ELF_TSV     Export labels to TSV file (ELF section flags format)
  -i IMPORT_TSV         Import labels from TSV file
  -o OBJ_FILE           Write ELF relocatable object file (.o); class selected by -f (default: ELF64)
  -f {32,64}            ELF class for -o output: 64 for ELF64/ELFCLASS64, 32 for ELF32/ELFCLASS32
                        (default: 64). Independent of -m/--machine; a value that does not match the
                        selected machine's conventional class (e.g. -m 62 -f 32, the real x32 ABI's
                        EM_X86_64-in-ELFCLASS32 layout) is honored, with a warning. -g/--gen-debug
                        DWARF output currently requires 64.
  -m MACHINE            ELF e_machine value (default 62=EM_X86_64). Must be one of the architectures axx has
                        relocation-numbering support for -- see ELF_MACHINES near the top of this file for the full
                        list (currently: 3=i386, 4=M68K, 20=PowerPC, 21=PowerPC64, 22=s390x, 40=ARM, 42=SuperH,
                        43=SPARCV9, 62=x86-64, 183=AArch64, 243=RISC-V)
  -v, --verbose         Verbose: print assembly listing to stdout (default: silent)
  -d, --debug           Enable debug output (forward-ref fallback, relaxation log, etc.)
  -g, --gen-debug       Generate DWARF debug information (.debug_info/.debug_abbrev/.debug_line) in the ELF object so
                        that gdb/lldb can do source-level debugging. Effective only together with -o.
  --no-macro            Disable the macro preprocessor layer (!if/!while/!def/!return/!set and !{...} interpolation),
                        so the source is handed to the assembler exactly as written.
  -P [FILE], --macro-expand [FILE]
                        Macro-expand the source file and write the resulting assembly to FILE (or stdout if FILE is
                        omitted or "-") without assembling it. Useful for debugging macros.
  -p [FILE], --macro-expand-pattern [FILE]
                        The pattern-file counterpart of -P: macro-expand the pattern file and write the resulting
                        pattern text to FILE (or stdout if FILE is omitted or "-") without assembling. Useful for
                        debugging pattern-file macros.
```

### Differences in the C version's command line

`caxx` takes the same option names as `axx.py`, with the following exceptions:

- `-h` / `--help` is not accepted. Run `caxx` with no arguments to see the usage line.
- `-d` / `--debug` is not implemented.
- Because the filename after `-P` may be omitted, `caxx` treats the next
  argument as the output file only when both the pattern file and the source
  file have already been given, e.g. `caxx pat.axx src.s -P out.s`.

## Export / import file format

The files handled by `-e`, `-E` and `-i` are **tab-separated** (TSV). Fields
must be separated by a real tab character; a line separated by spaces is
silently ignored.

### Export (`-e`, `-E`)

Two kinds of record are written. A section record has three fields (four with
`-E`), and a label record has two:

```
sectionname   startaddress   size   [flags]
labelname     value
```

Addresses, sizes and values are written with a `0x` prefix. `-E` adds a fourth
field to the section records holding the ELF section flags (`AX`, `WA`, and so
on); `-e` omits the flags. Labels appear in the order in which `.export` /
`.global` declared them.

Example (`axx x86_64.axx hello.s -E hello.tsv`):

```
.text	0x401000	0x39	AX
_hello	0x401000
_start	0x401000
len	0xd
```

### Import (`-i`)

The import file uses the same two record shapes, and the two may be mixed in
one file. **Values are read as hexadecimal, without a `0x` prefix.**

- A three-field line `sectionname<TAB>start<TAB>size` declares the address
  range of a section.
- A two-field line `labelname<TAB>value` defines an imported label. Its
  section is inferred by finding which of the previously declared ranges the
  address falls into; if none matches, `.text` is assumed.

A relocation type can be attached to an imported label with `::` :

```
.text	401000	39
mylabel	401010
otherlabel::pc32	401020
```

The names accepted after `::` are the short names in the `named` table of the
selected machine in `ELF_MACHINES`. For x86-64 they are `abs64`, `abs32`,
`abs32s`, `abs16`, `abs8`, `pc32`, `rel32`, `plt32`, `pc16`, `pc8`, `pc64`,
`got32`, `gotpcrel` and `got64`. An unrecognized name produces a warning and
is ignored.

Section records are optional. If you only need label values, a file of
two-field lines is enough:

```
label1	0
label2	1
label3	2
```

## Explanation of Pattern Files

A pattern file is a processor description file, user-defined to correspond to an individual processor. It is a kind of metalanguage for machine code and assembly language. The DSL used for pattern files is a basic ISADL (ISA Description Language).

If you find defining pattern files difficult, you can write them as string literals, passing only the minimum number of operands to the expression evaluation.

Furthermore, the parts of the ISA that are difficult to structure will be resolved by enumeration.

The pattern data in a pattern file is arranged as follows:

```
instruction :: error_patterns :: binary_list
instruction :: error_patterns :: binary_list
instruction :: error_patterns :: binary_list
:
:
```
`instruction` is mandatory. `error_patterns` is optional. `binary_list` is mandatory.
`instruction`, `error_patterns`, and `binary_list` should be separated by `::`.

for example (x86_64)

```
RET :: 0xc3
```
Comments

Writing `/*` in a pattern file makes everything after `/*` on that line a comment. Currently, closing with `*/` is not possible. It is only effective for everything after `/*` on that line.

Case Sensitivity, Variables

Uppercase letters, numbers, and symbols in the pattern file's instructions are treated as character constants. Uppercase letters match both uppercase and lowercase characters. Lowercase letters are treated as single-character variables. The value of the symbol at that position on the assembly line is assigned to the variable. Using `!lowercase` assigns the value of the integer expression at that position, `!!lowercase` assigns the value of the factor at that position, `!Flowercase` assigns the integer bit pattern of the 32-bit floating-point expression at that position, `!Dlowercase` assigns the 64-bit floating-point expression at that position, and `!Qlowercase` assigns the integer bit pattern of the 128-bit floating-point expression at that position. These values are then referenced from `error_patterns` and `binary_list`. All unassigned variables are initialized to 0. The `!` is not necessary when referencing from `error_patterns` and `binary_list`. All values are referenced similarly.

```
Uppercase letters, symbols, and escaped characters. Character constants.
Lowercase letters: Values of the symbol at that position.
!Lowercase letters: Values of integer expressions.
!!Lowercase letters: Values of integer factors.
!F lowercase letters: Values of 32-bit floating-point expressions.
!D lowercase letters: Values of 64-bit floating-point expressions.
!Q lowercase letters: Values of 128-bit floating-point expressions.
```

Lowercase variables are all initialized to 0 for each line of the pattern file.

From the assembly line, uppercase and lowercase letters are accepted the same, except for labels and section names.

#### Escape Characters

The escape character `\` can be used within the instruction.

#### error_patterns

`error_patterns` specifies the conditions under which an error occurs, using variables and comparison operators.

Multiple error patterns can be specified, separated by commas. For example:

```
a>3;4,b>7;5
```

In this example, when a>3, error code 4 is returned, and when b>7, error code 5 is returned.

The number after `;` is the error code. Codes 1, 2, 3, 5 and 6 have a message
text attached (see [errors](#errors) below); any other code, including 4 and
anything from 7 upward, is still reported and still aborts the assembly, but
prints an empty message. Pick one of the five with text where it fits, or add
your own message to the `ERRORS` table in `axx.py` and `caxx.c`.

Comparison operators including `!=` may be used here, so both
`a!=3;2` and `(s&0xf!=0)||(s>>4)>3;9` are valid error patterns.

Note that `error_patterns` is evaluated in floating-point mode, so a value
used here travels as an IEEE-754 double bit pattern. The bitwise and shift
operators compensate for this internally, and expressions such as
`(8>>2)>0;2` evaluate as written.

#### binary_list

`binary_list` specifies the output codes separated by commas. For example, 0x03,d will output 0x3 followed by d.

Let's take 8048 as an example. If the pattern file contains:

```
ADD A,R!n :: n>7;5 :: n|0x68
```

If you pass `add a,rn` to the assembly line, it will return error code 5 (Register out of range) when n>7, and generate a binary at address 0x69 with `add a,r1`.

If the elements of `binary_list` are empty, alignment is performed. If the beginning starts with a comma, or if it's 0x12,,0x13, etc., the empty part will be padded up to the exact address.

If an element of `binary_list` starts with a semicolon, and that element is 0, it will not be output.

###### @@[]

You can use `@@[n,\<str\>]` within `binary_list`. This means repeating `<str>` n times. To set index %% to 0, use `%0`.

#### symbol

```
.setsym :: symbol :: n
```

Writing this defines a symbol with the value n.

A symbol can be an alphabet, a number, or a sequence of symbols.

To define symbol2 with symbol1, you would write it as follows:

```
.setsym ::symbol1 ::1
.setsym ::symbol2 ::#symbol1
```

Here is an example of a symbol definition in z80. Within the pattern file, if you write:

```
.setsym ::B ::0
.setsym ::C ::1
.setsym ::D ::2
.setsym ::E ::3
.setsym ::H ::4
.setsym ::L ::5
.setsym ::A ::7
.setsym ::BC ::0x00
.setsym ::DE ::0x10
.setsym ::HL ::0x20
.setsym ::SP ::0x30
```

This defines the symbols B, C, D, E, H, L, A, BC, DE, HL, and SP as 0, 1, 2, 3, 4, 5, 7, 0x00, 0x10, 0x20, and 0x30, respectively. Symbols are case-insensitive.

If there are multiple definitions of the same symbol in the pattern file, the newer definition will overwrite the older one. That is,

```
.setsym ::B::0
.setsym ::C::1
ADD A,s

.setsym ::NZ::0
.setsym ::Z::1
.setsym ::NC::2
.setsym ::C ::3
RET s
```

In this case, the C in ADD A,C becomes 1, and the C in RET C becomes 3.

* Example of a symbol containing symbols, numbers, and letters

```
.setsym ::$s5:: 21
```

Symbols are cleared using .clearsym.

```
.clearsym::ax
```

The example above undefines the symbol ax.

To clear all symbols, do not specify any arguments.

```
.clearsym
```

You can determine the character set used for symbols from within the pattern file.

```
.symbolc::<characters>
```

This allows you to specify characters other than numbers and uppercase and lowercase letters using <characters>.

The default is alphabet + numbers + `_%$-~&|`.

Note that `-` is part of the default set. This is what lets a symbol be
followed directly by a negative displacement: the matcher tries the longest
symbol prefix first and falls back, so both of the following work as expected
without any special notation in the pattern file.

```
MOV EAX,[RBX-8]      ; x86_64.axx -> 8b 83 f8 ff ff ff
LD A,(IX-5)          ; z80.axx
```

A consequence of the same rule is that writing a negative value where the
pattern expects a symbol -- for example `ASR #-1` when the instruction has no
immediate form -- is reported as `undefined symbol: '#-1'` rather than as a
range error.

### Symbol Check

```
.check::x::r1,r2,r3
```

If you set this, an error will occur if a symbol other than r1, r2, or r3 appears at the position of x.

To clear .check, use

```
.clrcheck::x
```

`.check` is worth setting whenever a lowercase variable is reused for more
than one class of operand. Without it, the variable accepts **any** symbol
that happens to be defined anywhere in the pattern file, so a nonsensical
operand combination silently assembles into wrong bytes instead of being
rejected. Because `.check` is positional and stays in effect until changed,
place a new `.check` (or a `.clrcheck`) at each point in the file where the
meaning of the variable changes.

The handling of the same mnemonic in registers with different byte lengths is as follows:

```
.setsym::AL::0x00
.setsym::BL::0x01
.setsym::AX::0x00
.setsym::BX::0x01
.check::s::AL,BL
.check::t::AX,BX
MOV s,!a :: 0xb0|s,a
MOV t,!a ::0xb8|t,a,a>>8
```

This allows you to write it as (mov al,0x12,mov bl,0x12) and (mov ax,0x1234,mov bx,0x1234).


#### Double Braces

Optional parts within the instruction can be enclosed in double brackets. This shows the z80 `inc (ix)` instruction.

```
INC (IX[[+!d]]) :: 0xdd,0x34,d
```

In this case, since the initial value of lowercase variables is 0, `inc (ix+0x12)` outputs `0xdd,0x34,0x12` if not omitted, and `inc (ix)` outputs `0xdd,0x34,0x00` if omitted.

#### Specifying Padding Bytecode

From the pattern file,

```
.padding::0x12
```

This sets the padding bytecode to 0x12. The default is 0x00.

#### Specifying the Bit Count for Processors Where Words Are Not in 8-Bit Units

By adding the following to the pattern file:

```
.bits::12
```

You can handle 12-bit processors. The default is 8 bits.

This directive is used to assemble processors with fewer than 8 bits, such as bit-slice processors or processors where machine code words are not in byte units. Since axx outputs in 8-bit units, for a 4-bit processor, the lower 4 bits will be output. For an 11-bit processor, depending on the specified byte order, (lower 8 bits, upper 3 bits) or (upper 3 bits, lower 8 bits) will be output to the binary file in 8-bit increments. Extra bits within 8 bits are masked with 0.

When the `.bits` directive is specified, the value indicated by the address will be in word units. For example, the 64-bit processor x86_64 can process in byte units, so specifying the `.bits` directive is unnecessary.

Byte order is specified as follows:

```
.bits::big::12
```

The `big` option arranges bytes in big-endian format. `little` uses little-endian format.

The default is `little`, and it defaults to `little` even if not specified.

#### include

This allows you to include a file.

```
.include "file.axx"
```

#### Escape Characters in Expressions within Pattern Files

Expressions stop evaluating when they contain the escape character `\`. The handling of escaped characters is saved for later and processed again within the pattern file.

```text:Example
LEAQ r, [ s + t * !h \+ !i ] :: 0x48,0x8d,0x04,((@h)-1)<<6|t<<3|s,i
```

This example processes an assembly line like `leaq rax,[rax+rbx*(2+2)+0x40]` for x86_64.

```
LEAQ r,(s+t*!!h+!!i) :: 0x48,0x8d,0x04,((@h)-1)<<6|t<<3|s,i
```

This example is used in cases like `leaq rax,(rax+rbx*(2+2)+0x40)`.

#### Index Displacement Matching for Negative Values

For example, in the following case:

```
mov rax,[rbp-8]
```

It matches the following pattern:

```
MOV RAX,[RBP+!e]
```

This occurs because when the pattern matcher encounters a '-' in the source, it matches the '-' against the '+' in the pattern; it then skips over the '+' in the pattern and passes the expression starting with '-' directly to the next stage of expression evaluation.

## VLIW Processor

#### .vliw Directive

```
.vliw::128::41::5::00
```

This allows you to handle an EPIC processor with 128 bits in the bundle, 41 bits per instruction, 5 template bits, and a NOP code of 0x00 (Itanium example).

For example, in Itanium, there are three 41-bit instructions, resulting in an instruction set of 41 * 3 = 123 bits in length, plus a 5-bit template bit at the end. For non-EPIC processors, specify 0 for the template bit.

If the template bit is a positive number, it is placed at the right end; if it is a negative number, it is placed at the left end. The number of bits in the template bit is an absolute value. Specifying `big` for the endianness in the `.bits` directive reverses the byte order of the output compared to the default `little`.

##### For EPIC

For EPIC processors, the pattern file is written as follows:

```
/* VLIW
.setsym::R1::1
.setsym::R2::2
.setsym::R3::3
.setsym::R4::4
.vliw::128::41::5::00
EPIC::1,2::0x8|!!!!
EPIC::1::0x01
AD a,b,c:: ::0x01,0,0,a,b,c::1
LOD d,[!e]:: :: 0x00,0x01,0,d,e,e>>8::2
```

Written as above, ``!!!!` represents a stop bit. ``EPIC::1,2::0x8|!!!!` represents a set of EPIC instructions, a bitwise OR code of a bundle of instructions at indices 1 and 2, with a template of 0x8 and a stop bit. The following instruction, `AD a,b,c:: ::0x01,0,0,a,b,c::1`, outputs 0x01,0,0,a,b,c without error checking using ADD instructions r1,r2,r3, with an index code of 1. The instruction `LOD d,[!e]:: :: 0x00,0x01,0,d,e,e>>8::2` stores the contents of [!e] in the LOAD instruction r4, outputs 0,1,0,0xd,e (lower 8 bits) and e (upper 8 bits) without error checking, with an index code of 2. This sample is for testing purposes and differs from actual bytecode.

The parameter specified in .vliw must match the number of bytes represented by the pattern: (Bundle bit count - Template bit count divided by 8 (bits)) + (1 if there is a remainder, 0 otherwise). In EPIC, error patterns must be explicitly specified using `:: ::`.

#### For non-EPIC VLIW

For non-EPIC processors, the pattern file is written as follows:

```
/* VLIW
.setsym::R1::1
.setsym::R2::2
.setsym::R3::3
.setsym::R4::4
.vliw::128::32::0::0x00
AD a,b,c::0x01,a,b,c
LOD d,[!e]::0x02,d,e,e>>8
JMP !a ::0x03,a,a>>8,0
```

##### Instruction Concatenation

To bundle multiple VLIW instructions into one, connect them with !! as shown below.

```
ad r1,r2,r3 !! lod r4,[0x1234]
```

If `!!!` is present in the pattern file's binary_list, `!!!` represents the number of instructions concatenated with `!!`.

If `!!!!` is present at the end of the concatenation, it sets the stop bit.

#### Endianness

Big-endian or little-endian is specified by the output order of the data in binary_list.

## Explanation of the Assembly File

#### Label

Labels are defined from the assembly line in the following way.

Labels defined with `.equ` lose their relocation information and are treated as constants.

```
label1:
label2: .equ 0x10
label3: nop
```

Labels are sequences of letters, numbers, and some symbols, starting with a non-numeric ., an alphabet, or some other symbol.

You define a label using a label as follows:

```
label4: .equ label1
```

You can determine the character set to use for labels from within the pattern file.

```
.labelc::<characters>
```

This allows you to specify characters other than numbers and uppercase and lowercase alphabets using `<characters>`.

The default is alphabet + numbers + underscore + period.

#### ORG

ORG is defined from the assembly line as:

```
.org 0x800
or
.org 0x800,p
```

`.org` modifies the value of the location counter. If `,p` is present, and the previous location counter value is smaller than the value specified by `.org`, padding will be applied up to the value specified by `.org`.

#### Alignment

From the assembly line,

```
.align 16
```

This aligns to 16 (padding with the bytecode specified by `.padding` up to addresses that are multiples of 16). If the argument is omitted, alignment is performed using the number specified by the previous `.align` or the default value.

### Floating-Point Number Notation

For example, suppose a processor (such as ARM64) includes floating-point numbers as operands, and `VMOV.F32 S0, #3.14` loads the float (32-bit) value 3.14 into the S0 register, with its opcode 0x80. In that case, the pattern data will be:

```
VMOV.F32 S!n,#!Fd ::0x80|n,d>>24,d>>16,d>>8,d
```

If you pass `vmov.f32 s0,#3.14` to the assembly line, the binary output will be `0x80,0xc3,0xf5,0x48,0x40`. If `!F` becomes `!D`, it's a double-precision floating-point number. `!Q` is a 128-bit floating-point number.

Use the prefix `0b` for binary numbers.

Use the prefix `0x` for hexadecimal numbers.

#### Float notation in expressions

`!F` / `!D` / `!Q` capture a floating-point operand at a position in the
instruction. To write a floating-point value inside an ordinary integer
expression -- for instance to give it a name with `.equ` -- use the brace
notation instead. It evaluates its body as floating point and yields the
IEEE-754 bit pattern as an integer.

```
flt{expr}     ; 32-bit  (binary32) bit pattern
dbl{expr}     ; 64-bit  (binary64) bit pattern
qad{expr}     ; 128-bit (binary128) bit pattern
```

The inverse direction is provided by functions usable inside those bodies:

```
enfloat(v)  / enflt(v)     ; read v's low 32 bits back as a float
endouble(v) / endbl(v)     ; read v's low 64 bits back as a double
```

This makes a named floating-point constant possible, since the stored label
holds a bit pattern that can be decoded again and recomputed:

```
c1: .equ flt{3.14}
    LDF A,flt{enfloat(:c1)*2}
```

`:label` inside such an expression refers to the label's value directly.

`inf`, `-inf` and `nan` are accepted as floating-point values.

#### Strings

`.ascii` outputs the bytecode of a string, and `.asciz` outputs the bytecode of a string with 0x00 at the end.

```
.ascii "sample1"
.asciz "sample2"
```

#### Fill with 0x00

`.zero <expression>` fills the specified number of bytes with 0x00.

```
.zero 65536
```

#### reserve

Each reserves storage without emitting bytes. Simply increment the location
counter. `.resb` counts bytes; `.resw`, `.resd` and `.resq` count 2-, 4- and
8-byte units respectively.

```
.resb n ; reserve n bytes
.resw n ; reserve n words       (n*2 bytes)
.resd n ; reserve n doublewords (n*4 bytes)
.resq n ; reserve n quadwords   (n*8 bytes)
```

#### export

The following allows you to export a label along with section/segment information. Only the label specified by the `.export` command is exported.

```
.export label
.export label1,label2,label3     ; several labels at once
```

The exported labels are written out by the `-e` / `-E` options. See
[Export / import file format](#export--import-file-format) below.

#### .global

Pass the label externally. Like `.export`, it accepts a comma-separated list,
and the labels it declares are written out by `-e` / `-E` as well.


```
.global label
.global label1,label2
```

#### .extern

Declares the loading of an external label. A comma-separated list is accepted,
and a relocation type may be attached to an individual name with `:`.

```
.extern label
.extern label1,label2
.extern label1:2,label2          ; label1 uses relocation type 2
```

`.extern` and `-i` are designed to be combined: `-i` supplies the actual
address of an external label, and `.extern` declares that the name is
resolved elsewhere. When both name the same label, the value brought in by
`-i` is kept.

.global and .extern are processed by the ELF relocatable object file output function.

#### Section-related directives

In addition to `.section`/`.segment` below, the following are accepted:

```
.bss                ; switch to the .bss section
.rodata             ; switch to the .rodata section
.endsection         ; end the current section
.endsegment         ; end the current segment
```

#### .reloctype

Overrides the machine's default width-guess relocation type for
auto-detected label references in the current source file.

```
.reloctype name8,name16,name32,name64
```

#### .section

You can specify a section/segment as shown below.

```
.section .text
or
.segment .text
```

Currently, .section and .segment have the same meaning.

#### section sort

For example, with `z80.axx`:

```
.section .text
ld a,9
.section .data
.asciz "test1"
.section .text
ld b,9
.section .data
.ascii "test2"
```

If you do this, the elements will be arranged exactly as written, so use secsort.py to sort them.

```
.section .text
ld a,9
ld b,9
.section .data
.asciz "test1"
.ascii "test2"
```

Note that a byte-emitting mnemonic such as `DB` is **not** built into axx; it
only exists if the pattern file defines it. Among the bundled pattern files,
`8048.axx` and `x86_64.axx` define `DB`, while `z80.axx` does not. The built-in
data directives that are always available regardless of the pattern file are
`.ascii`, `.asciz`, `.zero` and the `.resb`/`.resw`/`.resd`/`.resq` family.

#### include

This is how you can include a file.

```
.include "file.s"
```

#### Comments

Comments in the assembly line are `;`.

## Expressions, Operators, and Special Terms

A special term is `!!!`. This term represents the number of instructions connected by !!.

`%%` returns the number of times %% has appeared (an index starting from 0).

`$$` returns the value of the current location counter.

`$.` returns the starting address of the instruction following that instruction.

Both the assembly line expression and the pattern data expression call the same function, so their function is almost identical. Lowercase variables cannot be referenced from the assembly line.

### Operator Precedence

Operators and their precedence are based on Python and are as follows:

```
(expression) Expression enclosed in parentheses
# Operator that returns the value of symbol
*(x,y) The yth byte from the least significant bit of x (y>=0)
-,~ Negative, bitwise NOT
@ Unary operator that returns the position of the most significant bit of the following value from the right
'c' Character code for 'c'
:= Assignment operator
** Exponentiation
*,/,// Multiplication, division, integer division
+,- Addition, subtraction
<<,>> Left shift, right shift
& Bitwise AND
| Bitwise OR
^ Bitwise XOR
' Sign extension
<=,<,>,>=,!=,== Comparison operators
not(x) Logical NOT
&& Logical AND
|| Logical OR
x?a:b Ternary operator
```

`:=` is used as an assignment operator. When you write `d:=24`, the value 24 is assigned to the variable `d`. The value held by the assignment operator is the value that was assigned.

The prefix operator `#` takes the value of the symbol that follows it.

The prefix operator `@` returns the position of the most significant bit of the following value from the right. We'll call this the Hebimarumatta operator.

The binary operator `'`, when written as `a'24`, performs sign extension by making the 24th bit of `a` the sign bit. We'll call this the SEX operator.

The binary operator `**` is exponentiation.

The ternary operator `?:`, in `x?a:b`, returns `a` if `x` is true, and `b` if `x` is false.

### Prompt Mode

When the prompt `>>` appears and you are typing from the keyboard, you can use the label display command `?`.

## Example

#### Z80

```
.setsym:: BC:: 0x00
.setsym:: DE:: 0x10
.setsym:: HL:: 0x20
LD s,!d:: (s&0xf!=0)||(s>>4)>3;9 :: s|0x01,d&0xff,d>>8
```

Then, `ld bc,0x1234`, `ld de,0x1234`, and `ld hl,0x1234` will output 0x01,0x34,0x12, 0x11,0x34,0x12, and 0x21,0x34,0x12, respectively.

## Testing some instructions on some processors

This is a test, so the binary is different from the actual code.

```test.axx
/* test
.setsym ::a:: 7
.setsym ::b:: 1
.setsym ::%% ::7
.setsym ::||:: 8
LDF A,!Fx :: 0x1,x,*(x,1),*(x,2),*(x,3)
LDD A,!Dx :: 0x1,@@[8,*(x,%%)]
LDQ A,!Qx :: 0x1,@@[16,*(x,%%)]
LDR A,[ [ !x ] ]:: ~~0x3?3:0,x,x>>8
LD\! A,B::0xcd

/* ARM64
.setsym ::r1 :: 2
.setsym ::r2 :: 3
.setsym ::r3 :: 4
.setsym ::lsl:: 6
VMOV.F32 S!n,#!Fd::0x80|n,d>>24,d>>16,d>>8,d
ADD w, x, y z #!d :: 0x88,d
.check ::q::r1,r2
ADD q, y, !e :: 0x91,q,y,e
.clrcheck::q

/* A64FX
.setsym ::v0 :: 0
.setsym ::x0 :: 1
ST1 {x.4S},\[y\] :: 0x01,x,y,0

/* MIPS
.setsym ::$s5 ::21
.setsym ::$v0 ::2
.setsym ::$a0 ::4
ADDI x,y,!d :: @@[4,*(e:=(0x20000000|(y<<21)|(x<<16)|d&0xffff),(3-%%))]

/* x86_64
.setsym ::rax:: 0
.setsym ::rbx:: 3
.setsym ::rcx ::1
.setsym ::rep ::1
.setsym ::per::2
.clearsym::per

MMX A,B ::  ,0x12,0x13
LEAQ r,\[s,t,!d,!e\] :: 0x48,0x8d,0x04,((@d)-1)<<6|t<<3|s,e
LEAQ r, ( s+t*!h\+!i) :: 0x48,0x8d,0x04,((@h)-1)<<6|t<<3|s,i
[[z]]MOVSB :: ;z?0xf3:0,0xa4
TEST !a:: a==3?0xc0:4,0x12,0x13

/* ookakko test
LD (IX[[+!d]]),(IX[[+!e]]):: 0xfd,0x04,d,e 
NOP :: 0x01
LOAD A,[B] :: 0x43
REPEAT !n::@@[n,%%],%0@@[n,0x10+%%]
```

```test.s
ldf a,3.14
ldf a,3.14*2+1
ldd a,3.14
ldd a,-inf
ldq a,3.14*2+1
leaq rax , [ rbx , rcx , 2 , 0x40]
leaq rax , ( rbx + rcx * (2+2) + 0x40 )
addi $v0,$a0,5
vmov.f32 s0,#3.14
st1 {v0.4s},[x0]
add r1, r2, r3 lsl #20
rep movsb
movsb
load a,[b]
repeat 10
ldf a,label
label: .equ flt{3.14}
ldf a,flt{enfloat(:label)*2}
```

##### Execution example

```
$ axx.py test.axx test.s -v
0000000000000000 test.s 1 ldf a,3.14  0x01 0xc3 0xf5 0x48 0x40
0000000000000005 test.s 2 ldf a,3.14*2+1  0x01 0xc3 0xf5 0xe8 0x40
000000000000000a test.s 3 ldd a,3.14  0x01 0x1f 0x85 0xeb 0x51 0xb8 0x1e 0x09 0x40
0000000000000013 test.s 4 ldd a,-inf  0x01 0x00 0x00 0x00 0x00 0x00 0x00 0xf0 0xff
000000000000001c test.s 5 ldq a,3.14*2+1  0x01 0x1f 0x85 0xeb 0x51 0xb8 0x1e 0x85 0xeb 0x51 0xb8 0x1e 0x85 0xeb 0xd1 0x01 0x40
000000000000002d test.s 6 leaq rax , [ rbx , rcx , 2 , 0x40]  0x48 0x8d 0x04 0x4b 0x40
0000000000000032 test.s 7 leaq rax , ( rbx + rcx * (2+2) + 0x40 )  0x48 0x8d 0x04 0x8b 0x40
0000000000000037 test.s 8 addi $v0,$a0,5  0x20 0x82 0x00 0x05
000000000000003b test.s 9 vmov.f32 s0,#3.14  0x80 0x40 0x48 0xf5 0xc3
0000000000000040 test.s 10 st1 {v0.4s},[x0]  0x01 0x00 0x01 0x00
0000000000000044 test.s 11 add r1, r2, r3 lsl #20  0x88 0x14
0000000000000046 test.s 12 rep movsb  0xf3 0xa4
0000000000000048 test.s 13 movsb  0xa4
0000000000000049 test.s 14 load a,[b]  0x43
000000000000004a test.s 15 repeat 10  0x00 0x01 0x02 0x03 0x04 0x05 0x06 0x07 0x08 0x09 0x10 0x11 0x12 0x13 0x14 0x15 0x16 0x17 0x18 0x19
000000000000005e test.s 16 ldf a,label  0x01 0xec 0x91 0x80 0x4e
0000000000000063 test.s 17 label: .equ flt{3.14} 
0000000000000063 test.s 18 ldf a,flt{enfloat(:label)*2}  0x01 0xec 0x91 0x81 0x4e
```

This is what an AArch64 logical immediate looks like. This is likely the most complex example. Logical immediates and the like can be consolidated into a single entity using macros.
```
AND d,n,#!v ::v==0;3,v==0xFFFFFFFFFFFFFFFF;3 ::;(e:=((v&3)*0x5555555555555555==v)?2:((v&0xf)*0x1111111111111111==v)?4:((v&0xff)*0x0101010101010101==v)?8:((v&0xffff)*0x1000100010001==v)?16:((v&0xffffffff)*0x100000001==v)?32:64)*0,;(m:=(1<<e)-1)*0,;(y:=v&m)*0,;(t:=@(y^(y-1))-1)*0,;(u:=y>>t)*0,;(w:=(y^m)==0?1:y^m)*0,;(p:=@(w^(w-1))-1)*0,;(q:=w>>p)*0,;(c:=((u+1)&u)==0)*0,;(b:=c?@u:e-@q)*0,
 ;(r:=c?(e-t)&(e-1):(e-(p+@q))&(e-1))*0,;(s:=((0-2*e)&0x7f)|(b-1))*0,;(z:=(1<<31)|(0x24<<23)|((((s>>6)&1)^1)<<22)|(r<<16)|((s&0x3f)<<10)|(n<<5)|d)*0,@@[4,z>>(%%*8)]
```
### errors

- If a label conflicts with a symbol in the pattern file, an "is a pattern file symbol" error occurs.

- Defining the same label more than once results in a "label already defined" error.

- If parsing is not possible, a "Syntax error" occurs.

- Referencing an undefined label results in a "Label undefined" error.

- If the syntax is incorrect, an "Illegal syntax in assembler line or pattern line" error occurs.

- If the EPIC template is not set, a "No VLIW instruction-set defined" error occurs.

- If the VLIW pattern file is incorrect, errors in the VLIW definition are reported during interpretation.

- An error will occur if any of the conditions in `error_patterns` are met. The code written after `;` selects the message:

| Code | Message |
|---|---|
| 1 | Invalid syntax. |
| 2 | Address out of range. |
| 3 | Value out of range. |
| 4 | (none) |
| 5 | Register out of range. |
| 6 | Port number out of range. |
| 7 and above | (none) |

  A code with no message still raises the error and still stops the output
  file from being written; only the text is blank. If there are not enough
  error types, please add error messages to the `ERRORS` table in the source
  code (`axx.py`, and the matching table in `caxx.c`).

### Macro -- axx Macro Layer Syntax Reference

The same material is kept as a standalone document in `MACRO.md` (Japanese)
and `macro_en.md` (English).

This is a source-to-source transformation stage that runs before the source is passed to the main assembler. Label values, `.equ` definitions, and `$` or `$$` symbols cannot be referenced (to ensure that expansion results remain consistent across relaxation passes).

It is implemented with identical specifications in both `axx.py` and `caxx.c`. The only difference between the two is numeric representation: the Python version uses arbitrary-precision integers, while the C version uses `int64`. Results will differ only when macro-time calculations exceed 64 bits (since the macro layer outputs source text, this does not affect the main assembler's 256-bit expression evaluation).

#### Statements

All statements begin with `!` at the start of the line (ignoring leading whitespace).

| Syntax | Meaning |
|---|---|
| `!def name(p1, p2, p3 = default) { ... }` | Macro/compile-time function definition |
| `!return expr` | Return value; also serves as an early exit from the body |
| `!if expr !then { ... } !elif expr !then { ... } !else { ... }` | Conditional branching |
| `!while expr { ... }` | Loop |
| `!break` / `!continue` | Loop control |
| `!set name = expr` | Assign by searching scopes from inner to outer; create in current scope if not found |
| `!local name [= expr]` | Declare in the current scope |
| `!undef name` | Delete variable/macro |
| `!name(a, b)` | Expand macro as a statement |
| `!include "file"` | Include text at macro-expansion time |
| `!error expr` | Abort expansion and report error |
| `!warning expr` / `!echo expr` | Output to stderr |

The opening `{` must appear at the end of the header line, and the closing `}` at the start of a line. `; comment` may be written after a statement.

#### Embedding in Expressions

| Notation | Meaning |
|---|---|
| `!{expr}` | Expand value to text |
| `!{expr:04x}` | Apply Python-style formatting |

The format spec is Python's format mini-language. Both implementations
implement the same grammar, and agree on which specs are accepted, which are
rejected, and the wording of the resulting error.

```
[[fill]align][sign][z][#][0][width][grouping][.precision][type]
  align     ::= "<" | ">" | "=" | "^"
  sign      ::= "+" | "-" | " "
  grouping  ::= "," | "_"
  type      ::= b c d e E f F g G n o s x X %
```

`!{255:#06x}` gives `0x00ff`, `!{1234567:,d}` gives `1,234,567`, `!{255:*^9b}`
gives `*11111111*`, `!{255:.2f}` gives `255.00`. Python's restrictions apply
too: no precision on integer types, no `,` with `x`/`X`/`o`/`b`/`c`/`n`, no
sign or `#` on a string.

Both implementations strip whitespace around the spec before interpreting it,
so Python's space-as-sign form (`!{5: d}`, which Python renders as `' 5'`) is
the one thing that cannot be expressed; it behaves like `!{5:d}`.

**Known difference**: `!{0:c}` (code point 0) yields a NUL character from
axx.py, but an empty string from caxx, which cannot carry a NUL inside a C
string.
| `\!{` | Literal `!{` |

#### Values and Operators

Values are limited to integers and strings. Operators are C-compliant:
`?:` `||` `&&` `|` `^` `&` `==` `!=` `<` `<=` `>` `>=` `<<` `>>` `+` `-` `*` `/` `%`
plus unary `-` `+` `~` `!`. `/` and `%` truncate towards zero, just like in C (`-7/2 == -3`).
`+` performs concatenation if either operand is a string; `"ab" * 3` performs repetition.
Integer literals: `10` / `0x1f` / `0b1010` / `0o17` (underscores allowed).
`'A'` is treated as a character code if it is a single character, or a string if multiple characters.

#### Built-in Functions

`len(s)` `hex(v[,digits])` `str(v)` `int(s[,base])` `upper(s)` `lower(s)`
`substr(s,start[,length])` `abs(v)` `min(...)` `max(...)` `uid()` `defined(name)`

`substr()` clamps its start and length to the string. A negative start means
the beginning (0), *not* Python-style indexing from the end; a negative length
is treated as 0.

#### Implicit Variables in Macros

| Name | Content |
|---|---|
| `__id__` | Integer unique to each invocation (for generating local labels) |
| `__name__` | Macro name |

#### CLI

| Option | Meaning |
|---|---|
| `--no-macro` | Completely disable the macro layer |
| `-P [FILE]`, `--macro-expand [FILE]` | Output only the expanded source and exit (defaults to stdout) |
| `-p [FILE]`, `--macro-expand-pattern [FILE]` | Output only the expanded pattern file and exit (defaults to stdout) |

caxx.c uses the same option names. To allow the filename to be omitted, the `-P` option in the C version interprets the subsequent argument as the output destination only when placed after both the pattern file and the source file have been specified (e.g., `caxx pat.axx src.s -P out.s`). `-p` follows the same rule. `--no-macro` disables both the source-side and the pattern-side layer.

#### Macros in Pattern Files

Pattern files (`.axx`) go through the same macro layer as source files. An instruction table tends to consist of rows of the same shape that differ only in a register number or an opcode, so those rows can be generated instead of written out by hand:

```
!def alu(name, base) {          /* pattern-file comment syntax, on a statement line
!local r = 0
!while r < 8 {
!{name} A,R!{r} :: 0x!{base + r:02x}
!set r = r + 1
}
}
!alu("ADD", 0x80)
!alu("SUB", 0x90)
```

The error field can be generated too, so a range check written once is applied to every generated row:

```
!def imm(name, op) {
!{name} A,!v :: v>0xff;2,v<0;2 :: 0x!{op:02x},v
}
!imm("ADDI", 0xc6)
!imm("SUBI", 0xd6)
```

Only three things differ from the source side; the syntax, the built-in functions and the runaway guards are all the same.

1. **A separate namespace.** The pattern side and the source side have independent macro environments and cannot see each other's macros or variables. A pattern file's macros can therefore never change how a source file expands, and the per-pass reset the source side performs during relaxation can never wipe macros defined while reading the pattern file.
2. **Comments on statement lines start with a slash-star sequence**, matching pattern-file convention. `;` is not a comment marker there, because it separates the error-code suffix of a pattern's error field (`v>0xff;2`).
3. **A stricter engage condition.** In a pattern file `!` is the pattern-variable sigil (`ADD A,!d`), so it appears on nearly every line. The layer is therefore engaged only when a line would really be taken as a macro statement, or contains an unescaped `!{...}`, or starts with `}`. A pattern file that uses no macros skips the layer entirely: every pattern file shipped with axx expands to itself byte-for-byte and assembles in the same time as before.

`.INCLUDE` on the pattern side is processed *after* macro expansion, so a macro can generate the `.INCLUDE` line itself. Each `.INCLUDE`d pattern file is macro-expanded in turn, inheriting the macros defined by the top-level pattern file.

Use `-p` to see the generated pattern text without assembling.

#### Backward Compatibility

- Lines starting with `!` are intercepted only if they contain a keyword, a predefined macro name, or are immediately followed by `(`.
VLIW-specific `!!` and `!F` / `!D` / `!Q` constructs remain untouched.
- A `}` at the start of a line is treated as a closing brace only when a block is currently open.
- Output for source code containing no macros remains identical to previous behavior.

#### Limitations

- Source-side `.INCLUDE` directives bypass the macro layer; use `!include` to import macro definition files. (Pattern-side `.INCLUDE` does run the included file through the macro layer.)
- Constructs like `!{a ? b : c:04x}` (combining a ternary operator with format specifiers) cannot currently be parsed.
- Interactive mode (when no source file is specified) bypasses the macro layer.

#### Runaway Protection

Limits: 200 levels of recursion, 1,000,000 `!while` iterations, 2,000,000 generated lines, and a nesting depth of 64 for `!include`.
Exceeding any of these limits triggers an error, and expansion is aborted for the remainder of the pass.

#### Example

```asm
!include "lib.inc"

!def table(name, from, to) {
!{name}:
!set v = from
!while v <= to {
DB !{v}
!set v = v + 1
}
}

!def loopblk(n) {
!if n == 0 !then {
!return
}
L!{__id__}_top:
LD A,!{n}
LD HL,L!{__id__}_top
}

!def sq(x) {
!return x * x
}

start:
LD HL,end
!table("mytab", 1, 5)
!loopblk(2)
LD HL,!{sq(16)}
end:
NOP
```

### Comments

* Apologies for the unconventional notation.

* It may be an unreasonable thing to ask for, but axx does not support quantum computers or LISP machines. The assembly language for quantum computers is called quantum assembly, not assembly language, and programs for LISP machines are not assembly language either.

* From homemade processors to supercomputers, please feel free to use it.

* Please evaluate, extend, and modify axx. The structure is complex, but since it's written in Python, extension is easy. Please feel free to extend it.

* Currently, only quadruple-precision floating-point numbers can be handled as constants. This is due to the Python 3 specification. It would be great if Python 4 could handle quadruple-precision floating-point numbers.

* Macro functionality is built in, but to cover all assembly languages, a high-performance macro processor is needed to translate high-level assembly constructs — such as functional and structured assembly languages — into imperative assembly language.

* Specifying the `-i` option imports labels from a TSV file. Specifying the `-e` option exports the labels specified in `.export`, along with the section/segment to which they belong, to a TSV file.

* Creating axx pattern files is difficult with a large ISA, and since the specifications are fixed, I hope that AI can handle this. While assemblers were originally created to make machine code easier for humans to understand, in today's world where AI writes code, a generalized assembler for both assembly language and computers would be beneficial.

### Unimplemented Items

* If one were to prepare pattern files for axx and add advanced structured macros and optimization features, it would become a truly impressive system; however, since it is difficult for a single individual to cover the full range of structured assembly-style macros, I hope someone else will take on the task. I would be delighted to see this realized.

### axx2 (the next generation of axx) concept. Explanation of pattern files (processor description files). Feature not available now.

- Using a more descriptive metalanguage for pattern files would improve readability, eliminate dependency on evaluation order, make control statements easier to write, and make processor description file debugging easier. However, pattern data is more intuitive. Further generalizing the metalanguage and using a descriptive metalanguage for pattern files, adding string literals, string operations, and numeric operations to binary_list, and adding control statements, would enable the generation of intermediate languages and converters between assembly languages. In this case, the binary_list would be renamed object_list, and the pattern file would be renamed processor_specification_file. The metalanguage would be a multi-line description language rather than pattern data. This is feasible. Apparently, someone is currently working on it based on axx. Even in pattern files, you can write macros smartly by setting a='MOV b,c', assigning commands (strings) to character variables (currently lowercase letters, but if you expand this to what we normally call symbols), and writing them in binary_list. Allowing loop structures makes debugging difficult if an infinite loop occurs during processing within axx.py, but allowing evaluation only in pattern files simplifies debugging and allows loop and branch structures. Turing-completeness allows processing of any processor architecture. Lisp machines are also possible in principle. Self-reference checks are required. Use expand(a) to expand. For example, if a='b ; c' b='MOV AX,d' c='JMPC e', the result becomes 'MOV AX,d ; JMPC e'. Use expression(a) to evaluate the expression, and label: to define the label. Keeping labels separate in the processor description file and the assembly file eliminates the need to worry about the same label appearing in both. Meta-processing like EPIC is solved by enumerating variables. Making it a descriptive metalanguage requires drastic rewriting. If the assembler's processor characteristic description file becomes complex, it becomes difficult to make the file compatible with General Disassembler.

### Request

If you find a bug, I would appreciate it if you could let me know what isn't working in axx.

### Acknowledgements

I would like to express my gratitude to my mentor, Junichi Hamada, and Tokyo Denshi Sekkei, who gave me the problems and hints, the University of Electro-Communications, the computer scientists and engineers, Qiita, Google, IEEE, The Alan Turing Institute and some unforgettable people. I received a passing grade from Emeritus professor Kameda of the Information Processing Society of Japan. Thank you very much.

### English is not my mother tongue, so this document was translated with Google Translate. There may be some mistakes, and I apologize for my broken English.

### Mascot Character

<img alt="image" width="200px" height="200px" src="https://github.com/fygar256/axx/blob/main/axxgirl.png">

