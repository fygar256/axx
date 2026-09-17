# axx — General Assembler

axx (**A**rbitrary e**X**tended **X** assembler) is a *general* assembler: the
assembler itself holds no knowledge of any instruction set. All
processor-specific knowledge lives in an external, declarative **pattern file**.
Writing a pattern file for a processor gives you an assembler for it.

## Quick start

```sh
git clone https://github.com/fygar256/axx.git
cd axx
make                            # builds and installs caxx, paxx, axx and the man page (uses sudo)
```

To build only the C implementation:

```sh
gcc caxx.c -o caxx -lm -O2      # -lm is required: the expression evaluator uses libm
```

Assemble:

```sh
axx z80.axx z80.s -v            # listing to stdout
axx z80.axx z80.s -b out.bin    # raw binary
axx x86_64.axx hello.s -o out.o # ELF relocatable object
```

## Two implementations

| Language | File | Nickname | Role |
|---|---|---|---|
| Python | `axx.py` | Paxx | Reference implementation; new features land here first |
| C | `caxx.c` | Caxx | Much faster; may lag behind Paxx |

The two are intended to produce **byte-identical output** for the same input.
The bundled pattern files, test sources and the `test1` script exist to check
exactly that: `test1` assembles fourteen bundled pattern/source pairs with both
implementations and `cmp`s the results.

**Contents**

1. [Scope: what axx can and cannot do](#1-scope-what-axx-can-and-cannot-do)
2. [Command line](#2-command-line)
3. [Pattern file reference](#3-pattern-file-reference)
4. [VLIW and EPIC processors](#4-vliw-and-epic-processors)
5. [Assembly source reference](#5-assembly-source-reference)
6. [Expressions and operators](#6-expressions-and-operators)
7. [Macro layer](#7-macro-layer)
8. [Object output, export and import](#8-object-output-export-and-import)
9. [Errors](#9-errors)
10. [Design notes and background](#10-design-notes-and-background)

Appendices: [A. Examples](#appendix-a-examples) ·
[B. Bundled pattern files](#appendix-b-bundled-pattern-files) ·
[C. Related resources](#appendix-c-related-resources) ·
[D. Roadmap](#appendix-d-roadmap) ·
[E. Project notes](#appendix-e-project-notes)

---

## 1. Scope: what axx can and cannot do

Read this section first. The rest of the document assumes you know where the
boundary is.

### 1.1 The model

Every pattern in a pattern file has this shape:

```
instruction :: error_patterns :: binary_list
```

- `instruction` — the syntax to match against an assembly line. Mandatory.
- `error_patterns` — conditions that make the line an error. Optional.
- `binary_list` — the bytes to emit. Mandatory.

Example (x86_64):

```
RET :: 0xc3
```

That is the whole model. The claim axx makes rests on two separate legs, and
they have different reach:

### 1.2 Leg one: instruction syntax — very wide

An `instruction` is any combination of

- string literals (uppercase letters, digits, symbols),
- symbols replaceable by integer values,
- integer expressions,
- integer factors,
- floating-point expressions.

This is enough to express the *surface syntax* of essentially any imperative
assembly language, and it is not restricted to conventional mnemonic-plus-
operand forms. `r1 = r2 + r3` is a legal instruction pattern, which makes axx
usable as a general binary generator rather than only as an assembler.

### 1.3 Leg two: binary generation — deliberately narrower

`binary_list` has only five control structures: assignment, the ternary
operator, the `;` modifier, alignment, and `@@[]`. This is **not** a universal
encoder. The practical condition is:

> axx can assemble a processor whose instructions map **one-to-one** onto
> machine code.

Two consequences follow, and both are design decisions rather than oversights:

**The pattern notation itself is Turing-incomplete.** This guarantees that
pattern *matching* terminates. An encoding that needs unbounded computation
cannot be written in `binary_list` alone.

**Unbounded computation is available, but only by asking for it.** A
`binary_list` element may be `.call name(...)`, which runs a function written in
the **mini language** of [section 3.15](#315-mini-language-func--call) — loops,
recursion, conditionals and arrays, and therefore Turing complete. Matching
still terminates; only the encoding step can compute without a fixed bound, and
it is bounded in practice by the step, depth and output caps in section 3.15.
(The macro layer in section 7 is a third, earlier stage and is likewise not
restricted.)

**Some real architectures fall outside the model.** Not because their syntax
cannot be written down, but because their encoding cannot be produced by
`binary_list`:

| Processor | Why it is out of scope |
|---|---|
| Mill CPU | Belt architecture: operand references depend on execution history |
| ZISC | Has no instructions at all |
| Thinking Machines | Massively parallel; no per-instruction encoding to target |

Quantum computers and LISP machines are also out of scope; what they run is
not an imperative assembly language.

EPIC and VLIW machines have meta-level structure in their machine code that the
basic model does not cover, and are handled by a later extension — see
[section 4](#4-vliw-and-epic-processors).

### 1.4 Where axx sits relative to other tools

axx operates at a **lower level of abstraction** than LLVM, CGen or customasm.
It is not a "general-purpose assembler" in the sense of being widely usable
out of the box; it is a "general assembler" in the sense of having one common
mechanism underneath every target.

It does not do the optimizations a hand-written assembler for a specific chip
would do, and it does not translate structured or functional assembly
constructs down into imperative form. It does have a full macro layer
(section 7).

Because the pattern file and the source file are separate, one source can be
assembled for a different processor by swapping the pattern file, and a common
source language can target several processors. Whether that is *useful* depends
entirely on how much work you are willing to put into the pattern files.

### 1.5 Practical note on writing pattern files

Writing a pattern file for a large ISA is a long job, but a finished one is
done for good and is reusable. The format is declarative and mechanical, which
makes it a reasonable target for AI-assisted generation — for a small ISA you
can have a model produce the pattern file and have a working assembler quickly.

If a pattern proves hard to express, the fallback is always available: pass
only the operands that really need evaluating, and write the rest as string
literals. Parts of an ISA that resist structure can simply be enumerated.

The execution platform is not significant. `chr(13)` at the end of DOS lines is
ignored, and Paxx runs anywhere Python 3 runs.

---

## 2. Command line

### 2.1 Synopsis

```
axx [-h] [--osabi ELF_OSABI] [-b OUTFILE] [-e EXPORT_TSV]
    [-E EXPORT_ELF_TSV] [-i IMPORT_TSV] [-o OBJ_FILE] [-f {32,64}]
    [-m MACHINE] [-v] [-d] [-g] [--no-macro] [-P [FILE]] [-p [FILE]]
    patternfile [sourcefile]
```

| Argument | Meaning |
|---|---|
| `patternfile` | Pattern definition file (`.axx`). Required. |
| `sourcefile` | Assembly source (`.s`). Omit to read from stdin (prompt mode). |

| Option | Meaning |
|---|---|
| `-b OUTFILE` | Write raw binary |
| `-o OBJ_FILE` | Write ELF relocatable object; class selected by `-f` |
| `-f {32,64}` | ELF class for `-o`. Default 64 |
| `-m MACHINE` | ELF `e_machine` value. Default 62 (`EM_X86_64`) |
| `--osabi ELF_OSABI` | ELF OSABI. Default FreeBSD; FreeBSD/Linux, case-insensitive |
| `-e EXPORT_TSV` | Export labels to TSV (plain format) |
| `-E EXPORT_ELF_TSV` | Export labels to TSV (with ELF section flags) |
| `-i IMPORT_TSV` | Import labels from TSV |
| `-v`, `--verbose` | Print assembly listing to stdout (default: silent) |
| `-d`, `--debug` | Debug output: forward-ref fallback, relaxation log |
| `-g`, `--gen-debug` | Emit DWARF (`.debug_info`/`.debug_abbrev`/`.debug_line`). Requires `-o` and ELF64 |
| `--no-macro` | Disable the macro layer on both the source and pattern side |
| `-P [FILE]` | Macro-expand the source and write it out without assembling |
| `-p [FILE]` | Macro-expand the pattern file and write it out without assembling |
| `-h`, `--help` | Usage |

If no output option is given, nothing is written; `-v` is what makes the run
visible.

### 2.2 ELF output

`-o` produces a relocatable object and works on FreeBSD and Linux. It is not
limited to x86_64. `-m` accepts any architecture axx has relocation numbering
for:

| Value | Machine | Value | Machine |
|---|---|---|---|
| 3 | i386 | 43 | SPARCV9 |
| 4 | M68K | 62 | x86-64 (default) |
| 20 | PowerPC | 183 | AArch64 |
| 21 | PowerPC64 | 243 | RISC-V |
| 22 | s390x | | |
| 40 | ARM | | |
| 42 | SuperH | | |

`-f` selects ELF32 or ELF64 independently of `-m`. A combination that is not
conventional for the chosen machine (for example `-m 62 -f 32`, the real x32
ABI layout) is honored, with a warning.

### 2.3 Differences in the C version

`caxx` takes the same option names as `axx.py`, except:

- `-h` / `--help` is not accepted. Run `caxx` with no arguments for usage.
- `-d` / `--debug` is not implemented.
- Because the filename after `-P` may be omitted, `caxx` treats the next
  argument as the output file only when both the pattern file and the source
  file have already been given: `caxx pat.axx src.s -P out.s`. `-p` follows the
  same rule.

### 2.4 Prompt mode

With no source file, axx reads assembly lines from the terminal at a `>>`
prompt. `?` displays the label table. The macro layer is bypassed in this mode.

---

## 3. Pattern file reference

### 3.1 Structure

A pattern file is a processor description file. It is a small ISA description
language (ISADL) — a metalanguage for the relationship between assembly text
and machine code.

```
instruction :: error_patterns :: binary_list
instruction :: error_patterns :: binary_list
:
```

The three fields are separated by `::`. `error_patterns` may be empty, but if
you omit it entirely the line has only one `::`, which is the two-field form.

**Comments.** `/*` starts a comment. If `*/` appears later on the *same* line,
only the text between `/*` and `*/` is removed and the rest of the line is
read normally — `/* note */ MORE` keeps `MORE`. Otherwise the comment behaves
like a real block comment and continues onto the following lines until a line
containing `*/` is found; text after that `*/` on the closing line is read
normally again.

For backward compatibility with older pattern files that write `/*` at the
start of every commented line instead of opening one real block, a comment
does **not** extend past its own line when either of these holds:

- the very next line itself begins with `/*`, or
- no `*/` occurs anywhere later in the file at all.

In both cases the line is truncated at its own `/*` and nothing carries over,
matching the original single-line behavior — and a whole run of such lines is
treated the same way, including the run's last line even though the line
right after it is ordinary (non-comment) content.

In short: closing every block comment with its own `*/`, and opening every
commented line with its own `/*`, are both fully supported conventions and
may be mixed freely within one file.

### 3.2 Pattern order does not matter

Directive definitions **are** order-dependent — a later `.setsym` overrides an
earlier one, and `.check` applies from where it appears. **Patterns are not.**

axx does not stop at the first pattern that matches. It tries every pattern,
scores each successful match, and emits the best one. The score is the tuple

```
(n_expr, -n_lit, n_sym)
```

where `n_expr` counts `!`-prefixed expression captures, `n_lit` counts literal
characters matched, and `n_sym` counts symbol captures. The **smallest** tuple
wins, which reads as:

1. Fewest expression captures.
2. On a tie, the most literal characters matched.
3. On a tie, the fewest symbol captures.

In other words the most specific pattern wins, whatever order it sits in. Given

```
MOV A,!d :: 0xAA,d
MOV A,B  :: 0xBB
```

`mov a,b` emits `0xBB` and `mov a,5` emits `0xAA 0x05`, and swapping the two
lines changes nothing.

This removes the bookkeeping that table-driven assemblers usually demand —
there is no need to hand-sort an instruction table so that special forms
precede general ones. It matters most in a large pattern file, where the
special cases are far from the general rule they override.

### 3.3 Case and variables

In the `instruction` field:

| Written as | Meaning |
|---|---|
| Uppercase letters, digits, symbols, escaped characters | Character constants. Uppercase matches both cases in the source. |
| lowercase letter | Value of the **symbol** at that position |
| `!x` | Value of the **integer expression** at that position |
| `!!x` | Value of the **integer factor** at that position |
| `!Fx` | IEEE-754 bit pattern of a **32-bit** float expression |
| `!Dx` | IEEE-754 bit pattern of a **64-bit** float expression |
| `!Qx` | IEEE-754 bit pattern of a **128-bit** float expression |
| `!Ex` | Value of an **enumerated operand list** declared with `.enum` (section 3.7.1) |
| `!S{{name}}x` | Value of the matching entry of the **sub table** `name` declared with `.sub` (section 3.7.2) |

Captured values are referenced from `error_patterns` and `binary_list` by the
bare letter — the `!` prefix is not repeated there. Every lowercase variable is
reset to 0 for each pattern line, so an unmatched optional operand reads as 0.

Assembly lines are case-insensitive except for labels and section names.

The escape character `\` may be used inside `instruction`.

### 3.4 error_patterns

Conditions that raise an error, comma-separated, each with an error code after
`;`:

```
a>3;4,b>7;5
```

Here `a>3` raises code 4 and `b>7` raises code 5. Comparison operators
including `!=` are available, so `a!=3;2` and `(s&0xf!=0)||(s>>4)>3;9` are both
valid.

Codes 1, 2, 3, 5 and 6 have message text; see [section 9](#9-errors). Any other
code — including 4, and anything from 7 up — still raises the error and still
aborts the assembly, but prints an empty message. Either pick one of the five
with text, or add your own to the `ERRORS` table in `axx.py` and `caxx.c`.

`error_patterns` is evaluated in floating-point mode, so values travel as
IEEE-754 double bit patterns. The bitwise and shift operators compensate
internally, so `(8>>2)>0;2` evaluates as written.

### 3.5 binary_list

Comma-separated output values. `0x03,d` emits `0x03` followed by `d`.

```
ADD A,R!n :: n>7;5 :: n|0x68
```

`add a,r1` emits `0x69`; `n>7` raises code 5 (Register out of range).

- An **empty element** performs alignment. A leading comma, or `0x12,,0x13`,
  pads to the exact address.
- An element starting with `;` is **suppressed when its value is 0**.
- An element starting with `;;` is **evaluated but never output**. `0x11,;;n,0x22`
  emits two words, and a `binary_list` of just `;;n` emits none at all.

#### 3.5.1 `@@[]` — repetition

`@@[n,<str>]` repeats `<str>` n times. `%%` is the repetition index; `%0`
resets it to 0.

### 3.6 Symbols

```
.setsym :: name :: value
```

A symbol name may contain letters, digits and symbol characters. Symbols are
case-insensitive. A later definition of the same name overrides an earlier one,
so the same identifier can mean different things in different regions of the
file:

```
.setsym::B::0
.setsym::C::1
ADD A,s              /* C here is 1

.setsym::NZ::0
.setsym::Z::1
.setsym::NC::2
.setsym::C ::3
RET s                /* C here is 3
```

To define a symbol from another symbol, use `#`:

```
.setsym ::symbol1 ::1
.setsym ::symbol2 ::#symbol1
```

Z80 register example:

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

Symbols may contain punctuation and digits: `.setsym ::$s5:: 21`.

**Clearing.** `.clearsym::ax` undefines `ax`; `.clearsym` with no argument
clears everything.

**Character set.** `.symbolc::<characters>` extends the character set used for
symbols. The default is letters, digits, and `_%$-~&|`.

Note that `-` is in the default set. This is what lets a symbol be followed
directly by a negative displacement — the matcher tries the longest symbol
prefix first and falls back:

```
MOV EAX,[RBX-8]      ; x86_64.axx -> 8b 83 f8 ff ff ff
LD A,(IX-5)          ; z80.axx
```

The same rule means that writing a negative value where the pattern expects a
symbol — `ASR #-1` when the instruction has no immediate form — is reported as
`undefined symbol: '#-1'` rather than as a range error.

### 3.7 Symbol check (`.check`)

```
.check::x::r1,r2,r3
```

Restricts what may appear at the position captured by `x`. Anything else is an
error. `.clrcheck::x` removes the restriction.

**`.check` is worth setting whenever a lowercase variable is reused for more
than one class of operand.** Without it the variable accepts *any* symbol
defined anywhere in the pattern file, so a nonsensical operand combination
assembles silently into wrong bytes instead of being rejected. `.check` is
positional and stays in effect until changed, so place a new `.check` (or a
`.clrcheck`) at each point where the meaning of the variable changes.

Registers of different widths sharing a mnemonic:

```
.setsym::AL::0x00
.setsym::BL::0x01
.setsym::AX::0x00
.setsym::BX::0x01
.check::s::AL,BL
.check::t::AX,BX
MOV s,!a :: 0xb0|s,a
MOV t,!a :: 0xb8|t,a,a>>8
```

This distinguishes `mov al,0x12` from `mov ax,0x1234`.

**Optional positions.** `""` in a `.check` list permits the position to be
absent:

```
.setsym::a1::1
.setsym::a2::2
.setsym::a3::3
.setsym::b1::1
.setsym::b2::2
.setsym::b3::3
.setsym::c1::1
.setsym::c2::2
.setsym::c3::3
.check::a::a1,a2,a3,""
.check::b::b1,b2,b3,""
.check::c::c1,c2,c3,""
MOVabc:: ::a*100+b*10+c
```

```
mov                  0
mova1              100
mova1c3            103
movb2               20
movb2c1             21
```

AVX-512 masking notation uses the same mechanism:

```
.symbolc::{}
.setsym::EAX::0
.setsym::EBX::1
.setsym::{K1}::1
.setsym::{K2}::2
.check::x::EAX,EBX
.check::k::{K1},{K2},""
FOO xk,y :: :: 0x90,k,x,y
```

```
FOO EAX,EBX          -> 0x90 0x00 0x00 0x01   (k omitted)
FOO EAX{K1},EBX      -> 0x90 0x01 0x00 0x01
FOO EAX{K2},EBX      -> 0x90 0x02 0x00 0x01
```

#### 3.7.1 Enumerated operand lists (`.enum`)

Where `.check` restricts a position to *one* symbol out of a set, `.enum`
declares a position that takes a *list* of them — a register list such as the
68000's `MOVEM`.

```
.enum::<variable>::<element,element,...>::<expression>
```

The element order is the enumeration order, and it is what a `-` range in the
source means. In `<expression>` each element name evaluates to

- its `.setsym` value, if that element appears in the source list, and
- `0`, if it does not.

The list is captured with `!E<variable>`; the value of `<expression>` is bound
to the variable and is then referenced from `error_patterns` and `binary_list`
by the bare letter, exactly like every other capture.

```
.setsym::A0::0x01
.setsym::A1::0x02
.setsym::A2::0x04
.setsym::B0::0x08
.setsym::B1::0x10
.setsym::B2::0x20
.enum::x::A0,A1,A2,B0,B1,B2::A0|A1|A2|B0|B1|B2
MOVEM !Ex :: :: @@[8,*(x,%%)]
```

```
movem a0-a2,b2       -> 27 00 00 00 00 00 00 00   (0x01|0x02|0x04|0x20)
movem a0-a2/b2       -> the same; `,` and `/` are both separators
movem a0/a2          -> 05 00 00 00 00 00 00 00
movem a1             -> 02 00 00 00 00 00 00 00
```

The expression is an ordinary axx expression, so the elements do not have to
combine as a bit mask. Weighting them by hand gives a positional encoding
instead:

```
.enum::y::A0,A1,A2,B0,B1,B2::A0*100000+A1*10000+A2*1000+B0*100+B1*10+B2
```

Notes.

- **Separators.** `,` and `/` both separate elements, and `first-last` is a
  range over the enumeration order. A separator is consumed only when another
  element follows it, so a pattern may keep using `,` after the list:
  `PUSH !Ex,-(SP)` matches `push a0-a2,-(sp)`. A `-` that is not followed by an
  element is likewise left for the rest of the pattern, so `SUBT !Ev-!d`
  matches `subt a0-9`.
- **A reversed range** (`a2-a0`) is not read as a range; the `-` is left to the
  pattern.
- **An element that appears in the source but has no `.setsym` definition**
  makes the pattern not match, rather than contributing 0 silently.
- `#name` inside `<expression>` is the plain `.setsym` value, unaffected by
  whether the element appeared.
- `.enum` is positional like `.check`: a later `.enum` for the same variable
  replaces the earlier one, and `.clrenum::x` (or `.clrenum` with no argument)
  removes it.

#### 3.7.2 Sub tables (`.sub` / `.return`)

A sub table is a named set of alternatives that can be spliced into a position
of an `instruction` field. Where `.check` restricts a position to one *symbol*,
a sub table lets that position be a whole *pattern*, each alternative carrying
its own value.

```
.sub::<name>
<pattern>::<value list>
...
.return
```

The table is referenced with `!S{{<name>}}<variable>`. Every entry is tried in
the order written; the entry's `<pattern>` is matched in place of the reference,
and the value of its `<value list>` is bound to the variable, which is then
referenced from `error_patterns` and `binary_list` by the bare letter, exactly
like every other capture.

```
MOV!S{{sub1}}x A,!e :: 0x01,x<<8,x,e<<8,e
.sub::sub1
R1::0x01,0x01
R2::0x02,0x02
R3::0x03,0x03
.return
```

```
movr1 a,0x22         -> 01 00 01 00 22
movr2 a,0x33         -> 01 00 02 00 33
```

A value list with more than one element is packed into a single value, the
first element highest, `.bits` bits each — so `0x01,0x02` is `0x0102` at the
default width. A single element is the value itself.

Notes.

- The entry pattern is an ordinary pattern, so it may itself capture: with
  `.sub::cc` holding `NZ::0` / `Z::0x08`, `JMP!S{{cc}}c !e` matches `jmpz 0x1234`.
- The value list is evaluated **after** the match, so it may use variables the
  entry pattern captured: `R!n::n` binds the captured digit.
- The entries live in the sub table only; they are never matched as ordinary
  pattern lines.
- The whole pattern file is read before references are resolved, so a table may
  be defined after its use. Unknown table names and circular references are
  reported once when the pattern file is read.

**Nesting.** A `.sub` block may **not** be written inside another `.sub` block;
that is an error. Nesting is expressed instead by letting an entry pattern
reference a second table, which is expanded exactly like a reference in an
ordinary pattern:

```
LD!S{{outer}}a :: 0x10,a
.sub::outer
A!S{{inner}}b::b
B!S{{inner}}b::b+0x40
.return
.sub::inner
1::0x01
2::0x02
.return
```

```
lda1                 -> 10 01
ldb2                 -> 10 42
```

The inner variable is bound before the outer one, so an outer value list may use
it — above, `b` is the inner value and the outer entry adds `0x40` to it.

A chain of references is expanded at most **8** deep. A longer chain is not
expanded, and the line simply fails to match.

### 3.8 Optional parts (`[[ ]]`)

Double brackets mark an optional section of an instruction:

```
INC (IX[[+!d]]) :: 0xdd,0x34,d
```

`inc (ix+0x12)` emits `0xdd,0x34,0x12`; `inc (ix)` emits `0xdd,0x34,0x00`,
because lowercase variables default to 0.

### 3.9 Padding

```
.padding::0x12
```

Sets the padding byte used by alignment. Default `0x00`.

### 3.10 Word widths other than 8 bits (`.bits`)

```
.bits::12
.bits::big::12
```

For bit-slice processors and machines whose word is not a byte. Default is 8
bits and `little`.

Output is always in 8-bit units, so a 4-bit machine emits the low 4 bits per
byte, and an 11-bit machine emits (low 8, high 3) or (high 3, low 8) depending
on endianness. Unused bits within a byte are masked to 0.

When `.bits` is in effect, **the location counter counts words, not bytes**.
For a byte-addressable machine such as x86_64, `.bits` is unnecessary.

### 3.11 Include

```
.include "file.axx"
```

On the pattern side this is processed *after* macro expansion, so a macro can
generate the `.include` line itself. Each included file is macro-expanded in
turn and inherits the macros defined by the top-level pattern file.

### 3.12 Escapes in expressions

Expression evaluation stops at the escape character `\`. The escaped part is
deferred and processed again within the pattern file.

```
LEAQ r, [ s + t * !h \+ !i ] :: 0x48,0x8d,0x04,((@h)-1)<<6|t<<3|s,i
```

matches `leaq rax,[rax+rbx*(2+2)+0x40]`, and

```
LEAQ r,(s+t*!!h+!!i) :: 0x48,0x8d,0x04,((@h)-1)<<6|t<<3|s,i
```

matches the parenthesized form `leaq rax,(rax+rbx*(2+2)+0x40)`.

### 3.13 Negative index displacements

```
mov rax,[rbp-8]
```

matches

```
MOV RAX,[RBP+!e]
```

When the matcher meets `-` in the source where the pattern has `+`, it matches
the two against each other, skips the pattern's `+`, and hands the expression —
starting at the `-` — to the expression evaluator. No special notation is
needed in the pattern file.

### 3.14 Custom error messages (`.error`)

```
.error::n::"Message text"
```

Registers the text shown for error code `n` — the same `n` an
`error_patterns` condition raises with `;n` (section 3.4). Two of the six
built-in codes (4, and 7 and above) ship with no message (section 9); `.error`
gives them one, and can also override the text of an existing code (1, 2, 3,
5, 6). `n` must be a non-negative integer expression; the message must be a
double-quoted string literal, with the same `\n` `\t` `\r` `\"` `\\`
`\xHH` `\uHHHH` `\UHHHHHHHH` escapes as `.INCLUDE` filenames (section 3.11).

```
.error::4::"Immediate value not representable in this addressing mode."
.error::9::"Shift amount out of range."
ADD A,!v :: v<0||v>0xff;4 :: 0xc6,v
SHL A,!v :: v>7;9 :: 0xd0,v
```

`add a,300` now reports code 4 with the message above instead of the default
empty text; `shl a,9` reports the newly-defined code 9. Like `.setsym`, a
later `.error` for the same `n` overrides an earlier one — but unlike
`.setsym`, the table has no meaningful notion of region-dependent
redefinition, so in practice one `.error` per code near the top of the file is
the natural style. A code that is never given a message still raises its
error and still blocks the output file from being written; only the printed
text stays blank, exactly as for an undeclared code today.

### 3.15 Mini language (`.func` / `.call`)

A `binary_list` element may be `.call name(argument, ...)`, which runs a
function written in a small procedural language and emits the words that
function produces — the values it passes to `.emit`, followed by its return
value if it has one. The language has assignment, `.if`/`.elif`, `.while`,
`.for`, recursion and arrays, so an encoding that cannot be written as a fixed
expression can be computed instead. `.echo` prints to stderr without emitting
anything, for working out why a function produced what it did.

A function is defined at the top level of a pattern file:

```
.func <name>(<parameter, parameter, ...>)
<statements>
.endfunc
```

Everything between the header and the matching `.endfunc` is the body; those
lines are never matched as ordinary pattern lines. Parameters may be empty
(`.func name()`, or just `.func name`) — the same shape as the `.call name(...)`
that invokes it. The older `.func::name::params` header is still read; a `::`
directly after `.func` selects it, so existing pattern files keep working.

```
MOV a,!b,!c :: .call name(a,b,c)
```

The arguments at the call site are ordinary axx pattern expressions, so `a`,
`b` and `c` there mean the captured pattern variables. Inside the function they
become its parameters, which are local to the call. `.call` is one
comma-separated element like any other, so it can be mixed with plain values:

```
MIX !e :: 0x90,.call rep(e),0xff
```

An argument written `[e1, e2, ...]` is an **array**; its elements are pattern
expressions too. `[]` is the empty array.

```
LOG !v :: .call table([0x11,0x22,v],3)
```

The `;` modifier of [section 3.5](#35-binary_list) applies to `.call` as well:
`;.call f(a)` emits nothing when the call's whole output is a single word equal
to 0, which is how a prefix byte that is sometimes absent is written. `;;.call
f(a)` runs the call and discards its output.

#### Statements

| Statement | Meaning |
|---|---|
| `name = expression` | Assign to a local variable |
| `name[index] = expression` | Assign to an array element |
| `.emit(e1, e2, ...)` | Append one word per value to the output |
| `.echo(item, item, ...)` | Print strings and values to stderr — for debugging only, emits nothing |
| `.raise <expr>` | Report an error whose error code is the value of `<expr>` |
| `.call name(args)` | Call another function |
| `name = .call name(args)` | Call another function and assign its return value |
| `.if <expr> .then` / `.elif <expr> .then` / `.else` / `.endif` | Conditional; `.elif` may repeat, `.else` is optional |
| `.while(<expr>)` / `.endwhile` | Loop while the condition is non-zero |
| `.for <name> in range(...)` / `.next` | Loop over `range(stop)`, `range(start, stop)` or `range(start, stop, step)` |
| `.nonlocal a, b` | Bind these names to the enclosing call instead of locally |
| `.return` | Return from the function. May appear anywhere in the body (top level or inside `.if`/`.while`/`.for`), any number of times |
| `.return <expr>` | Return a value from the function |
| `.endfunc` | Close the function's body (see above) |

`.emit` appends one word of `.bits` width per value — one byte at the default
width. The number of words a call emits is the instruction's length, so a
function must emit the same count in both passes for addresses to settle.

The `.if` and `.elif` lines must end with `.then`. Any number of `.elif`
branches may follow an `.if`, an `.else` may close the chain, and one `.endif`
ends the whole chain:

```
.if n > 100 .then
.emit(0xff, n & 0xff)
.elif n > 10 .then
.emit(0xfe, n & 0xff)
.else
.emit(n & 0xff)
.endif
```

`.echo` is the debugging counterpart of `.emit`: it writes to stderr and
appends nothing to the output, so adding or removing one never changes the
generated bytes. Each item is either a `"..."` string literal or an expression,
and the two may be mixed:

```
.echo("Example", n, 1)          /* -> Example 7 1 */
.echo("n=", n, "arr=", a)       /* -> n= 7 arr= [7, 14] */
```

A string prints as written, an integer as signed decimal, an array as
`[1, 2, 3]`, and the items of one call share a line separated by spaces — the
same output routine the macro layer's `!echo` uses, so the two agree.
`.echo()` with no item prints an empty line. Nothing is printed while the
assembler is measuring instruction lengths or converging in pass 1, so each
line appears once per assembled instruction, not once per relaxation
iteration.

Strings may appear only in the argument list of `.echo`. Values are integers
and arrays only, so a string cannot be assigned to a variable or used in an
expression. The escapes are `\\`, `\"`, `\n` and `\t`; any other `\` is an
error. A string cannot contain `/*` — that is the pattern file's comment
marker, stripped before the mini language sees the line.

`.raise <expr>` reports an error whose error code is the value of `<expr>`, in
exactly the format an `error_patterns` field produces for `condition;code`
([section 3.4](#34-error_patterns)); a message registered with
`.error::code::"text"` is used the same way, and an unregistered code prints
the number alone. Reporting does not stop the function — execution continues
with the next statement, so follow it with `.return` to stop there — and, like
`.echo`, it stays quiet while instruction lengths are only being measured and
during pass-1 relaxation, so each assembled instruction reports at most once.
As with a triggered `error_patterns`, the assembly fails and no output file is
written.

```
.error::3::"immediate out of range"

MOV !n :: .call mov(n)

.func mov(n)
.if n > 255 .then
.raise 3
.return
.endif
.emit(0xb0, n)
.return
.endfunc
```

Values are 256-bit two's complement integers, the same as everywhere else in
axx. Operators, from loosest to tightest: `||`, `&&`, `!`, comparisons
(`== != < <= > >=`), `|`, `^`, `&`, `<< >>`, `+ -`, `* / %`, unary `- + ~`,
`**`, subscript. `/` truncates toward zero and `%` takes the sign of the
dividend. `>>` is arithmetic.

Four terms are handed to the assembler's own expression evaluator instead:
`$$`, `$.`, `#name`, and a bare name that no local variable claims (read as a
label or `.equ`). Both sides are 256-bit, so the value comes back usable as it
is.

```
BR !t :: .call rel8(t)

.func rel8(target)
d = target - $.
.if d < -128 || d > 127 .then
.echo("branch out of range:", d)
.endif
.emit(d & 0xff)
.return
.endfunc
```

Pattern variables `a`-`z` and `!!!` are *not* available there: nothing has
bound them while a `.func` body runs, so pass them in at the call site as
`.call f(a,b)`. [Section 6.3](#63-what-is-available-where) has the full table.
A value derived from an undefined label comes through as 0, the same treatment
`.call` arguments get, so a huge sentinel cannot blow up a loop count.

#### Return values

`.return <expr>` returns a value, and the caller takes it with
`var = .call name(args)`:

```
.func hypot2(a,b)
.return a*a+b*b
.endfunc

.func emit_h(a,b)
v = .call hypot2(a,b)
.emit(v)
.return
.endfunc
```

The value may be a number or an array; an array is passed as a copy. The target
may be an array element (`a[i] = .call f(x)`), in which case the returned value
must be a number. Calling a function that returns nothing in that form is an
error, and `.call` cannot appear inside a larger expression — take the value
into a variable first. `.return` never closes the body — only `.endfunc` does
that — so `.return <expr>` may also be used as an early return from inside a
block, any number of times:

```
.func firstdiv(n)
i=2
.while(i<n)
.if n%i==0 .then
.return i
.endif
i=i+1
.endwhile
.return 0
.endfunc
```

When a function is called straight from `binary_list`, its return value becomes
output: a number is one word, an array is one word per element from index 0.
That is in addition to whatever it passed to `.emit`, so a function that only
`.emit`s and returns nothing behaves exactly as before.

```
SEQ !n :: 0xaa,.call seq(n),0xbb

.func seq(n)
a=[]
.for i in range(n)
a[i]=0xc0+i
.next
.return a
.endfunc
```

```
seq 4                -> aa c0 c1 c2 c3 bb
```

#### Arrays

An array is written `[]`, or `[e1, e2, ...]`, or produced by slicing. An array
may also be passed as a function argument, both between functions and from a
`binary_list` call site.

```
a = []
a[3] = 5          /* a is now [0,0,0,5] — the gap is filled with 0 */
.emit(a[0])       /* 0 */
.emit(a[99])      /* 0 — reading past the end gives 0, without extending */
.emit(.len(a))    /* 4 */
b = a[1:3]        /* [0,0] — the end index is not included */
```

Assigning past the end extends the array with zeros. Reading past the end, or
at a negative index, gives `0` and leaves the array alone. Slice bounds are
clamped to the array. `.len(x)` is the length. Array elements are numbers, not
arrays.

#### Scope and nesting

Each call gets its own variables. A name read before it is set is an error, so
a typo does not silently read zero.

Functions may be defined inside other functions. An inner function is visible
to its enclosing function and resolves names outward; `.nonlocal` lets it
assign to a variable of an enclosing call rather than creating its own:

```
.func outer()
n=7
.func inner()
.nonlocal n
n=n+1
.emit(n)
.return
.endfunc
.call inner()
.call inner()
.emit(n)
.return
.endfunc
```

```
-> 08 09 09
```

`.nonlocal` must appear before the name is otherwise used in that function.

#### Example

A sieve, and an instruction whose encoding is a Collatz step count:

```
PRIMES !n  :: .call sieve(n)
COLLATZ !n :: .call collatz(n)

.func sieve(n)
mark=[]
mark[n]=0
i=2
.while(i*i<n)
.if mark[i]==0 .then
j=i*i
.while(j<n)
mark[j]=1
j=j+i
.endwhile
.endif
i=i+1
.endwhile
.for k in range(2,n)
.if mark[k]==0 .then
.emit(k)
.endif
.next
.return
.endfunc

.func collatz(n)
c=0
.while(n!=1)
.if n%2==0 .then
n=n/2
.else
n=3*n+1
.endif
c=c+1
.endwhile
.emit(c)
.return
.endfunc
```

```
primes 50            -> 02 03 05 07 0b 0d 11 13 17 1d 1f 25 29 2b 2f
collatz 27           -> 6f
```

The same material is kept as a standalone document in `MINI.md` (Japanese) and
`mini_en.md` (English).

#### A worked example from a real ISA

`aarch64_logical_mini.axx` encodes the AArch64 logical-immediate group
(AND / ORR / EOR / ANDS / TST, 32- and 64-bit) this way. ARM's `DecodeBitMasks`
run in reverse is split across four functions — `highbit`, `find_e`, `pack_rs`
and `emit_logical` — which leaves each instruction line short:

```
AND  d,n,#!v ::v==0;3,v==0xFFFFFFFFFFFFFFFF;3 :: .call emit_logical(v,1,0,n,d,64)
```

[Appendix A.3](#a3-aarch64-logical-immediate) gives the same encoding written
instead as a single chained-ternary `binary_list`, which is what the mini
language is there to replace. Both compute in the same 256-bit arithmetic; what
the function form gains is that each call has its own local scope, so its
working variables cannot collide with the pattern layer's captured ones, and
that one body serves both widths — the 32-bit forms only bound the element-size
search to 32 instead of 64, where the `binary_list` version needs the width
folded into the expression.

#### Limits

The language is Turing complete, so a buggy pattern file could otherwise hang
the assembler. Four caps stop that and report the offending line instead:

| Cap | Value |
|---|---|
| Statements executed per `.call` | 4,000,000 |
| Call nesting | 128 |
| Words emitted per `.call` | 1,048,576 |
| Array length | 1,048,576 |

An argument that came from an undefined label is passed as `0`, so a
forward reference cannot blow a loop count up during the first pass.


---

## 4. VLIW and EPIC processors

### 4.1 `.vliw`

```
.vliw::<bundle bits>::<instruction bits>::<template bits>::<NOP code>
.vliw::128::41::5::00
```

The example describes Itanium: a 128-bit bundle holding three 41-bit
instructions (123 bits) plus 5 template bits, with NOP `0x00`.

- For non-EPIC machines, give `0` for the template bits.
- A positive template-bit count places the template at the right end; negative
  places it at the left end, using the absolute value as the width.
- `.bits::big` reverses the byte order of the output relative to the default
  `little`.

The number of bytes a pattern emits must match
`(bundle bits − template bits) ÷ 8`, rounded up.

### 4.2 EPIC

EPIC patterns take a **fourth** field: the index code.

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

- `EPIC::1,2::0x8|!!!!` describes a bundle of the instructions with index codes
  1 and 2, with template `0x8`, OR'd with the stop bit.
- `!!!!` denotes the stop bit.
- `AD a,b,c` has index code 1; `LOD d,[!e]` has index code 2.

**In EPIC patterns the error field must be written explicitly**, even when
empty — hence the `:: ::`.

(The values above are a test fixture and do not correspond to real Itanium
encodings.)

### 4.3 Non-EPIC VLIW

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

### 4.4 Bundling in the source

Instructions are bundled with `!!`:

```
ad r1,r2,r3 !! lod r4,[0x1234]
```

In `binary_list`, `!!!` is the number of instructions joined by `!!`, and
`!!!!` at the end of a bundle sets the stop bit.

### 4.5 Endianness

Determined by the order in which you write the values in `binary_list`.

---

## 5. Assembly source reference

Lines read from a source file or from stdin are called **assembly lines**.
Comments start with `;`.

### 5.1 Labels

```
label1:
label2: .equ 0x10
label3: nop
label4: .equ label1
```

A label is a sequence of letters, digits and some symbols, starting with a
non-digit. A label defined with `.equ` loses its relocation information and is
treated as a constant.

`.labelc::<characters>` extends the label character set. The default is
letters, digits, `_` and `.`.

### 5.2 Location counter

```
.org 0x800
.org 0x800,p
```

`.org` sets the location counter. With `,p`, if the counter is currently below
the target, the gap is padded.

```
.align 16
```

Aligns to a multiple of 16, padding with the `.padding` byte. With no argument,
the previous (or default) alignment is used.

### 5.3 Data

```
.ascii "sample1"        ; string bytes
.asciz "sample2"        ; string bytes plus a trailing 0x00
.zero 65536             ; 65536 zero bytes
```

Reserve storage without emitting bytes — the location counter simply advances:

```
.resb n     ; n bytes
.resw n     ; n words       (n*2 bytes)
.resd n     ; n doublewords (n*4 bytes)
.resq n     ; n quadwords   (n*8 bytes)
```

**A byte-emitting mnemonic such as `DB` is not built into axx.** It exists only
if the pattern file defines it. Among the bundled files, `8048.axx` and
`x86_64.axx` define `DB`; `z80.axx` does not. The data directives that are
always available regardless of the pattern file are `.ascii`, `.asciz`, `.zero`
and the `.resb`/`.resw`/`.resd`/`.resq` family.

### 5.4 Floating point

`!F` / `!D` / `!Q` capture a floating-point operand at a position in the
instruction:

```
VMOV.F32 S!n,#!Fd :: 0x80|n,d>>24,d>>16,d>>8,d
```

`vmov.f32 s0,#3.14` emits `0x80,0xc3,0xf5,0x48,0x40`.

To write a floating-point value inside an ordinary integer expression — to give
it a name with `.equ`, for instance — use the brace forms. Each evaluates its
body as floating point and yields the IEEE-754 bit pattern as an integer:

```
flt{expr}     ; 32-bit  (binary32) bit pattern
dbl{expr}     ; 64-bit  (binary64) bit pattern
qad{expr}     ; 128-bit (binary128) bit pattern
```

The inverse functions are usable inside those bodies:

```
enfloat(v)  / enflt(v)     ; read v's low 32 bits back as a float
endouble(v) / endbl(v)     ; read v's low 64 bits back as a double
```

Which makes a named floating-point constant work, since the stored label holds
a bit pattern that can be decoded and recomputed:

```
c1: .equ flt{3.14}
    LDF A,flt{enfloat(:c1)*2}
```

`:label` inside such an expression refers to the label's value directly.
`inf`, `-inf` and `nan` are accepted. Use `0b` for binary literals and `0x` for
hexadecimal.

### 5.5 Sections

```
.section .text
.segment .text          ; currently identical in meaning
.endsection
.endsegment
```

Section names are matched against `.text`, `.data`, `.rodata` and `.bss` when
deriving ELF section flags for `-o` and `-E` output.

> **Note.** `.section` (or `.segment`) is the only way to switch sections.
> There is no bare `.text` / `.data` / `.rodata` / `.bss` shorthand — writing
> one of those on its own line is a syntax error in both Paxx and Caxx.

#### 5.5.1 `.reloctype`

Overrides the machine's default width-guess relocation type for auto-detected
label references in the current source file:

```
.reloctype name8,name16,name32,name64
```

#### 5.5.2 Section ordering

Sections are laid out exactly in the order written, so this:

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

does not group by section. Run `secsort.py` to get:

```
.section .text
ld a,9
ld b,9
.section .data
.asciz "test1"
.ascii "test2"
```

### 5.6 Linkage

```
.export label
.export label1,label2,label3
.global label1,label2
.extern label1,label2
.extern label1:2,label2          ; label1 uses relocation type 2
```

- `.export` marks labels for `-e` / `-E` output, together with their
  section/segment. Only labels named here are exported.
- `.global` passes a label externally; it is written out by `-e` / `-E` as well.
- `.extern` declares that a name is resolved elsewhere. A relocation type may
  be attached to an individual name with `:`.

`.extern` and `-i` are designed to be used together: `-i` supplies the actual
address of an external label and `.extern` declares that the name is resolved
elsewhere. When both name the same label, the value brought in by `-i` wins.

`.global` and `.extern` are consumed by the ELF object writer.

### 5.7 Include

```
.include "file.s"
```

On the source side this **bypasses the macro layer**; use `!include` (section
7) to bring in macro definitions.

---

## 6. Expressions and operators

The assembly line and the pattern data call the same expression evaluator, so
the two behave almost identically. The one restriction is that **lowercase
pattern variables cannot be referenced from an assembly line.**

### 6.1 Special terms

| Term | Meaning |
|---|---|
| `!!!` | Number of instructions joined by `!!` |
| `%%` | Number of times `%%` has appeared so far (index from 0) |
| `$$` | Current location counter |
| `$.` | Start address of the following instruction |

### 6.2 Operators

Precedence follows Python, loosest last:

```
(expr)          parenthesized expression
#               value of the following symbol
*(x,y)          the yth byte of x from the least significant end (y>=0)
-, ~            negation, bitwise NOT
@               position of the most significant set bit, counted from the right
'c'             character code
:=              assignment
**              exponentiation
*, /, //        multiplication, division, integer division
+, -            addition, subtraction
<<, >>          shifts
&               bitwise AND
|               bitwise OR
^               bitwise XOR
'               sign extension
<=, <, >, >=, !=, ==     comparison
not(x)          logical NOT
&&              logical AND
||              logical OR
x?a:b           ternary
```

- `d:=24` assigns 24 to `d` and evaluates to 24.
- `#name` yields the value of symbol `name`.
- `@v` gives the bit position of the highest set bit of `v` counted from the
  right. (The Hebimarumatta operator.)
- `a'24` sign-extends `a`, treating bit 24 as the sign bit. (The SEX operator.)

### 6.3 What is available where

The same evaluator is called from three places — an assembly line, a pattern
file's fields, and (by delegation) the macro layer and the mini language — and
not every term means something in every one of them. A capability descriptor
decides, so the feature set changes with the moment of the call:

| Term | Pattern line | Assembly line | Mini language | Macro layer |
|---|---|---|---|---|
| Label / `.equ` | yes | yes | yes | previous iteration's value |
| `$$` / `$.` | yes | yes | yes | `$` / `$$`, previous iteration |
| `#symbol` | yes | yes | yes | — |
| Pattern variables `a`-`z` | yes | uppercase only | no | no |
| `!!!` / `!!!!` | yes | no | no | no |
| `@`, `'`, `*(x,y)` | yes | yes | yes | yes |

Pattern variables are dropped for the mini language because nothing has bound
them while a `.func` body runs — pass them in at the call site instead. `!!!`
only means anything on a VLIW pattern line. In a pattern file the macro layer
runs before any source is assembled, so it has no labels and no location
counter to read at all.

`@`, `'` and `*(x,y)` are implemented once and called from both the assembler's
evaluator and the macro layer, so they mean the same thing in either. In the
macro layer `'` binds looser than the bitwise operators and tighter than `&&`;
the position differs from the assembler's, where it sits between `^` and the
comparisons, because macro-layer precedence follows C and there comparisons
bind tighter than the bitwise operators.

### 6.4 Very large values and the UNDEF sentinel

An undefined label carries a sentinel value through ordinary arithmetic, so
that `label+4` stays recognisably undefined instead of raising. Paxx can put
that sentinel out of band — its integers are arbitrary-precision, so the
sentinel lives above `2**768` where no real value reaches. Caxx has no headroom
above 256 bits, so it treats any magnitude of `2**192` or more as
sentinel-derived, and says so once in a warning.

Keep computed values below `2**192` and the two implementations agree exactly.
Above it they part company, each in its own way:

| Value | Paxx | Caxx |
|---|---|---|
| magnitude ≥ `2**192` | a normal value | reported as an undefined-label reference |
| bit 255 set | positive, so `>>` shifts in zeros | negative, so `>>` shifts in ones |
| ≥ `2**256` | kept as-is | wrapped to 256 bits |

Both implementations warn when a value enters the band they cannot judge. This
is a property of the sentinel design, not of any one operator: giving Caxx an
out-of-band sentinel would mean widening its value type beyond 256 bits.

---

## 7. Macro layer

The same material is kept as a standalone document in `MACRO.md` (Japanese) and
`macro_en.md` (English).

This is a source-to-source transformation that runs **before** the assembler
proper. Macros in source files can nonetheless read label values, `.equ`
definitions and the `$` / `$$` location counter: what they see is the value from
the *previous* relaxation iteration (0 / undefined on the first one). Because
expansion can then change from iteration to iteration, convergence is enforced
by the relaxation loop itself — it caps iterations, detects oscillation, and
aborts without writing an output file rather than emitting a wrong binary.
Pattern-file macros run before any source is assembled and so have no access to
either. See `MACRO.md` / `macro_en.md` for the details.

Both `axx.py` and `caxx.c` implement the same specification. The only
difference is numeric representation: Paxx uses arbitrary-precision integers,
Caxx uses `int64`. Results diverge only when a macro-time calculation exceeds
64 bits, and since the macro layer emits source text, this does not affect the
assembler's own 256-bit expression evaluation.

### 7.1 Statements

Every statement starts with `!` at the beginning of a line (leading whitespace
is ignored).

| Syntax | Meaning |
|---|---|
| `!def name(p1, p2, p3 = default) { ... }` | Macro / compile-time function |
| `!return expr` | Return a value; also an early exit |
| `!if expr !then { ... } !elif expr !then { ... } !else { ... }` | Conditional |
| `!while expr { ... }` | Loop |
| `!break` / `!continue` | Loop control |
| `!set name = expr` | Assign, searching scopes inner to outer; create in current scope if not found |
| `!local name [= expr]` | Declare in the current scope |
| `!undef name` | Delete a variable or macro |
| `!name(a, b)` | Expand a macro as a statement |
| `!include "file"` | Include text at expansion time |
| `!error expr` | Abort expansion with an error |
| `!warning expr` / `!echo expr` | Write to stderr (`!echo` shares its layout with the mini language's `.echo`, [section 3.15](#315-mini-language-func--call)) |

The opening `{` must be the last thing on the header line, and the closing `}`
must start a line. `; comment` may follow a statement.

### 7.2 Interpolation

| Notation | Meaning |
|---|---|
| `!{expr}` | Expand the value as text |
| `!{expr:04x}` | Apply a Python-style format spec |
| `\!{` | A literal `!{` |

The format spec is Python's format mini-language. Both implementations accept
the same specs, reject the same specs, and agree on the error wording.

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

Two known divergences from Python:

- Both implementations strip whitespace around the spec before interpreting it,
  so the space-as-sign form (`!{5: d}`, which Python renders as `' 5'`) cannot
  be expressed; it behaves like `!{5:d}`.
- `!{0:c}` yields a NUL character from Paxx, but an empty string from Caxx,
  which cannot carry a NUL inside a C string.

### 7.3 Values, operators, built-ins

Values are integers and strings. Operators are C-compliant:

```
?:  ||  &&  |  ^  &  ==  !=  <  <=  >  >=  <<  >>  +  -  *  /  %
unary:  -  +  ~  !
```

`/` and `%` truncate toward zero as in C (`-7/2 == -3`). `+` concatenates if
either operand is a string; `"ab" * 3` repeats. Integer literals: `10`,
`0x1f`, `0b1010`, `0o17`, underscores permitted. `'A'` is a character code if
it is one character, a string if more.

Three more come across from the assembler's own evaluator, sharing one
implementation with it so that they mean the same thing in either place:
`@v` (position of the highest set bit), `v'bits` (sign extension) and
`*(v, n)` (byte extract) — `!{@255}` is 8, `!{0xff'8}` is -1, `!{*(0xabcd,1)}`
is 171. `'` binds looser than the bitwise operators and tighter than `&&`;
see [section 6.3](#63-what-is-available-where) for why the position differs
from the assembler's. Only a `*(` where a value is expected is a byte extract;
an infix `*` is still multiplication.

Built-in functions:

```
len(s)  hex(v[,digits])  str(v)  int(s[,base])  upper(s)  lower(s)
substr(s,start[,length])  abs(v)  min(...)  max(...)  uid()  label(name)
defined(name)
```

`substr()` clamps start and length to the string. A negative start means the
beginning (0), **not** Python-style indexing from the end; a negative length is
treated as 0.

`label(name)` reads an assembler-side label or `.equ` value for a name that
cannot be written as a macro identifier, such as `label(".L1")`. A name that
*is* a valid identifier is read by writing it bare — a bare identifier resolves
to a macro variable first, and to a label only if no variable is found. Both
forms work in source files only; in a pattern file no labels exist yet, so a
bare identifier resolves only as a macro variable. What either form reads is
the value from the previous relaxation iteration, as described at the top of
this section.

Implicit variables inside a macro:

| Name | Content |
|---|---|
| `__id__` | Integer unique to each invocation — for generating local labels |
| `__name__` | Macro name |

### 7.4 Macros in pattern files

Pattern files go through the same macro layer. An instruction table tends to be
rows of the same shape differing only in a register number or an opcode, so the
rows can be generated:

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

The error field can be generated too, so a range check written once applies to
every generated row:

```
!def imm(name, op) {
!{name} A,!v :: v>0xff;2,v<0;2 :: 0x!{op:02x},v
}
!imm("ADDI", 0xc6)
!imm("SUBI", 0xd6)
```

Three things differ from the source side; the syntax, built-ins and runaway
guards are identical.

1. **Separate namespace.** The pattern side and source side have independent
   macro environments and cannot see each other's macros or variables. A
   pattern file's macros can therefore never change how a source file expands,
   and the per-pass reset the source side performs during relaxation can never
   wipe macros defined while reading the pattern file.
2. **Comments on statement lines use `/*`,** matching pattern-file convention.
   `;` is not a comment marker there, because it introduces the error-code
   suffix in an error field (`v>0xff;2`).
3. **Stricter engage condition.** In a pattern file `!` is the pattern-variable
   sigil (`ADD A,!d`) and appears on nearly every line, so the layer engages
   only when a line would really be taken as a macro statement, contains an
   unescaped `!{...}`, or starts with `}`. A pattern file that uses no macros
   skips the layer entirely: every bundled pattern file expands to itself
   byte-for-byte and assembles in the same time as before.

Use `-p` to inspect the generated pattern text without assembling.

### 7.5 Compatibility and limits

Backward compatibility:

- A line starting with `!` is intercepted only if it contains a keyword, names
  a defined macro, or is immediately followed by `(`. The VLIW `!!` and the
  `!F` / `!D` / `!Q` forms are untouched.
- A `}` at the start of a line closes a block only when a block is open.
- Source containing no macros produces identical output to before the macro
  layer existed.

Limitations:

- Source-side `.include` bypasses the macro layer; use `!include` for macro
  definition files. (Pattern-side `.include` *does* run through the layer.)
- `!{a ? b : c:04x}` — a ternary combined with a format spec — cannot currently
  be parsed.
- Prompt mode bypasses the macro layer.

Runaway protection: 200 levels of recursion, 1,000,000 `!while` iterations,
2,000,000 generated lines, `!include` nesting depth 64. Exceeding any limit
raises an error and aborts expansion for the rest of the pass.

### 7.6 Example

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

---

## 8. Object output, export and import

### 8.1 File format

The files handled by `-e`, `-E` and `-i` are **tab-separated**. Fields must be
separated by a real tab; a line separated by spaces is silently ignored.

Two record shapes exist. A section record has three fields (four with `-E`); a
label record has two:

```
sectionname   startaddress   size   [flags]
labelname     value
```

### 8.2 Export (`-e`, `-E`)

Addresses, sizes and values are written with a `0x` prefix. `-E` adds a fourth
field to section records holding the ELF section flags (`AX`, `WA`, …); `-e`
omits them. Labels appear in the order `.export` / `.global` declared them.

`axx x86_64.axx hello.s -E hello.tsv`:

```
.text	0x401000	0x39	AX
_hello	0x401000
_start	0x401000
len	0xd
```

### 8.3 Import (`-i`)

The import file uses the same two record shapes and may mix them.
**Values are read as hexadecimal, without a `0x` prefix** — this differs from
the export format.

- A three-field line declares the address range of a section.
- A two-field line defines an imported label. Its section is inferred by
  finding which declared range the address falls into; if none matches, `.text`
  is assumed.

A relocation type can be attached to an imported label with `::`:

```
.text	401000	39
mylabel	401010
otherlabel::pc32	401020
```

The names accepted after `::` are the short names in the `named` table of the
selected machine in `ELF_MACHINES`. For x86-64: `abs64`, `abs32`, `abs32s`,
`abs16`, `abs8`, `pc32`, `rel32`, `plt32`, `pc16`, `pc8`, `pc64`, `got32`,
`gotpcrel`, `got64`. An unrecognized name produces a warning and is ignored.

Section records are optional. If you only need label values:

```
label1	0
label2	1
label3	2
```

---

## 9. Errors

Diagnostics raised by the assembler itself:

| Condition | Message |
|---|---|
| A label collides with a pattern-file symbol | *is a pattern file symbol* |
| A label is defined more than once | *label already defined* |
| A line cannot be parsed | *Syntax error* |
| A referenced label is never defined | *Label undefined* |
| Malformed assembler or pattern line | *Illegal syntax in assembler line or pattern line* |
| An EPIC template is not set | *No VLIW instruction-set defined* |
| A malformed VLIW pattern file | reported during interpretation |

Errors raised by `error_patterns`, selected by the code after `;`:

| Code | Message |
|---|---|
| 1 | Invalid syntax. |
| 2 | Address out of range. |
| 3 | Value out of range. |
| 4 | *(none)* |
| 5 | Register out of range. |
| 6 | Port number out of range. |
| 7 and above | *(none)* |

A code with no text still raises the error and still prevents the output file
from being written; only the message is blank. To add or override messages
from a pattern file, without touching either implementation's source, use
`.error::n::"Message"` (section 3.14).

---

## 10. Design notes and background

*This section is background. Nothing here is needed to use axx.*

### 10.1 Origin

`axx` abbreviates "Arbitrary eXtended X(cross) assembler". The name also comes
from superimposing an X — an unknown CPU — onto "ASM". Since the reference
implementation is Python, its nickname is Paxx.

The core idea, the name, and a prototype in C existed in 1986, conceived during
university while working part-time at Tokyo Denshi Sekkei. The original listing
resurfaced 38 years later, and the working code released today is a 2024
rewrite of it in Python.

### 10.2 The metalanguage

The `instruction` field is a metalanguage for imperative assembly languages.
It is a DSL without a fixed grammar — a free-syntax pattern language in which
you build your own grammar out of string literals, symbols and expressions.

Reduced to its minimum, an imperative assembly language is
`instruction :: binary_list`; error checking is an addition, and axx's
`binary_list` adds expression evaluation, alignment and the `;` modifier for
practical use rather than out of necessity.

What axx does is extract the common structure of the von Neumann architecture,
metamodel the ISA, and formalize the result as pattern matching.

### 10.3 Why the pattern language is not Turing-complete

A processor architecture can be made arbitrarily complex if one chooses to make
it so. A Turing-complete pattern language could follow it anywhere; axx's
cannot, which is what makes it a general rather than a universal assembler.

The reason for the restriction is that a Turing-complete DSL would make the
pattern file a *program*, and pattern matching would no longer be guaranteed to
terminate. That guarantee was judged worth more than the extra reach. The macro
layer is a separate stage and is not restricted this way.

While the pattern file is not Turing-complete, when computation is required, you can invoke a Turing-complete function (a mini-language) from the `binary_list` using `.call func()`.

Because a pattern file has no explicit structure, it suits unstructured
instruction encodings well; `.check` (section 3.6) is what lets you impose
structure — such as an instruction `MOVabc r,s` where `a`, `b`, `c` each range
over a fixed set — when you want it.

---

## Appendix A. Examples

### A.1 Z80

```
.setsym:: BC:: 0x00
.setsym:: DE:: 0x10
.setsym:: HL:: 0x20
LD s,!d:: (s&0xf!=0)||(s>>4)>3;9 :: s|0x01,d&0xff,d>>8
```

`ld bc,0x1234`, `ld de,0x1234` and `ld hl,0x1234` emit `0x01,0x34,0x12`,
`0x11,0x34,0x12` and `0x21,0x34,0x12`.

### A.2 Fragments of several processors

A test fixture; the encodings are not the real ones.

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

```
$ axx test.axx test.s -v
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

### A.3 AArch64 logical immediate

Probably the most complex thing expressible in a single pattern. Encodings like
this can be folded into one macro (section 7.4).

The bundled `aarch64_logical_mini.axx` covers this same instruction group with
the mini language of [section 3.15](#315-mini-language-func--call) instead, and
is the form to start from if you are writing something like this yourself; the
one-liner below is kept here as a demonstration of the declarative core's
reach.

```
AND d,n,#!v ::v==0;3,v==0xFFFFFFFFFFFFFFFF;3 ::;(e:=((v&3)*0x5555555555555555==v)?2:((v&0xf)*0x1111111111111111==v)?4:((v&0xff)*0x0101010101010101==v)?8:((v&0xffff)*0x1000100010001==v)?16:((v&0xffffffff)*0x100000001==v)?32:64)*0,;(m:=(1<<e)-1)*0,;(y:=v&m)*0,;(t:=@(y^(y-1))-1)*0,;(u:=y>>t)*0,;(w:=(y^m)==0?1:y^m)*0,;(p:=@(w^(w-1))-1)*0,;(q:=w>>p)*0,;(c:=((u+1)&u)==0)*0,;(b:=c?@u:e-@q)*0,
 ;(r:=c?(e-t)&(e-1):(e-(p+@q))&(e-1))*0,;(s:=((-2*e)&0x7f)|(b-1))*0,;(z:=(1<<31)|(0x24<<23)|((((s>>6)&1)^1)<<22)|(r<<16)|((s&0x3f)<<10)|(n<<5)|d)*0,@@[4,z>>(%%*8)]
```

---

## Appendix B. Bundled pattern files

`x86_64.axx`, `x86_64m.axx`, `68000.axx`, `z80.axx`, `8080.axx`, `8048.axx`,
`8051.axx`, `6502.axx`, `6800.axx`, `6809.axx` and `4004.axx` are for practical
use, as is `aarch64_logical_mini.axx` within the one instruction group it
covers. The rest are test fixtures.

The x86_64 pattern file is also maintained separately at
<https://github.com/fygar256/x86_64_pattern_file_for_axx>.

| Pattern file | Size | `::` lines | Source | Notes |
|---|---|---|---|---|
| **x86_64.axx** | 3.9 MB | 23,923 | **hello.s** | x86_64-v3: segment addressing, AVX/AVX2, BMI1/BMI2, x87, EVEX/AVX-512 |
| **x86_64m.axx** | 935 KB | 5,787 | **hello.s** | x86_64-v3 written with macros. Also used by the Brainfuck demo |
| **aarch64_logical_mini.axx** | 9.2 KB | 86 | **aarch64_logical_mini_demo.s** | AArch64 logical (immediate): AND/ORR/EOR/ANDS/TST, 32- and 64-bit. Encodes the bitmask immediate with the mini language (section 3.15) |
| **6809.axx** | 124 KB | 1,950 | **6809.s** | Motorola 6809 |
| **68000.axx** | 51 KB | 453 | **68000.s** | Motorola 68000 |
| **6800.axx** | 18 KB | 271 | **6800.s** | Motorola 6800 |
| **6502.axx** | 14 KB | 192 | **6502.s** | MOS 6502 |
| **z80.axx** | 7.5 KB | 283 | **z80.s** | Zilog Z80 |
| **8051.axx** | 8.9 KB | 111 | **8051.s** | Intel 8051 |
| **8080.axx** | 6.0 KB | 113 | **8080.s** | Intel 8080 |
| **8048.axx** | 6.3 KB | 95 | **8048.s** | Intel 8048 |
| **4004.axx** | 5.4 KB | 53 | **4004.s** | Intel 4004 |
| **test.axx** | 1.1 KB | 40 | **test.s** | Fragments of several ISAs; test only |
| **itanium.axx** | 281 B | 12 | **vliw.s** | Itanium (EPIC) sketch; incomplete |
| **vliw.axx** | 178 B | 10 | **vliw.s** | Non-EPIC VLIW; test only |
| **bf.axx** | 128 B | 9 | **bf.s** | Brainfuck virtual CPU; hello-world demo. Bundled, but not part of `test1` |

Note that `x86_64.axx` pairs with `hello.s`, not with a file named `x86_64.s`.
`itanium.axx` also uses `vliw.s`, and `aarch64_logical_mini.axx` pairs with
`aarch64_logical_mini_demo.s`.

`test1` runs fourteen of the pairs above through both implementations and
compares the results. `bf.axx` / `bf.s` is the one bundled pair it does not
cover.

x86_64 and legacy CPUs make up most of what is currently implemented, but that
reflects where the work has gone, not the limit of what axx can describe.

---

## Appendix C. Related resources

### C.1 Documents in this repository

| File | Contents |
|---|---|
| `MACRO.md` / `macro_en.md` | Macro layer reference (Japanese / English). Same material as section 7 |
| `MINI.md` / `mini_en.md` | Mini language reference (Japanese / English). Same material as section 3.15 |
| `axx_introduction_paper.md` / `_en.md` | Introduction paper: the design rationale behind the free-syntax pattern language, the specificity score, and the separation of computational power from the declarative core |
| `axxsemantics` | A denotational-semantics formalization of axx, including relaxation read as a fixed point over the label environment. The formulas in it are that document's own construction, not an official specification |
| `FILE_DESCRIPTION` | One-line description of every file |
| `format_of_exp_imp_file` | Export/import file format |
| `axx.1.gz` | Man page |

`test1` assembles fourteen bundled pattern/source pairs with both
implementations and compares the results.

### C.2 External

**Test environment:** FreeBSD, Linux terminal.

- Original article (Japanese): <https://qiita.com/fygar256/items/1d06fb757ac422796e31>
- Relocatable ELF generation: <https://github.com/fygar256/axx_relocatable_elf_generation>
- Brainfuck interpreter demonstration:
  <https://github.com/fygar256/brainfuck_interpreter_for_axx_on_freebsd_of_x86_64>

---

## Appendix D. Roadmap

### D.1 Not implemented

Pattern files plus advanced structured macros and optimization would make this
a considerably more capable system, but covering the full range of
structured-assembly macro constructs is more than one person can do. If someone
wants to take it on, I would be glad to see it.

### D.2 The axx2 concept

A more descriptive metalanguage for pattern files would improve readability,
remove the dependence on evaluation order, make control statements easier to
write, and make processor description files easier to debug. Pattern data is
more intuitive, so this is a trade rather than a straight win.

Generalizing further — a descriptive metalanguage, string literals and string
operations in what is currently `binary_list`, plus control statements — would
allow intermediate-language generation and conversion between assembly
languages. `binary_list` would become `object_list` and the pattern file would
become a *processor specification file*, described in a multi-line language
rather than as pattern data. This is feasible; apparently someone is working on
it based on axx.

Even in the current pattern files, macros can be written by assigning command
strings to variables — `a='MOV b,c'` — and referring to them in `binary_list`.
Extending single-character lowercase variables to full symbols, adding
`expand(a)` for expansion (with `a='b ; c'`, `b='MOV AX,d'`, `c='JMPC e'`
giving `'MOV AX,d ; JMPC e'`), `expression(a)` for evaluation, and `label:` for
definitions would go a long way.

Loop structures inside axx itself would make an infinite loop hard to debug;
confining evaluation to the pattern file keeps debugging tractable while still
permitting loops and branches, with self-reference checks. Turing completeness
would allow any processor architecture — LISP machines included, in principle.
Keeping the pattern file's labels separate from the assembly file's removes any
concern about the same label appearing in both. EPIC-style meta-processing is
solved by enumerating variables.

The cost is a drastic rewrite, and a more complex processor description file
makes compatibility with a general disassembler harder.

---

## Appendix E. Project notes

### E.1 Notes

- Apologies for the unconventional notation.
- axx does not support quantum computers or LISP machines. What quantum
  computers run is quantum assembly, and what LISP machines run is not assembly
  language at all.
- From homemade processors to supercomputers, please feel free to use it.
- Please evaluate, extend and modify axx. The structure is complex, but it is
  Python, so extending it is easy.
- Constants are currently limited to quadruple precision, which is a Python 3
  limitation. It would be good if Python 4 handled quad precision natively.
- The macro layer is built in, but covering every assembly language would need
  a stronger macro processor — one that lowers functional and structured
  assembly constructs into imperative form.
- Assemblers were originally built to make machine code readable by humans. Now
  that AI writes code, a generalized assembler covering both assembly language
  and the machine seems worth having — and generating pattern files for large
  ISAs is exactly the kind of work AI should be doing. Recent AI can do it.

### E.2 Bug reports

If you find a bug, please let me know what is not working.
