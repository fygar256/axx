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
axx 8080toz80.axx hello8080.s -V > out.s  # translated text to stdout
```

## Two implementations

| Language | File | Nickname | Role |
|---|---|---|---|
| Python | `axx.py` | Paxx | Reference implementation; new features land here first |
| C | `caxx.c` | Caxx | Much faster; may lag behind Paxx |

The two are intended to produce **byte-identical output** for the same input.
The bundled pattern files, test sources and the `test1` script exist to check
exactly that: `test1` assembles all nineteen bundled pattern/source pairs with both
implementations and `cmp`s the results. For the two `.textmode` pairs it also
`cmp`s the translated text each implementation sends to standard output under
`-V`, for twenty-one comparisons in all.

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
| `-V`, `--text-output` | Print the text built from string templates (section 3.5.2) plain to stdout (default: silent). This is what you use to translate a source with `.textmode` (section 3.18) |
| `-d`, `--debug` | Debug output: forward-ref fallback, relaxation log |
| `-g`, `--gen-debug` | Emit DWARF (`.debug_info`/`.debug_abbrev`/`.debug_line`). Requires `-o` and ELF64 |
| `--no-macro` | Disable the macro layer on both the source and pattern side |
| `-P [FILE]` | Macro-expand the source and write it out without assembling |
| `-p [FILE]` | Macro-expand the pattern file and write it out without assembling |
| `-h`, `--help` | Usage |

If no output option is given, nothing is written; `-v` is what makes the run
visible. Use `-V` when you want only the translated text of the string
templates, plain.

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
| lowercase name | Value of the **symbol** at that position |
| `!x` | Value of the **integer expression** at that position |
| `!!x` | Value of the **integer factor** at that position |
| `!Fx` | IEEE-754 bit pattern of a **32-bit** float expression |
| `!Dx` | IEEE-754 bit pattern of a **64-bit** float expression |
| `!Qx` | IEEE-754 bit pattern of a **128-bit** float expression |
| `!Lx` | Value of an **integer expression**, exactly as `!x`; in addition, the **text of that expression or label as written in the source** is remembered (section 3.18, `{{.exp(x)}}`) |
| `!Ex` | Value of an **enumerated operand list** declared with `.enum` (section 3.7.1) |
| `!S{{name}}x` | Value of the matching entry of the **sub table** `name` declared with `.sub` (section 3.7.2) |

Captured values are referenced from `error_patterns` and `binary_list` by the
bare name — the `!` prefix is not repeated there. Every variable is reset to 0
for each pattern line, so an unmatched optional operand reads as 0.

**Variable names.** A variable is written `x` above, but a name may be longer:
it starts with a lowercase letter and continues over lowercase letters, digits
and `_`, so `abcdef`, `var1` and `var_2` are all variable names. The same names
are used by `.check`, `.enum`, `.clrcheck`, `.clrenum`, `.map` and `.free`.

```
.check::reg::BC,DE,HL,SP
INC reg,!imm_1 :: :: 0x03|reg,imm_1
```

Length makes no difference: `a` and `var_2` are read by the same rule. In
`error_patterns` and `binary_list`, a run of text that starts with a lowercase
letter is a variable, whether or not this line captured it — an uncaptured name
reads as 0, the same as an unmatched optional operand. Nothing has to be
declared first.

A bare lowercase word there is therefore never a label. The run stops at the
first character that is not a lowercase letter, a digit or `_`, and if the
character that follows is one a label may contain (an upper-case letter or `.`),
the whole word is a label after all — so `aB` and `a.b` still read as labels,
while `a1` and `var_2` are variables. A label a pattern line has to name must
therefore carry an upper-case letter or a `.` somewhere in it.

**A separator that is itself a name character.** Because `_` continues a
variable name, an underscore written in `instruction` directly after a capture
is swallowed by that name rather than matched as text. In

```
MRS xt,S!S{{tbl}}a_Z
```

the name reads as `a_`, the separator disappears, and `mrs x0,s3_z` no longer
matches. Escaping it ends the name and matches the underscore literally:

```
MRS xt,S!S{{tbl}}a\_Z          /* matches mrs x0,s3_z */
```

The same escape is what separates two expression captures, since a numeric
literal also accepts `_` as a digit separator — `!v_!w` reads `3_5` as the
single number 35, while `!v\_!w` reads it as 3 and 5. This applies to every
kind of capture: a symbol placeholder, `!x`, `!!x` and `!S{{name}}x` alike.
An underscore that is not preceded by a capture needs no escape, and a
`.setsym` name containing one — `TPIDR_EL0` — is unaffected, because `_` is in
the default symbol character set and the whole word is one symbol.

Assembly lines are case-insensitive except for labels and section names.

The escape character `\` may be used inside `instruction`; see
[section 3.12](#312-escapes-in-expressions).

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

#### 3.5.2 Text templates — emitting a string

An element of the `binary_list` may be a **string** in double quotes instead
of an expression. It builds **text**: the assembly result for that source
line, written in some other mnemonic syntax. This turns a pattern file into a
source-to-source translator. The same text is also emitted as **binary**, one
byte per word, so the string itself becomes the output of that line.

```
MOV R!r,!e:: "LD R{{r}},0x{{.hex(e)}}"
```

Given `MOV R1,0x10`, that pattern outputs `LD R1,0x10`, as both text and the
ten bytes `4c 44 20 52 31 2c 30 78 31 30`.

A string is one element of the list like any other, so it may be mixed freely
with expressions, repeated with `@@[...]`, and written more than once. A comma
inside a string does not separate elements.

```
MOV A,!e::"load a,{{e}}\n",0x12,0x13
```

```
MOV A,3   ->  6c 6f 61 64 20 61 2c 33 0a 12 13   ("load a,3\n" then 0x12 0x13)
```

**Only `{{ }}` is substituted.** Everything else in the string is the text as
written — upper case, lower case, `.hex(e)` outside braces, all of it comes
out unchanged. The only other thing read is a backslash escape.

| Form | Meaning |
|---|---|
| `{{<expr>}}` | Evaluate the expression and insert it in decimal |
| `{{.hex(<expr>)}}` | Hexadecimal digits of the value |
| `{{.dec(<expr>)}}` | Decimal digits of the value |
| `{{.bin(<expr>)}}` | Binary digits of the value |
| `{{.float(<expr>)}}` | The value as a decimal 128-bit floating point number, 34 significant digits (`16` becomes `16.0`) |
| `{{<name>}}` `{{<name>[<expr>]}}` | A string symbol or array symbol, else a pattern variable — see below |
| `{{.index <name>[<expr>]}}` | The subscript that `{{<name>[<expr>]}}` uses, in decimal (3.6.1) |
| `{{.exp(<variable>)}}` | The expression or label captured by `!L<variable>`, spelled exactly as in the source (3.18) |
| `\n` `\t` `\r` `\\` `\"` | Newline, tab, carriage return, backslash, double quote |
| `\<char>` | any other `<char>` literally |

The four conversions emit digits only, with no radix prefix, so you write the
prefix yourself — `0x{{.hex(e)}}`, `0b{{.bin(e)}}`.

`.float` renders the value as a decimal 128-bit floating point number: 34
significant digits, rounded half to even. A value with no fractional part still
gets one, so `16` is written `16.0`. Beyond 34 digits, or for very small
magnitudes, it switches to exponent form (`1.234567890123456789012345678901235e+36`).
Both implementations produce byte-identical text.

**Names in `{{ }}`.** A name written alone inside the braces resolves in this
order:

1. a **string symbol** — `.setsym::<name>::"<text>"` — inserts its text;
2. an **array symbol** — with `[<expr>]`, the item at that index;
3. anything else — the **expression**, so a pattern variable gives its value in
   decimal.

That is why `R{{r}}` becomes `R1`: `R` is outside the braces and therefore
literal, and `r` is bound by `!r`.

Numeric `.setsym` symbols are deliberately *not* looked up by rule 1, so a
plain word is never silently replaced by a number. Write `{{#NAME}}` when you
want the value of a numeric symbol.

**String symbols.** `.setsym` stores text instead of a number when its value
field starts with a double quote:

```
.setsym::x::"LD"
MOV R!r,!e::"{{x}} R{{r}},{{.dec(e)}}"        ->  LD R0,12
```

```
.setsym::x::"LO"
.setsym::y::"AD"
MOV R!r,!e::"{{x}}{{y}} R{{r}},{{.dec(e)}}"   ->  LOAD R0,12
```

Given `mov r0,12`, those produce `LD R0,12` and `LOAD R0,12`. A string symbol
carries no numeric value, so it cannot appear in an expression — it exists for
text templates. `.clearsym` removes string symbols in the same way as numeric
ones.

Given `MOV R1,0x10`:

```
MOV R!r,!e:: "LD R{{r}},0x{{.hex(e)}}"    ->  LD R1,0x10
MOV R!r,!e:: "LD R{{r}},{{.dec(e)}}"      ->  LD R1,16
MOV R!r,!e:: "LD R{{r}},0b{{.bin(e)}}"    ->  LD R1,0b10000
MOV R!r,!e:: "LD R{{r}},0f{{.float(e)}}"  ->  LD R1,0f16.0
```

Where the text goes:

- A newline appears only where you write one. To make one source line become one
  output line, `.eol` (section 3.17) can do it instead of an `\n` in every
  template.
- It is emitted as bytes, exactly like `.ascii` (section 4.4): the rendered
  text is encoded in UTF-8 and each byte becomes one output word, so the line
  advances the location counter and lands in the binary and ELF output. A byte
  wider than the output word width (`.bits`) is truncated with a warning.
  There is no `\0` or `\xHH` escape — a byte that is not text is written as a
  number in the list, next to the string.
- With `-V`, the rendered line alone is also written to standard output, so
  the translated program can simply be redirected to a file. Without `-V`
  nothing reaches standard output (silent by default).
- With `-v`, it appears at the end of that line's diagnostic, after the `//`,
  enclosed in double quotes: `... MOV R1,0x10 // "LD R1,0x10"`. There it is
  shown escaped — a newline reads `\n`, not a line break — so the diagnostic
  stays on one line, and a line with several strings shows them apart, as they
  are written in the field: `... // "A","B"`.

  A `;;` element is evaluated and emitted nowhere, text included; a `;` string
  is skipped when it renders empty.

So one pattern file serves both uses at once: the text on standard output for
translation (`-V`), and the same string in the binary for assembly (`-b`/`-o`).

```
NOP  :: "ABC"
DW !e:: e,e>>8
```

```
NOP        ->  0x41 0x42 0x43
NOP        ->  0x41 0x42 0x43
L1:
DW L1      ->  0x06 0x00        ; L1 is 6, the three bytes of each NOP counted
```

### 3.6 Symbols

```
.setsym :: name :: value
```

One directive defines every kind of symbol; what the value field looks like
decides which kind it is:

| Value field | Defines |
|---|---|
| `0x20`, `#OTHER+1` | a **numeric symbol** — any pattern expression |
| `"LD"` | a **string symbol** — text for a template (3.5.2) |
| `[1,"A",#B]` | an **array symbol** — a list of numbers and text (3.6.1) |
| `other` | a **copy** of that string or array symbol, or else a **string symbol holding that name** (3.6.1) |
| `r0,r1,r2` | a **set** — a list of names (3.6.2) |
| `a&b`, `a\|b`, `a^b`, `a+b`, `a-b` | a **set** computed from other sets (3.6.2) |

The special forms — a quote, a bracket, a bare name, a list of names, a set
expression — are recognised as such wherever they fit; a field that is none of
them is read as a numeric expression. Each form is described in the section
named beside it.

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

A value field that starts with a double quote makes a **string symbol**:

```
.setsym::x::"LD"
```

String symbols hold text rather than a number, so they cannot appear in an
expression. They are used by text templates (section 3.5.2), where `{{x}}`
inserts `LD`. `.clearsym` removes them like any other symbol.

#### 3.6.1 Array symbols

A value field that starts with `[` makes an **array symbol**. Its items may be
numeric expressions, bare names, string literals, or a mix of them:

```
.setsym::x::[1,2,3,4,5]
.setsym::y::["A","B","C","D","E"]
.setsym::regs::[R0,R1,R2]          /* the same as ["R0","R1","R2"] */
```

Items are separated by top-level commas; commas inside `"..."` or inside nested
brackets or parentheses do not split. An item that is a **bare name** (`R0`,
`_tmp`) is held as text, spelled exactly as written, so `[r0,r1]` keeps its
lower case. Every other item is an ordinary pattern expression, so earlier
symbols are available (`.setsym::m::[1,#BASE,#BASE+1]`); write `#R0` when you
want the number a name was given by `.setsym` or `.map` rather than the name
itself.

An item is selected with `[<index>]`, counting from 0. The index is itself an
expression, so a pattern variable can drive it:

| Where | How | Example |
|---|---|---|
| Text template (3.5.2) | `{{x[3]}}` | `{{y[3]}}` → `D` |
| Expression | `#x[3]` | `MOV !e :: #x[3],e` emits `4` |

In a template, a numeric item is written in decimal and a string item is
inserted as text. `#x[3]` in an expression needs a numeric item — a string item
is an error there, since it has no numeric value. An array name with no index
in a template expands to all of its items joined by `,`.

**How a subscript resolves.** In a template — `{{<name>[<expr>]}}` and
`{{.index <name>[<expr>]}}` — a subscript written as a **string literal** is
opened to its text first, so `arrb["CX"]` reads the same as `arrb[CX]`. Inside a
template the closing `"` of the pattern's own string comes first, so the literal
is escaped there: `{{.index arrb[\"CX\"]}}`. The text is then resolved in this
order:

1. the name of a **string symbol** — its text is read again as the subscript;
2. the name of a **pattern variable** — rule 4 (the variable's value is used);
3. the name of an **item of that array** — the position of that item;
   failing that, a `.setsym` or `.map` **numeric symbol** of the same name — its
   value;
4. anything else — an ordinary **expression**.

Rule 3 is what makes a name usable as a subscript. Given

```
.map::r::AX,BX,CX                  /* AX=0, BX=1, CX=2 and .check::r */
.setsym::arrb::[R0,R1,R2]
.setsym::arra::[AX,BX,CX]
.setsym::var1::BX                  /* var1 is the name BX (3.6) */
```

`{{arrb[var1]}}` is `R1`: `var1` is the name `BX` (rule 1), `BX` is not an item
of `arrb`, and `BX` is the numeric symbol 1 that `.map` defined (rule 3), so the
subscript is 1. `{{arra[var1]}}` is `BX` for the other half of rule 3 — `BX` is
an item of `arra`, at position 1. `{{arrb[r]}}` uses rule 2, so
`MOV r,!e::"LD {{arrb[r]}},0x{{.hex(e)}}"` turns `mov bx,5` into `LD R1,0x5`.

**`.index` — the subscript itself.** `{{.index <name>[<expr>]}}` resolves the
subscript by exactly those rules and writes the resulting index in decimal
instead of the item. It is the name-to-number direction of a lookup:

```
.setsym::var1::BX
TEST v::"LD A,{{.index arra[v]}}"     /* TEST CX  ->  LD A,2 */
                                      /* {{.index arrb[var1]}}    ->  1 */
                                      /* {{.index arrb[\"CX\"]}}   ->  2 */
                                      /* {{.index arra[\"CX\"]}}   ->  2 */
```

The last two are the two halves of rule 3 arriving at the same answer: `CX` is
not an item of `arrb`, so its numeric symbol 2 is the subscript, while in `arra`
it is the item at position 2.

`.index(<name>[<expr>])` may be written with parentheses; the two forms are the
same. The array must exist and the subscript must be in range, as for any other
reference.

Out-of-range indices and `name[...]` on a name that is not an array are
reported as errors. `.clearsym` removes array symbols like any other symbol.

**Copying.** A value field that is just the name of an array or string symbol
copies it:

```
.setsym::x::["R1","R2","R3"]
.setsym::y::x                  /* y is now a copy of x */
```

The copy is independent — redefining `x` afterwards leaves `y` as it was. A bare
name that is neither an array nor a string symbol becomes a **string symbol
holding that name**:

```
.setsym::var1::BX              /* var1 is the name BX; {{var1}} writes BX */
```

That is what lets a name be carried around and used as a subscript (see *How a
subscript resolves* above). Write `#BX` for the number the name was given by
`.setsym` or `.map`, and `BX+0` (any expression, not a lone name) when you mean
the value of a *label* called `BX`.

**An array can stand in for a list of elements.** Wherever a directive takes an
enumerated list of names — `.check`, `.enum` and `.map` — writing the name of an
array symbol expands it to its contents in place:

```
.setsym::regs::["R0","R1","R2","R3","R4"]
.check::x::regs           /* same as .check::x::R0,R1,R2,R3,R4 */
.map::x::regs::1<<x       /* same as .map::x::R0,R1,R2,R3,R4::1<<x */
.enum::f::regs::…
```

Arrays and plain names may be mixed in one list (`.check::x::regs,SP`), and a
numeric item contributes its decimal spelling. One list of register names can
therefore be written once and used by every directive that needs it.

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

#### 3.6.2 Sets

A value field that is a plain list of names, separated by commas, makes a
**set**:

```
.setsym::a::a1,a2,a3
.setsym::b::b1,b2,b3,a2
```

A set is an array symbol whose items are those names, so everything in section
3.6.1 applies to it — `.check::x::a`, `.map::x::a::…`, `.enum::f::a::…`, and
`{{a}}` or `{{a[0]}}` in a template all work. Its items are names rather than
numbers, so `#a[0]` in an expression reports a string item as it would for any
other array of text. Names are upper cased like any other symbol name, and a
name repeated in the list is kept once. A name in the list that is itself a set
is expanded in place, so `.setsym::c::a,b` is the union of the two.

**Set algebra.** Sets combine with five operators:

| Written | Result |
|---|---|
| `a&b` | intersection — the names in both |
| `a\|b` | union — the names in either |
| `a+b` | union, the same as `a\|b` |
| `a^b` | symmetric difference — the names in one but not the other |
| `a-b` | difference — the names in `a` that are not in `b` |

```
.setsym::x::a&b        /* A2                      */
.setsym::y::a|b        /* A1,A2,A3,B1,B2,B3       */
.setsym::z::a^b        /* A1,A3,B1,B2,B3          */
.setsym::t::a+b        /* A1,A2,A3,B1,B2,B3       */
.setsym::q::a-b        /* A1,A3                   */
```

Each result is an independent copy, so redefining `a` afterwards leaves `x`
… `q` as they were, and `.setsym::a::a|b` is safe.

Order follows the first appearance of each name: the left operand's names
first, then the right operand's. Operators are applied left to right with no
precedence of their own, so `a&b|c` means `(a&b)|c`.

**When the field is not a set.** The set reading is tried before the ordinary
numeric one and gives way to it whenever the field cannot be a set, so nothing
that assembled before changes meaning:

- every item of a comma list must be a name — a list whose items start with a
  digit, such as `.setsym::X::1,2`, is left to the expression evaluator;
- every operand of an operator must be a bare identifier naming an existing
  set — `.setsym::X::#N1+#N2` adds two numeric symbols as it always did;
- a field holding a single name is a copy (section 3.6.1), not a one-element
  set. Write `.setsym::a::["A1"]` for that.

Because `-`, `&` and `|` may appear inside a symbol name, an operand is only
recognised as a set when it is spelled with letters, digits and `_` alone.

### 3.7 Symbol check (`.check`)

```
.check::x::r1,r2,r3
```

Restricts what may appear at the position captured by `x`. Anything else is an
error. `.clrcheck::x` removes the restriction. The list may be an array symbol
(section 3.6.1) or a set (section 3.6.2), or a mix of those and plain names.

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

#### 3.7.1 Enumerated operand lists (`.enum`)

Where `.check` restricts a position to *one* symbol out of a set, `.enum`
declares a position that takes a *list* of them — a register list such as the
68000's `MOVEM`.

```
.enum::<variable>::<element,element,...>::<expression>
```

The element list may be an array symbol (section 3.6.1) instead of names
written out.

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

#### 3.7.3 `.map` — a symbol table and its check in one line

```
.map::<variable>::<name,name,...>::<expression in the variable>
.map::<variable>::<name,name,...>::<value,value,...>
```

Gives each name in the list a value, and restricts the variable to that list.
The value field is read either way round: one expression that computes every
value, or a list of values that pairs up with the names one by one.

Inside the expression the variable stands for the **position of the name in the
list**, counted from 0.

```
.map::x::R0,R1,R2,R3,R4::1<<x
```

is exactly equivalent to:

```
.setsym::R0::1<<(0)
.setsym::R1::1<<(1)
.setsym::R2::1<<(2)
.setsym::R3::1<<(3)
.setsym::R4::1<<(4)
.check::x::R0,R1,R2,R3,R4
```

The expression may be left out, in which case it is the variable itself, so the
names get 0, 1, 2, … in order:

| Written | Values given to `R0`…`R4` |
|---|---|
| `.map::x::R0,R1,R2,R3,R4` | 0, 1, 2, 3, 4 |
| `.map::x::R0,R1,R2,R3,R4::x` | 0, 1, 2, 3, 4 |
| `.map::x::R0,R1,R2,R3,R4::1<<x` | 1, 2, 4, 8, 16 |
| `.map::x::R0,R1,R2,R3,R4::10**x` | 1, 10, 100, 1000, 10000 |

**A list of values.** When the value field holds more than one item, separated
by commas, the items pair up with the names in order:

```
.map::x::R0,R1,R2,R3::9,7,14,41
```

is exactly equivalent to:

```
.setsym::R0::9
.setsym::R1::7
.setsym::R2::14
.setsym::R3::41
.check::x::R0,R1,R2,R3
```

That is the form for a table whose values follow no rule. The two lists must be
the same length, or the directive reports an error and defines nothing. Each
item is an expression like any other, so `.map::x::R0,R1,R2::x*10,100+x,7`
gives 0, 101 and 7 — the variable still stands for the position.

Only commas outside brackets separate the items, so an expression that contains
one of its own is a single item: `.map::x::R0,R1,R2::*(#W,x)` stays one
expression, and the names get successive bytes of `W`.

Register files, bit masks and other tables whose names *are* the numbering are
the common case, and writing the `.setsym` lines out by hand makes it easy for
the list and the values to drift apart. `.map` is expanded into the directives
above as the pattern file is read, so nothing downstream treats it specially.

The position is substituted into the expression in parentheses, so operator
precedence is unaffected, and only whole-word occurrences of the variable are
replaced — the `x` of `0xff` is left alone.

An empty element (`""`) consumes its position without defining a symbol, which
keeps the numbering aligned while marking the operand as optional in the
`.check` list. With a list of values it consumes its value too, so the two
lists stay aligned.

The list may also be an array symbol (section 3.6.1), so the register names can
be written once and shared with `.check` and `.enum`:

```
.setsym::regs::["R0","R1","R2","R3","R4"]
.map::x::regs::1<<x
```

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

#### 3.7.4 `.free` — release a name from every table

```
.free::x1,y1,z1
```

Removes each name from every table the pattern layer keeps, so the name can be
reused without having to remember which directive defined it. It clears:

- the `.setsym` numeric, string, array and set symbol of that name;
- the `.sub` table of that name;
- that name wherever it appears as a candidate in a `.check` list;
- and, when the name reads as a variable name, that variable's whole
  `.check` list and its `.enum`.

Like `.clearsym` and `.clrcheck`, `.free` is positional: patterns written above
it still see the names, patterns below it do not.

```
.setsym::N1::7
.sub::T1
X::0x99
.return
BEFORE     :: :: #N1        /* 0x07 */
.free::N1,T1
AFTER      :: :: #N1        /* error - undefined symbol: '#N1' */
```

#### 3.7.5 `.reloc` — declaring a relocation type

```
.reloc::<variable>::<type name>
```

Writes the label reference that variable captured into the `-o` output as the
named ELF relocation. Like `.check` it is positional: a later `.reloc` replaces
an earlier one, `.clrreloc::x` takes it back (with no argument, all of them),
and `.free` clears it too.

The type name comes from the name table of the machine selected with `-m` — the
same table the source-side `::pc32` spelling uses (section 8.3).

The declaration only has an effect when `-o` was given. Without it the rows
below it behave exactly as if it were not there, which is what lets one set of
rows serve both outputs: a relocation for the linker under `-o`, an address axx
worked out itself under `-b`.

**Why it is needed.** Normally the type and the addend are inferred from the
emitted bytes: the value sits there as a plain integer across consecutive
bytes, so "emitted value minus label value" is the addend. But an AArch64
branch or address-generation instruction packs its value into scattered bit
fields of a 32-bit instruction word, scaled to words or to pages. The addend
cannot be read back out of that, and a guess made from width alone gives `bl` a
`PREL32` — which links without complaint and then branches four times too far.

`.reloc` states the type per instruction. The addend becomes the difference
between the operand value the pattern captured and the label value, so `bl
func` gives 0 and `bl func+8` gives 8. The instruction's own bit field is
emitted as 0 (RELA, so the linker fills it in — the same shape GNU as
produces).

```
.reloc::t::call26
BL !t :: :: @@[4,(0x94000000|(((t-$$)>>2)&0x3ffffff))>>(%%*8)]
.clrreloc::t
```

```
bl func      ->  R_AARCH64_CALL26  func + 0
bl func+8    ->  R_AARCH64_CALL26  func + 8
```

**Why it cannot be stated on the symbol.** The type follows the operand
position, not the symbol. The `adrp` / `add` pair that builds one address on
AArch64 refers to the same symbol under two different types,
`ADR_PREL_PG_HI21` and `ADD_ABS_LO12_NC`. A per-symbol spelling such as
`.extern name::type` cannot express that at all.

```
.reloc::p::adrp
ADRP X!d,!p :: :: ...
.clrreloc::p
.reloc::o::add_abs_lo12_nc
ADD X!d,X!n,#!o :: :: ...
.clrreloc::o
```

```
adrp x0,msg      ->  R_AARCH64_ADR_PREL_PG_HI21  msg + 0
add  x0,x0,#msg  ->  R_AARCH64_ADD_ABS_LO12_NC   msg + 0
```

Because `t` is the operand variable of nearly every row in a large pattern
file, the `.clrreloc` matters as much as the `.reloc`: without it the
declaration stays in force for every row the pattern scan walks past
afterwards. `aarch64.axx` is the worked example — its Relocation modifiers
section declares a type for each of `:lo12:`, `:pg_hi21:`, `:abs_g*:`,
`:prel_g*:`, `:got:` and `:got_lo12:`, and takes it back immediately after the
rows it belongs to.

One caveat when both outputs are asked for in the same run. The fields left at
0 are left at 0 in the raw binary too, so a `-b` image written alongside a `-o`
object is only correct once that object has been linked. axx says so rather
than letting it pass:

```
 warning - 16 instruction field(s) were left 0 for the linker (.text+0x0, ...);
 this raw binary is only correct after linking a.o. Drop -o to have axx fill
 them in.
```

These are the instruction-field types available for AArch64. The data types
(`abs64` `abs32` `abs16` `pc64` `pc32` `pc16`) are still inferred without a
`.reloc`.

| Type name | ELF | Field |
|---|---|---|
| `call26` / `jump26` | 283 / 282 | imm26 of `bl` / `b` |
| `condbr19` | 280 | imm19 of `b.cond`, `cbz` |
| `tstbr14` | 279 | imm14 of `tbz` / `tbnz` |
| `adr_prel_lo21` | 274 | immlo/immhi of `adr` |
| `adr_prel_pg_hi21` (`adrp`) | 275 | immlo/immhi of `adrp` |
| `adr_prel_pg_hi21_nc` | 276 | the same, without the overflow check |
| `add_abs_lo12_nc` | 277 | imm12 of `add` |
| `ldst8_abs_lo12_nc` | 278 | imm12 of a load or store |
| `ldst16` / `ldst32` / `ldst64` / `ldst128_abs_lo12_nc` | 284 / 285 / 286 / 299 | the same, scaled per access width |
| `movw_uabs_g0` ... `g3` (`_nc` forms too) | 263-269 | imm16 of `movz` / `movk` |
| `movw_prel_g0` ... `g3` (`_nc` forms too) | 287-293 | the same, PC-relative |
| `got_page` (`adr_got_page`) | 311 | immlo/immhi of `adrp` — the GOT page |
| `got_lo12` (`ld64_got_lo12_nc`) | 312 | imm12 of a 64-bit `ldr` — offset within the GOT |
| `got_ld_prel19` | 309 | imm19 of a literal `ldr` |
| `ld64_gotpage_lo15` | 313 | imm12 |

The two GOT types differ in kind from the rest. Their value is the address of a
GOT entry the linker builds, so it is not knowable at assembly time: the field
goes out as 0 and the relocation carries the whole meaning.

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

The escape also ends a **name** that would otherwise run on. A variable name
continues over lowercase letters, digits and `_`, and a numeric literal accepts
`_` between digits, so an underscore meant as a separator has to be escaped
where a capture precedes it:

```
MRS xt,S!S{{p0}}a\_!S{{d8}}b\_C!S{{d16}}c\_C!S{{d16}}e\_!S{{d8}}f
T   xt,!v\_!w
```

The first matches `mrs x0,s3_3_c4_c2_0`, binding the five fields separately;
the second matches `t x0,3_5` as 3 and 5 rather than as the number 35. Written
without the escapes, both lose the separator. `aarch64.axx` uses the first form
for the generic system-register spelling. Section
[3.3](#33-case-and-variables) has the rule this follows from.

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
| `... .call name(args) ...` | A call used as a term inside an expression — its value is the return value |
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

Pattern variables and `!!!` are *not* available there: nothing has
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
error.

`.call name(args)` may also appear as a term *inside* a larger expression, where
it stands for the value the function returns:

```
d = .call hypot2(a,b) + .call hypot2(c,e)
.if(.call firstdiv(n) == n)
m = t[.call idx(k)]
```

The call may be nested in the arguments of another call, and its arguments are
ordinary expressions. A function that returns nothing cannot be used this way —
it is an error, the same as in the assignment form. `.return` never closes the body — only `.endfunc` does
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

### 3.16 `.passthru` — letting unmatched lines through

By default a source line that matches no pattern is a `Syntax error` (code 1)
and the output is discarded. `.passthru` switches that to **emitting the line as
text, unchanged, instead of failing**. It is meant for translator use (the text
templates of section 3.5.2): write patterns for the lines you want to rewrite
and let the rest through.

```
.passthru          /* the same as on */
.passthru::on      /* let lines through */
.passthru::off     /* stop letting lines through (the default) */
```

The newline at the end of a line is not this directive's business. Write `.eol`
(section 3.17) alongside it when you want one source line to become one output
line.

A line let through is treated exactly as if a pattern whose encoding field was
`"<that line>"` had matched: one UTF-8 byte becomes one output word, the
location counter advances by that much, and, with `-V`, the text goes to
standard output.
The same text is produced in both passes, so labels after such a line still get
the right address.

```
.bits::8
.passthru
.eol
.map::r::AX,BX,CX
.setsym::rn::[AX,BX,CX]
MOV r,!e::"LD {{rn[r]}},0x{{.hex(e)}}"
```

```
	mov	bx,5        ->  LD BX,0x5
	xyzzy	foo, bar    ->  xyzzy foo, bar     /* let through */
	r1 = r2 + r3        ->  r1 = r2 + r3       /* let through */
```

What comes out is **the line as it was offered to the matcher**: tabs and runs of
spaces squeezed to one space, a `;` comment removed, and a leading label
definition removed (the label is still defined). In text replacement mode
(section 3.18) that comment and that label definition come back into the output
spelled as they were written.

The pattern file is scanned in full for every source line, so `.passthru` acts as
a setting for the whole file (the last one in the file wins).

Built-in assembly directives such as `.ascii` and `.resb` (section 5.3) are
handled before this, so they keep their meaning. A **misspelling** such as
`.aling`, on the other hand, is let through — with pass-through on, a typo flows
into the output instead of being reported.

### 3.17 `.eol` — a newline per line

A setting for text conversion: it **appends one newline word (`\n`) to every line
that produced output**. One source line becomes one output line without writing
`\n` into every text template.

```
.eol          /* the same as on */
.eol::on      /* append a newline per line */
.eol::off     /* do not (the default) */
```

```
.bits::8
.eol
.map::r::AX,BX,CX
.setsym::rn::[AX,BX,CX]
MOV r,!e::"LD {{rn[r]}},0x{{.hex(e)}}"
NOP::"NOP"
```

```
	mov	ax,0x10     ->  LD AX,0x10\n
	nop                 ->  NOP\n
```

- Only the **output words** get it. The text sent to standard output (the
  translator's own output under `-V`) does not, because that is already printed
  one line at a time — so a `-b`/`-o` file gains the newlines while standard
  output looks exactly as before.
- A line that produced no output word gets nothing (a comment-only line, a
  pattern that emits nothing, a directive line such as `.section`). Bytes written
  directly by `.ascii` and friends (section 5.3) are not affected either. In text
  replacement mode (section 3.18) a comment-only line and a directive line do
  emit text, so those do get the newline.
- With `.vliw` on it does nothing, so packets stay intact.
- Lines let through by `.passthru` (section 3.16) get the newline the same way.

The pattern file is scanned in full for every source line, so this acts as a
setting for the whole file (the last one in the file wins).

### 3.18 `.textmode` — text replacement mode

The setting for rewriting a source into text in another notation (using axx as a
translator). It does four things at once.

```
.textmode          /* same as on */
.textmode::on      /* text replacement mode */
.textmode::off     /* off (the default) */
```

1. Turns `.passthru` (3.16) on — lines that match nothing are let through.
2. Turns `.eol` (3.17) on — one source line becomes one output line.
3. An **undefined label inside what `!L` captured is not an error**. Its value
   becomes 0, and `{{.exp()}}` still emits the text as written.
4. A `;` comment in the source is **not dropped: it comes out after the rewritten
   text** (below).

`.passthru` and `.eol` move together, so to set one of them differently write that
directive after this line (directives take effect in the order written).

#### `!L<variable>` — the expression/label capture

Reads one expression and binds its value exactly as `!<variable>` does (3.3), and
**in addition remembers the text as written in the source**. The text template
`{{.exp(<variable>)}}` emits that text verbatim.

```
.textmode
LXI H,!La :: "LD HL,{{.exp(a)}}"
JMP  !La  :: "JP {{.exp(a)}}"
```

```
	lxi	h,msg       ->  LD HL,msg
	lxi	h,0x1234+2  ->  LD HL,0x1234+2
	jmp	loop        ->  JP loop
```

This is the case where the spelling matters and the value does not. Written with
`!a` and `{{.hex(a)}}`, a label collapses into a number such as `0x122` and the
label is gone from the rewritten text. With `!La` and `{{.exp(a)}}`, `msg` stays
`msg` and `0x1234+2` stays `0x1234+2`.

- The value side keeps working. One line may use both `{{.exp(a)}}` and
  `{{.hex(a)}}`, and `error_patterns` may still test `a>0xffff;2`.
- The extent read is the same as `!<variable>`, and `!La\,` gives it a stop
  character with `\` in the same way. Surrounding blanks are trimmed off the
  remembered text.
- When the capture sat inside `[[ ]]` (3.8) and was not taken that time,
  `{{.exp()}}` is empty. A name that is not used as a variable at all is a
  mistake and is reported as an error.
- Outside text replacement mode `!L` behaves exactly like `!` (an undefined label
  is an error). The text is remembered either way.

#### A leading `label:`

In text replacement mode a label definition at the start of a line **is emitted
at the start of the output**. The label is registered as a label and also stays
in the output spelled as written, so the rewritten text can be assembled as it
is.

```
	lxi	h,msg
here:	nop
msg:
```

```
LD HL,msg
here: NOP
msg:
```

A line holding nothing but a label comes out as its own line. A line that emitted
numbers rather than text (`.ascii` and the other built-in directives of section
5.3) is left alone, so data is not corrupted. With `.vliw` on it does nothing, as
`.eol` does not, so packets stay intact.

The label's value points at the **start of what the line emits, the label's own
spelling included**. Both passes emit the same text, so the size of the line and
the value of the label agree across the two passes.

#### `;` comments

In text replacement mode a `;` comment in the source **stays in the output spelled
as written**. It comes after the rewritten text with a single blank between them.

```
	mvi	c,9		; BDOS function 9    ->  LD C,9 ; BDOS function 9
	.org	0x100		; loaded at 0x100    ->  .org 0x100 ; loaded at 0x100
here:	; a comment after a label only       ->  here: ; a comment after a label only
; a whole-line comment                       ->  ; a whole-line comment
```

- A line holding nothing but a comment comes out as **its own line**. Outside text
  replacement mode nothing is emitted for it, as before.
- A `;` inside a string `"..."` or a character literal `'x'` is real data, so it
  does not start a comment. A `;` written as `\;` becomes a plain `;` with the
  backslash taken off and does not start one either (section 3.2).
- The comment is attached to a line that emitted text and to a comment-only or
  label-only line. A line that emitted numbers rather than text is left alone, so
  data is not corrupted. With `.vliw` on it does nothing, as `.eol` does not, so
  packets stay intact.
- The comment on an `.include` line is not echoed: the lines it pulls in are
  translated first, and a comment coming out after them would read out of order.
- The label's value points at the start of the line, the comment included. Both
  passes emit the same text, so the size of the line and the value of the label
  agree across the two passes.

#### Built-in directive lines

In text replacement mode a line holding one of axx's own built-in assembly
directives (section 5) **also comes out as text**, so that lines such as `.org`
and `.section` do not vanish from the translation.

```
	.org	0x100        ->  .org 0x100
	.section .text       ->  .section .text
	.global	start        ->  .global start
buf:	.resb	16           ->  buf: .resb 16
msg:	.ascii	"Hello"      ->  msg: .ascii "Hello"
val:	.equ	0x1234       ->  val: .equ 0x1234
```

- `.org`, `.align`, `.zero`, `.ascii`, `.asciz`, `.resb`, `.resw`, `.resd` and
  `.resq` come out as text and **emit nothing of their own**. Emitting padding or
  raw data as well as the text of the line would put the content in twice and mix
  it into the rewritten text. What text replacement mode emits *is* the rewritten
  text, so a `-b` file is exactly the translated text.
- `.section`, `.endsection`, `.labelc`, `.extern`, `.reloctype`, `.export`,
  `.global` and `label: .equ <expr>` do their job as before and come out as text
  as well.
- `.include` alone is not echoed: the lines it pulls in are translated in place,
  so echoing it too would duplicate them.

The pattern file is scanned in full for every source line, so this acts as a
setting for the whole file (the last one in the file wins).

#### Example: 8080 to Z80

The bundled `8080toz80.axx` is this mode at work: it reads Intel 8080 source and
writes Zilog Z80 source text for the same program.

```sh
axx 8080toz80.axx hello8080.s -V > helloz80.s
```

`hello8080.s`, the bundled input (its comments are written in Japanese):

```
        .org 0x100        ; .COM は 0x100 にロードされる
start:
        mvi c,9          ; BDOS function 9 = print $-terminated string
        lxi d,msg        ; DE = アドレス of msg
        call 0x0005      ; BDOS entry at 0005h
        ret              ; CP/M に戻る

msg:    db 'Hello, world$'
```

and the `helloz80.s` that comes out:

```
.org 0x100 ; .COM は 0x100 にロードされる
start:
LD C,9 ; BDOS function 9 = print $-terminated string
LD DE,msg ; DE = アドレス of msg
CALL 0x0005 ; BDOS entry at 0005h
RET ; CP/M に戻る
msg: db 'Hello, world$'
```

Its operands are captured with `!L` and emitted with `{{.exp()}}`, so `msg` stays
a label and `0x0005` keeps the spelling it was written with, and every comment
stays where it was written. The `helloz80.s` that
comes out assembles as it is with `z80.axx`. Sending the text to standard output
is `-V`'s job, so without it nothing appears on screen (`-b` still writes the
same text to a file).


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
Comments start with `;`. A comment is dropped, except in text replacement mode
(section 3.18), where it stays in the output spelled as written.

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
| Pattern variables | yes | uppercase only | no | no |
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

The pattern file's `.reloc` (section 3.7.5) takes the same names. An
instruction-field type such as AArch64's `call26` only means anything there,
because a per-symbol spelling cannot say which operand position it applies to.

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
| A line cannot be parsed | *Syntax error* (let through instead when `.passthru` is on — section 3.16) |
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

A `.raise n` directive in axx mini language raises an error with an error code n.

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

`x86_64.axx`, `x86_64m.axx`, `aarch64.axx`, `68000.axx`, `z80.axx`, `8080.axx`,
`8048.axx`, `8051.axx`, `6502.axx`, `6800.axx`, `6809.axx` and `4004.axx` are
for practical use, as is `aarch64_logical_mini.axx` within the one instruction
group it covers. The rest are test fixtures.

The x86_64 pattern file is also maintained separately at
<https://github.com/fygar256/x86_64_pattern_file_for_axx>.

| Pattern file | Size | `::` lines | Source | Notes |
|---|---|---|---|---|
| **x86_64.axx** | 3.9 MB | 23,923 | **hello.s** | x86_64-v3: segment addressing, AVX/AVX2, BMI1/BMI2, x87, EVEX/AVX-512 |
| **x86_64m.axx** | 935 KB | 5,787 | **hello.s** | x86_64-v3 written with macros. Also used by the Brainfuck demo |
| **aarch64.axx** | 339 KB | 8,214 | **aarch64.s** | AArch64 (A64): data processing, branches, exception generation, hints, barriers, system registers and SYS aliases, loads and stores, LSE atomics, scalar floating point, Advanced SIMD (vector and scalar) including the LD1-LD4 / ST1-ST4 structure accesses, cryptography, and the scalar extensions (PAuth, MTE, MOPS, FCMA, dot product, BFloat16, matrix multiply, LS64), and the GNU-style relocation modifiers `:lo12:`, `:pg_hi21:`, `:abs_g0:`-`:abs_g3:`, `:prel_g0:`-`:prel_g3:` and `:got:` / `:got_lo12:`, which with `-o` are emitted as relocations for the linker to fill in (`R_AARCH64_ADR_PREL_PG_HI21`, `ADD_ABS_LO12_NC`, the `LDST*_ABS_LO12_NC` family, `MOVW_UABS_G*` / `MOVW_PREL_G*`, `ADR_GOT_PAGE` and `LD64_GOT_LO12_NC`) and which with `-b` axx resolves itself, reading the GOT pair as naming the slot. Also SVE and SVE2 -- arithmetic, shifts, compares, predicates, element counts, permutes, reductions, the whole load/store family (contiguous, replicating, non-fault, first-fault, gather, scatter, prefetch), the widening and narrowing groups, complex arithmetic and the SVE2 cryptography -- SME: streaming mode, the ZA array, and the integer, floating-point and BFloat16 outer products -- and SME2: the predicate-as-counter registers, the ZT0 lookup table, the multi-vector operations on Z registers, accumulation into the ZA array, and the multi-vector loads and stores in both their consecutive and strided forms |
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
| **8080toz80.axx** | 5.8 KB | 117 | **hello8080.s** | Intel 8080 to Zilog Z80 source translator; `.textmode`, `!L` and `{{.exp()}}` (3.18) at work |
| **textmode.axx** | 1.8 KB | 13 | **textmode.s** | `.textmode`, `!L`, `{{.exp()}}` and `;` comments (3.18); test only |
| **arrindex.axx** | 860 B | 14 | **arrindex.s** | Array symbols: bare names as items, a name as a subscript, `.index` (3.6.1); test only |
| **passthru.axx** | 686 B | 6 | **passthru.s** | `.passthru` and `.eol` (3.16 / 3.17); test only |
| **itanium.axx** | 281 B | 12 | **vliw.s** | Itanium (EPIC) sketch; incomplete |
| **vliw.axx** | 178 B | 10 | **vliw.s** | Non-EPIC VLIW; test only |
| **bf.axx** | 128 B | 9 | **bf.s** | Brainfuck virtual CPU; hello-world demo. Bundled, but not part of `test1` |

Note that `x86_64.axx` pairs with `hello.s`, not with a file named `x86_64.s`.
`itanium.axx` also uses `vliw.s`, and `aarch64_logical_mini.axx` pairs with
`aarch64_logical_mini_demo.s`.

`test1` runs all nineteen of the pairs above through both implementations and
compares the `-b` raw binaries. For the two pairs that use `.textmode`
(`textmode.axx` and `8080toz80.axx`) it also compares the translated text each
implementation writes to standard output under `-V`, for twenty-one comparisons
in all.

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

`test1` assembles all nineteen bundled pattern/source pairs with both
implementations and compares the results, plus the `-V` translation text of the
two `.textmode` pairs.

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
