# axx: Generalizing Imperative Assembly Language — Design and Implementation of a General Assembler Based on a Free-Syntax Pattern Language and a Three-Layer Architecture

**An introductory paper on axx.py / caxx.c by Taisuke Maekawa (fygar256) — October 2026 edition**

## Abstract

axx (Arbitrary eXtended X assembler) departs from the conventional practice of implementing a dedicated assembler for each processor. It is built on a single insight: every imperative assembly language can be reduced to one pattern form, `instruction :: error_patterns :: binary_list`. This paper presents the central invention of axx — its free-syntax pattern language — together with the design decisions that follow from it: tokenizer-less character-level matching, order-independent pattern matching driven by a specificity score, and the separation of computational power from the declarative core. The current version of axx has a three-layer architecture: a macro layer that computes before reading, a declarative pattern layer, and a mini language invoked during encoding. The pattern layer guarantees termination of matching as a property of the language, and hands control to a Turing-complete mini language only when the author explicitly writes `.call`.

This edition newly discusses two major milestones that the current specification has reached since the previous edition. The first is the **generalization of ELF**. Branching on the machine number has been removed from the code that writes ELF, so that everything from relocation types, ELF class, RELA/REL, bit fields within instruction words, paired relocations, the layout of `r_info` and the unit of addends, through section groups and CFI, can be described purely by declarations in the pattern file. The built-in tables for eleven machines are nothing more than such declarations written in advance. The second is **source-to-source translation through text output**. Now that `binary_list` can contain string templates, a pattern file is at once a binary generator and a translator between assembly languages; part of the direction the author laid out as the axx2 concept has thus been realized on the current declarative core. In addition, the paper reports the enriched symbol system (sets and set algebra, the symbol capturer `!Y`), practical pattern files covering AArch64 (through SVE/SME2), PowerPC64 (POWER10), the whole of RISC-V RV64 and MIPS (MIPS I through MIPS64 Release 6 with its extensions), and a verification regime that cross-checks the two implementations in 182 comparisons. It places axx within the historical lineage of meta-assemblers and discusses its significance in an era in which AI generates pattern files.

## 1. Introduction

Assemblers have conventionally been implemented in one-to-one correspondence with a particular instruction set architecture (ISA). Even in a multi-target assembler such as GNU as, each target exists as a backend hard-coded into the program, and supporting a new processor means modifying the assembler itself.

axx inverts this arrangement. The assembler proper is a minimal matching engine with no knowledge of any ISA; all knowledge of individual processors lives in external declarative data — the pattern file (processor description file). A user obtains an assembler for a processor simply by transcribing its specification into a pattern file. axx targets not only virtual CPUs but "abstracted real CPUs": once a real processor's specification has been turned into a pattern file, it can be assembled for directly.

In the current version, the principle that "the engine does not know the machine" extends beyond instruction encoding to object file generation. Which CPU a linkable ELF is produced for is likewise determined solely by declarations in the pattern file (Section 7).

The idea dates from 1986, when the author was a university student working part-time at Tokyo Denshi Sekkei; the name AXX and a prototype in C already existed at that time. The working code was published in 2024, after the original program listing resurfaced 38 years later and was rewritten in Python. What matters is that those 38 years were not mere dormancy: they served as a validation period showing that the idea remained valid through the diversification of hardware — VLIW, EPIC, processors whose word size is not 8 bits, and scalable vector extensions.

## 2. The Central Invention: Reduction to a Single Pattern Form

The most fundamental claim of axx is that every imperative assembly language, except EPIC/VLIW with their meta-level complexity in machine code, can be reduced to the structure

```
instruction :: error_patterns :: binary_list
```

Omitting error checking, this simplifies further to `instruction :: binary_list`. This is a minimization of the definition "an assembler is the grammar of instructions plus binary generation based on it"; it amounts to extracting what is common to imperative ISAs of the von Neumann architecture, meta-modelling the ISA, and formalizing the result as pattern matching.

An instruction is defined as a combination of string literals, symbols replaceable by integer values, integer expressions, integer factors and floating-point expressions. The content of the reduction thesis is that combinations of these five elements suffice to handle any imperative assembly language; any processor whose instructions correspond one-to-one to machine code can be handled.

The x86_64 RET instruction, for example, is complete in a single line:

```
RET :: 0xc3
```

Instructions with operands also fit in one line as combinations of variables and expressions. For the 8048,

```
ADD A,R!n :: n>7;5 :: n|0x68
```

produces 0x69 from `add a,r1`, and returns error code 5 (Register out of range) if the register number is out of range. Syntax, validity checking and code generation are declared as a single-line correspondence. This granularity of "one line = one instruction pattern" is what guarantees that a specification can be transcribed.

In practice, binary_list also offers complex expression evaluation, alignment, the `;` prefix that suppresses output when the value is 0, and the `;;` prefix that evaluates without emitting; but these are not needed by the minimal model. The core is the single line above.

## 3. Design as a Free-Syntax Pattern Language

### 3.1 A grammar without a grammar

The pattern language of axx (the instruction field) is a DSL, yet it has no fixed grammar. It is a free-syntax language in which users build their own grammar from string literals, symbols, integer expressions, integer factors and floating-point expressions. As a result, it is not bound to the traditional `mnemonic operand` form: an ISA with assignment-style notation such as `r1 = r2 + r3`, and ARM64 SIMD notation such as `{v0.4s}`, can be described in the same framework. This property makes axx not only an assembler but also a general-purpose binary generator.

This stands out in contrast to existing large-scale infrastructure. LLVM's assembler-generation machinery (TableGen/AsmMatcher) assumes mnemonic-led syntax and needed special handling for Hexagon's mnemonic-less `r0 = r1` transfer syntax. axx never had that assumption built in.

The name reflects the design philosophy. axx is not a general-purpose assembler in the sense of "widely usable", but a general assembler in the sense of "common to everything".

### 3.2 Tokenizer-less character-level matching

axx has no lexical analyzer; it matches patterns character by character. This is a deliberate design decision: to handle syntax in which mnemonics contain symbol characters (real ISAs have many register names and mnemonics containing `.`, `$` or `%`), it is better not to fix the notion of a token in advance.

The conventions are simple. In a pattern file, uppercase letters, digits and symbols are character constants (an uppercase letter matches both upper and lower case in the assembly line), and a name beginning with a lowercase letter (`a`, `var1` and `var_2` all follow the same rule) is a variable bound to the value of the symbol at that position. Prefixing `!` binds an integer expression, `!!` an integer factor, and `!F` / `!D` / `!Q` the value of a 32/64/128-bit floating-point expression. The current version adds `!L`, which also keeps the source spelling of an expression; `!E` for enumerated operand lists; `!Y`, which captures the index of an item in a set; and `!S` for referring to subtables (Section 3.6, Section 6). All unbound variables are initialized to 0. Given only these minimal conventions, deciding where the boundary between lexis and syntax lies is left to the pattern author.

### 3.3 The character set itself is configurable

A consequence of the tokenizer-less design is that even "which characters make up an identifier" can be declared from the pattern file. `.symbolc` extends the character set used for symbols, and `.labelc` the character set used for labels. This is how MIPS register notations such as `$s5` and `$v0` can be written as symbols without special treatment. That even lexical rules are not fixed by the implementation is a consistent extension of the free-syntax design.

### 3.4 Order-independent matching via a specificity score

In a pattern file, directives (`.setsym` and so on) are order-dependent, but patterns themselves are not. axx does not stop at the first matching pattern; it assigns a specificity tuple `(n_expr, -n_lit, n_sym)` to every pattern that matches and selects the smallest. That is, the pattern with the fewest expression captures wins; ties go to the one with the most literal characters matched, then to the one with the fewest symbol captures.

```
MOV A,!d :: 0xAA,d
MOV A,B  :: 0xBB
```

Swapping these two lines does not change the result. Pattern authors are freed from the implicit burden of table-driven assemblers: "write the more specific pattern first". This matters most in large pattern files such as x86_64, where special cases sit far from the general rules they override.

The current version can extend this property to the directives as well. With the one line `.unordered` in a pattern file, every directive holds for the whole file, and neither where a directive is written nor how the directives are arranged among themselves means anything. Two different definitions of the same thing, and directives such as `.clrcheck` that only mean "from here on", are errors. References between `.setsym` definitions are resolved in dependency order. `.map` keeps a table of names and values per variable, so a name like the Z80 `C`, which is 1 as a register and 3 as a condition (carry), can be written both ways in one file without redefining it with `.setsym`. A file without `.unordered` is still read from top to bottom.

### 3.5 The symbol system — numbers, strings, arrays and sets

`.setsym::name::value` is a single directive that defines different kinds of symbol depending on how the value field looks.

| Value field | Defines |
|---|---|
| `0x20`, `#OTHER+1` | numeric symbol |
| `"LD"` | string symbol (for text templates) |
| `[1,"A",#B]` | array symbol |
| `r0,r1,r2` | set |
| `a&b`, `a\|b`, `a^b`, `a+b`, `a-b` | set computed from other sets |

A later definition of the same name overrides an earlier one, which lets a situation in which "the same characters have different values depending on context" (such as the Z80 register `C` and the condition flag `C`) be expressed naturally through the order of description in the pattern file.

Sets can be combined by intersection, union, symmetric difference and difference, and each result is kept as an independent copy. Because a register class can be defined by set operations, as in "general registers minus the stack pointer", operand constraints appearing in a specification can be transcribed in the form they take there. Importantly, the set interpretation is tried before the numeric one, but a field that cannot be a set always falls back to the numeric reading as before, so the meaning of existing pattern files does not change.

### 3.6 Constraining and capturing positions

On top of the symbol system sit mechanisms for constraining and capturing operand positions.

`.check::x::r1,r2,r3` restricts which symbols may appear at the position of variable x. This is equivalent to type checking of register classes, and it makes it possible to write groups of registers with the same role but different widths — `AL`/`BL` and `AX`/`BX` — as separate patterns without ambiguity.

```
.check::s::AL,BL
.check::t::AX,BX
MOV s,!a  :: 0xb0|s,a
MOV t,!a  :: 0xb8|t,a,a>>8
```

`.map::x::R0,R1,R2,R3::1<<x` combines giving values to a list of names and the `.check` for that position into one line. `.enum` captures register *lists* (including `-` ranges) such as those of the 68000 `MOVEM` and folds their composition into a single value. `.sub` gathers the alternatives that may appear at a position into a named *table of patterns*, referred to by `!S{{name}}variable`. Whereas `.check` restricts a symbol, a subtable lets a pattern stand at that position.

The symbol capturer `!Yset[variable]`, added in the current version, reads one item name of a set at that position and binds its *index* to the variable.

```
.setsym::x::AX,BX,CX
ENC !Yx[z] :: 0x40|z
```

Whereas `.check` merely restricts a position, `!Y` restricts it and also passes on "which one it was". Because the lookup runs from name to index and from index to name, two sets with the same ordering let one spelling be mapped onto the other. This plays a central role in the source-to-source translation of Section 6.

Finally, `.free` releases the given names from every table the pattern layer holds, so that a name can be reused without remembering which directive defined it. It keeps things hygienic when large pattern files are combined as modules.

The consistent policy of axx is that the parts of an ISA that resist structuring are resolved by these enumeration and capture mechanisms.

## 4. Isolating Computational Power — A Declarative Core and Computation That Must Be Asked For

The pattern notation of axx itself is Turing incomplete. binary_list has only five control constructs: assignment (`:=`), the ternary operator, the `;` prefix, alignment, and `@@[]` (repetition).

This is a design choice, not a lack of capability. Making the notation Turing complete would turn the whole DSL into a "program" and lose the guarantee that pattern matching terminates. Processor architectures can be made arbitrarily complex if one so chooses; a Turing-complete notation could follow any architecture, but at the cost of the pattern file becoming code rather than declarative data. axx chose to remain declarative data with guaranteed termination.

The current version does not, however, make this choice an inescapable constraint. Only when an element of binary_list is written as `.call name(args, …)` does control pass to a function in the mini language defined by `.func` … `.endfunc`. The mini language is a Turing-complete procedural language with assignment, `.if`/`.elif`/`.else`/`.endif`, `.while`, `.for`, recursion and variable-length arrays; values passed to `.emit` become the words at that position. When it detects an out-of-range value or the like, it can report an error code with `.raise`, and `.echo` provides debugging output that does not affect the result. Labels, the location counter and `.setsym` symbols can be read through the assembler's own expression evaluator.

```
BR !t :: .call rel8(t)

.func rel8(target)
d = target - $.
.if d < -128 || d > 127 .then
.raise 2
.endif
.emit(d & 0xff)
.return
.endfunc
```

As a real example, the AArch64 logical immediate requires a search that decomposes a bitmask into `N:immr:imms`, an encoding hard to express with a fixed expression. The bundled `aarch64_logical_mini.axx` writes it in the mini language and fits the whole instruction group into 86 pattern lines.

What matters is that this computational power is not mixed into the pattern notation. Computation appears only as a separate language called by name, when the author explicitly writes `.call`. Matching terminates as before, and instructions that can be written declaratively remain declarative single lines. Whether to step into unbounded computation is a per-line choice, not a property of the pattern file as a whole.

In the current version the mini language has gained one more entry point besides binary_list. When writing ELF, write-back into fields in REL format (`.elfencode`) and the construction of `r_info` (`.elfrinfo`) can be delegated to functions written in the pattern file (Section 7). Here too, computation appears only as functions declared by name, and the ELF-writing code itself stays ignorant of the machine. This shows that the principle of isolating computational power is applied consistently even outside encoding.

ISAs outside the scope still exist, but the reason lies in the reduction thesis itself, not in computational power. The following three lie outside the model of "one-to-one correspondence between instructions and machine code", so no amount of added computational power reaches them.

| Processor | Why it is out of scope |
|---|---|
| Mill CPU | belt architecture: operand references depend on execution history |
| ZISC | there are no instructions |
| Thinking Machines | massively parallel; there is no per-instruction encoding to target |

The current technical manual also documents implementation limits explicitly. Machines whose smallest addressable unit exceeds 64 bits and non-binary machines such as the ternary Setun are not handled, and conversion of floating-point data is limited to IEEE 754 formats (half to quadruple precision). Stating the boundaries of applicability as specification, in terms of both the model and the implementation, is an honest contrast to tool designs that tend to proclaim themselves "universal".

## 5. The Three-Layer Architecture — Macro Layer, Pattern Layer, Mini Language

The current version of axx consists of three layers of different character.

1. **Macro layer.** A source-to-source transformation stage that runs before the source reaches the assembler proper. It has `!def`/`!if`/`!while` and is syntactically capable of general computation.
2. **Pattern layer.** The declarative core responsible for matching and encoding. Its notation is Turing incomplete, and matching always terminates.
3. **Mini language.** A procedural language called by name during encoding (and during ELF writing). Turing complete.

The important point is that both layers with computational power are added **as layers separate from the pattern layer**, so the declarativeness of the pattern layer itself is preserved. The macro layer sits before reading and the mini language at encoding time, and each is activated only when an explicit notation is written (a statement beginning with `!`, a `.call`, or a function named in a declaration). Both are implemented to the same specification in `axx.py` and `caxx.c`.

The practical effect of the macro layer is substantial. The x86_64 pattern set through AVX-512 is 23,923 lines when written flat, but `x86_64m.axx`, written with macros, is 5,787 lines — about a quarter — and expands at load time into a byte-for-byte identical pattern set. AArch64 (2,068 lines → 9,387), Power ISA (452 → 4,774) and the whole of RISC-V (2,186 → 4,137) are likewise written with the macro layer.

### 5.1 Syntax

Every statement begins with `!` at the start of a line.

| Syntax | Meaning |
|---|---|
| `!def name(p1, p2, p3 = default) { ... }` | macro / compile-time function definition |
| `!return expr` | return value; also exits the body early |
| `!if expr !then { ... } !elif ... !else { ... }` | conditional |
| `!while expr { ... }` | loop |
| `!break` / `!continue` | loop control |
| `!set` / `!local` / `!undef` | assign, declare, delete a variable |
| `!include "file"` | textual inclusion at expansion time |
| `!error` / `!warning` / `!echo` | abort expansion / diagnostics |

Values are interpolated with `!{expr}`, and with Python-style format specifications as `!{expr:04x}`. Format specifications follow Python's format mini-language; both implementations accept the same specifications and reject the same ones. Values are limited to integers and strings, and operators follow C (`/` and `%` truncate toward zero). Inside a macro, `__id__`, unique per call (for generating local labels), and `__name__` are implicitly defined.

### 5.2 A different approach to termination

Because the macro layer has `!while` and recursion, it is syntactically capable of general computation. However, resource limits are imposed on execution: exceeding 200 levels of recursion, 1 million `!while` iterations, 2 million generated lines or 64 levels of `!include` nesting raises an error and aborts further expansion. The mini language is similar: exceeding 4 million executed statements, 128 levels of call nesting, 1,048,576 output words or an array length of 1,048,576 per `.call` raises an error pointing at the offending line. In these two layers, termination is secured not by "cutting down the expressiveness of the language" but by "imposing resource limits".

Herein lies the meaning of the three-layer architecture. The pattern layer remains declarative data and guarantees termination of matching as a property of the language. The parts that need computational power are isolated in separate layers — a preceding source-to-source transformation and a mini language called by name — which are protected by resource limits. The choice of a "declarative core" described in Section 4 has not been withdrawn by adding these layers; it has been preserved by separating their scope of influence.

### 5.3 Reading assembler-side values, and how convergence is secured

In the current version, the macro layer can read values from the assembler proper, on the source side (`.s`) only. Label values and `.equ` definitions are read as bare identifiers, names that cannot be written as macro identifiers through `label("...")`, and the location counter through `$` / `$$`. Macros on the pattern-file side run before the source is assembled and so are outside this facility; the declarative pattern layer itself is unaffected.

What can be read here is not "the current value". Macro expansion runs before addresses are fixed, so at that moment the value does not exist in principle. What is actually read is the value obtained in *the previous relaxation iteration*; in the first iteration, labels are 0, `defined()` is false and `$` / `$$` are 0.

What this design gives up is the idempotence of expansion. Since the result of expansion depends on label values, expansion is no longer a function of the source text alone and may change from iteration to iteration. The macro layer has become not "a preceding stage that runs once before assembly" but a component participating in the relaxation fixed-point iteration.

The securing of convergence thus moves from a structural guarantee to run-time detection. The relaxation loop has an upper bound on iterations, judges convergence when label placement agrees between iterations, detects periodic oscillation, and if it fails to converge, exits with an error without writing the output file. This is not a newly added safety net: the mechanism already existed for the problem axx had from the start — forward references in variable-length instructions. What the change added is not a new kind of danger but a new entry point to it. In either case, a wrong binary is never silently written.

Termination and convergence are now secured in three tiers: matching in the pattern layer by the language specification, individual macro expansions and mini-language executions by resource limits, and the sequence of expansions by the relaxation fixed point. The first two are static guarantees, while only the third is run-time detection; this design asymmetry deserves to be stated explicitly. It is also given a semantic position by the bundled `axxsemantics`, which formalizes relaxation as a fixed point over label environments.

### 5.4 Semantics across the two implementations

`axx.py` and `caxx.c` implement the same specification for the macro layer; the only difference is numeric representation. The Python version uses arbitrary-precision integers and the C version `int64`, so results differ only when macro-time computation exceeds 64 bits. Because the output of the macro layer is source text, this difference does not propagate into the assembler's own 256-bit expression evaluation. That the location and reach of the difference are documented is practically important for maintaining two implementations.

### 5.5 Current limitations

The source-side `.include` does not pass through the macro layer, so `!include` must be used to bring in macro definition files (the pattern-side `.include` does pass through the layer). Interactive mode (when no source file is given) bypasses the macro layer. A notation combining the ternary operator with a format specification, such as `!{a ? b : c:04x}`, cannot currently be parsed. Output for sources without macros is identical to before, so backward compatibility is maintained. `--no-macro` disables the whole layer, and `-P` / `-p` output only the expansion of the source side and pattern side respectively. Note, however, that `-P` does not assemble, so all assembler-side values are expanded as undetermined, and the result does not match the expansion during actual assembly.

## 6. Two Kinds of Output — Binary and Text

### 6.1 Text templates

In the current version, an element of binary_list can be a double-quoted string instead of an expression. Inside the string only the parts enclosed in `{{ }}` are evaluated: `{{e}}` (decimal), `{{.hex(e)}}`, `{{.bin(e)}}`, `{{.float(e)}}` (128-bit floating point, 34 significant digits), references to string and array symbols, and `{{.exp(x)}}`, which emits an expression captured by `!L` exactly as it was spelled in the source.

```
MOV R!r,!e:: "LD R{{r}},0x{{.hex(e)}}"
```

This one line rewrites `MOV R1,0x10` into `LD R1,0x10`. The same text is also emitted as binary, one byte per word, and the location counter advances accordingly, so labels after a line that emits text are still placed correctly. With `-V`, the assembled text is streamed as-is to standard output. The pattern file has become, at the same time as a binary generator, a **source-to-source translator**.

### 6.2 Text replacement mode

`.textmode` sets up translator use with a single directive. It turns on `.passthru`, which passes through lines that match no pattern, and `.eol`, which makes one source line into one output line; in addition, it does not treat undefined labels in expressions captured by `!L` as errors, and it carries the source's `;` comments and leading indentation over to the rewritten text. Only the lines to be rewritten need patterns; the rest flows through verbatim.

The bundled `8080toz80.axx` translates Intel 8080 source into Zilog Z80 notation, and `intel2att.axx` translates x86-64 Intel syntax into AT&T syntax. The latter combines spelling maps built from sets and `!Y` with pattern generation in the macro layer; its 60 lines expand into 3,437 patterns. The translated output passes through GNU as. `a64tox64_axx.axx` translates AArch64 assembly into the notation of axx's own `x86_64.axx`, handling the register mapping, the calling-convention glue and the remapping of system calls together with a small runtime. A Brainfuck interpreter written for AArch64 is translated and turned into an x86_64 executable with axx alone, and it runs `mandelbrot.bf` correctly.

### 6.3 Significance

What this extension shows is that the right-hand side of the reduction thesis, `binary_list`, is not limited to "machine code". The structure — match the syntax of an instruction and assemble another representation from the captured values — is the same whether the output is a byte sequence or text. axx achieves this extension without changing either the declarativeness or the Turing incompleteness of the pattern layer. As Section 12 explains, it is also a partial realization, on the current core, of the direction the author sketched in the axx2 concept: "add string literals and string operations to binary_list, enabling translation between assembly languages".

## 7. The Generalization of ELF

### 7.1 Principle: the code that writes ELF does not know the machine

At the time of the previous edition, ELF64 relocatable object output via `-o` worked mainly for x86-64. In the current version this has been generalized to any CPU. The key to the design is splitting the knowledge needed to build an ELF into two parts and placing each where it belongs.

- **Machine-dependent knowledge** — relocation types, ELF class, RELA/REL, ELF header fields, section header attributes, the shape of fields within instruction words, paired and accompanying relocations, the layout of `r_info`, the unit of addends, section groups, and CIE fields for CFI. These are declared in the **pattern file**.
- **Program-dependent knowledge** — symbol type, size, binding, visibility, common symbols, and per-function CFI (`.cfi_*`). These are declared in the **source file**.

The code that writes ELF contains no processing that branches on the machine number. axx has built-in tables for eleven machines — i386, M68K, PowerPC, PowerPC64, s390x, ARM, SuperH, SPARCV9, x86-64, AArch64 and RISC-V — but these are merely declarations written in advance, and with `.elfbuiltin::0` an ELF can be built from declarations alone without using the tables. `--elfdesc` writes out the effective description, combining built-in tables and declarations, in the form of pattern-file declarations. The implementation itself thus provides a way to confirm that tables and declarations have the same expressive power.

### 7.2 The vocabulary of declarations

The declarations are designed as a small vocabulary corresponding one-to-one with the individual elements of ELF.

| Declaration | Describes |
|---|---|
| `.elftype` | name, number and field width of a relocation type, and whether it is PC-relative |
| `.elfclass` / `.elfrela` / `.elfheader` | ELF32/64, RELA/REL, ELF header fields |
| `.elfsection` / `.elflink` / `.elfgroup` | section type, flags, alignment and entry size; `sh_link`/`sh_info`; COMDAT groups |
| `.elffield` | bit fields within instruction words (mask, offset, shift, adjustment) |
| `.elfencode` | function that writes back into a field in REL format (mini language) |
| `.elfextra` / `.elfdiff` | paired and accompanying relocations; sums and differences of labels |
| `.elfrinfo` | construction of `r_info` (mini language) |
| `.elfunit` | unit of addends and symbol values (byte/word) |
| `.elfcfi` / `.elfcfiinit` / `.elfcfireg` | CIE and initial instructions of `.eh_frame`, register names |

With these, the same writing code handles not only RELA machines such as x86-64 and AArch64 but also ARM and MIPS32, which embed addends back into instruction fields under REL; MIPS64 n64, which packs three types into `r_info`; RISC-V, which attaches `R_RISCV_RELAX` for linker relaxation and expresses label differences as `ADD`/`SUB` pairs; and even a hypothetical machine with 16-bit words and word addressing. MSP430 and MN10300, which have no built-in tables, also produce ELF from pattern-file declarations alone. The priority of relocation types is defined as "built-in table < pattern file < source file", and type names can also be specified from the source side via `.reloc` / `.extern` / `.global`.

ELF32 or ELF64 can be chosen with `-f` independently of `-m`, and `-g` adds DWARF (`.debug_info` / `.debug_abbrev` / `.debug_line`). Writing the same `.cfi_*` directives as GNU as in the source builds `.eh_frame`. There is no limit on the number of sections; when it exceeds `SHN_LORESERVE`, axx follows the ELF convention of using `.symtab_shndx`.

### 7.3 Verification

The correctness of the generalization is backed by comparison with external toolchains. For the bundled test fixtures, the outputs for ARM (REL instruction fields), RISC-V (paired relocations, COMDAT, `SHF_LINK_ORDER`, label differences and CFI after linker relaxation), MIPS32 (write-back of `R_MIPS_HI16`, `.text` after linking), MIPS64 (`r_info`) and x86-64 (`.eh_frame`) have been confirmed to match those of llvm-mc / ld.lld. Among the practical pattern files, PowerPC64 ELF objects link with GNU ld using the relocations of the 64-bit PowerPC ABI (`REL24`, `REL14`, the `@l` / `@ha` / `@high` / `@highest` family, `D34` / `PCREL34`), and RISC-V ELF objects link with `ld -m elf64lriscv`.

### 7.4 How failure is handled, and the scope

In the generalization of ELF as well, axx keeps to its policy of **never silently producing something broken**. It emits no relocation for references whose type cannot be determined or for label differences of undeclared width (reporting them with `-d`), warns once when a type name in a declaration cannot be resolved, and treats a missing write-back function or a mismatched argument count as an error. Type numbers that do not fit the default ELF32 `r_info` produce a warning. This is the same attitude as the relaxation of Section 5.3, which writes no output when it fails to converge, and shows the consistency of design across axx as a whole.

The output is limited to relocatable objects (`ET_REL`). Generating executables (`ET_EXEC`) or shared libraries (`ET_DYN`) — resolving relocations by per-type formulas and building program headers and dynamic-linking tables — is the linker's job and is deliberately placed outside the scope. When an image with fixed addresses is needed, it can be obtained as a raw binary with `-b`. It is a generalization that correctly confines the assembler's responsibility to the assembler's domain.

## 8. Demonstrated Extensibility

Evidence that the minimal core has been correctly carved out is that later extensions sit on it without changing the core. In addition to Sections 6 and 7, axx demonstrates this with the following.

**VLIW/EPIC support.** Declaring the bundle bit count, instruction bit count, template bit count and NOP code, as in `.vliw::128::41::5::00`, and adding only a few symbols — `!!` (instruction concatenation), `!!!` (number of concatenated instructions) and `!!!!` (stop bit) — handles VLIW processors including Itanium-style EPIC. EPIC patterns take an index code as a fourth field, and the template is determined by the combination of indices. Template bits are placed at the right end if the count is positive and at the left end if negative. The part excluded from the reduction thesis in Section 2 ("except EPIC/VLIW") is recovered by extension.

**Non-8-bit word widths.** A declaration such as `.bits::12` handles bit-slice processors and processors whose machine words are not byte-sized (4, 11, 12 bits and so on, from 1 to 64 bits), endianness included. When `.bits` is set, addresses are in words, and in ELF output `.elfunit::word` makes addends and symbol values word-based as well.

**Floating-point immediates.** `!F` (32-bit), `!D` (64-bit) and `!Q` (128-bit) evaluate a floating-point expression to an integer bit pattern. An instruction such as ARM64's `vmov.f32 s0,#3.14` can be written as a one-line pattern.

**Optional parts.** A part of the instruction enclosed in `[[ ]]` is optional; when omitted, the variable's initial value 0 is used. This is how Z80 `inc (ix)` and `inc (ix+d)` can be written in one line.

**Describing diagnostics.** `.error::n::"text"` gives text to an error code, and `.echo` written on a body line provides debug output for pattern files. Diagnostics, too, are declared on the pattern-file side.

**Original operators.** Operators specialized for binary generation are integrated into the expression language: the prefix operator `@`, which returns the position of the most significant set bit (the Hebimarumatta operator); the binary operator `'`, which sign-extends from an arbitrary bit position (the SEX operator); symbol-value reference `#`; and `*(x,y)`, which takes the y-th byte from the bottom. Integers in expressions and in the mini language wrap around at 256 bits. These make it possible to fit the encoding of addressing modes into a one-line expression (for example, computing the bit position of the scale value in x86_64 LEAQ: `((@h)-1)<<6|t<<3|s`).

## 9. Implementation, Verification and Practicality

### 9.1 Two implementations

axx has a Python implementation (axx.py, nicknamed Paxx, the reference implementation) and a C implementation (caxx.c, nicknamed Caxx), and runs on FreeBSD and Linux. At the time of writing they are about 15,000 and about 20,000 lines respectively. New features land in Paxx first, and Caxx is far faster (assembling hello world against the roughly 24,000 x86_64 patterns finishes in well under a second). The two implementations are maintained with the goal of producing byte-for-byte identical output for the same input.

### 9.2 Cross-checking the two implementations

The bundled `test1` assembles 50 pattern/source pairs with both implementations and compares the raw `-b` binaries with `cmp`. For pairs using `.textmode` it also compares the `-V` text; for the `.echo` pair, the standard-error output; for pairs that verify ELF declarations, the `-o` objects; and for `aarch64.axx` and others, the `--elfdesc` output. The sixteen core pairs are additionally run with `-o` (ELF64), `-m 3 -f 32 -o` (ELF32), `-g -o` (with DWARF), `-v` (listing) and `-V` (text output), for 182 comparisons in all. That two independent implementations continue to agree — from raw binaries through object files, debug information and translated text — is strong evidence that the specification is defined independently of either implementation.

### 9.3 Practical pattern files

The pattern files bundled for practical use now range from legacy CPUs to today's major ISAs.

| ISA | Coverage |
|---|---|
| x86_64 | x86_64-v3: segment addressing, AVX/AVX2, BMI1/BMI2, x87, EVEX/AVX-512 |
| AArch64 | A64 in general, Advanced SIMD, cryptography, scalar extensions, SVE/SVE2, SME/SME2; GNU-style relocation modifiers |
| PowerPC64 | Power ISA v3.1 (POWER10), big/little endian; VMX, VSX, quad precision, MMA, prefixed instructions (with a nop inserted before one that would cross a 64-byte boundary) |
| RISC-V | the whole of RV64: I/M/A/F/D/Q/Zfh/C and derivatives, bit manipulation, scalar crypto, CSRs, privileged and H extension, V 1.0 and its vector crypto, GNU pseudo-instructions |
| MIPS | MIPS I through MIPS64 Release 6, big/little endian, o32 and n64; integer, privileged, FPU (paired single, COP1X), COP2, the extensions (DSP, MSA, MT, VZ, EVA, MIPS-3D, SmartMIPS, MCU, XPA, CRC, GINV), the new instructions of Release 6, GNU pseudo-instructions, relocation modifiers such as `%hi` / `%lo` / `%got` / `%pcrel` |
| Legacy | Motorola 68000 / 6809 / 6800, MOS 6502, Zilog Z80, Intel 8080 / 8051 / 8048 / 4004 |

PowerPC64 and the MIPS base set have been checked byte-for-byte against GNU as, and the MIPS extensions and Release 6 and RISC-V against llvm-mc. Demonstrations are also available, such as a Brainfuck virtual CPU and Brainfuck interpreters assembled with axx (AArch64, PowerPC64 and RISC-V versions; the x86_64 version lives in a separate repository).

### 9.4 Connecting to toolchains

The toolchain connections are in place: external symbol linkage via `.global` / `.extern`; ELF symbol attributes on the source side (`.type`, `.size`, `.weak`, `.hidden`, `.protected`, `.comm` and so on); export/import of label and section information in TSV format (`-e` / `-E` / `-i`); and source-level debugging in gdb/lldb through DWARF. Generated objects link with GNU ld and LLVM ld.lld, and have reached the point of calling C library functions and building shared objects.

The execution platform is not tied to any particular system. DOS-style `chr(13)` line endings are ignored, and Paxx runs wherever Python runs.

That the abstract idea of a "general assembler" now has concrete outlets connecting to real toolchains, including major ISAs, is important in demonstrating that the idea is real.

## 10. Position in the Lineage

The idea of a table-driven assembler or meta-assembler itself has precedents in computing history. The meta-assemblers of the 1960s, and in modern times LLVM's TableGen instruction descriptions, CGEN (which generates parts of GNU binutils), and customasm (written in Rust), belong to a related lineage. Within this lineage, the originality of axx lies in the following points.

First, the granularity and freedom of description. Whereas TableGen is tightly coupled to C++ backends and practical targets carry thousands of lines of hand-written C++, axx pattern files are free-syntax text fully separated from the implementation and can be written to look almost isomorphic to the instruction tables in a specification. Whereas CGEN describes the *semantics* of instructions in an RTL-like form, axx describes the correspondence between surface syntax and encoding. A tokenizer-less free-syntax DSL has no precedent.

Second, the explicit adoption of Turing incompleteness. Many existing meta-assemblers moved toward general computational power as extensions of their macro facilities; axx went the opposite way, toward minimality and guaranteed termination, and carved out the parts needing computational power as separate layers.

Third, order-independent pattern matching. The specificity score removes the need for the "careful ordering of definitions" implicitly required by table-driven approaches. Declaring `.unordered` makes the directives order-independent too.

Fourth, the generalization of object output. customasm shares the idea of describing an ISA declaratively, but its output stops at binaries and dump formats, with no relocatable objects. LLVM MC is a production-grade infrastructure handling ELF, COFF and Mach-O, but per-machine object output is implemented as code. axx generates linkable ELF from declarations rather than per-machine code. That a declarative pattern description and a declarative ELF description live together in the same file is unique to axx within this lineage.

As the author himself states, the aim of axx is not its spread as a tool per se but the presentation of an academic insight: that all imperative assembly languages can be pressed into a single pattern form. axx is positioned one layer below ordinary assemblers, as a tool of the meta layer that defines assemblers. The bundled `axxsemantics` formalizes this structure from the standpoint of denotational semantics as a meaning function Assembly Source → Pattern Matching → Environment → Binary → Object, an attempt to describe axx as a meta layer theoretically.

## 11. Significance in the Age of AI

Writing pattern files for huge ISAs is laborious for humans, but converting a specification into a pattern file is a transcription task of fixed form, well suited to AI. Once written, a pattern file is a finished product for that ISA and can be reused. That in the current version enormous instruction sets such as AArch64 SVE/SME2, Power ISA v3.1 and the whole of RISC-V were turned into pattern files in a short time and checked byte-for-byte against external assemblers shows that this prospect has become reality.

If assemblers were originally born "to make machine code understandable to humans", then in an age when AI writes code, the significance of a generalized-assembler layer serving both humans and computers as an intermediate representation is growing. The separation of pattern files and source files makes it possible in principle to generate machine code for different processors from common source, and combined with the source-to-source translation of Section 6, it opens the possibility of application as a simple retargetable infrastructure linking assembly languages with one another.

## 12. Future Work — The axx2 Concept and What the Current Version Has Reached

The author has published a concept for a next-generation axx2. It would move the description language of pattern files from a pattern-data format to a more descriptive multi-line meta-language, renaming binary_list to object_list and the pattern file to processor_specification_file. Introducing string literals, string operations and control statements would bring the generation of intermediate languages and of translators between assembly languages into view. The pattern file would then be Turing complete and could in principle handle even Lisp machines, but self-reference checks would become necessary, and infinite loops inside the implementation would make debugging difficult. The author's view is that confining evaluation to the pattern file would allow loops and branches while preserving debuggability.

The current version has realized two parts of this concept ahead of time, without rebuilding the whole description language.

One is the part "introduce loops and branches into the pattern file and confine evaluation within it", realized as the mini language (Section 4). It keeps the existing pattern notation declarative and calls by name only where computation is needed, and it answers the concern about debugging infinite loops by stopping as soon as a resource limit is exceeded and naming the offending line.

The other is the part "add string literals and string operations to binary_list, enabling translation between assembly languages", realized as text templates and `.textmode` (Section 6). Though binary_list keeps its name, it already has the character of an object_list, in the sense that its output may be either bytes or text.

Regarding the remaining tasks, the author notes that the pattern-data format is more intuitive and that a descriptive meta-language would require a major rewrite. He also considers that high-performance macros translating structured and functional assembly into imperative assembly, optimization features, and pattern files for ARM (A32/T32), SPARC, 32-bit PowerPC and RV32 — including validation on real hardware or emulators — are too large for one person to complete, and welcomes collaborators. These are constraints of labour, not of design, and the pattern-file format is fully documented.

## 13. Conclusion

The invention of axx comes down to three points: a single reduction thesis (`instruction :: error_patterns :: binary_list`), a free-syntax pattern language for writing it, and the design decision to separate computational power from the declarative core. The macro layer and mini language added in the current version do not withdraw the third point; they make it concrete. Computation is isolated in a preceding source transformation and in a separate language that appears only when called by name, and the pattern layer remains declarative data, continuing to guarantee termination of matching as a property of the language.

The two milestones reached since the previous edition have greatly widened the reach of this design. The generalization of ELF pushes the principle that "the engine does not know the machine" from instruction encoding all the way to object file generation, making it possible to produce linkable ELF from declarations rather than per-machine code. Text output shows that the right-hand side of the reduction thesis is not limited to machine code, and turns the pattern file into a translator between assembly languages. Both sit on the core without changing its declarativeness or Turing incompleteness, and both share the attitude of "never silently producing wrong output".

The 1986 idea was validated by the 2024 implementation; extensions — VLIW/EPIC, arbitrary word widths, ELF32/64 object output and its machine independence, DWARF and CFI, the macro layer, the mini language and source-to-source translation — have accumulated without changing the design of the core; and today's major ISAs, x86_64, AArch64, PowerPC64, RISC-V and MIPS, obtain output on top of it that matches external toolchains. All this demonstrates that the extracted "essence" was correct. The idea of handling everything from homemade processors to supercomputers with a single matching engine has redefined the assembler — from a per-ISA implementation artifact into a meta-language processor for describing ISAs.

## References

- GitHub repository: https://github.com/fygar256/axx
- Technical manual: `Technical_Manual.md` / `Technical_Manual_ja.md`
- Generalization of ELF: `elf_generalization_en.md` / `elf_generalization.md`
- Macro layer reference: `macro_en.md` / `MACRO.md`
- Mini language reference: `mini_en.md` / `MINI.md`
- Formalization in denotational semantics: `axxsemantics`
- x86_64 pattern file: https://github.com/fygar256/x86_64_pattern_file_for_axx
- Relocatable ELF generation: https://github.com/fygar256/axx_relocatable_elf_generation
- Demonstration of a brainfuck interpreter assembled with axx: https://github.com/fygar256/brainfuck_interpreter_for_axx_on_freebsd_of_x86_64
- Original article in Japanese (Qiita: fygar256): https://qiita.com/fygar256/items/1d06fb757ac422796e31
