# axx: Generalizing Imperative Assembly Language — Design and Implementation of a General Assembler Based on a Free-Syntax Pattern Language and a Two-Layer Architecture

**An introductory paper on axx.py / caxx.c by Taisuke Maekawa (fygar256)**

## Abstract

axx (Arbitrary eXtended X assembler) departs from the conventional practice of implementing a dedicated assembler for each processor. It is built on a single insight: every imperative assembly language can be reduced to one pattern form, `instruction :: error_patterns :: binary_list`. This paper presents the central invention of axx — its free-syntax pattern language — together with three design decisions that follow from it: tokenizer-less character-level matching, order-independent pattern matching driven by a specificity score, and deliberate Turing incompleteness. It further positions the macro layer added in the current version as a two-layer architecture that cleanly separates a *computing* source-to-source transformation stage from a *declarative* pattern layer, and argues that this separation is the means by which axx gains practical expressive power without retracting its original commitment to Turing incompleteness. Finally, it shows that extensions such as VLIW/EPIC support, non-8-bit word widths, and ELF64 relocatable object output sit naturally on top of the minimal core; it places axx within the historical lineage of meta-assemblers; and it discusses its significance in an era in which AI can generate pattern files.

## 1. Introduction

Assemblers have conventionally been implemented in one-to-one correspondence with a particular instruction set architecture (ISA). Even in a multi-target assembler such as GNU as, each target exists as a backend hard-coded into the program, and supporting a new processor means modifying the assembler itself.

axx inverts this arrangement. The assembler proper is a minimal matching engine that holds no knowledge of any ISA; all processor-specific knowledge resides in external declarative data — the pattern file, or processor description file. A user obtains an assembler for a given processor simply by transcribing that processor's specification into a pattern file. The targets of axx are not limited to virtual CPUs: they include "abstracted real CPUs," and converting the specification of an actual processor into a pattern file makes it directly assemblable.

The idea originated in 1986, while the author was working part-time at Tokyo Denshi Sekkei during his university years; the name AXX and a prototype in C already existed at that point. Working code was published in 2024, after the original program listing was rediscovered 38 years later and rewritten in Python. What matters here is that those 38 years were not a mere gap: they served as a validation period, during which the idea remained applicable across the diversification of hardware — VLIW, EPIC, and processors with non-8-bit word widths.

## 2. The Central Invention: Reduction to a Single Pattern Form

The most essential claim of axx is that every imperative assembly language — with the exception of EPIC/VLIW, whose machine code carries meta-level complexity — reduces to the structure

```
instruction :: error_patterns :: binary_list
```

Omitting error checking simplifies this further to `instruction :: binary_list`. This is a minimization of the definition "an assembler is a grammar for instructions plus binary generation based on it." It amounts to extracting what is common to imperative ISAs of the von Neumann architecture, metamodeling the ISA, and formalizing it through pattern matching.

An `instruction` is defined as a combination of five elements: string literals, symbols replaceable by integer values, integer expressions, integer factors, and floating-point expressions. The reduction claim states that these five elements alone suffice to process any imperative assembly language; any processor whose instructions map one-to-one onto machine code can be handled.

For example, the x86_64 RET instruction is complete in a single line:

```
RET :: 0xc3
```

Instructions with operands also fit on one line, using variables and expressions. In the 8048 example,

```
ADD A,R!n :: n>7;5 :: n|0x68
```

`add a,r1` generates 0x69, and a register number out of range returns error code 5 (Register out of range). Instruction syntax, validity checking, and code generation are declared as a single line of correspondence. This granularity — one line per instruction pattern — is what guarantees transcribability from a specification document.

In practice, `binary_list` also carries complex expression evaluation, alignment, and the `;` prefix modifier that suppresses output when the value is 0; but these are unnecessary in the minimal model. The core remains the one line above.

## 3. Design as a Free-Syntax Pattern Language

### 3.1 A grammar without a grammar

Although the pattern language of axx (the `instruction` part) is a DSL, it has no fixed grammar. It is a free-syntax language in which users construct their own grammar by combining string literals, symbols, integer expressions, integer factors, and floating-point expressions. Consequently it is not bound to the traditional `mnemonic operand` form: an ISA with assignment-style notation such as `r1 = r2 + r3`, and ARM64 SIMD notation such as `{v0.4s}`, can both be described within the same framework. Because of this property, axx functions as a general-purpose binary generator as well as an assembler.

The name reflects the design intent. axx is not a *general-purpose* assembler in the sense of "widely usable," but a *general* assembler in the sense of "common to everything."

### 3.2 Tokenizer-less character-level matching

axx has no lexical analyzer; it matches patterns character by character. This is a deliberate design decision rather than an implementation shortcut. To handle syntax in which mnemonics contain symbol sequences — and real ISAs contain many register names and mnemonics with `.`, `$`, or `%` — it is advantageous not to fix the notion of a token in advance.

The convention is simple. Uppercase letters, digits, and symbols in the pattern file are treated as character constants (uppercase matches both cases on the assembly line), while lowercase letters are single-character variables to which the value of the symbol at that position is assigned. Prefixing `!` assigns the value of an integer expression, `!!` an integer factor, and `!F` / `!D` / `!Q` the value of a 32/64/128-bit floating-point expression. All unassigned variables are initialized to 0. With only this minimal convention in place, the decision of where lexis ends and syntax begins is left to the pattern author.

### 3.3 The character set itself is configurable

A consequence of the tokenizer-less design is that even the question "which characters constitute an identifier?" is declared from the pattern file. `.symbolc` specifies the character set used for symbols and `.labelc` that used for labels (the defaults are alphanumerics plus `_%$-~&|`, and alphanumerics plus underscore and period, respectively). This mechanism is why MIPS register notation such as `$s5` and `$v0` can be written as ordinary symbols without special-casing. That even the lexical rules are not fixed in the processing system is a consistent extension of the free-syntax design.

### 3.4 Order-independent matching via a specificity score

In a pattern file, directives such as `.setsym` are order-dependent, but the patterns themselves are not. This is achieved by automatic ordering based on the specificity score tuple `(n_expr, -n_lit, n_sym)`, which frees pattern authors from the implicit burden of conventional table-driven assemblers — that of writing more specific patterns first. The pattern evaluation ordering problem has been solved by extending this specificity-score-based automatic ordering to general pattern matching.

### 3.5 Symbols and pre-checking

Symbols are defined with `.setsym::name::value`. Redefinition of the same name takes the later definition, and this is used to express naturally, through ordering within the pattern file, situations in which the same character carries different values in different contexts (such as the Z80 register `C` and the condition flag `C`).

Additionally, `.check::x::r1,r2,r3` restricts, by enumeration, which symbols may appear at the position of variable x. This is a mechanism equivalent to type checking of register classes, and it makes it possible to write unambiguously separate patterns for register groups that serve the same role at different widths, such as `AL`/`BL` versus `AX`/`BX`:

```
.check::s::AL,BL
.check::t::AX,BX
MOV s,!a  :: 0xb0|s,a
MOV t,!a  :: 0xb8|t,a,a>>8
```

Resolving hard-to-structure parts of an ISA by enumeration is a consistent policy throughout axx.

## 4. Deliberate Turing Incompleteness

The pattern file of axx is Turing incomplete. The control constructs available in `binary_list` are limited to five: assignment (`:=`), the ternary operator, the `;` prefix modifier (no output when the value is 0), alignment, and `@@[]` (repetition).

This is a design choice, not a deficiency in capability. If the DSL were Turing complete it would become a *program*, and the guarantee that pattern matching terminates would be lost. Processor architectures can be made arbitrarily complex if one chooses; a Turing-complete description language could follow them anywhere, but at the cost of turning the pattern file from declarative data into code. axx chose "being declarative data" and "guaranteed termination," and it explicitly states which ISAs fall outside its scope as a consequence:

| Processor | Reason it is out of scope |
|---|---|
| Mill CPU | Belt architecture |
| ZISC | No instructions |
| Thinking Machines | Massively parallel |

Documenting the boundary of applicability as part of the specification stands as an honest contrast to tool designs that tend to advertise universality.

## 5. The Two-Layer Architecture — A Computing Macro Layer and a Declarative Pattern Layer

The current version of axx incorporates a macro layer. It is a source-to-source transformation stage that runs before the source is handed to the assembler proper, and it is implemented with identical specifications in both `axx.py` and `caxx.c`. What this paper regards as significant, in relation to the design decision of Section 4, is that this layer is added **as a separate layer, independent of the pattern layer**.

### 5.1 Syntax

Every statement begins with `!` at the start of a line.

| Syntax | Meaning |
|---|---|
| `!def name(p1, p2, p3 = default) { ... }` | Macro / compile-time function definition |
| `!return expr` | Return value; also an early exit from the body |
| `!if expr !then { ... } !elif ... !else { ... }` | Conditional branching |
| `!while expr { ... }` | Loop |
| `!break` / `!continue` | Loop control |
| `!set` / `!local` / `!undef` | Assign, declare, delete a variable |
| `!include "file"` | Text inclusion at macro-expansion time |
| `!error` / `!warning` / `!echo` | Abort expansion / diagnostic output |

Embedding into text is done with `!{expr}`, or `!{expr:04x}` with Python-style formatting. Values are limited to integers and strings, and operators follow C (with `/` and `%` truncating toward zero). Built-in functions include `len`, `hex`, `str`, `int`, `upper`, `lower`, `substr`, `abs`, `min`, `max`, `uid`, and `defined`; within a macro, `__id__` (unique per invocation, for generating local labels) and `__name__` are implicitly defined.

### 5.2 A different approach to termination

Because the macro layer has `!while` and recursion, it is syntactically capable of general computation. However, limits are imposed on execution resources: exceeding 200 levels of recursion, 1,000,000 `!while` iterations, 2,000,000 generated lines, or 64 levels of `!include` nesting raises an error and aborts the remainder of the expansion. Termination is thus secured not by *removing expressive power from the language* but by *bounding its resources*.

Here lies the point of the two-layer architecture. The pattern layer remains declarative data and guarantees termination as a property of the language specification, while the portion that requires computational power is isolated into a separate source-to-source layer protected by resource limits. The choice of Turing incompleteness described in Section 4 has not been retracted by the addition of the macro layer; it has been preserved with its scope of influence separated. This reading is the assessment of the present paper, though the fact that the two layers adopt different means of guaranteeing termination is stated explicitly in the documentation.

### 5.3 Idempotent expansion through restricted references

The macro layer cannot reference label values, `.equ` definitions, or `$` / `$$`. This is a restriction and at the same time a requirement for guaranteeing that expansion results remain consistent across relaxation passes (the iterative passes used for instruction-length optimization). Label values may vary from pass to pass; permitting expansion that depends on them would generate a different source on each pass, and convergence would no longer be guaranteed. The restriction confines the macro layer to pure text transformation prior to address resolution, and it is the precondition for placing computational power in an upper layer.

### 5.4 Semantics across the two implementations

`axx.py` and `caxx.c` share identical specifications for the macro layer; the only difference is numeric representation. The Python version uses arbitrary-precision integers and the C version uses `int64`, so results differ only when a macro-time computation exceeds 64 bits. Since the macro layer emits source text, this difference does not propagate into the 256-bit expression evaluation of the assembler proper. Making the location and reach of the divergence explicit is practically important for maintaining a two-implementation arrangement.

### 5.5 Current limitations

Assembler-level `.include` directives bypass the macro layer, so `!include` must be used to import macro definition files. Interactive mode (when no source file is specified) also bypasses the macro layer. Notations that combine a ternary operator with a format specifier, such as `!{a ? b : c:04x}`, cannot currently be parsed. Output for sources containing no macros is identical to previous behavior, so backward compatibility is preserved. `--no-macro` disables the layer entirely, and `-P` emits only the expanded result.

## 6. Demonstrated Extensibility

Evidence that a minimal core has been carved out correctly is that later extensions can be added without changing the core. In axx, the following demonstrate this.

**VLIW/EPIC support.** A declaration such as `.vliw::128::41::5::00` specifies bundle bit count, instruction bit count, template bit count, and NOP code; with only a few added notations — `!!` (instruction concatenation), `!!!` (number of concatenated instructions), and `!!!!` (stop bit) — VLIW processors including Itanium-style EPIC are handled. A positive template bit count places the template at the right end and a negative one at the left end, with the bit count taken as the absolute value. The exclusion clause of the reduction claim in Section 2 ("except EPIC/VLIW") is thereby recovered through extension.

**Non-8-bit word widths.** A declaration such as `.bits::12` handles bit-slice processors and processors whose machine-code words are not byte-sized (4-bit, 11-bit, 12-bit, and so on), including endianness specification. Output is emitted in 8-bit units, with surplus bits masked to 0. When `.bits` is specified, addresses are counted in words.

**Floating-point immediates.** `!F` (32-bit), `!D` (64-bit), and `!Q` (128-bit) evaluate floating-point expressions as integer bit patterns. An instruction such as ARM64's `vmov.f32 s0,#3.14` can be described by a single-line pattern.

**Optional parts.** Portions of an `instruction` enclosed in `[[ ]]` become optional, and the variable's initial value of 0 is used when they are omitted. This mechanism is why the Z80's `inc (ix)` and `inc (ix+d)` fit on one line.

**Custom operators.** The expression language integrates operators specialized for binary generation: the prefix `@` returning the position of the most significant bit of a value (the Hebimarumatta operator), the binary `'` performing sign extension from an arbitrary bit position (the SEX operator), `#` for symbol value reference, and `*(x,y)` taking the n-th byte from the least significant end. These make it possible to fit addressing-mode encoding into a single-line expression — for example, the scale-value bit position computation `((@h)-1)<<6|t<<3|s` in the x86_64 LEAQ instruction.

## 7. Implementation and Practicality

axx has a Python implementation (axx.py, nicknamed Paxx) and a C implementation (caxx.c, nicknamed Caxx), and runs on FreeBSD and Linux. The C version is faster, while feature additions land first in the Python version.

Beyond a research core, the following have been achieved on the practical side. ELF64 relocatable object output (`-o`) works primarily for x86-64, and `-m` specifies the e_machine value for header generation targeting AArch64, RISC-V, i386, PPC, ARM, and others. External symbol linkage via `.global` / `.extern`, export/import of label and section information in TSV format (`-e` / `-E` / `-i`), and generation of DWARF debug information (.debug_info / .debug_abbrev / .debug_line) via the `-g` option together enable source-level debugging in gdb/lldb. The generated objects have been verified to link with both GNU ld and LLVM's ld.lld, and the work has reached the point of calling C library functions and creating shared objects.

The execution platform is likewise system-independent. A trailing `chr(13)` in DOS-format files is ignored, and it should run on any system where Python runs.

That an abstract conception — the "general assembler" — has acquired a concrete outlet connecting it to an actual toolchain is important as evidence of the conception's reality.

## 8. Position in the Lineage

The idea of a table-driven assembler, or of a meta-assembler, has precedents in computing history: the meta-assemblers of the 1960s, and in the present day LLVM's instruction descriptions via TableGen belong to a related lineage. Within that lineage, the distinctiveness of axx lies in the following three points.

First, the granularity and freedom of description. Whereas TableGen is a description language tightly coupled to a C++ backend, the pattern file of axx is free-syntax text completely separated from the processing system, and can be written to look almost isomorphic to the instruction table in a specification document. Second, the explicit adoption of Turing incompleteness. Many existing meta-assemblers moved toward general computational power as an extension of their macro facilities; axx moved in the opposite direction, toward minimality and a termination guarantee, and split the part requiring computational power into a separate layer. Third, order-independent pattern matching. The "care about definition order" implicitly demanded by table-driven approaches is made unnecessary by the specificity score.

As the author himself states, the purpose of axx is not adoption as a tool but the presentation of an academic insight: that every imperative assembly language can be compressed into a single pattern form. axx is positioned one layer below an ordinary assembler — as a tool of the meta-layer that defines assemblers.

## 9. Significance in the Age of AI

Creating pattern files for large ISAs is laborious for humans, but the conversion from specification document to pattern file is transcription work in a fixed format, and therefore well suited to AI. Once created, a pattern file is a finished artifact for that ISA and can be reused. If assemblers were originally born to make machine code easier for humans to understand, then in an era where AI writes code, an intermediate representation layer in the form of a generalized assembler addressed to both humans and machines gains in significance. Because pattern files and source files are separated, generating machine code for different processors from a common source is possible in principle, which suggests applicability as a simple retargetable code-generation substrate.

## 10. Future Work — The axx2 Concept

The author has published a concept for a next-generation version, axx2. It would migrate the description language for pattern files from a pattern-data form to a more descriptive, multi-line metalanguage, renaming `binary_list` to `object_list` and the pattern file to the processor specification file. Introducing string literals, string operations, and control statements would bring intermediate-language generation and assembly-language-to-assembly-language converters into view. In that case the pattern file side would become Turing complete and even Lisp machines would in principle be tractable, but self-reference checking would become necessary, and infinite loops inside the processing system would make debugging difficult. The author's view is that confining evaluation to within the pattern file preserves debuggability while allowing loop and branch structures.

As for the current version, the pattern-data form is noted as more intuitive, and converting to a descriptive metalanguage would require drastic rewriting. Now that the core is complete, expanding the set of pattern files and adding high-performance macros that translate structured and functional assembly into imperative assembly, together with optimization features, would complete the system — though the author's present assessment is that a project of that size is large for one person to finish.

## 11. Conclusion

The invention of axx converges on three points: a single reduction claim (`instruction :: error_patterns :: binary_list`), a free-syntax pattern language for expressing it, and a deliberate Turing incompleteness that guarantees termination. The macro layer added in the current version does not retract the third point; by isolating computational power into a separate source-transformation layer, it is a solution that extends expressive power while preserving the character of the declarative pattern layer.

That an idea from 1986 was validated by an implementation in 2024, and that extensions — VLIW/EPIC, arbitrary word widths, ELF64 object output, DWARF debug information, and the macro layer — accumulated without altering the design of the core, is a demonstration that the extracted "essence" was correct. The conception of handling everything from homemade processors to supercomputers with a single matching engine redefines the assembler: from an artifact implemented per ISA into a metalanguage processor for describing ISAs.

## References

- GitHub repository: https://github.com/fygar256/axx
- Pattern files for x86_64 / z80 / 8048: https://github.com/fygar256/x86_64_pattern_file_for_axx
- Relocatable ELF generation: https://github.com/fygar256/axx_relocatable_elf_generation
- Demonstration of a brainfuck interpreter assembled with axx: https://github.com/fygar256/brainfuck_interpreter_for_axx_on_freebsd_of_x86_64
- Original article in Japanese (Qiita: fygar256): https://qiita.com/fygar256/items/1d06fb757ac422796e31
