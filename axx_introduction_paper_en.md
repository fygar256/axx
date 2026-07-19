# axx: Generalizing Imperative Assembly Languages ​​— Design and Implementation of a Universal Assembler Using a Free-Syntax Pattern Language

**An introductory paper on axx.py by Taisuke Maekawa (fygar256)**

## Abstract

axx (Arbitrary eXtended X assembler) is a universal assembler that breaks away from the traditional paradigm of implementing dedicated assemblers for individual processors. It is built upon the insight that all imperative assembly languages ​​can be reduced to a single pattern format: `instruction :: error_patterns :: binary_list`. This paper introduces the core innovations of axx—a free-syntax pattern language, character-by-character matching without a tokenizer, order-independent pattern matching based on specificity scores, and intentional Turing incompleteness—and demonstrates how extensions such as VLIW/EPIC support and ELF64 relocatable object output are seamlessly realized atop this minimal core. Additionally, the paper discusses the positioning of axx within the historical lineage of meta-assemblers and its significance in an era where AI generates pattern files.

## 1. Introduction

Assemblers have traditionally been implemented with a one-to-one correspondence to specific Instruction Set Architectures (ISAs). Even in multi-target assemblers like GNU as, each target exists as a hard-coded backend within the code; supporting a new processor requires modifying the assembler itself.

axx reverses this paradigm. The assembler core is a minimal matching engine possessing no knowledge of any specific ISA; all knowledge regarding individual processors resides in external declarative data—specifically, pattern files (processor description files). Users can obtain an assembler for a given processor simply by transcribing that processor's specifications into a pattern file.

The concept originated in 1986 while the author was working part-time at Tokyo Denshi Sekkei during his university years; the name "AXX" and a prototype written in C already existed at that time. The release of the working code in 2024 was made possible by the rediscovery of the original program listing—after 38 years—and its subsequent rewrite in Python. What is significant here is that those 38 years were not merely a void; they served as a validation period, demonstrating that the underlying concept remained valid even as hardware diversified (spanning VLIW, EPIC, and non-8-bit word-width processors).

## 2. Core Invention: Reduction to a Single-Pattern Format

The fundamental premise of axx is that all imperative assembly languages—with the exception of EPIC/VLIW architectures, which introduce meta-level complexity—can be reduced to the following structure:

```
instruction :: error_patterns :: binary_list
```

If error checking is omitted, this simplifies further to `instruction :: binary_list`. This represents a minimization of the definition of an assembler—viewing it simply as a set of grammatical rules for instructions and the generation of binary code based on them. It equates to extracting the essence common to imperative ISAs of the von Neumann architecture, creating an ISA meta-model, and formalizing the process through pattern matching.

For example, the x86_64 `RET` instruction is fully defined in a single line:

```
RET :: 0xc3
```

Instructions requiring operands can also be expressed in a single line using a combination of variables and expressions. In the case of the 8048, writing:

```
ADD A,R!n :: n>7;5 :: n|0x68
```

results in `add a,r1` generating `0x69`, while an error code of `5` is returned if the register number exceeds the valid range. Instruction syntax, validity checking, and code generation are all declared as a single-line correspondence. This granularity—"one line equals one instruction pattern"—ensures that specifications can be directly transcribed into the system.

## 3. Design as a Free-Syntax Pattern Language

### 3.1 A Grammar Without Grammar

Although the axx pattern language (specifically the `instruction` component) functions as a DSL, it does not possess a fixed grammar. It is a free-syntax language that allows users to define their own grammar by combining string literals, symbols, integer expressions, integer factors, and floating-point expressions. Consequently, it is not bound by the traditional "mnemonic operand" format; instead, it can describe ISAs using assignment-style notation (e.g., `r1 = r2 + r3`) or ARM64 SIMD notation (e.g., `{v0.4s}`) within the same framework. Due to this characteristic, axx functions not only as an assembler but also as a general-purpose binary generator.

### 3.2 Tokenizer-less, Character-by-Character Matching

axx does not employ a lexical analyzer; instead, it matches patterns character by character. This is a deliberate design choice rather than a sign of immature implementation. Avoiding a fixed token concept beforehand is advantageous when handling syntax where mnemonics include symbol sequences (many real-world ISAs feature register names or mnemonics containing characters like `.`, `$`, or `%`). The system relies on a simple convention—uppercase letters and symbols represent character constants, while lowercase letters represent variables—leaving the definition of boundaries between lexical elements and syntax entirely to the pattern author.

### 3.3 Order-Independent Matching via Specificity Scores

While directives (such as `.setsym`) in the pattern file are order-dependent, the patterns themselves are not. This is achieved through automatic ordering based on a specificity score tuple `(n_expr, -n_lit, n_sym)`, liberating pattern authors from the implicit burden—common in traditional table-driven assemblers—of having to write more specific patterns first. The challenge of determining the pattern evaluation order has been resolved by extending this specificity-score-based automatic ordering to general pattern matching.

## 4. Intentional Turing Incompleteness

axx pattern files are Turing-incomplete. The control constructs available in `binary_list` are limited to five types: assignment (`:=`), the ternary operator, the `;` prefix modifier (which suppresses output if the value is 0), alignment, and `@@[]` (iterative expansion).

This is a design choice, not a lack of capability. Making the language Turing-complete would turn the DSL into a "program," thereby forfeiting the guarantee of termination. While Turing completeness would allow it to support any processor architecture—given that processor architectures can be arbitrarily complex—the trade-off is that pattern files would become code rather than declarative data. axx prioritizes being "declarative data" and "guaranteeing termination"; consequently, it explicitly excludes ISAs such as the Mill CPU (belt architecture), ZISC (which lacks instructions), and massively parallel machines. By codifying the boundaries of its applicability in the specification, axx stands in honest contrast to tool designs that often claim to be "universal."

## 5. Demonstrating Extensibility

Proof that the minimal core has been correctly isolated lies in the ability to add extensions without modifying the core itself. In axx, the following features demonstrate this:

**VLIW/EPIC Support.** Using the `.vliw` directive to declare bundle bits, instruction bits, template bits, and NOP codes—along with the addition of just a few symbols like `!!` (instruction concatenation), `!!!` (number of concatenated instructions), and `!!!!` (stop bit)—axx handles VLIW processors, including Itanium-style EPIC architectures. The exceptions noted in Section 2 regarding EPIC/VLIW are thus addressed through these extensions.

**Non-8-bit Word Widths.** Declarations such as `.bits::12` allow for the handling of bit-slice processors and architectures where machine-language words are not byte-aligned (e.g., 4-bit, 11-bit, or 12-bit words), including endianness specifications.

**Floating-point Immediates.** ** `!F` (32-bit), `!D` (64-bit), and `!Q` (128-bit)** allow floating-point expressions to be evaluated as integer bit patterns. This enables instructions like ARM64's `vmov.f32 s0,#3.14` to be written as a single-line pattern.

**Custom Operators.** A suite of operators specialized for binary generation is integrated into the expression language, including the prefix operator `@` (Hebimarumatta operator) which returns the position of the most significant bit; the binary operator `'` (SEX operator) which performs sign extension from an arbitrary bit position; the symbol value reference `#`; and `*(x,y)` which extracts the *n*-th byte from the least significant end. These operators allow complex logic—such as calculating bit positions for scale values ​​in x86-64 LEAQ addressing mode encoding—to be expressed in a single line.

## 6. Implementation and Practicality

axx is implemented in both Python (`axx.py`) and C (`caxx.c`) and runs on FreeBSD and Linux. Beyond its role as a research-oriented core, it offers practical capabilities: it supports ELF64 relocatable object output (`-o`), primarily for x86-64, while also supporting header generation for architectures such as AArch64, RISC-V, i386, and PPC via the `e_machine` specification. It supports external symbol linkage via `.global` and `.extern`, label and section information export/import in TSV format (`-e` / `-i`), and source-level debugging in `gdb` or `lldb` through the generation of DWARF debug information (`.debug_info`, `.debug_abbrev`, `.debug_line`) using the `-g` option. The generated objects have been verified to link successfully with both GNU `ld` and LLVM `ld.lld`, and the tool supports calling C library functions and creating shared objects. The fact that the abstract concept of a "general-purpose assembler" has found a concrete outlet connecting to an actual toolchain is significant in demonstrating the viability of the concept.

## 7. Positioning within the Lineage

The concept of table-driven systems or meta-assemblers has precedents in the history of computing. Meta-assemblers from the 1960s and modern instruction descriptions using LLVM's TableGen belong to a similar lineage. Within this lineage, axx’s uniqueness lies in the following points:

First is the granularity and flexibility of the description. While TableGen is a description language tightly coupled with a C++ backend, axx’s pattern files are free-form text files completely decoupled from the processing system; they can be written to look almost identical to the instruction tables found in technical specifications. Second is the explicit adoption of Turing incompleteness. Many existing meta-assemblers evolved toward general-purpose computational capabilities by extending macro mechanisms, whereas axx moved in the opposite direction—prioritizing minimalism and guaranteed termination. Third is order-independent pattern matching. It eliminates the need for carefully managing definition order—a requirement often implicit in table-driven approaches—by utilizing a specificity score.

As the author states, the goal of axx is not merely widespread adoption as a tool, but rather the presentation of an academic insight: that all imperative assembly languages ​​can be encapsulated within a single pattern format. axx is positioned at a layer below standard assemblers—specifically, as a tool within the meta-layer used to define assemblers themselves.

## 8. Significance in the AI ​​Era

Creating pattern files for massive Instruction Set Architectures (ISAs) is labor-intensive for humans; however, converting specifications into pattern files is a transcription task with a fixed format, making it well-suited for AI. Once created, a pattern file serves as a finished product for that ISA and is reusable. If assemblers were originally created to make machine code easier for humans to understand, then in today’s era where AI writes code, there is increasing significance in having an intermediate representation layer—a generalized assembler—that caters to both humans and computers. The separation of pattern files from source files makes it theoretically possible to generate machine code for different processors from a single source, suggesting potential applications as a lightweight infrastructure for retargetable code generation. ## 9. Conclusion

The axx invention can be summarized by three key elements: a single reduction proposition (`instruction :: error_patterns :: binary_list`), a free-form pattern language for describing it, and intentional Turing incompleteness to guarantee termination. The fact that the 1986 concept was validated by the 2024 implementation—and that extensions such as VLIW/EPIC, arbitrary word widths, ELF64 object output, and DWARF debug information were layered on without altering the core design—demonstrates the validity of the distilled "essence." The vision of handling everything from homemade processors to supercomputers with a single matching engine redefined the assembler: shifting it from an implementation specific to a single ISA to a meta-language processing system for describing ISAs.

## References

- GitHub repository: https://github.com/fygar256/axx
- Related articles (Qiita: fygar256) covering x86_64 pattern files, ELF linking and execution examples, a Brainfuck interpreter, etc.