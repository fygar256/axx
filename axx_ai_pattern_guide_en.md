# Writing axx pattern files with AI: a step-by-step guide

2026-11-11

## Introduction

Let the AI do the bulk transcription of the pattern file, while a person decides the scope and checks the result by machine. This is the shortest way to put axx to practical use.

An axx pattern file is declarative data, one line per instruction. Writing it means transcribing the instruction tables of a specification into a fixed form, which is exactly the kind of work an AI does well. Because a single wrong line becomes wrong machine code, always pair it with a byte-for-byte comparison against an external assembler.

**What you need**

- axx (`git clone https://github.com/fygar256/axx.git`, then `make` to build caxx and paxx)
- The specification of the target ISA (the instruction list and the encoding tables)
- An external assembler for comparison (llvm-mc or GNU as, with support for the target ISA)
- An AI that can read and write files and run commands (Claude Code or similar)

## Overview of the workflow

The work runs in seven steps. Steps 3 to 5 repeat for each instruction group.

1. **Decide the scope**: which instruction groups, in which syntax, in which order
2. **Build the skeleton**: word width, byte order, register names, error messages
3. **Generate one instruction group at a time**: pattern lines paired with a test source
4. **Check against an external assembler**: hand the differences back to the AI to fix
5. **Test edges and errors**: lines that must assemble and lines that must be refused
6. **Compress with the macro layer**: generate regular rows with `!def` / `!while`
7. **Add the ELF description**: write linkable `.o` files with `-o`

The roles are divided as follows.

| Who | Main work |
| --- | --- |
| Person | Sets scope and priorities, checks the comparison results, accepts the final file |
| AI | Writes the pattern lines and test sources, runs the comparisons, fixes the differences |
| Machine | Byte-for-byte comparison with the external assembler, agreement between caxx and paxx |

## Preparation: material to give the AI

Give the AI the following material together at the start. Adding an existing pattern file as a model keeps the style consistent and cuts mistakes sharply.

| Material | Why it is given |
| --- | --- |
| The target ISA's instruction and encoding tables | The ground truth to transcribe |
| `Technical_Manual.md` (chapter 3 above all) | The rules for patterns, variables, `.check`, `.map`, `[[ ]]` and `error_patterns` |
| `mini_en.md` | For encodings that cannot be written as one expression, via `.call` |
| `macro_en.md` | For generating regular rows with `!def` / `!while` |
| `elf_generalization_en.md` | Only when ELF output with `-o` is needed |
| `axx.py` | To learn the grammar of pattern files and the structure of axx from the reference implementation (below) |
| An existing pattern file of a similar ISA | A model of how to write it |

Pick a model close to the target.

- **8-bit or small variable-length CPUs**: `z80.axx`, `6502.axx`, `8051.axx`
- **Fixed-length RISC**: `riscv64.axx` (a small model), `riscv64full.axx`, `mips_isa.axx`, `sparc.axx`
- **Complex variable-length CISC**: `68000.axx`, `x86_64m.axx`
- **Encodings with scattered bit fields**: `aarch64_logical_mini.axx` (how to use the mini language)
- **ELF for a machine without a built-in table**: `elfgen.axx` (MSP430), `elfrel.axx` (ARM, REL)

**Have the AI read `axx.py` to learn the grammar and the structure**

`axx.py` is the reference implementation (Paxx). Reading it lets the AI see the rules of the manual as actual behaviour, so fine points are mistaken less often. It runs to more than 17,000 lines, so reading it in this order works well.

1. **The docstring at the top**: the flow of processing (reading → macro expansion → pass 1 relaxation → pass 2 → output) and the three layers, macro layer, pattern layer and mini language
2. **`PatternMatcher`** (`match` / `match0` / `match0_brackets`): character-by-character matching, the kinds of capture (`!`, `!!`, `!F` / `!D` / `!Q`, `!L`, `!E`, `!Y`, `!S`), the specificity score `(n_expr, -n_lit, n_sym)` and the combinations of `[[ ]]`
3. **`PatternFileReader`**: splitting into fields on `::`, and how `.sub`, `.func` and `.include` are handled
4. **`ExpressionEvaluator`**: the operator precedence (`term0` to `term11`)
5. **`DirectiveProcessor`**: directives such as `.setsym`, `.check`, `.map`, `.reloc` and `.elf*`
6. **`ObjectGenerator.makeobj`**: evaluating `binary_list` (`;`, `;;`, `@@[]`, text templates, `.call`)
7. When needed, **`MiniInterp`** (the mini language) and **`MacroPreprocessor`** (the macro layer)

After the reading, have the AI explain "does this spelling match?" and "which of these two rows wins on score?" before it starts generating, so the points that are easy to trip over are checked in advance.

```text
Read axx.py in the order above and summarize the grammar of pattern files and the flow of processing in axx.
Then explain, for `mov a,b` and `mov a,5`, which of the two rows below is chosen and what is emitted.
MOV A,!d :: 0xAA,d
MOV A,B  :: 0xBB
```

## Step 1: decide the scope

A person first decides what to build, in which syntax and in which order. Leaving this vague and handing it to the AI leaves no fixed standard for the comparison, and costs rework.

1. **Choose one syntax**: following the syntax of the external assembler used for comparison (GNU as or llvm-mc) is the safe choice. The same source then goes through both.
2. **Fix the byte order and word width**: big- or little-endian, and whether the smallest addressable unit is 8 bits.
3. **Split into instruction groups and rank them**: for example loads and stores, then arithmetic, then branches, then floating point, then extensions.
4. **Start small**: finish something that works with the base instructions first, the way `riscv64.axx` (RV64I only) grew into `riscv64full.axx` (the whole of RV64).
5. **Decide whether to include pseudo-instructions**: `li`, `la`, `mov` and the like, matching what the external assembler accepts.

Write these decisions in a `/*` comment at the top of the pattern file, so the AI keeps the premises in view in later work.

## Step 2: build the skeleton

Before any instructions, have the AI build only the groundwork every line will use, and check it yourself. Once the groundwork is solid, later instruction groups can be produced in the same shape.

The skeleton contains:

- **Word width and byte order**: `.bits::big::8` and the like (manual 3.10)
- **Characters allowed in identifiers**: `.symbolc` when register names look like `$v0` or `%r1` (3.6)
- **Register names and numbers**: an array symbol holding the names, then `.map` to give each variable its numbers and its check in one line (3.6.1, 3.7.3)
- **Error messages**: register the text for each code with `.error` (3.14)

An example skeleton (a made-up 32-bit machine; the encoding is for illustration):

```
/* TOY32: 32-bit fixed length, big-endian, GNU as syntax
.bits::big::8
.error::3::"Immediate out of range."
.error::5::"Register out of range."
.setsym::gpr::[R0,R1,R2,R3,R4,R5,R6,R7]
.map::rd::gpr
.map::rs::gpr
.map::rt::gpr

/* one model line (the AI extends this shape to the other instructions)
ADD rd,rs,rt :: @@[4,*((0x01<<26)|(rs<<21)|(rt<<16)|(rd<<11),3-%%)]
```

An example request to the AI:

```text
Read the attached specification and the axx technical manual, and build only the skeleton of the TOY32 pattern file.
- Word width and byte order, register names and numbers (.map), and error messages (.error).
- Write only the ADD line as a model instruction, and also write a test source that exercises that line.
- Follow GNU as syntax.
```

## Step 3: generate one instruction group at a time

Generate the instructions one group at a time, not all at once. The key is to have the AI write **each pattern line together with a test line that exercises it**. The bundled `ppc64_test.s` and `sparc_test.s` were built the same way, one test line per pattern row.

**Instructions to give when generating**

- One instruction per line, in the same order as the specification's tables (so a person can compare them later)
- Check the ranges of immediates and displacements in `error_patterns`; never truncate an out-of-range value silently (3.4)
- Write optional operands with `[[ ]]` (3.8)
- When an encoding cannot be one expression (bitmask immediates, variable-length pseudo-instructions), write a mini-language `.func` and call it with `.call` (3.15)
- For every new line, add the matching test line in the same order

**An example request**

```text
Add the instructions in the "Arithmetic" section of the specification to the existing toy32.axx skeleton.
- One instruction per line, in the same order as the specification's table.
- Report an out-of-range immediate as error code 3.
- For each line you add, append one line that exercises it to toy32_test.s.
- When done, run the comparison of Step 4 and report the result.
```

Handing over a few dozen instructions at a time is the safe size. When a mistake turns up, you can quickly tell which batch introduced it.

## Step 4: check against an external assembler

Never judge the AI's lines correct by reading them: **always compare them byte for byte with an external assembler**. Run the same test source through both and compare the raw binaries with `cmp`.

```sh
# axx side (both the C and the Python versions)
caxx toy32.axx toy32_test.s -b axx.bin
paxx toy32.axx toy32_test.s -b paxx.bin

# reference side (GNU as)
as toy32_test.s -o ref.o
objcopy -O binary -j .text ref.o ref.bin

# reference side (llvm-mc; set <triple> for the target)
llvm-mc -triple=<triple> -filetype=obj toy32_test.s -o ref.o
llvm-objcopy -O binary --only-section=.text ref.o ref.bin

# compare
cmp axx.bin ref.bin
cmp axx.bin paxx.bin
```

When they differ, find the line and hand it back to the AI.

- The listing of `caxx toy32.axx toy32_test.s -v` shows the address and output bytes of each line.
- With llvm-mc, `-show-encoding` shows the reference bytes line by line too.
- Giving the AI only the difference, "this line is X in axx and Y in the reference", makes the fix fast and precise.

**Notes on the test source**

- A line that refers to an external label becomes a relocation on the reference side and the bytes will not match. At this stage use only numbers or labels inside the same source (relocations are checked in Step 7).
- For a variable-length ISA whose syntax does not match the reference, feed axx's output to the reference disassembler instead. `x86_64.axx` was verified this way, by filling every row with random operands and comparing against the llvm-mc disassembler.

## Step 5: edge and error tests

Passing correct input is not enough. Check in separate test files that **values at the very edge of a range assemble**, and that **out-of-range values are refused rather than silently truncated**. The bundled pattern files keep both kinds of test as well.

| File | Contents | How to check |
| --- | --- | --- |
| `toy32_edge.s` | Values exactly at the edge of a range (the largest and smallest immediates, the farthest branch, and so on) | Compare the `-b` output with the reference, as in Step 4 |
| `toy32_err.s` | Values one past the edge, registers that do not exist, misaligned displacements | Every line is an error and no output file is written |

Diagnostics go to standard error. Check that caxx and paxx agree on them too.

```sh
caxx toy32.axx toy32_err.s -b /dev/null 2> c.err
paxx toy32.axx toy32_err.s -b /dev/null 2> p.err
diff c.err p.err
```

Asking the AI "from the field widths in the specification, write one value that must pass at the edge and one that must be refused for each instruction" covers them without gaps. Immediates that accept both signed and unsigned values (for 8 bits, -128 to 255) are an edge worth special care.

## Step 6: compress with the macro layer

Once the comparisons pass, have the AI rewrite rows of the same shape so that the macro layer generates them. The file shrinks to a fraction of its size and becomes easier for a person to read and check. For x86_64, the 28,659 lines of `x86_64.axx` become 6,531 lines in `x86_64m.axx`, written with macros.

An example rewrite:

```
!def r3(name, fn) {
!{name} rd,rs,rt :: @@[4,*((0x!{fn:02x}<<26)|(rs<<21)|(rt<<16)|(rd<<11),3-%%)]
}
!r3("ADD", 0x01)
!r3("SUB", 0x02)
```

**The condition for compression is that the output does not change.** Before and after the rewrite, check two things.

```sh
# read the expanded patterns
caxx toy32.axx -p > expanded.axx

# check that the test output is the same as before the rewrite
caxx toy32_old.axx toy32_test.s -b old.bin
caxx toy32.axx     toy32_test.s -b new.bin
cmp old.bin new.bin
```

In the macro layer of a pattern file, comments on statement lines use `/*`, not `;`, because `;` separates the error code in an error field (`v>0xff;2`) (manual 7.4).

## Step 7: add the ELF description

Do this step only when you want linkable `.o` files with `-o`. If raw `-b` binaries are enough, skip it. All the machine-specific ELF knowledge can be written as declarations in the pattern file, so this can be handed to the AI as well (manual 3.7.5 to 3.7.11, `elf_generalization_en.md`).

1. **Get a base**: for one of the 11 built-in machines, `caxx toy32.axx -m <number> --elfdesc` writes its description out as declarations. For any other machine, use a close machine's description or `elfgen.axx` as the model.
2. **Give the AI the ABI's relocation table**: have it transcribe each type's name, number, width, PC-relativeness and the bits of the instruction word it fills into `.elftype` and `.elffield`.
3. **Assign types to instructions**: wrap the branch and address-building rows between `.reloc` and `.clrreloc`.
4. **Resolve branches within a section**: declare with `.elfresolve` the types the reference assembler resolves itself.
5. **Compare**: write a test that refers to external labels (`toy32_reloc.s`) and compare the output of `readelf -r` with the reference `.o`. Finally, link with ld or ld.lld and run the result.

An example declaration (PowerPC64 `bl`, from manual 3.7.7):

```
.elftype::rel24::10::4::1
.elffield::rel24::0x03fffffc

.reloc::t::rel24
BL !t :: .call w4(0x48000001|((t-$$)&0x3fffffc))
.clrreloc::t
```

```sh
caxx toy32.axx toy32_reloc.s -o axx.o
readelf -r axx.o > axx.rel
readelf -r ref.o > ref.rel
diff axx.rel ref.rel
```

When a declaration is missing, axx does not guess a type and writes no relocation for that reference. With `-d` it lists the places it left out, which you can hand to the AI to fill in.

## Pitfalls to include in the AI's instructions

The table below lists the axx rules an AI tends to get wrong. Pasting it at the start of the request cuts rework considerably.

| Pitfall | Correct form | Manual |
| --- | --- | --- |
| An `_` right after a capture is swallowed into the variable name (`!v_!w` reads as `v_`) | Write `!v\_!w` or `!v _!w` | 3.3, 3.12 |
| Lowercase means a variable, uppercase a literal. A label named on a pattern line needs an uppercase letter or a `.` | Put an uppercase letter or a `.` in such label names | 3.3 |
| Reusing a lowercase variable for another kind of operand makes it accept any symbol | Place a new `.check` or `.map` wherever its meaning changes | 3.7 |
| `.reloc` stays in force for every following row until it is taken back | Write `.clrreloc` right after the rows it belongs to | 3.7.5 |
| `!x` does not match when there is no expression | Enclose optional operands in `[[ ]]` | 3.3, 3.8 |
| The sign of `%` differs: divisor's sign in the pattern layer, dividend's in the mini language and macro layer | Do not move expressions with negative values between layers | 6.2 |
| Inside `binary_list`, `x%0` is not a remainder but resets the repeat index | Write `x % 0` with a space, or parenthesize | 6.2 |
| Comments start with `/*`. A continued line ends in `\`, and the next line must not be indented | Follow the `/*` and `\` rules | 3.1 |
| At most 20 `[[ ]]` groups per line | Split the pattern into several lines | 3.8 |
| Error codes 4 and 7 and above have no message text | Register messages with `.error` | 3.14 |
| Directives apply in the order written; a later `.setsym` overrides an earlier one | Declare `.unordered` to make the order irrelevant | 3.2, 3.19 |

## Completion checklist

When every item below holds, the pattern file is ready for practical use.

- [ ] The scope, syntax and byte order are written at the top of the file
- [ ] Every pattern line has a matching test line
- [ ] The `-b` output of the test source matches the external assembler byte for byte
- [ ] caxx and paxx produce the same output
- [ ] The edge tests (`_edge.s`) match the external assembler
- [ ] Every line that must be refused (`_err.s`) is an error, with the same diagnostics in both implementations
- [ ] After compression with macros, the output is the same as before
- [ ] (With `-o`) the output of `readelf -r` matches the reference, and the linked executable runs
- [ ] (With `-o`) `-d` reports no reference left without a relocation
