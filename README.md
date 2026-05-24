---
title: Generalized assembler 'axx General Assembler'
tags: Terminal Python general assembler
author: fygar256
slide: false
---
GENERAL ASSEMBLER 'axx.py'

C version is also available. C version is nameded Caxx. Caxx is much faster than Paxx.

Paxx is newest version. Due to Paxx version upgrades, updates to caxx may be delayed.

# Test environment

FreeBSD terminal

# Original article in Japanese

Qiita: https://qiita.com/fygar256/items/1d06fb757ac422796e31

# Relocatable ELF creation of axx

GitHub: https://github.com/fygar256/axx_relocatable_elf_generation

# Demonstration of brainfuck interpreter that assembled with axx

https://github.com/fygar256/brainfuck_interpreter_for_axx_on_freebsd_of_x86_64

---
title: Generalized Assembler 'axx General Assembler'
tags: Terminal Python general assembler
author: fygar256
slide: false
---
GENERAL ASSEMBLER 'axx.py'

Since it's written in Python, the nickname is Paxx. axx is an abbreviation for 'Arbitrary eXtended X(cross) assembler'. It also means that 'AXX' was created by superimposing X, which is an unknown CPU, onto 'ASM'.

The idea for axx, the name 'AXX', and the prototype written in C already existed in 1986, when I was working part-time at Tokyo Electronics Design during my university days. However, it wasn't until 2024, 38 years later, that I published working code like the one we see today. It was dormant for 30 years. The `instruction` in the axx pattern file is the meta-language for all imperative assembly languages. While it's a DSL, it doesn't have a defined grammar; it's a pattern language where grammar is constructed by combining string literals, symbols, and expressions.

All imperative assembly languages, except for EPIC/VLIW which have meta-level complexity in machine code, can essentially be reduced to a simple structure: `instruction :: error_patterns :: binary_list`. Further simplification by omitting error checking results in `instruction::binary_list`. Here, axx's binary_list includes complex expression calculations, alignment, and the `;` prefix modifier (which prevents binary output if 0) for practical purposes, but these are unnecessary in the minimal model. An instruction is a combination of (string literals, symbols replaceable by integer values, integer expressions, integer factors, and floating-point expressions). This allows processing of any imperative assembly language. However, the binary generation function isn't universal, limiting compatible processors; however, any processor where instructions and machine code are a one-to-one mapping can be processed. axx can also process Itanium-type EPIC and vliw processors through later extensions.

It extracts the essential commonalities of the von Neumann architecture, metamodels the instruction set architecture (ISA), and formalizes it using pattern matching.

# Test Environment

FreeBSD terminal

# Text

axx.py is a general assembler that generalizes assembly language. It can process almost any processor architecture. A pattern file (processor description file) is required to process individual processor architectures. While you can define free-form instructions, creating a pattern file according to the target processor's assembly language allows it to process that processor's assembly language, albeit with slightly different notation. Essentially, it's just a grammatical rule for instructions and binary generation based on it. axx targets not only virtual CPUs but also "abstracted real CPUs." Converting the specifications of a real processor into a pattern file allows for direct assembly. In that sense, creating pattern files for large ISAs is well-suited to AI, considering the human effort involved. Creating pattern files for large ISAs is time-consuming, but once created, the ISA is complete and can be reused.

This is not a "general-purpose assembler" in the sense of being "widely usable." It's a "general assembler" in the sense of being "common to everything." The `binary_list` only has five control structures: assignment, ternary operators, the `;` modifier, alignment, and `@@[]`. While ordinary general assemblers have `mnemonic operand definitions` alongside pattern definitions, axx's pattern definitions are arranged as `instruction :: error_pattern :: binary_list`, allowing for flexible instruction patterns. Therefore, notations like `r1 = r2 + r3` are possible, making it usable not only for assembly language but also as a general-purpose binary generator. The pattern file is Turing incomplete. Because of this Turing incompleteness, it's not suitable for processors with extremely complex architectures. Processor architectures can become infinitely complex if one chooses to make them so. If it were Turing complete, it could follow suit, but axx.py is Turing incomplete, and therefore not a "universal assembler." The reason it's currently Turing incomplete is that if it were Turing complete, the DSL would become a "program."

It cannot handle very specialized processors. For example, it cannot describe the ISAs of the following processors other than general-purpose processors:

Processor - Reason

Mill CPU - Belt architecture

ZISC - No instructions

Thinking Machines - Massively parallel

The execution platform is also independent of specific systems. It ignores `chr(13)` at the end of lines in DOS files. It should work on any system that runs Python.

This version only covers the core parts of the assembler, so it does not support practical features such as optimizations found in dedicated assemblers, or high-performance macros that convert structured/functional assembly to instructional assembly. For practical features, please use the macro processor. Optimization is not supported. Basic functions are present, so please adapt them. The current version lacks practicality.

Because pattern files and source files are separated, it's possible to generate machine code for a different processor from the source code of one instruction set, provided you don't consider the effort involved in coding. It's also possible to generate machine code for different processors from a common language. Writing multiple instruction codes in the pattern data's binary_list functions as a macro, but it's not very elegant. This allows you to write a simple compiler.

`axx` reads assembler pattern data from the first argument and assembles the source file (second argument) based on that pattern data. During this process, the pattern data is matched line by line from top to bottom against each assembly line, and the binary_list of matching patterns is output as the result. If the second argument is omitted, the source is input from the terminal (standard input).

The result is output as text to standard output, and if the -o option is specified, a binary file is output to the current directory. The -e option outputs the labels specified in `.export` along with section/segment information to a file in TSV format.

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

patternfile.axx --- Pattern file
source.s --- Assembly source
outfile.bin --- Raw binary output file
expfile.tsv --- Section label information export file
impfile.tsv --- Section label information import file
object.o ---- ELF relocatable object file

Relocatable object output works on FreeBSD, x86_64.

## Explanation of Pattern Files

A pattern file is a processor description file, and is user-defined to correspond to individual processors. It is a kind of metalanguage for machine code and assembly language.

If you find defining pattern files difficult, you can write them as string literals, passing only the minimum number of operands to the expression evaluation.

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

Uppercase letters in the instruction in a pattern file are treated as character constants. Lowercase letters are treated as single-character variables. The value of the symbol at that position on the assembly line is assigned to the variable. Using `!lowercase` assigns the value of the integer expression at that position, `!!lowercase` assigns the value of the factor at that position, `!Flowercase` assigns the integer bit pattern of the 32-bit floating-point expression at that position, `!Dlowercase` assigns the 64-bit floating-point expression at that position, and `!Qlowercase` assigns the integer bit pattern of the 128-bit floating-point expression at that position. These values ​​are then referenced from `error_patterns` and `binary_list`. All unassigned variables are initialized to 0. The `!` is not necessary when referencing from `error_patterns` and `binary_list`. All values ​​are referenced similarly.

```
Uppercase letters, symbols, and escaped characters. Character constants.
Lowercase letters: Values ​​of the symbol at that position.
!Lowercase letters: Values ​​of integer expressions.
!!Lowercase letters: Values ​​of integer factors.
!F lowercase letters: Values ​​of 32-bit floating-point expressions.
!D lowercase letters: Values ​​of 64-bit floating-point expressions.
!Q lowercase letters: Values ​​of 128-bit floating-point expressions.
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

### Symbol Check

```
.check::x::r1,r2,r3
```

If you set this, an error will occur if a symbol other than r1,r2, orr3 appears at the position of x.

To clear .check, use

```
.clrcheck::x
```

#### Pattern Order

Pattern files are evaluated from top to bottom, so those placed earlier take precedence. Special patterns should be placed first, and general patterns later. As shown below.

```
LD A,(HL)
LD A,e
```

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

The parameter specified in .viw must match the number of bytes represented by the pattern: (Bundle bit count - Template bit count divided by 8 (bits)) + (1 if there is a remainder, 0 otherwise). In EPIC, error patterns must be explicitly specified using `:: ::`.

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

Each reserves n words. Simply increment the location counter by n*size.

```
.resb n ; reserve n bytes
.resw n ; reserve n words
.resd n ; reserve n double words
.resq n ; reserve n quadruple words
```

#### export

The following allows you to export a label along with section/segment information. Only the label specified by the `.export` command is exported.

```
.export label
```

#### .global

Pass the label externally.


```
.global label
```

#### .extern

Declares the loading of an external label.

```
.extern label
```

.global and .extern are processed by the ELF relocatable object file output function.

#### .section

You can specify a section/segment as shown below.

``
.section .text
or
.segment .text
```

Currently, .section and .segment have the same meaning.

#### section sort

For example,

```
.section .text
ld a,9
.section .data
.asciiz "test1"
.section .text
ld b,9
.section .data
db 0x12
```

If you do this, the elements will be arranged exactly as written, so use secsort.py to sort them.

```
.section .text
ld a,9
ld b,9
.section .data
.asciz "test1"
db 0x12
```

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

#### 8086

Handling the same mnemonic in registers with different byte lengths is as follows:

```8086.axx
.setsym::SI::0
.setsym::BX::0

/***********************************************************/
/* At this point, if AX or AL appear, neither will match the pattern */

/* Define AL. At this point, AL matches the pattern
.setsym::AL::0xb0
MOV s,!a :: 0xb0,a
.clearsym::AL /* Clear symbol AL

/* Define AX. At this point, AX matches the pattern.
.setsym::AX::0xb8
MOV s,!a::0xb8,a,a>>8
.clearsym::AX /* Clear symbol AX
/***********************************************************/
MOV BYTE [e + f + !c],!d::0xc6,c>=0x100?0x80:0x40,c,;c>>8,d
MOV BYTE [e + f],!g :: 0xc6,0,g
MOV BYTE [!a],!b :: 0xc6,0x6,a,a>>8,b
MOV WORD [e + f + !a],!b::0xc7,a>=0x100?0x80:0x40,a,;a>>8,b,b>>8
MOV WORD [e + f],!a :: 0xc7,0,a,a>>8
MOV WORD [!a],!b::0xc7,0x06,a,a>>8,b,b>>8
```

```8086.s
mov byte [bx+si],0x12
mov byte [0x3412],0x56
mov byte [bx+si+0x12],0x34
mov byte [bx+si+0x3412],0x56
mov al,0x12
mov word [bx+si],0x3412
mov word [0x3412],0x7856
mov word [bx+si+0x12],0x5634
mov word [bx+si+0x3412],0x7856
mov ax,0x3412
```

```plaintext:execution example
$ axx 8086. axx 8086.s
0000000000000000 8086.s 1 mov byte [bx+si],0x12 0xc6 0x00 0x12
0000000000000003 8086.s 2 mov byte [0x3412],0x56 0xc6 0x06 0x12 0x34 0x56
0000000000000008 8086.s 3 mov byte [bx+si+0x12],0x34 0xc6 0x40 0x12 0x34
000000000000000c 8086.s 4 mov byte [bx+si+0x3412],0x56 0xc6 0x80 0x12 0x34 0x56
0000000000000011 8086.s 5 mov al,0x12 0xb0 0x12
0000000000000013 8086.s 6 mov word [bx+si],0x3412 0xc7 0x00 0x12 0x34
0000000000000017 8086.s 7 mov word [0x3412],0x7856 0xc7 0x06 0x12 0x34 0x56 0x78
000000000000001d 8086.s 8 mov word [bx+si+0x12],0x5634 0xc7 0x40 0x12 0x34 0x56
0000000000000022 8086.s 9 mov word [bx+si+0x3412],0x7856 0xc7 0x80 0x12 0x34 0x56 0x78
0000000000000028 8086.s 10 mov ax,0x3412 0xb8 0x12 0x34
$
```

### Testing some instructions on some processors

This is a test, so the binary is different from the actual code.

```test.axx
/* test
.setsym ::a:: 7
.setsym ::b:: 1
LDF A,!Fx :: 0x1,@@[4,x>>(%%*8)]
LDD A,!Dx :: 0x1,@@[8,x>>(%%*8)]
LDQ A,!Qx :: 0x1,@@[16,x>>(%%*8)]
REPEAT !n :: @@[n,0x99],%0@@[n,0x88]

/* ARM64
.setsym ::r1 :: 2
.setsym ::r2 :: 3
.setsym ::r3 :: 4
.setsym ::lsl:: 6
ADD w, x, y z #!d :: 0x88,d
ADD x, y, !e :: 0x91,x,y,e

/* A64FX
.setsym ::v0 :: 0
.setsym ::x0 :: 1
ST1 {x.4S},\[y\] :: 0x01,x,y,0

/* MIPS
.setsym ::$s5 ::21
.setsym ::$v0 ::2
.setsym ::$a0 ::4
ADDI x,y,!d :: (e:=(0x20000000|(y<<21)|(x<<16)|d&0xffff))>>24,e>>16,e>>8,e

/* x86_64
.setsym ::rax:: 0
.setsym ::rbx:: 3
.setsym ::rcx ::1
.setsym ::rep ::1

MMX A,B :: ,0x12,0x13
LEAQ r,\[s,t,!d,!e\] :: 0x48,0x8d,0x04,((@d)-1)<<6|t<<3|s,e
LEAQ r, \[ s+t*!h\+!i\] :: 0x48,0x8d,0x04,((@h)-1)<<6|t<<3|s,i
[[z]]MOVSB ​​:: ;z?0xf3:0,0xa4
TEST !a:: a==3?0xc0:4,0x12,0x13

/* ookakko test
L.D. (IX[[+!d]]),(IX[[+!e]]):: 0xfd,0x04,d,e
NOP :: 0x01
```

```test.s
leaq rax , [ rbx , rcx , 2 , 0x40]
leaq rax , [ rbx + rcx * 2 + 0x40]
addi $v0,$a0,5
st1 {v0.4s},[x0]
add r1, r2, r3 lsl #20
rep movsb
movsb
```

##### Execution example

```
$ axx.py test.axx test.s
0000000000000000 test.s 1 leaq rax , [ rbx , rcx , 2 , 0x40] 0x48 0x8d 0x04 0x4b 0x40
0000000000000005 test.s 2 leaq rax , [ rbx + rcx * 2 + 0x40] 0x48 0x8d 0x04 0x4b 0x40
000000000000000a test.s 3 addi $v0,$a0,5 0x20 0x82 0x00 0x05
000000000000000e test.s 4 st1 {v0.4s},[x0] 0x01 0x00 0x01 0x00
0000000000000012 test.s 5 add r1, r2, r3 lsl #20 0x88 0x14
0000000000000014 test.s 6 rep movsb 0xf3 0xa4
0000000000000016 test.s 7 movsb 0xa4
```
### errors

- If a label conflicts with a symbol in the pattern file, an "is a pattern file symbol" error occurs.

- Defining the same label more than once results in a "label already defined" error.

- If parsing is not possible, a "Syntax error" occurs.

- Referencing an undefined label results in a "Label undefined" error.

- If the syntax is incorrect, an "Illegal syntax in assembler line or pattern line" error occurs.

- If the EPIC template is not set, a "No VLIW instruction-set defined" error occurs.

- If the VLIW pattern file is incorrect, some errors in VLIW definition errors occur during interpretation. * An error will occur if any of the conditions in `error_patterns` are met. In that case, the following messages will be displayed for error codes 1, 2, 3, 5, and 6 respectively: (Invalid syntax, Address out of range, Value out of range, Register out of range, Port number out of range). If there are not enough error types, please add error messages to the source code.

### Comments

* While this is an unreasonable request, it does not support quantum computers or LISP machines. The assembly language for quantum computers is called quantum assembly, not assembly language. Programs for LISP machines are not assembly language.

* From homemade processors to supercomputers, please feel free to use it.

* Please evaluate, extend, and modify axx. The structure is complex, but since it's written in Python, extension is easy. Please feel free to extend it.

* Currently, only quadruple-precision floating-point numbers can be handled as constants. This is due to the Python 3 specification. It would be great if Python 4 could handle quadruple-precision floating-point numbers.

* Macro functionality requires a macro processor. To cover all assembly languages, a high-performance macro processor is needed to translate high-level assembly languages ​​such as functional and structured assembly languages ​​into imperative assembly language.

* Specifying the `-i` option imports labels from a TSV file. Specifying the `-e` option exports the labels specified in `.export`, along with the section/segment to which they belong, to a TSV file.

* Creating axx pattern files is difficult with a large ISA, and since the specifications are fixed, I hope that AI can handle this. While assemblers were originally created to make machine code easier for humans to understand, in today's world where AI writes code, a generalized assembler for both assembly language and computers would be beneficial.

* I disliked the massive, complex, and existential nature of LLVM, so I aimed for a simple, beautiful, and essential structure. However, due to circumstances, I used AI too much in the coding, resulting in complex code. I regret this. Is this how programming is these days? Even so, I believe the purity of the design philosophy remains.


### Unimplemented Items

* Difficulty in determining the order of pattern file evaluation.

* Now that the core is complete, adding pattern files to axx, along with high-performance macros and optimization features, would create a magnificent system. However, such a large project is difficult for an individual to complete, so I hope someone will create it. It would be great if it could be put into practical use.

### axx2 (the next generation of axx) concept. Explanation of pattern files (processor description files). Feature not available now.

- Using a more descriptive metalanguage for pattern files would improve readability, eliminate dependency on evaluation order, make control statements easier to write, and make processor description file debugging easier. However, pattern data is more intuitive. Further generalizing the metalanguage and using a descriptive metalanguage for pattern files, adding string literals, string operations, and numeric operations to binary_list, and adding control statements, would enable the generation of intermediate languages ​​and converters between assembly languages. In this case, the binary_list would be renamed object_list, and the pattern file would be renamed processor_specification_file. The metalanguage would be a multi-line description language rather than pattern data. This is feasible. Apparently, someone is currently working on it based on axx. Even in pattern files, you can write macros smartly by setting a='MOV b,c', assigning commands (strings) to character variables (currently lowercase letters, but if you expand this to what we normally call symbols), and writing them in binary_list. Allowing loop structures makes debugging difficult if an infinite loop occurs during processing within axx.py, but allowing evaluation only in pattern files simplifies debugging and allows loop and branch structures. Turing-completeness allows processing of any processor architecture. Lisp machines are also possible in principle. Self-reference checks are required. Use expand(a) to expand. For example, if a='b ; c' b='MOV AX,d' c='JMPC e', the result becomes 'MOV AX,d ; JMPC e'. Use expression(a) to evaluate the expression, and label: to define the label. Keeping labels separate in the processor description file and the assembly file eliminates the need to worry about the same label appearing in both. Meta-processing like EPIC is solved by enumerating variables. Making it a descriptive metalanguage requires drastic rewriting. If the assembler's processor characteristic description file becomes complex, it becomes difficult to make the file compatible with General Disassembler.

### Request

If you find a bug, I would appreciate it if you could let me know how axx won't work.

### Acknowledgements

I would like to express my gratitude to my mentor, Junichi Hamada, and Tokyo Denshi Sekkei, who gave me the problems and hints, the University of Electro-Communications, the computer scientists and engineers, Qiita, Google, IEEE, The Alan Turing Institute and some unforgettable people. I received a passing grade from Professor Kameda of the Information Processing Society of Japan. Thank you very much.

### English is not my mother tongue so this document is translated by google translation. there may be some mistakes and sorry for my broken English.

### Mascot Character

<img alt="image" width="200px" height="200px" src="https://github.com/fygar256/axx/blob/main/axxgirl.png">

