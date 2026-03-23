---
title: Generalized assembler 'axx General Assembler'
tags: Terminal Python general assembler
author: fygar256
slide: false
---
GENERAL ASSEMBLER 'axx.py'

# Test environment

FreeBSD terminal

# Original article in Japanee

Qiita: https://qiita.com/fygar256/items/1d06fb757ac422796e31

# Relocatable ELF creation examination of axx

GitHub: https://github.com/fygar256/axx_relocatable_elf_generation

C version is also available. C version is nameded Caxx. C version is much faster than Python version.

Paxx is newest version , Caxx is version 7.5.4.2, Raxx and Gaxx are version 7.2.

## install and execution(assemble) Python version 'Paxx'

```
# install
git clone https://github.com/fygar256/axx.git
cd axx
chmod +x axx.py
sudo cp axx.py /usr/local/bin/paxx

# execution(assemble)
paxx patternfile.axx [source.s] [-b outfile.bin] [-e expfile.tsv] [-i impfile.tsv] [-o object.o]
```

patternfile.axx --- pattern file

source.s --- assembly source

outfile.bin --- raw binary output file

expfile.tsv --- section and label information export file

impfile.tsv --- section and label information import file

object.o --- ELF relocatable object file

#### sample test of hello world on x86_64 FreeBSD

```
% paxx hello.axx hello.s -o hello.o # assemble
% ld hello.o -o hello               # link
% ./hello
hello, world
```

#### compile c version 'Caxx'

```
cc -o caxx caxx.c -lm -O2
caxx z80.axx z80.s [ option ] # execution
```

Because caxx is written in C, I'm wondering if someone will incorporate this into their toolchain.

Since I wrote it in Python, its nickname is Paxx. axx is an abbreviation for 'Arbitrary eXtended X(cross) assembler'. It also signifies doubling the CPU unknown X in 'ASM' to create 'AXX'.

The idea for axx, the name 'AXX', and a prototype written in C already existed in 1986 when I was working part-time at Tokyo Electronics Design during my university days. However, it wasn't until 2024, 38 years later, that I published working code like the one we see today. It was dormant for 30 years. The axx pattern file is the metalanguage of all imperative assembly languages. It's a DSL, but it doesn't have a specific grammar; it's a pattern language that creates grammar by combining string literals, symbols, and expressions.

All imperative assemblies except EPIC, which have meta-level complexity in machine code, essentially reduce to a simple structure: `instruction :: error_patterns :: binary_list`. Further simplification, omitting error checking, results in `instruction::binary_list`. While axx's `binary_list` includes complex expression calculations, alignment, and the `;` prefix (which prevents binary output if zero) for practical purposes, these are unnecessary in the minimal model. An instruction is a combination of (string literals, symbols replaceable by integer values, integer expressions, integer factors, and floating-point expressions). This allows processing of any imperative assembly language. However, the binary generation capability is not universal, limiting compatible processors; it can process any processor where the instruction and machine code are a one-to-one mapping. Through later extensions, axx can also process Itanium-type EPIC and vliw processors.


Extraction of essential commonalities in the von Neumann architecture
Metamodeling of the instruction set architecture (ISA)
Formalization through pattern matching


# Test Environment

FreeBSD terminal

# Text

axx.py is a general assembler that generalizes assembly language. It can handle almost any processor architecture. A pattern file (processor description file) is required to handle individual processor architectures. While you can define free-form instructions, creating a pattern file according to the target processor's assembly language will allow you to process that processor's assembly language, albeit with slightly different notation. In short, it's just a grammatical rule for instructions and binary generation based on it. axx targets not only virtual CPUs but also "abstracted real CPUs." By converting the specifications of a real processor into a pattern file, assembly becomes possible directly. In that sense, creating pattern files for large ISAs is well-suited to AI, considering the human effort involved.

It's not a "general-purpose assembler" in the sense of being "widely usable." It's a "general assembler" in the sense of being "common to everything." The pattern data only contains five control structures: assignment, ternary operators, the `;` modifier, alignment, and `@@[]`. While typical general-purpose assemblers list them alongside `mnemonic operand definitions`, axx's pattern definitions are listed alongside `instruction :: error_pattern :: binay_list`, allowing for flexible instruction patterns. Therefore, notations like `r1 = r2 + r3` are possible, making it usable not only for assembly language but also as a general-purpose binary generator. The pattern file is Turing incomplete. Because of this Turing incompleteness, it's not suitable for processors with extremely complex architectures. Processor architectures can become infinitely complex if one chooses to. While a Turing-complete assembler could keep up, axx.py, being Turing incomplete, is not a "universal assembler." The reason it's currently Turing incomplete is that if it were Turing-complete, the DSL would become a "program."

It cannot handle very specialized processors. For example, the ISAs of processors other than general-purpose processors, such as those listed below, cannot be described.

Processor - Reason

Mill CPU - Belt Architecture

ZISC - No Instructions

Thinking Machines - Massively Parallel

The execution platform is also independent of any specific system. It ignores `chr(13)` at the end of lines in DOS files. It should work on any system that runs Python.

This version only covers the core of the assembler, so it does not support practical features such as optimizations found in dedicated assemblers, or high-performance macros that convert structured/functional assemblies to instructional assemblies. For practical features, please use a macro processor. For now, please use a program that manages binary and label (symbol) files as the linker/loader. Optimization is not supported. Basic functionality should be available, so please adapt it. The current version lacks practicality.

Because the pattern file and source file are separated, it is possible to generate machine code for a different processor from the source code of one instruction set, provided you don't consider the effort involved in coding. It's also possible to generate machine code for different processors from a common language. Writing multiple instruction codes in the pattern data's `binary_list` functions as a macro, but it's not very elegant. This allows for the creation of simple compilers.

`axx` reads assembler pattern data from the first argument and assembles the source file (second argument) based on that pattern data. During this process, the pattern data is matched line by line from top to bottom against each assembly line, and the `binary_list` of matching patterns is output as the result. If the second argument is omitted, the source is input from the terminal (standard input).

The result is output as text to standard output, and if the `-o` option is specified, a binary file is output to the current directory. The `-e` option outputs the labels specified in `.export` along with section/segment information to a file in TSV format.

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

``
instruction :: error_patterns :: binary_list
instruction :: error_patterns :: binary_list
instruction :: error_patterns :: binary_list
:
:
```
`instruction` is mandatory. `error_patterns` is optional. `binary_list` is mandatory.
`instruction`, `error_patterns`, and `binary_list` should be separated by `::`.

for ex. (x86_64)

```
RET　:: 0xc3
```

Comments

Writing `/*` in a pattern file makes everything after `/*` on that line a comment. Currently, closing with `*/` is not possible. It is only effective for everything after `/*` on that line.

Case Sensitivity, Variables

Uppercase letters in the instruction field of a pattern file are treated as character constants. Lowercase letters are treated as single-character variables. The value of the symbol at that position on the assembly line is assigned to the variable. `!lowercase` assigns the value of the integer expression at that position, `!!lowercase` assigns the value of the factor at that position, `!Flowercase` assigns the integer conversion of the 32-bit floating-point expression at that position, and `!Dlowercase` assigns the integer conversion of the 64-bit floating-point expression at that position. These values ​​are then referenced from error_patterns and binary_list. All unassigned variables are initialized to 0. `!` is not necessary when referencing from `error_patterns` and `binary_list`. All values ​​are referenced similarly.

```
Uppercase: Character constant
Lowercase: Value of the symbol at that position
!Lowercase: Value of an integer expression
!!Lowercase: Value of an integer factor
!FLowercase: Value of a 32-bit floating-point expression
!DLowercase: Value of a 64-bit floating-point expression
!QLowercase: Value of a 128-bit floating-point expression
```

Lowercase variables are all initialized to 0 for each line in the pattern file.

From the assembly line, uppercase and lowercase letters are treated the same, except for labels and section names.

The special variable `$$` represents the current location counter.

And there's %%, which returns the number of times %% appears (index starting from 0).

Since the assembly line expressions and pattern data expressions call the same functions, they work almost the same. Variables in lowercase cannot be referenced from the assembly line.

#### Operator precedence

Operators and precedence are based on Python and are as follows.

```
(expression)         An expression enclosed in parentheses
#                    An operator that returns the value of a symbol
enflt{x},endbl{x}    Operators that convert x(byte code) to floating point number.
flt{x},dbl{x}        Operators that convert x to float and double bytecodes, respectively
qad(x)               Operators that convert x to a 128-bit floating point number's bytcode. However, in this case, x can only be a constant.
*(x,y)               yth byte from the lowest value of x (y>=0)
-,~                  Negative, bitwise NOT
'c'                  character code of 'c'
@                    Unary operator that returns the bit position from the right of the most significant bit of the value that follows
:=                   Assignment operator
**                   Power
*,/,//               Multiplication, division, integer division
+,-                  Addition, subtraction
<<,>>                Left shift, right shift
&                    Bitwise AND
|                    Bitwise OR
^                    Bitwise XOR
'                    Sign extension
<=,<,>,>=,!=,==      Comparison operators
not(x)               Logical NOT
&&                   Logical AND
||                   Logical OR
x?a:b                Ternary operator
```

There is an assignment operator `:=`. If you enter `d:=24`, 24 will be assigned to the variable d. The value of the assignment operator is the assigned value.

The prefix operator `#` takes the value of the symbol that follows.

The prefix operator `@` returns the bit position from the right of the most significant bit of the value that follows. We'll call this the Hebimarumatta operator.

The binary operator `'`, for example `a'24`, will make the 24th bit of a the sign bit and perform sign extension (Sign EXtend). We'll call this the SEX operator.

The binary operator `**` is exponentiation.

The ternary operator `?:`, for example `x?a:b`, will return a if x is true and b if it is false.

### Prompt Mode

When the prompt `>>>` appears and you enter text from the keyboard, you can use the label display command `?`.

## Example of binary output

```
.setsym:: BC:: 0x00
.setsym:: DE:: 0x10
.setsym:: HL:: 0x20
LD s,!d:: (s&0xf!=0)||(s>>4)>3;9 :: s|0x01,d&0xff,d>>8
```

Then, `ld bc,0x1234, ld de,0x1234, ld hl,0x1234` output `0x01,0x34,0x12, 0x11,0x34,0x12, 0x21,0x34,0x12`, respectively.

#### 8086

The same mnemonic for registers of different byte length is handled as follows.

```8086.axx
.setsym::SI::0
.setsym::BX::0

/*********************************************************************/
/* If AX or AL appears at this point, neither will match the pattern */

/* Define AL. At this point, AL matches the pattern
.setsym::AL::0xb0
MOV s,!a :: 0xb0,a
.clearsym::AL　/* Clear symbol AL

/* Define AX. At this point, AX matches the pattern.
.setsym::AX::0xb8
MOV s,!a::0xb8,a,a>>8
.clearsym::AX　/* Clear symbol AX
/********************************************************************/
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

##### execution sample

```
$ axx 8086.axx 8086.s
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

Because this is a test, the binary is different from the actual code.

```test.axx
/* test
.setsym ::a:: 7
.setsym ::b:: 1
LDF A,!x :: 0x1,@@[16,*(x,%%)]

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
ST1 {x.4S},[y] :: 0x01,x,y,0

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
LEAQ r,[s,t,!d,!e] :: 0x48,0x8d,0x04,((@d)-1)<<6|t<<3|s,e
LEAQ r, [ s + t * !h \+ !i ] :: 0x48,0x8d,0x04,((@h)-1)<<6|t<<3|s,i
[[u]]MOVSB ​​:: ;u?0xf3:0,0xa4
TEST !a:: a==3?0xc0:4,0x12,0x13

/* ookakko test
LD (IX[[+!d]]),(IX[[+!e]]):: 0xfd,0x04,d,e
NOP :: 0x01
```

For x86_64 expressions such as `LEAQ r,[s+t*h+i]`, please write `LEAQ r,[s+t*!!h+!!i]`. If you write `!h` instead of `!!h`, when pattern matching, the assembly line expression evaluation function will interpret the part after 2 in `leaq rax,[rbx+rcx*2+0x40]` as `!h`, and will interpret the part after that as an expression, 2+0x40, as `!h`, and 2+0x40 will be substituted for h, resulting in a syntax analysis error for the remaining `+!!i`. `!!h` is a factor, and `!h` is an expression. This is because escape characters in expressions cannot be processed.

```test.s 
leaq rax , [ rbx , rcx , 2 , 0x40]
leaq rax , [ rbx + rcx * 2 + 0x40]
addi $v0,$a0,5
st1 {v0.4s},[x0]
add r1, r2, r3 lsl #20
rep movsb
movsb
```

Execution example 

``` $ axx.py test.axx test.s
0000000000000000 test.s 1 leaq rax , [ rbx , rcx , 2 , 0x40] 0x48 0x8d 0x04 0x4b 0x40
0000000000000005 test.s 2 leaq rax , [ rbx + rcx * 2 + 0x40] 0x48 0x8d 0x04 0x4b 0x40
000000000000000a test.s 3 addi $v0,$a0,5 0x20 0x82 0x00 0x05
000000000000000e test.s 4 st1 {v0.4s},[x0] 0x01 0x00 0x01 0x00
0000000000000012 test.s 5 add r1, r2, r3 lsl #20 0x88 0x14
0000000000000014 test.s 6 rep movsb 0xf3 0xa4
0000000000000016 test.s 7 movsb 0xa4
```

## errors

・If the label overlaps with a symbol in the pattern file, a "is a pattern file symbol error" will occur.

・If the same label is defined more than once, a "label already defined" error will occur.

・If syntax analysis is not possible, a "syntax error" will occur.

・If an undefined label is referenced, a "Label undefined" error will occur.

・If the syntax is incorrect, an "Illegal syntax in assembler line" or "pattern line" will occur.

・If no template set for instruction of EPIC, "No template set." error will occur.

・If any of the conditions in error_patterns are met, an error will occur. In that case, the following messages will appear for error codes 1, 2, 3 , 5, and 6 (Invalid syntax, Address out of range, Value out of range, Register out of range, Port number out of range). If there are not enough types of errors, add an error message to the source.

## Comments

-Sorry for the original notation.

-I know it's a ridiculous request, but quantum computers and LISP machines are not supported.

The assembly language of quantum computers is called quantum assembly, and is not assembly language.

LISP machine programs are not assembly language.

-From homemade processors to supercomputers, please feel free to use axx.py.

-Please evaluate, extend, and modify axx. The structure is difficult to understand, but since it is written in Python, it is easy to extend. Please feel free to extend it.

-For now, only constants can be used for quadruple precision floating point numbers. This is the specification of python3. It would be nice if quadruple precision floating point numbers could be handled in python4.

-nan, inf, and -inf processing can only be used in flt{x}, dbl{x}, and qad{x}. Nan, inf, and -inf are first loaded into registers or memory, or constants are taken as operands, and then the processor performs the calculations, so this may be sufficient.

- Use a preprocessor for macro functionality. To cover all assembly languages, a high-performance macro processor is needed to translate functional,structured and such high-level assembly language into imperative assembly language.

- For now, when the linker loader specifies option `-i`, it imports labels from the TSV file, and when the option `-e` is specified, the label specified in .export is exported to the file in TSV along with the section/segment to which the label belongs, so this is used.

- Creating axx pattern files is difficult for large ISAs, and since the specifications have been fixed, I'm wondering if AI can do it. Assemblers were originally created to make machine code easier for humans to understand, but in today's world where AI is writing code, I think it would be good to have general assemblers for both assembly language and computers.

## Items not yet implemented

- Make it compatible with the linker generally.

・The order of evaluation of pattern files is difficult.

・Make it possible to take an equation for x in qad(x).

・Now that the core is made, I think it would be a complete system if I prepared a pattern file for axx and added a high-performance macros, and optimization functionalities, I would be happy if it were put to practical use.

### Looking Back

axx has been compiled to allow for the description of all classic and past processors.

### Looking to the Future / axx2 (the next generation of axx) concept. Explanation of pattern files (processor description files). Feature not available now.

- Using a more descriptive metalanguage for pattern files would improve readability, eliminate dependency on evaluation order, make control statements easier to write, and make processor description file debugging easier. However, pattern data is more intuitive. Further generalizing the metalanguage and using a descriptive metalanguage for pattern files, adding string literals, string operations, and numeric operations to binary_list, and adding control statements, would enable the generation of intermediate languages ​​and converters between assembly languages. In this case, the binary_list would be renamed object_list, and the pattern file would be renamed processor_specification_file. The metalanguage would be a multi-line description language rather than pattern data. This is feasible. Apparently, someone is currently working on it based on axx. Even in pattern files, you can write macros smartly by setting a='MOV b,c', assigning commands (strings) to character variables (currently lowercase letters, but if you expand this to what we normally call symbols), and writing them in binary_list. Allowing loop structures makes debugging difficult if an infinite loop occurs during processing within axx.py, but allowing evaluation only in pattern files simplifies debugging and allows loop and branch structures. Turing-completeness allows processing of any processor architecture. Lisp machines are also possible in principle. Self-reference checks are required. Use expand(a) to expand. For example, if a='b ; c' b='MOV AX,d' c='JMPC e', the result becomes 'MOV AX,d ; JMPC e'. Use expression(a) to evaluate the expression, and label: to define the label. Keeping labels separate in the processor description file and the assembly file eliminates the need to worry about the same label appearing in both. Meta-processing like EPIC is solved by enumerating variables. Making it a descriptive metalanguage requires drastic rewriting. If the assembler's processor characteristic description file becomes complex, it becomes difficult to make the file compatible with General Disassembler.

### Request

If you find a bug, I would appreciate it if you could let me know how　axx　won't work.

### Acknowledgements

I would like to express my gratitude to my mentor, Junichi Hamada, and Tokyo Electronics Design, who gave me the problems and hints, the University of Electro-Communications, the computer scientists and engineers, Qiita, Google, IEEE, The Alan Turing Institute and some unforgettable people. Thank you very much.

### English is not my mother tongue so this document is translated by google translation. there may be some mistakes and sorry for my broken English.

### Mascot Character

<img alt="image" width="200px" height="200px" src="https://github.com/fygar256/axx/blob/main/axxgirl.png">

