# axx Macro Layer Syntax Reference

This is a source-to-source transformation stage that runs before the source is passed to the main assembler. Label values, `.equ` definitions, and `$` or `$$` symbols cannot be referenced (to ensure that expansion results remain consistent across relaxation passes).

It is implemented with identical specifications in both `axx.py` and `caxx.c`. The only difference between the two is numeric representation: the Python version uses arbitrary-precision integers, while the C version uses `int64`. Results will differ only when macro-time calculations exceed 64 bits (since the macro layer outputs source text, this does not affect the main assembler's 256-bit expression evaluation).

## Statements

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

The opening `{` must appear at the end of the header line, and the closing `}` at the start of a line. `; comment` may be written after a statement. ## Embedding in Expressions

| Notation | Meaning |
|---|---|
| `!{expr}` | Expand value to text |
| `!{expr:04x}` | Apply Python-style formatting |
| `\!{` | Literal `!{` |

## Values ​​and Operators

Values ​​are limited to integers and strings. Operators are C-compliant:
`?:` `||` `&&` `|` `^` `&` `==` `!=` `<` `<=` `>` `>=` `<<` `>>` `+` `-` `*` `/` `%`
plus unary `-` `+` `~` `!`. `/` and `%` truncate towards zero, just like in C (`-7/2 == -3`).
`+` performs concatenation if either operand is a string; `"ab" * 3` performs repetition.
Integer literals: `10` / `0x1f` / `0b1010` / `0o17` (underscores allowed).
`'A'` is treated as a character code if it is a single character, or a string if multiple characters.

## Built-in Functions

`len(s)` `hex(v[,digits])` `str(v)` `int(s[,base])` `upper(s)` `lower(s)`
`substr(s,start[,length])` `abs(v)` `min(...)` `max(...)` `uid()` `defined(name)`

## Implicit Variables in Macros

| Name | Content |
|---|---|
| `__id__` | Integer unique to each invocation (for generating local labels) |
| `__name__` | Macro name |

## CLI

| Option | Meaning |
|---|---|
| `--no-macro` | Completely disable the macro layer |
| `-P [FILE]`, `--macro-expand [FILE]` | Output only the expanded result and exit (defaults to stdout) |

caxx.c uses the same option names. To allow the filename to be omitted, the `-P` option in the C version interprets the subsequent argument as the output destination only when placed after both the pattern file and the source file have been specified (e.g., `caxx pat.axx src.s -P out.s`). ## Backward Compatibility

- Lines starting with `!` are intercepted only if they contain a keyword, a predefined macro name, or are immediately followed by `(`.
VLIW-specific `!!` and `!F` / `!D` / `!Q` constructs remain untouched.
- A `}` at the start of a line is treated as a closing brace only when a block is currently open.
- Output for source code containing no macros remains identical to previous behavior.

## Limitations

- Assembler-level `.INCLUDE` directives bypass the macro layer; use `!include` to import macro definition files.
- Constructs like `!{a ? b : c:04x}` (combining a ternary operator with format specifiers) cannot currently be parsed.
- Interactive mode (when no source file is specified) bypasses the macro layer.

## Runaway Protection

Limits: 200 levels of recursion, 1,000,000 `!while` iterations, 2,000,000 generated lines, and a nesting depth of 64 for `!include`.
Exceeding any of these limits triggers an error, and expansion is aborted for the remainder of the pass.

## Example

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