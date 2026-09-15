# axx Mini Language Syntax Reference

A small Turing-complete procedural language, invoked from a `binary_list` field
with `.call`. It is used only inside a pattern file (`.axx`).

It is a separate stage from the macro layer. Where the macro layer transforms
text before the file is read, the mini language runs at encoding time — once per
assembled instruction. It runs only for lines whose `binary_list` says `.call`;
write no `.call` and the pattern file stays the declarative data it always was.

It is implemented with identical specifications in both `axx.py` and `caxx.c`.
Values are 256-bit two's complement in both, and the same input produces the same
bytes.

## Defining and calling

```
.func::<name>::<parameter, parameter, ...>
<statements>
.return
```

Everything from the header to the matching `.return` is the body; those lines are
never matched as pattern lines. The parameter field may be empty
(`.func::name::`). Names and parameter names are letters, digits and `_`.

```
MOV a,!b,!c :: .call name(a,b,c)
```

`.call` is one comma-separated element, so it can be mixed with plain values.

```
MIX !e :: 0x90,.call rep(e),0xff
```

A function may be defined after the place that uses it; references are resolved
once the whole pattern file has been read.

## Statements

One statement per line.

| Syntax | Meaning |
|---|---|
| `name = expr` | Assign to a local variable |
| `name[index] = expr` | Assign to an array element |
| `.emit(e1, e2, ...)` | Output one word per value |
| `.call name(args)` | Call another function |
| `.if expr .then` / `.else` / `.endif` | Conditional; `.else` is optional |
| `.while(expr)` / `.endwhile` | Repeat while the value is non-zero |
| `.for name in range(...)` / `.next` | `range(stop)`, `range(start, stop)`, `range(start, stop, step)` |
| `.nonlocal a, b` | Treat these names as belonging to an enclosing call |
| `.return` | Return from the function |
| `.func::name::params...` | Nested function definition |

The `.if` line must end with `.then`. The condition of `.while` needs no
parentheses of its own (`(expr)` simply reads as a parenthesized expression). The
`step` of `range()` must not be 0.

## Expressions and operators

Loosest first.

| Precedence | Operators |
|---|---|
| 1 | `\|\|` |
| 2 | `&&` |
| 3 | `!` (prefix) |
| 4 | `==` `!=` `<` `<=` `>` `>=` |
| 5 | `\|` |
| 6 | `^` |
| 7 | `&` |
| 8 | `<<` `>>` |
| 9 | `+` `-` |
| 10 | `*` `/` `%` |
| 11 | `-` `+` `~` (prefix) |
| 12 | `**` (right associative) |
| 13 | `[index]` `[start:end]` |

- `/` truncates toward zero and `%` takes the sign of the dividend (`-7/2` is
  `-3`, `-7%3` is `-1`).
- `>>` is arithmetic. For a shift count of 256 or more, `<<` gives 0 and `>>`
  gives 0 or `-1` according to the sign.
- The exponent of `**` may not be negative. The result wraps within 256 bits.
- Comparisons and logical operators yield 1 or 0. `&&` and `||` short-circuit.
- Numbers may be decimal, `0x` hex or `0b` binary, with `_` as a digit separator.
- `.len(expr)` is the length of an array.

Only 0 is false.

## Values and arrays

A value is an integer or an array. Array elements are integers; arrays of arrays
do not exist.

```
a = []
a[3] = 5          /* a is now [0,0,0,5]; the gap is filled with 0 */
.emit(a[0])       /* 0 */
.emit(a[99])      /* 0 — reading past the end gives 0 and does not extend */
.emit(.len(a))    /* 4 */
b = a[1:3]        /* [0,0] — the end index is not included */
```

| Operation | Behaviour |
|---|---|
| `a[i] = v` (`i` at or past the end) | Extend with zeros to length `i+1` |
| `a[i]` (out of range, or negative) | Gives `0`; the array is unchanged |
| `a[i] = v` (`i` negative) | Error |
| `a[lo:hi]` | Clamped to the array; `hi` is not included |
| `.len(a)` | Length |

Reading a name before it is assigned is an error, so a misspelling does not
silently read as 0.

## Scope and nesting

Each call gets its own set of variables, and parameters are local to that call.

Functions may be defined inside functions. An inner function is visible to its
enclosing function, and a name resolves outward: itself, then its parent, and so
on to the top level. `.nonlocal` makes a name refer to a variable of an enclosing
call instead of a local one.

```
.func::outer::
n=7
.func::inner::
.nonlocal n
n=n+1
.emit(n)
.return
.call inner()
.call inner()
.emit(n)
.return
```

```
-> 08 09 09
```

`.nonlocal` must appear before that name is otherwise used in the function. If no
enclosing call has the name, it is an error.

## The boundary with the pattern layer

- **Arguments are pattern-layer expressions.** In `.call f(a,b)`, `a` and `b` mean
  the captured pattern variables. Anything writable in `binary_list` works —
  labels, `.equ`, `$.` — including forward-referenced labels.
- **Variable namespaces are separate.** Mini-language variables have nothing to do
  with pattern variables `a`–`z` or with `.setsym` symbols; pass what you need as
  an argument.
- **An argument derived from an undefined label arrives as 0,** so a sentinel
  value cannot blow up a loop count while instruction sizes are being measured in
  the first pass.
- **`.emit` outputs one word of `.bits` width** — one byte at the default 8, or
  one 12-bit word under `.bits::12`.
- **The number of words emitted is the instruction's length.** Emit the same count
  in both passes; a count that varies by pass will not let addresses settle.
- **`;` cannot be applied to `.call`.** For conditional output, wrap `.emit` in
  `.if`.

## Runaway guards

The language is Turing complete, so a mistake in a pattern file could otherwise
stop the assembler from finishing. Exceeding any of these reports an error naming
the offending line.

| Cap | Value |
|---|---|
| Statements executed per `.call` | 4,000,000 |
| Call nesting | 128 |
| Words emitted per `.call` | 1,048,576 |
| Array length | 1,048,576 |

Syntax errors are reported when the pattern file is read, run-time errors when
that instruction is assembled; both carry a file name and line number.

## Examples

A sieve, and an instruction whose encoding is a Collatz step count.

```
PRIMES !n  :: .call sieve(n)
COLLATZ !n :: .call collatz(n)

.func::sieve::n
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

.func::collatz::n
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
```

```
primes 50            -> 02 03 05 07 0b 0d 11 13 17 1d 1f 25 29 2b 2f
collatz 27           -> 6f
```

Recursion works too.

```
FIB !n :: .call fib(n)

.func::fib::k
.if k<2 .then
.emit(k)
.else
.call fib(k-1)
.call fib(k-2)
.endif
.return
```
