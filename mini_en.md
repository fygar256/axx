# axx Mini Language Syntax Reference

A small Turing-complete procedural language, invoked from a `binary_list` field
with `.call`. It is used only inside a pattern file (`.axx`).

It is a separate stage from the macro layer. Where the macro layer transforms
text before the file is read, the mini language runs at encoding time — once per
assembled instruction. It runs only for lines whose `binary_list` says `.call`;
write no `.call` and the pattern file stays the declarative data it always was.

It is implemented with identical specifications in both `axx.py` and `caxx.c`.
Values are 256-bit two's complement in both, and the same input produces the same
bytes — and the same `.echo` text on stderr.

## Defining and calling

```
.func <name>(<parameter, parameter, ...>)
<statements>
.endfunc
```

Everything from the header to the matching `.endfunc` is the body; those lines are
never matched as pattern lines. The parameter field may be empty
(`.func name()`, or just `.func name`). Names and parameter names are letters,
digits and `_`. It is the same shape as the call site's `.call name(a,b)`.

The older `.func::name::params` header is still read. A `::` directly after
`.func` selects it, so existing pattern files keep working unchanged.

```
MOV a,!b,!c :: .call name(a,b,c)
```

`.call` is one comma-separated element, so it can be mixed with plain values.

```
MIX !e :: 0x90,.call rep(e),0xff
```

An argument written `[expr, expr, ...]` is an array; `"..."`, `.exp(variable)`
or the name of a string symbol makes a string element, and its other elements are pattern
expressions too. `[]` is the empty array.

```
LOG !v :: .call table([0x11,0x22,v],3)
```

An argument written `"..."` is a string (see "Strings" below). A comma or a
parenthesis inside the string does not split the arguments.

```
MSG !n :: .call func1(n,"text")
```

An argument written `.exp(variable)` passes, as a string, the text that pattern
variable captured from the source. It is the same text the template
`{{.exp(variable)}}` emits (Technical_Manual section 3.18), and any capture form
works, not only `!L`.

```
SPELL !x,r :: .call func1(x,.exp(x),.exp(r))
```

```
spell 1+2*3,rb       -> func1(7, "1+2*3", "rb")
```

An argument that is just the name of a string symbol (`.setsym::name::"..."`)
passes that string. It is read as if `.call func1(10,"...")` had been written,
so the same four escapes are opened. The name is case-insensitive. When the name
is part of an expression, as in `msg+1`, it is read as an expression as before.
A pattern variable of the same name does not hide it: as with `{{name}}`, the
string symbol is found first.

```
.setsym::msg::"text"
MSG :: .call func1(10,msg)          /* func1(10, "text") */
```

An argument that is just the name of an array symbol (`.setsym::name::[...]`)
passes that array. Numeric items become integers; `"..."` items and bare-name
items (`AX` and so on) become strings — the same text `{{name[i]}}` emits —
with the escapes opened as if `"..."` had been written. A string symbol of the
same name is found first. It cannot be written inside an array (`[regs]`).

```
.setsym::regs::[AX,BX,0x10]
REGS :: .call func1(regs)           /* func1(["AX", "BX", 16]) */
```

A function may be defined after the place that uses it; references are resolved
once the whole pattern file has been read.

## Statements

One statement per line.

| Syntax | Meaning |
|---|---|
| `name = expr` | Assign to a local variable |
| `name[index] = expr` | Assign to an array element |
| `name[lo:hi] = expr` | Replace a range: from `lo` up to but not including `hi`, with the right side (a string for a string, an array for an array). The length may change |
| `.emit(e1, e2, ...)` | Output one word per integer; a string one word per byte, an array element by element (a string element one word per byte) |
| `.echo(item, item, ...)` | Print strings and values to stderr; outputs no word |
| `.raise expr` | Report an error whose error code is the value of `expr` |
| `.call name(args)` | Call another function |
| `name = .call name(args)` | Call another function and assign its return value |
| `.if expr .then` / `.elif expr .then` / `.else` / `.endif` | Conditional; `.elif` may repeat, `.else` is optional |
| `.while(expr)` / `.endwhile` | Repeat while the value is non-zero |
| `.for name in range(...)` / `.next` | `range(stop)`, `range(start, stop)`, `range(start, stop, step)` |
| `.for name in array` / `.next` | Loop over the array's elements (integers or strings) from index 0 |
| `.break` | Leave the innermost `.while` / `.for` loop |
| `.continue` | Skip to the next iteration of the innermost `.while` / `.for` loop |
| `.nonlocal a, b` | Treat these names as belonging to an enclosing call |
| `.return` | Return from the function. May appear anywhere in the body (top level or inside `.if`/`.while`/`.for`), any number of times |
| `.return expr` | Return a value from the function |
| `.func name(params...)` … `.endfunc` | Nested function definition; `.endfunc` closes the body |

The `.if` and `.elif` lines must end with `.then`. Any number of `.elif`
branches may follow an `.if`, and an `.else` may close the chain; a single
`.endif` ends the whole chain. The condition of `.while` needs no
parentheses of its own (`(expr)` simply reads as a parenthesized expression). The
`step` of `range()` must not be 0.
In `.for name in expr`, anything after `in` other than `range(` is read as an
expression; its value must be an array, and its elements are assigned to the name
in turn. The array is copied before the loop starts, so changing it in the body
does not change the elements visited.

```
.for op in ["mov", "add", "jmp"]
.emit(.len(op))
.next
```
`.break` and `.continue` may only appear inside a `.while` or `.for` body;
outside a loop they are an error at parse time. Each affects only the innermost
loop.

```
.for i in range(10)
.if i == 3 .then
.continue          /* skip 3 and go on */
.endif
.if i == 7 .then
.break             /* stop at 7 */
.endif
.emit(i)
.next
```

```
.if n > 100 .then
.emit(0xff, n & 0xff)
.elif n > 10 .then
.emit(0xfe, n & 0xff)
.else
.emit(n & 0xff)
.endif
```

`.echo` is for debugging. It prints to stderr and outputs nothing, so adding
or removing one never changes the generated bytes. Each item is either a
`"..."` string literal or an expression, and the two may be mixed. A string
prints as written, an integer as signed decimal, an array as `[1, 2, 3]`, and
the items of one call share a line separated by spaces; `.echo()` prints an
empty line. The layout comes from the same output routine the macro layer's
`!echo` uses, so the two agree. Nothing is printed while instruction lengths
are being measured or while pass 1 is still converging, so a line appears once
per assembled instruction. The same `.echo` can also be written on a body line
of a pattern file (Technical_Manual section 3.14.1).

```
.echo("Example", n, 1)          /* -> Example 7 1 */
.echo("n=", n, "arr=", a)       /* -> n= 7 arr= [7, 14] */
```

An item may also be a string built by an expression (`.echo("n=" + n)`). A
string prints as its bytes, except that a NUL (`.chr(0)`) prints as `\0`.

## Reporting an error

`.raise expr` reports an error whose error code is the value of `expr`. The
format is exactly the one an `error_patterns` field produces for
`condition;code`, and a message registered with `.error::code::"text"` is used
the same way.

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

```
MOV 300              -> Line 1 Error code 3 immediate out of range:
```

- **Reporting does not stop the function.** Execution continues with the next
  statement, so follow it with `.return` when you mean to stop there, as above.
- **The code need not be registered.** An unregistered one simply prints the
  number with no text: `Line 1 Error code 9 : `.
- **Like `.echo`, it stays quiet** while instruction lengths are only being
  measured and during pass-1 relaxation, so each assembled instruction reports
  at most once.
- **The assembly fails.** As with a triggered `error_patterns`, no output file
  is written.

## Delegating to the assembler's expression evaluator

Write any of these in an expression and that term is evaluated by the
assembler's own expression evaluator. Both sides are 256-bit, so the value
comes back usable as it is.

| Written | Meaning |
|---|---|
| `$$` | Location counter (the address this instruction starts at) |
| `$.` | Address the next instruction starts at |
| `#name` | A symbol defined with `.setsym` |
| `name` | An assembler label or `.equ`, when no local variable has that name |

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

Which terms that evaluator accepts depends on the context it is called from (a
capability descriptor). Called from the mini language it looks like this:

| Term | Pattern line | Mini language |
|---|---|---|
| Label / `.equ` | yes | yes |
| `$$` / `$.` | yes | yes |
| `#symbol` | yes | yes |
| Pattern variables | yes | **no** |
| `!!!` / `!!!!` | yes | **no** |

Pattern variables are dropped because nothing has bound them at the time a
`.func` body runs; pass them in at the call site instead, as `.call f(a,b)`.
`!!!` is dropped for the same kind of reason — it only means anything on a VLIW
pattern line.

A value derived from an undefined label comes through as 0, the same treatment
`.call` arguments get, so that a huge sentinel cannot blow up a loop count. A
misspelling is still a mini-language error: by pass 2 the assembler's tables are
complete, so "no such name" can be stated with certainty.

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
- `.len(expr)` is the length of an array or a string.
- `+` `*` `==` `!=` `<` `<=` `>` `>=` with a string on either side are string
  operations (see "Strings" below).

Only 0 is false.

## Values and arrays

A value is an integer, an array or a string (next section). Array elements are
integers or strings; arrays of arrays do not exist.

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
| `a[lo:hi] = b` | Replaces the range with the array `b`; the length may change. The bounds are clamped as for `a[lo:hi]`; `lo == hi` inserts |
| `.len(a)` | Length |

The right side of an array range replacement `a[lo:hi] = right` must be an
array. A string is not split into elements; writing one is an error. To put a
single string in as one element, wrap it in `[...]` as a one-element array.

```
a = [1, 2, 3]
a[1:2] = "qwert"       /* error: an array slice can only be given an array */
a[1:2] = ["qwert"]     /* [1, "qwert", 3] — one element replaced by one string */
a[1:2] = [7, 8, 9]     /* [1, 7, 8, 9, 3] — one element replaced by three; the length changes */
a[1:2] = []            /* [1, 3] — the element is removed */
```

(Each line shows the result when written against `a = [1, 2, 3]`.)

Reading a name before it is assigned is an error, so a misspelling does not
silently read as 0.

## Strings

Besides integers and arrays, a value can be a string. A string is written
`"..."` and can be used anywhere: in an expression, assigned to a variable, as an
argument and as a return value. From a `binary_list` it is passed as in
`.call func1(10,"text")`.

A string is **a sequence of bytes**. The characters written in the source go in
as their UTF-8 bytes, so `"あ"` has length 3. Lengths and subscripts count bytes,
and both implementations give the same values.

| Written | Result |
|---|---|
| `"ab" + "cd"` | `"abcd"` (concatenation) |
| `"n=" + 7`, `7 + "!"` | `"n=7"`, `"7!"` (an integer is joined as signed decimal) |
| `"ab" * 3`, `3 * "ab"` | `"ababab"` (repetition; `""` for 0 or less) |
| `s == t`, `s != t` | Whether the contents are the same; a string never equals an integer |
| `s < t` and so on | Byte-wise lexicographic order; a string and an integer cannot be ordered (error) |
| `s[i]` | The value (0–255) of byte `i`; `0` when out of range or negative |
| `s[lo:hi]` | Substring, clamped like an array slice; `hi` is not included |
| `s[i] = v` | Rewrites byte `i`; `v` is an integer 0–255 or a one-byte string. Past the end, the string is extended with NUL (0) bytes |
| `s[lo:hi] = t` | Replaces the range with the string `t`; the length may change (`s[1:2] = "10000"` on `"abc"` gives `"a10000c"`). The bounds are clamped as for `s[lo:hi]`; `lo == hi` inserts |
| `.len(s)` | Number of bytes |
| `.str(v)` | An integer as a signed decimal string; a string is returned as is |
| `.chr(n)` | The one-byte string of value `n` (0–255) |
| `.int(s)` | Reads a string as an integer: surrounding blanks, `+` `-`, `0x` `0b` and `_` are accepted; anything else is an error |

```
.func label(n, s)
t = s + ":" + n           /* "loop:3" */
.emit(.len(t))
.emit(t)                  /* one word per byte */
.return t[0:1] * 2        /* "ll" */
.endfunc
```

- **Output is one word per byte.** Both `.emit(s)` and a string returned by a
  function called from `binary_list` output each byte as one word, in order.
- **Strings can be rewritten a byte at a time.** `s[i] = 65` and `s[i] = "A"`
  mean the same. A negative index, a value outside 0–255 and a string of two or
  more bytes are errors. To change the length, build a new string with `+` and
  `[lo:hi]`. Strings are passed as copies, so rewriting one never changes the
  caller's variable it was passed from, or a copy held in another variable.
- **A string can be an array element.** `a = ["ab", 1]` and `a[i] = "x"` are
  allowed and `a[i]` reads the string back. `.echo` prints such an array as
  `["ab", 1]`, quoting only the string elements.
- **Not for conditions or arithmetic.** `.if s .then`, `s - 1`, `-s` and the
  like are errors.
- **Escapes** are `\\`, `\"`, `\n` and `\t`; any other `\` is an error. Use
  `.chr(0)` for a NUL.
- A string may contain both `/*` and `::`. Inside `"..."` they are neither a
  comment nor a field separator (Technical_Manual section 3.1).
- The length limit is the same as for arrays, 1,048,576 bytes.

## Scope and nesting

Each call gets its own set of variables, and parameters are local to that call.

Functions may be defined inside functions. An inner function is visible to its
enclosing function, and a name resolves outward: itself, then its parent, and so
on to the top level. `.nonlocal` makes a name refer to a variable of an enclosing
call instead of a local one.

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

`.nonlocal` must appear before that name is otherwise used in the function. If no
enclosing call has the name, it is an error.

## Return values

`.return expr` returns a value. The caller receives it by writing
`var = .call name(args)`.

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

- **The value may be a number, an array or a string.** An array is passed as a copy, so
  changing it in the caller does not affect the callee's variable.
- **The target may be an array element.** `a[i] = .call f(x)` is allowed; the
  returned value must then be a number or a string.
- **Calling a function that returns nothing with `var = .call ...` is an error.**
  That covers both a valueless `.return` and a body that ends without reaching
  one.
- **`.call` may appear inside an expression.** `x = 1 + .call f(y)` and
  `.emit(.call f(1) + .call g(2))` are fine — anywhere a value is expected.
  A function called this way must return a value; it is an error if it does not.
- **`.return` never closes the body.** Only `.endfunc` does that; `.return` and
  `.return expr` may appear anywhere in the body — top level or nested inside
  `.if`/`.while`/`.for` — any number of times, as an early-exit statement.
- **The return value of a function called from `binary_list` becomes output.**
  A number is one word; an array is one word per element from index 0 (a
  string element one word per byte); a string is one word per byte. It
  follows whatever the function passed to `.emit`, so a function that only
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

```
.func mkarr(n)
a=[]
.for i in range(n)
a[i]=i*i
.next
.return a
.endfunc

.func use(n)
v = .call mkarr(n)
.emit(.len(v))
.emit(v[2])
.return
.endfunc
```

Returning early works as well.

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

## The boundary with the pattern layer

- **Arguments are pattern-layer expressions.** In `.call f(a,b)`, `a` and `b` mean
  the captured pattern variables. Anything writable in `binary_list` works —
  labels, `.equ`, `$.` — including forward-referenced labels. An array argument
  is written `[expr, expr, ...]`, a string argument `"..."`, and `.exp(variable)`
  passes the text a pattern variable captured, as a string. The bare name of a
  string symbol passes that string, and the bare name of an array symbol
  passes that array.
- **Variable namespaces are separate.** Mini-language variables have nothing to do
  with pattern variables or with `.setsym` symbols; pass what you need as
  an argument.
- **An argument derived from an undefined label arrives as 0,** so a sentinel
  value cannot blow up a loop count while instruction sizes are being measured in
  the first pass.
- **`.emit` outputs one word of `.bits` width** — one byte at the default 8, or
  one 12-bit word under `.bits::12`.
- **The number of words emitted is the instruction's length.** Emit the same count
  in both passes; a count that varies by pass will not let addresses settle.
- **`;` may be applied to `.call`.** `;.call f(a)` emits nothing when the call's
  whole output is a single word equal to 0 — that is how a prefix byte which is
  sometimes absent is written. `;;.call f(a)` runs the call and discards its
  output.
- **`;;element` outputs nothing.** Writing `;;` in front of a `binary_list`
  element evaluates it but emits no word. A `binary_list` of just `;;n` has
  length 0.

## Functions called while writing the ELF

Besides `.call` in a `binary_list`, two declarations have axx call a function
while it writes the `-o` ELF (Technical Manual section 3.7.10).

| Declaration | Arguments | Return value |
|---|---|---|
| `.elfencode::<type>::<function>` | (the field's value, the addend) | the new field written back under REL |
| `.elfrinfo::<function>` | (symbol index, type number) | the `r_info` of a relocation entry |

- Two arguments, and a number (not an array or a string) returned; anything else is an
  error.
- The addend may be negative. It arrives as a 256-bit two's complement value,
  so `>>` and `&` pick out the bits needed.
- `.emit` produces no output words here; only the return value is used.

```
.elfencode::hi16::hi16enc
.func hi16enc(f, a)
.return (f & 0xffff0000) | (((a + 0x8000) >> 16) & 0xffff)
.endfunc
```

## Runaway guards

The language is Turing complete, so a mistake in a pattern file could otherwise
stop the assembler from finishing. Exceeding any of these reports an error naming
the offending line.

| Cap | Value |
|---|---|
| Statements executed per `.call` | 4,000,000 |
| Call nesting | 128 |
| Words emitted per `.call` | 1,048,576 |
| Array length, string bytes | 1,048,576 |

Syntax errors are reported when the pattern file is read, run-time errors when
that instruction is assembled; both carry a file name and line number.

## Examples

A sieve, and an instruction whose encoding is a Collatz step count.

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

Recursion works too.

```
FIB !n :: .call fib(n)

.func fib(k)
.if k<2 .then
.emit(k)
.else
.call fib(k-1)
.call fib(k-2)
.endif
.return
.endfunc
```

With return values, the same recursion can build the value itself.

```
FIBV !n :: .call fibv(n)

.func fibn(k)
.if k<2 .then
.return k
.endif
p = .call fibn(k-1)
q = .call fibn(k-2)
.return p+q
.endfunc

.func fibv(n)
v = .call fibn(n)
.emit(v)
.return
.endfunc
```

```
fibv 10              -> 37
```
