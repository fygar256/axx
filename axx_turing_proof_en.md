# Proof that axx as a whole is Turing complete

2026-11-25

## Summary

Result: axx as a whole is Turing complete. More strongly, one fixed pattern file, `utm.axx`, runs any Turing machine written on a single source line (universality).

There are three proofs, and any one of them is enough.

1. **A universal Turing machine in the mini language (`.func` / `.call`)** (Theorem 1, the main proof).
2. **A universal Turing machine in the source-side macro layer (`!def` / `!while`)** (Theorem 2).
3. **A universal Turing machine in the pattern-file macro layer** (Corollary 2.1). Proofs 2 and 3 share one macro library, `tm.inc`.

axx is also Turing complete when the pattern file is viewed as the program and the .s source file as its input (Theorems 3 and 4, section 5). Any Turing machine M can be written in a .axx file that outputs the result of applying M to the input written in the .s file. The input may sit on one line, or be spread over the whole file through the location counter `$$`.

Like every real computer, the axx implementation has runaway guards (4 million statements per `.call`, and others). This document therefore makes the limits explicit as a resource parameter Λ and considers the family axx_Λ. It shows that halting computations are reproduced exactly once Λ is large enough, and that non-halting computations end in an error with no output for every finite Λ. This is the standard meaning of Turing completeness.

The constructions were run on both caxx (the C version) and paxx (the Python version). For 500 randomly generated Turing machines, the output matched a reference simulator byte for byte (section 7).

Subject: [fygar256/axx](https://github.com/fygar256/axx) at commit `df463099` (2026-11-21). The document also completes the sketch of Lemma 1 in the existing `axx_generality_proof.md`, adding the universal machine, resource parameters and the non-halting case.

## 1. Scope: axx's structure and the properties the proof relies on

axx works in three layers: macro layer → pattern layer → mini language (README.md, axxsemantics.md section 3). The pattern layer is deliberately kept Turing incomplete so that matching always halts; computational power lives in the macro layer and the mini language (Technical_Manual.md section 10.3, axxsemantics.md section 12). Following that design, the proofs here put the computation in the mini language or the macro layer.

| Layer | When it runs | Tools for computation | Integers | Runaway guards in the implementation |
| --- | --- | --- | --- | --- |
| Pattern-file macros | Before the pattern file is read | `!def`, `!while`, `!if`, recursion, strings | paxx arbitrary precision, caxx int64 | 1,000,000 iterations per `!while`, recursion depth 200, 2,000,000 generated lines |
| Source macros | Before the source is assembled (each relaxation iteration) | Same | Same | Same |
| Pattern layer | Once per instruction line | Matching, expressions, `;`, `@@[]` | 256 bits | (matching is designed to halt) |
| Mini language | At a `.call` in `binary_list` | Assignment, `.while`, `.if`, recursion, growable arrays, strings | 256-bit two's complement | 4,000,000 statements per `.call`, nesting 128, array length 1,048,576, output 1,048,576 words |

The properties the proof uses, with the documents and code that support them, are listed below. The two implementations share one specification, and in the experiments here their outputs also matched byte for byte.

| Label | Property | Source |
| --- | --- | --- |
| P1 | Reading an array out of range, or at a negative index, returns 0 and leaves the array unchanged | MINI.md "Values and arrays", axx.py lines 6874–6877 |
| P2 | `a[i] = v` with i ≥ length pads with 0 and extends the array to length i+1 | MINI.md, axx.py `_store` (line 7008) |
| P3 | Sequential semantics of `.while`, `.if`, `.break`, assignment and `.call` (a condition is false only when it is 0) | MINI.md "Statements" and "Expressions and operators", axx.py `_exec` (line 7084) |
| P4 | `.exp(x)` passes the spelling that capture variable x picked up from the source, as a string | MINI.md, Technical_Manual.md section 3.18 |
| P5 | An array returned by a function called from `binary_list` becomes output, one element per word | MINI.md "Return values", axx.py around line 7420 |
| P6 | Each `.call` creates a new interpreter `MiniInterp` and keeps no state across calls | axx.py line 7411 |
| P7 | Exceeding a limit makes that line an error, and no output file is written | MINI.md "Runaway guards", axx.py `_tick` (line 7043), caxx.c line 10658 |
| P8 | Macro-layer `!while`, `!set`, `!if`, `!return`; `substr`, `len`, `int`, `str`; string `+` and `*`; expansion of `!{expr}` into body lines | MACRO.md, axx.py lines 10267, 10535, 10559 |

## 2. Definitions

**Turing machine.** Write M = (k, m, δ). States are 0, 1, …, k (1 is the start state, 0 the halting state); symbols are 0, 1, …, m−1 (0 is blank). δ is a partial function from (q, s) to (w, d, q′): write w, move left if d = 0 and right if d = 1, and enter state q′. The tape is infinite in both directions. The input x = x₀…x_{n−1} sits at addresses 0…n−1 and the head starts at address 0. M halts when q = 0 or when δ(q, s) is undefined. The output out(M, x) on halting is the symbol string from the leftmost to the rightmost non-blank cell. This class of machines is a standard model that computes every partial computable function.

**Encoding.** Write a sequence of integers a₁, …, a_r in decimal separated by `+` as ⟨a₁, …, a_r⟩ = `a1+a2+…+ar`. ⟨δ⟩ lists each rule (q, s) ↦ (w, d, q′) as the five numbers q, s, w, d, q′; ⟨x⟩ is the input (an empty input is `0`). The source line is src(M, x) = `TM ⟨δ⟩,⟨x⟩`.

**Resource parameters.** Collect the implementation's limits as Λ = (S, D, A, E, B): S is the number of statements per `.call`, D the call nesting, A the array and string length, E the number of output words, and B the integer width in bits. The real axx is Λ₀ = (4×10⁶, 128, 2²⁰, 2²⁰, 256). axx_Λ means axx with only these limits replaced by Λ. The values are constants in the code (`MAX_STEPS`, `_MINI_BITS`, and so on), so the family can be realised directly. Setting all of them to ∞ gives the idealisation axx_∞. Λ ≤ Λ′ is compared component by component.

**Meaning of Turing completeness.** Here, "axx is universal (and hence Turing complete)" means that there is a fixed pattern file U satisfying (U1) and (U2) below. Real computers and language implementations are called Turing complete in the same sense.

- **(U1) Halting computations are reproduced.** If M halts on x, there is a Λ* such that for every Λ with Λ* ≤ Λ (including ∞), axx_Λ(U, src(M, x), `-b`) writes exactly out(M, x).
- **(U2) Non-halting computations do not halt.** If M does not halt on x, axx_∞ does not halt. Moreover, for every Λ with finite S and a sufficient integer width (2^(B−2) > max(S, 10N), where N is the largest number in src), axx_Λ reports a resource error and writes no output file. The real Λ₀ meets this condition whenever N < 2²⁵⁰.

Given one universal machine, any partial computable function f can be computed on axx by choosing a machine M_f that computes f and supplying src(M_f, x). (U1) and (U2) are therefore a stronger claim than Turing completeness.

## 3. Theorem 1: a universal Turing machine in the mini language

**Theorem 1.** The pattern file U = `utm.axx` in Appendix A satisfies (U1) and (U2). Hence axx is Turing complete.

U consists of one pattern line and two functions.

```
TM !d,!x :: .call utm(.exp(d),.exp(x))
```

`nums(s)` turns a `+`-separated decimal string into an array of integers. `utm(d, x)` builds the rule table `rules` and the tape, runs the machine one step at a time, and returns the tape when it halts. The tape is held in two arrays: address p ≥ 0 is `rt[p]`, and address p < 0 is `lt[-p-1]`.

Below, r is the number of rules, t the number of steps until M halts, and [−ℓ, ρ] the smallest interval containing the input addresses and every address the head visits.

### Lemma 1.1 (reading the input)

The pattern `TM !d,!x` matches src(M, x), and `utm` receives the strings ⟨δ⟩ and ⟨x⟩. Moreover, `nums(⟨a₁,…,a_r⟩)` returns the array [a₁, …, a_r].

*Proof.* The line starts with `TM` and contains neither `;` nor `name:`, so it is neither a built-in directive nor a label and goes to pattern matching. `a1+a2+…` is a valid integer expression, so `!d` captures everything up to `,` and `!x` everything to the end of the line. By P4, `.exp` passes those spellings (the values of the expressions are not used). For `nums`, the following invariant holds before each iteration of the loop: "of the prefix read so far, the numbers closed by `+` are in a[0..n−1], and v is the value of the number not yet closed." A digit sets v ← 10v + digit; a `+` sets a[n] ← v by P2, preserving the invariant. At the end the last number is appended. If the integer width exceeds 10N there is no wraparound. ∎

### Lemma 1.2 (correctness of one step)

Write a configuration of M as C = (q, h, τ), where τ maps addresses to symbols. The variables represent C when the variables q and h equal the values in C and the following holds at every address p, where "read" includes the out-of-range 0 of P1.

```math
\tau(p) = \begin{cases} \mathrm{read}(rt,\ p) & (p \ge 0) \\ \mathrm{read}(lt,\ -p-1) & (p < 0) \end{cases}
```

**Claim.** If the variables represent C_j at the start of iteration j of the outer `.while(q!=0)`, and δ is defined at C_j, then the variables represent C_{j+1} at the end of that iteration.

*Proof.*

1. j = 0: `rt[i] = inp[i]` places the input at addresses 0…n−1, and every other address is 0 (blank) by P1. With q = 1 and h = 0 the variables represent C₀.
2. Read: the branch on `h>=0` gives c = τ(h).
3. Rule lookup: the inner loop runs k = 0, 1, …, puts the smallest k with `rules[5k] == q` and `rules[5k+1] == c` into f, and `.break`s. If there is none, f = −1. Since ⟨δ⟩ is the table of a function δ, at most one entry matches, and if f ≥ 0 then (rules[5f+2], rules[5f+3], rules[5f+4]) = δ(q, c).
4. Write: w goes into `rt[h]` or `lt[-h-1]`. By P2, reads at other addresses do not change and any extended part is 0, so the arrays represent τ[h ↦ w].
5. Move and state: h ← h−1 if d = 0, otherwise h ← h+1; then q ← q′. This is exactly one step of M. Since |h| ≤ t, there is no wraparound when the integer width is sufficient. ∎

### Lemma 1.3 (correspondence of halting)

The outer loop exits after j iterations if and only if C_j is a halting configuration, that is, q = 0 or δ(q, τ(h)) is undefined.

*Proof.* The loop has only two exits: the condition `q!=0` becoming false, and the `.break` taken when f < 0 (P3). By step 3 of Lemma 1.2, the latter coincides exactly with δ being undefined. ∎

### Lemma 1.4 (output)

If M halts after t steps, the return value of `utm` equals out(M, x).

*Proof.* By Lemmas 1.2 and 1.3, when the loop exits the arrays represent the tape of the halting configuration C_t. `tape` lists lt in reverse followed by rt, so it holds addresses −|lt| through |rt|−1 in order. Everything outside this interval is blank. Dropping the 0s at both ends leaves the cells from the leftmost to the rightmost non-blank cell. ∎

### Proof of Theorem 1

**(U1).** Suppose M halts on x after t steps. One iteration of the outer loop executes at most 11 + 3r statements. Taking the following Λ* keeps every limit out of reach.

| Component | Sufficient value |
| --- | --- |
| S (statements) | (11 + 3r)(t + 1) + c·(｜⟨δ⟩｜ + ｜⟨x⟩｜ + ℓ + ρ + 1), c a small constant |
| D (nesting) | 3 (`.call utm` → `nums`) |
| A (array length) | max(5r, ℓ + ρ + 1) + 1 |
| E (output words) | ℓ + ρ + 1 |
| B (integer width) | 2^(B−2) > max(t, 10N) |

By Lemmas 1.1–1.4, `.call utm(…)` returns the array out(M, x), and by P5 it becomes the line's word sequence (with the default `.bits::8`, symbols must be below 256; m = 2 is enough for universality). The line references no labels, and by P6 it returns the same value however many times it is called. The line's length therefore does not change between iterations, and pass 1 converges in two iterations (the same argument as the corollary in section 7 of axx_generality_proof.md). Pass 2 emits the same words, and with no errors the `-b` file is exactly out(M, x). The same argument holds for any Λ ≥ Λ*.

**(U2).** Suppose M does not halt on x. By Lemmas 1.2 and 1.3 the outer loop never exits, and each iteration executes at least one statement.

- In axx_∞, the first `.call` in pass 1 never returns, so axx_∞ does not halt.
- If S is finite, `_tick` raises an exception once S statements are exceeded (P7). If the array length exceeds A first, that limit raises the exception instead. Meanwhile |h| ≤ S, and the condition 2^(B−2) > max(S, 10N) rules out wraparound, so Lemma 1.2 still applies; no "false halt" can occur. The length-measuring trial in pass 1 suppresses diagnostics, but pass 2 reports the same exception, and axx ends without writing an output file. ∎

Since the universal machine U exists, every partial computable function f can be computed on axx with the one-line source src(M_f, x). This establishes that axx is Turing complete.

## 4. Theorem 2: independent proof through the macro layer

**Theorem 2.** The macro layer alone makes axx universal. Include the library `tm.inc` from Appendix B and write the two lines below in the source; then the same properties as (U1) and (U2) hold for any machine M with at most 10 symbols. Any pattern file will do (the experiments used the single line `NOP :: 0x00`).

```
!include "tm.inc"
!tm_db("⟨δ⟩", "⟨x⟩")
```

The number of states is unbounded, and Turing machines restricted to two symbols still compute every computable function (Shannon). Limiting the symbols to 0–9 therefore keeps universality.

**Construction.** Macro-layer values are integers and strings; there are no arrays. So the tape and the rule table are both held as strings (P8).

1. Rule table: find the largest number of digits W among the numbers in ⟨δ⟩, zero-pad each number to W digits and concatenate them (`substr("0" * W + f, len(f), W)`). Field i is read with `int(substr(T, i*W, W), 10)`. W comes from the input, so there is no bound on the number of states.
2. Tape: a digit string `tape`, one character per cell, and a head h. A write is `substr(tape,0,h) + str(w) + substr(tape,h+1)`. Moving past the right end appends `"0"`; moving past the left end prepends `"0"` and keeps h = 0.
3. Execution: inside `!while q != 0`, look up the rule from the start of the table, and `!break` if there is none.
4. Output: return the string with the `0`s at both ends removed (`tm_eval`). `tm_db` generates one body line `.db !{…}` per cell, and the assembler emits each as one word.

*Proof.* It has the same shape as Theorem 1. The invariant is: "at the start of iteration j of the outer `!while`, for some integer o (the number of `0`s prepended on the left), q = q_j, h − o = h_j, character i of tape = τ_j(i − o), and everything outside tape is blank." Prepending `"0" + tape` at the left end increases o by 1 and leaves h unchanged, matching a move to h_j − 1. Appending `tape + "0"` at the right end only makes one more blank cell visible. Rule lookup, the correspondence of halting and the output follow by the same arguments as Lemmas 1.2–1.4. The macros reference no labels, so they expand to the same text in every relaxation iteration and pass 1 converges.

For resources, (U1) holds once the iteration count I of a single `!while`, the number of generated lines and the integer range are sufficient. Here the outer loop runs t times, the inner one r times, and the generated lines number ℓ + ρ + 1. paxx integers are arbitrary precision, so no range condition is needed; for caxx, state numbers and lengths must stay below 2⁶³. For (U2), a non-halting machine drives the outer `!while` past I iterations. That produces the error `'!while' ran more than 1000000 iterations`, and no output file is written (axx.py lines 10267–10275). With I = ∞ the expansion never ends, and axx does not halt. ∎

**Corollary 2.1 (pattern-file macros).** Writing the two lines below in the pattern file, and making the source the single line `RESULT`, gives the same properties.

```
!include "tm.inc"
RESULT :: !{tm_list("⟨δ⟩", "⟨x⟩")}
```

*Proof.* According to MACRO.md, pattern-file macros have the same syntax, built-in functions and runaway guards as source macros; they differ only in namespace, comment form and activation condition. `tm.inc` contains no comments, so both sides read it as is. `tm_list` formats the output comma-separated, such as `2,2,1,1` (`;;0` when empty), producing the pattern line `RESULT :: 2,2,1,1`. The source line `RESULT` emits that word sequence. In the non-halting case, the same `!while` limit error prevents any output from being written (confirmed in section 7). ∎

## 5. Theorems 3 and 4: Turing completeness with the pattern file as the program and the .s file as the input

Result: the code of a .axx pattern file is Turing complete as a program whose input is a .s source file. For any Turing machine M there is a pattern file P_M that performs the same computation as M and outputs the result of applying M to the input written in the .s file. The input may be on one line (Theorem 3) or split over several lines of the whole file (Theorem 4).

The difference from Theorem 1 is the division of roles. In Theorem 1 the machine description ⟨δ⟩ was also written in the .s file. Here the machine (the program) is written only in the .axx file, and the .s file holds only the input data.

### Definition

A pattern file P defines a partial function F_P that maps a .s file S to the output axx(P, S, `-b`). "The code of a .axx file is Turing complete with respect to .s files" means that for every Turing machine M there is a P_M meeting the conditions below. The rule enc that writes an input word w as a .s file and the rule dec that reads the output back are fixed computable functions that do not depend on M.

- If M halts on w, then dec(F_{P_M}(enc(w))) = out(M, w) for sufficiently large Λ.
- If M does not halt on w, axx_∞ does not halt, and axx_Λ with finite S ends with a resource error and no output (under the same conditions as (U2)).

Moreover, building P_M from M is a simple embedding of a string and is computable: there is a compiler from Turing machines to .axx files.

### Theorem 3 (one input per line)

**Construction.** P_M is the functions `nums` and `utm` of Appendix A plus the line below, where ⟨δ⟩ is M's rule table embedded as a string literal.

```
IN !x :: .call utm("⟨δ⟩",.exp(x))
```

enc(w) is the single line `IN ⟨w⟩`, and dec is the identity.

**Theorem 3.** P_M meets the definition above. Moreover, if the .s file consists of n lines `IN ⟨w₁⟩`, …, `IN ⟨w_n⟩` and M halts on each of them, the output is the concatenation out(M, w₁) out(M, w₂) ⋯ out(M, w_n). In this case P_M acts as a program that applies M to every line of the .s file.

*Proof.* According to MINI.md, a string written as `"..."` in a `.call` argument is passed as a string as is. So `utm` receives the same arguments ⟨δ⟩ and ⟨w⟩ as in Theorem 1, and Lemmas 1.1–1.4 apply unchanged. No line reads labels or `$$`, and by P6 no state survives across calls, so the output of line k is determined by out(M, w_k) alone. Line lengths do not change between iterations, pass 1 converges, and pass 2 writes each line's output in line order. If some line does not halt, that line becomes an error by the same argument as (U2) of Theorem 1, and no output is written. ∎

### A channel for information across lines: the location counter `$$`

To treat the whole file as one input, the contents of earlier lines must reach later lines. Each `.call` runs in a fresh interpreter (P6). Experiments also confirmed that a value stored with the pattern layer's `:=` does not survive to the next line (`z` is 0 on the line after `SET 7`). On the other hand, the mini language can read `$$`, the address of the current line (MINI.md "Delegation to the main expression evaluator"). `$$` is the total number of words emitted by the earlier lines, so information can be sent forward through "the length of the output". Theorem 4 uses this channel.

### Theorem 4 (the whole .s file is the input)

Let the symbols be 0, …, b−1 (b ≥ 2). The input w = w₁…w_n is written as a .s file of n lines `D w_k` followed by one final line `END`. Call this enc(w).

**Construction.** P_M is the functions of Appendix A plus the two lines and two functions below (Appendix C has the full text for b = 3).

```
D !v :: v<0;1,v>2;1 :: .call acc($$,v)
END :: .call fin($$)
```

- `acc(a, v)` emits a(b−1) + v + 1 zeros.
- `fin(a)` reads a as a bijective base-b numeral (repeating d = ((a−1) mod b) + 1, a ← (a−d)/b until a = 0), calls `utm("⟨δ⟩", …)` on the resulting sequence, and returns the marker 0xFF followed by that result.

Define the bijective base-b value of the prefix w₁…w_k as follows.

```math
N_0 = 0, \qquad N_k = b \cdot N_{k-1} + (w_k + 1) \quad (1 \le k \le n)
```

**Theorem 4.** If M halts on w, then for sufficiently large Λ the output is the word sequence below, and dec (discard everything up to the first 0xFF) returns out(M, w). If M does not halt, the `END` line becomes an error just as in (U2) of Theorem 1.

```math
F_{P_M}(\mathrm{enc}(w)) = 0^{N_n} \cdot \texttt{0xFF} \cdot \mathrm{out}(M, w)
```

*Proof.*

1. **`$$` carries the prefix.** By induction on k, `$$` on line `D w_{k+1}` is N_k. For k = 0 it is the start of the file, so 0 = N₀. The line emits N_k(b−1) + w_{k+1} + 1 words (P2, P5), so `$$` on the next line is N_k + N_k(b−1) + w_{k+1} + 1 = N_{k+1}. Hence `$$` on `END` is N_n.
2. **It can be decoded.** In bijective base b, digit strings over 1, …, b correspond one to one with non-negative integers. The digits of N_n are w₁+1, …, w_n+1 from the most significant, so the loop in `fin` extracts w_n, …, w₁ starting from the last digit and reverses them to build ⟨w⟩. If n = 0, N₀ = 0, the loop does not run, and the empty input `0` is passed.
3. **Computation and output.** By Lemmas 1.1–1.4, `utm` returns out(M, w), and `r[0:0]=[0xff]` puts the marker at the front. The marker differs both from the symbols (< b ≤ 255) and from the padding zeros, so dec is well defined.
4. **Convergence.** No line references labels, and each line's length depends only on `$$`, which is fixed by the lines before it. So every address is correct in the first iteration of pass 1, and the second iteration builds the same table. Pass 2 writes the word sequence above. ∎

**On the amount of padding.** The padding is N_n < b^(n+1) words, which grows exponentially with the input length. This is a property of the `$$` channel: for `END` to tell apart the b^n inputs of length n from `$$` alone, `$$` must take at least b^n distinct values. So for some input `$$` ≥ b^n − 1, meaning the earlier lines emitted that many words. The construction works for inputs of any length in the idealised axx_∞. With the real Λ₀, the 2²⁰ limits on array length and output limit inputs to roughly 11 lines for b = 3. For large inputs in practice, passing them on one line as in Theorem 3 works well.

**Checks.** P_M with M = "add 1 to a binary number" was run on both implementations. caxx and paxx produced byte-identical output.

| Theorem | Contents of the .s file | Output |
| --- | --- | --- |
| 3 | Three lines `IN 2+1+2+2`, `IN 2+2+2`, `IN 1` | `2 2 1 1 │ 2 1 1 1 │ 2` (1100, 1000, 1) |
| 4 | `D 2`, `D 1`, `D 2`, `D 2`, `END` | 111 zeros (= N₄), 0xFF, `2 2 1 1` |
| 4 | Random inputs of length 0–9 (40 on caxx, 10 on paxx) | Padding length N_n and result match a reference implementation in every case |

**Corollary 5 (computational power of the pattern-file language).** By Theorems 3 and 4, the ".s to output" transformations that can be written in .axx include every computable function. Conversely, axx is itself a program, so they go no further. The computation is carried by the mini language called through `.call`, while pattern matching sticks to capturing the input and passing it on. This is exactly axx's design: a declarative core whose matching always halts, plus a layer for computation that is called by name.

## 6. Corollaries and context

**Corollary 3 (Turing equivalence).** The functions computed by axx_∞ are exactly the partial computable functions. Theorem 1 shows that they include all of them; conversely, axx_∞ is just axx.py with its limits removed, so it cannot go beyond them.

**Corollary 4 (halting problem).** Whether axx_∞(P, S) halts for a pattern file P and source S is undecidable, even with P fixed to U. By Theorem 1, deciding it would decide the halting problem for Turing machines.

This corollary shows that axx's runaway guards are well founded in theory as well. No general method can tell infinite loops apart in advance, so stopping at a limit on statements or iterations, naming the offending line and writing no output is a sound choice for emitting only correct binaries.

**Relation to the pattern layer.** All of the computation here runs in `.call` and the macro layer; pattern matching itself is not used. This matches axx's design exactly: keep matching as a declarative core that always halts, and hand computation to a separate layer that is called by name (Technical_Manual.md section 10.3, axxsemantics.md section 12). axx as a whole is Turing complete, and that power acts only where it is explicitly invoked.

**Difference from the Brainfuck demos.** `patfile/bf.axx` and `bfsh/` show that axx can generate programs in a Turing-complete language and interpreters for it. The theorems here show something separate: axx itself can carry out any computation while it assembles.

**Relation to the existing generality proof.** Lemma 1 of `axx_generality_proof.md` corresponds to the (U1) part of Theorem 1. Because the construction here is a universal one with a single fixed pattern file, the G_i of the generality theorem can also be built uniformly, as "call `utm` with the rule table of the corresponding machine as an argument".

## 7. Checks on the implementations

Every construction was run on caxx (built with `make caxx`) and paxx (`python3 axx.py`, Python 3.13), with the expected results. All outputs of the two implementations matched byte for byte. The repository's `test1` was not run.

| What was checked | Input | Result (caxx and paxx) |
| --- | --- | --- |
| Theorem 1: add 1 to a binary number | 1011 (symbol 1 = "0", 2 = "1") | `02 02 01 01` (1100) |
| Theorem 1: 4-state busy beaver | Blank tape | `1 0 1×12` (13 ones, 107 steps) |
| Theorem 1: 15-state machine (two-digit state numbers) | Blank tape | 15 ones |
| Theorem 1: random machines | 300 (1–5 states, 2–4 symbols) and 200 (1–15 states) | All match a Python reference simulator |
| Theorem 1 (U2): a non-halting machine | Shuttles between two cells forever | `mini language ran more than 4000000 statements`, no output file |
| Theorem 2: source macros | The 1011 and busy-beaver cases above, the 15-state machine, 500 random machines | Same bytes as Theorem 1 |
| Theorem 2 (U2) | The same shuttling machine | `'!while' ran more than 1000000 iterations`, no output file |
| Corollary 2.1: pattern-file macros | 1011 and the busy beaver | Same bytes as Theorem 1 |
| Corollary 2.1 (U2) | The same shuttling machine (caxx) | `!while` limit error, no output file |

Example run (Theorem 1):

```
$ cat t1.s
TM 1+1+1+1+1+1+2+2+1+1+1+0+0+0+2+2+2+1+0+2+2+1+2+0+0+2+0+2+0+0,2+1+2+2
$ caxx utm.axx t1.s -b o.bin && od -An -tu1 o.bin
raw: wrote o.bin (4 bytes)
   2   2   1   1
```

For reference, a non-halting machine reached the limit in about 3.4 s on caxx and 59 s on paxx with the mini-language version, and in about 13 s on caxx and 8 min on paxx with the macro version. For a machine that keeps moving right so that the tape keeps growing, caxx took more than 5 minutes to reach the limit, so that measurement was stopped partway. This does not affect the conclusion of the proof.

## Appendix A: utm.axx (universal Turing machine in the mini language)

In a pattern file, a comment runs from `/*` to the end of the line. No comment lines are placed inside `.func` bodies.

```
/* utm.axx -- a universal Turing machine in the axx mini language
/*
/* One source line:  TM <rules>,<input>
/*   <rules>  quintuples q+s+w+m+n joined with '+'
/*            in state q reading symbol s: write w, move left if m=0 or right if m=1, go to state n
/*            start state 1, halting state 0, symbol 0 is blank; it also halts when (q,s) has no rule
/*   <input>  symbols joined with '+' (the head starts on the first symbol); 0 for a blank tape
/* Output:    the tape on halting, from the leftmost to the rightmost non-blank cell (one word per cell)

TM !d,!x :: .call utm(.exp(d),.exp(x))

/* "12+0+7" -> [12, 0, 7]
.func nums(s)
a=[]
n=0
v=0
i=0
.while(i<.len(s))
c=s[i]
.if c>=48 && c<=57 .then
v=v*10+(c-48)
.elif c==43 .then
a[n]=v
n=n+1
v=0
.else
.raise 1
.return a
.endif
i=i+1
.endwhile
a[n]=v
.return a
.endfunc

.func utm(d,x)
rules=.call nums(d)
inp=.call nums(x)
nr=.len(rules)/5
rt=[]
lt=[]
.for i in range(.len(inp))
rt[i]=inp[i]
.next
q=1
h=0
.while(q!=0)
.if h>=0 .then
c=rt[h]
.else
c=lt[-h-1]
.endif
f=-1
k=0
.while(k<nr)
.if rules[5*k]==q && rules[5*k+1]==c .then
f=k
.break
.endif
k=k+1
.endwhile
.if f<0 .then
.break
.endif
.if h>=0 .then
rt[h]=rules[5*f+2]
.else
lt[-h-1]=rules[5*f+2]
.endif
.if rules[5*f+3]==0 .then
h=h-1
.else
h=h+1
.endif
q=rules[5*f+4]
.endwhile
tape=[]
n=0
j=.len(lt)-1
.while(j>=0)
tape[n]=lt[j]
n=n+1
j=j-1
.endwhile
.for i in range(.len(rt))
tape[n]=rt[i]
n=n+1
.next
a=0
.while(a<n && tape[a]==0)
a=a+1
.endwhile
b=n
.while(b>a && tape[b-1]==0)
b=b-1
.endwhile
.return tape[a:b]
.endfunc
```

## Appendix B: tm.inc (universal Turing machine in the macro layer)

The file contains no comments, so `!include "tm.inc"` works on both the source side and the pattern side. The base is written explicitly as `int(…, 10)` because the default base 0 cannot read zero-padded numbers such as `"012"`.

```
!def tm_eval(rules, inp) {
!local W = 1
!local cur = 0
!local i = 0
!while i < len(rules) {
!if substr(rules, i, 1) == "+" !then {
!set cur = 0
} !else {
!set cur = cur + 1
!if cur > W !then {
!set W = cur
}
}
!set i = i + 1
}
!local T = ""
!local f = ""
!set i = 0
!while i <= len(rules) {
!if i == len(rules) || substr(rules, i, 1) == "+" !then {
!set T = T + substr("0" * W + f, len(f), W)
!set f = ""
} !else {
!set f = f + substr(rules, i, 1)
}
!set i = i + 1
}
!local tape = ""
!set i = 0
!while i < len(inp) {
!if substr(inp, i, 1) != "+" !then {
!set tape = tape + substr(inp, i, 1)
}
!set i = i + 1
}
!if len(tape) == 0 !then {
!set tape = "0"
}
!local n = len(T) / (5 * W)
!local q = 1
!local h = 0
!local c = 0
!local k = 0
!local w = 0
!while q != 0 {
!set c = int(substr(tape, h, 1), 10)
!set f = -1
!set k = 0
!while k < n {
!if int(substr(T, 5 * k * W, W), 10) == q && int(substr(T, (5 * k + 1) * W, W), 10) == c !then {
!set f = k
!break
}
!set k = k + 1
}
!if f < 0 !then {
!break
}
!set w = int(substr(T, (5 * f + 2) * W, W), 10)
!if w > 9 !then {
!error "tm: symbol must be 0..9"
}
!set tape = substr(tape, 0, h) + str(w) + substr(tape, h + 1)
!if int(substr(T, (5 * f + 3) * W, W), 10) == 0 !then {
!if h == 0 !then {
!set tape = "0" + tape
} !else {
!set h = h - 1
}
} !else {
!set h = h + 1
!if h == len(tape) !then {
!set tape = tape + "0"
}
}
!set q = int(substr(T, (5 * f + 4) * W, W), 10)
}
!local a = 0
!while a < len(tape) && substr(tape, a, 1) == "0" {
!set a = a + 1
}
!local b = len(tape)
!while b > a && substr(tape, b - 1, 1) == "0" {
!set b = b - 1
}
!return substr(tape, a, b - a)
}
!def tm_db(rules, inp) {
!local t = tm_eval(rules, inp)
!local i = 0
!while i < len(t) {
        .db !{int(substr(t, i, 1), 10)}
!set i = i + 1
}
}
!def tm_list(rules, inp) {
!local t = tm_eval(rules, inp)
!local s = ""
!local i = 0
!while i < len(t) {
!if i > 0 !then {
!set s = s + ","
}
!set s = s + substr(t, i, 1)
!set i = i + 1
}
!if len(s) == 0 !then {
!set s = ";;0"
}
!return s
}
```

## Appendix C: inc_file.axx (P_M for Theorem 4, M = add 1 to a binary number)

Only the beginning is shown; the rest is identical to Appendix A from `.func nums` onward. `inc_line.axx` for Theorem 3 replaces these two pattern lines and `acc`/`fin` with the single line `IN !x :: .call utm("…",.exp(x))`.

```
/* P_M for M = binary increment, reading the whole source file through $$
/* each line "D v" (v = 0..2) appends one symbol; the last line "END" runs M
D !v :: v<0;1,v>2;1 :: .call acc($$,v)
END :: .call fin($$)

.func acc(a,v)
z=[]
z[a*2+v]=0
.return z
.endfunc

.func fin(a)
ds=[]
n=0
.while(a>0)
d=(a-1)%3+1
ds[n]=d-1
n=n+1
a=(a-d)/3
.endwhile
inp=""
j=n-1
.while(j>=0)
.if j<n-1 .then
inp=inp+"+"
.endif
inp=inp+ds[j]
j=j-1
.endwhile
.if n==0 .then
inp="0"
.endif
r=.call utm("1+1+1+1+1+1+2+2+1+1+1+0+0+0+2+2+2+1+0+2+2+1+2+0+0+2+0+2+0+0",inp)
r[0:0]=[0xff]
.return r
.endfunc
```

## Sources

- [fygar256/axx](https://github.com/fygar256/axx) (commit df463099: `README.md`, `MINI.md`, `MACRO.md`, `Technical_Manual.md`, `axxsemantics.md`, `axx_generality_proof.md`, `axx.py`, `caxx.c`)
