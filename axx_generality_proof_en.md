# Proof of the Generality Proposition of axx

2026-11-20

## Introduction

With assumptions H1–H6 stated explicitly, the claim "axx can process any generic processor ISA" can be proved as a theorem about the axx specification. This document states that theorem and proves it.

The proposition comes from section 1.7 of the technical manual and section 14.1 of `axxsemantics.md`:

> For an ISA with an imperative assembly language whose mapping from assembly to machine code is one-to-one and a finite static transformation, axx can process that ISA's assembly.

The repository documents give the conditions and an outline of the construction. This document writes out the assumptions that the outline leaves implicit, and completes the proof.

**Approach.** The axx matcher and expression evaluator are treated as boxes that behave as specified. On that basis we show three things.

1. Per-line correctness: whichever pattern is chosen, the output equals the value of f (Lemma 2).
2. Computing power: the encoding of each form can always be written in the mini language (Lemma 1).
3. Global correctness: if pass 1 converges, the output of pass 2 equals f* (proof of the theorem).

The subject is `axx.py` and `caxx.c` in the axx repository (fygar256/axx, as of November 2026).

## 1. Notation and definitions

The encoding is a partial function from a line and an environment to a sequence of words.

| Symbol | Meaning |
| --- | --- |
| Line | The set of instruction lines of a source |
| σ ∈ Env | The environment: values of labels and `.equ`, and the location counter `$$` |
| W | The set of words {0, …, 2^w − 1}, with 1 ≤ w ≤ 64 |
| f | The encoding of the ISA, a partial function from Line × Env to W* |
| M_t | For an instruction field t of a pattern, the set of lines the axx matcher accepts |
| sp_t(ℓ) | For ℓ ∈ M_t, the tuple of spellings (s₁, …, s_k) the matcher captured |
| v_t(ℓ, σ) | Likewise, the tuple of values (v₁, …, v_k) the axx expression evaluator computed under σ |
| f*(S) | The values of f on the lines of source S, in line order, under the converged label table σ* |

The type of the encoding is:

```latex
f : \mathit{Line} \times \mathit{Env} \rightharpoonup W^{*}, \qquad W = \{0,1,\dots,2^{w}-1\},\ 1 \le w \le 64
```

The kind of capture (`!x`, `!!x`, `!F`, a lowercase symbol, `!Y` and so on) does not matter. A variable captured by any of them keeps both its value and its spelling (manual section 3.18).

## 2. Assumptions

The proof rests on six assumptions. H3 restates "static" and "finite" in axx's own terms; H1 and H2 are the assumptions the repository documents leave implicit.

| Assumption | Name | Content |
| --- | --- | --- |
| H1 | Lexical compatibility | Instruction lines do not clash with axx's source conventions: no `;` inside an instruction, a line is not read as a built-in directive (`.org` and so on) or as `name:`, and `!!` is not used |
| H2 | Coverage | There are finitely many instruction fields t₁, …, t_n, and dom f is contained in M_{t₁} ∪ … ∪ M_{t_n} |
| H3 | Determination by captures | For each i there is a computable partial function g_i satisfying the formula below |
| H4 | Width | Captured values fit in 256-bit two's complement, and the words f emits fit in w bits |
| H5 | Resources | Computing g_i stays within the mini language's limits (4,000,000 statements per call, arrays of 1,048,576 elements and so on). Not needed for an idealised axx without limits |
| H6 | Convergence | For source S, the pass 1 iteration reaches a state where the label table equals the previous one, within the iteration limit |

The formula of H3:

```latex
\forall \ell \in M_{t_i} \cap \operatorname{dom} f,\ \forall \sigma :\quad f(\ell,\sigma) = g_i\bigl(\mathit{sp}_{t_i}(\ell),\ v_{t_i}(\ell,\sigma),\ \sigma(\$\$)\bigr)
```

For each form, H3 covers every line that form accepts. This quantification is the heart of Lemma 2. Section 7 derives H3 from a simpler condition.

## 3. Theorem

**Theorem.** For every f satisfying H1–H5 there is a pattern file P_f with the following property. For every source S whose instruction lines all lie in dom f and for which H6 holds:

```latex
\mathrm{axx}(P_f,\ S,\ \texttt{-b}) \;=\; f^{*}(S) \;=\; f(\ell_1,\sigma^{*})\, f(\ell_2,\sigma^{*}) \cdots f(\ell_n,\sigma^{*})
```

Here σ* is the label table when pass 1 has converged; section 6 shows it is a consistent layout. The right-hand side is the concatenation of word sequences.

## 4. Lemma 1: the mini language can express every computable function

**Claim.** Every computable partial function g from tuples of byte strings and integers to W* can be written as a mini-language function G. Where g is undefined, G either does not halt or issues `.raise`.

**Proof.** Every computable function is computed by a Turing machine M with one tape that is infinite to the right; a two-way tape can be simulated by a one-way tape. Each part of M maps to the mini language as follows.

| Turing machine | Mini language (MINI.md) |
| --- | --- |
| Tape | Array t. A read out of range returns 0; a write out of range extends the array, filling with 0 |
| Head | Integer h |
| State | Integer q |
| Transition function δ | A finite chain of `.if q == … && t[h] == … .then` |
| Repeated steps | `.while(q != halting state)` |
| Input | Copy each byte s[i] of string s to the tape; integer arguments are copied as decimal strings via `.str()` |
| Output | After halting, build an array of words from the tape and `.return` it |

One step of M corresponds to the finitely many statements run in one turn of `.while`. If M halts, G halts and produces the same output from the same tape contents. If M does not halt, neither does G, and axx reports the line as an error at the resource limit. By H5, lines in dom f never reach the limit. ∎

A machine that adds 1 to a binary number was written with this mapping and run (section 8).

## 5. Lemma 2: per-line correctness (any chosen pattern will do)

**Construction.** Build P_f as follows.

1. Put `.bits::w` (with the byte order) at the top.
2. For each i, add one pattern line with an empty error field. Here x_j are the capture variables of t_i, and G_i is the function implementing g_i by Lemma 1.

```
t_i :: :: .call G_i(.exp(x₁),…,.exp(x_k), x₁,…,x_k, $$)
```

`.exp(x)` works for a variable captured by any kind of capture, and `$$` may be written as a `.call` argument (manual section 3.18, MINI.md).

**Claim.** When axx assembles ℓ ∈ dom f under environment σ, the output is f(ℓ, σ).

**Proof.**

1. By H1, ℓ is not treated as a comment or a built-in directive, so it goes to pattern matching.
2. By H2, the set of matching lines C = { i : ℓ ∈ M_{t_i} } is not empty.
3. `_match_line` in axx picks one p from C by specificity score. Which p is picked, and how ties are broken, are not used.
4. The error field is empty, so no error arises.
5. The output is the value of G_p. By Lemma 1 it equals the value of g_p, and since ℓ ∈ M_{t_p} ∩ dom f, it equals f(ℓ, σ) by H3.
6. By H4, no word is truncated.

Before the real evaluation, axx calls G_p once more in a trial run that only measures the length (`_assemble_best`). A mini-language function runs with a fresh set of variables on every call and keeps no state between calls. So both calls return the same value and the lengths agree. ∎

**Note.** The proof uses only that at least one pattern matches. The specificity score plays no part in correctness, so the step in the outline of `axxsemantics.md` that arranges the forms to be chosen uniquely by specificity is not needed.

## 6. Proof of the theorem

Consider a source S = ℓ₁, …, ℓ_n, including label definitions and `.equ` lines. When iteration r of pass 1 assembles line k, the label values that line sees are (`_pass1`):

- labels defined before line k: the value defined in this iteration;
- labels defined at or after line k: the value from the previous iteration (undefined in the first iteration, passed to the mini language as 0).

Call this environment σ_{r,k}.

### (a) The converged point is a consistent layout

By H6, in some iteration r the label table T_r equals the previous table T_{r−1}. Call it σ*.

1. axx rejects redefinition of a label, so a value defined in an iteration does not change within that iteration.
2. Hence both the current values of earlier labels and the previous values of later labels are σ*: for every k, σ_{r,k} = σ*.
3. By Lemma 2 the length of each line in iteration r is |f(ℓ_k, σ*)|. So the formula below holds for every label L, and σ* is a fixed point of the layout equation. The value of each `.equ` is likewise its expression evaluated under σ*.

```latex
\sigma^{*}(L) \;=\; \mathit{origin} + \sum_{k < \mathrm{pos}(L)} \bigl|\, f(\ell_k, \sigma^{*}) \,\bigr|
```

### (b) Pass 2 emits f*

Pass 2 starts with the label table T_r = σ*. By induction on the line number k, we show that the pass 2 environment σ_{2,k} equals σ*.

- Earlier labels: by the induction hypothesis, every line before k emitted the same length as in (a), so the values defined there equal σ*.
- Later labels: they are read from the table, which still holds σ*.

So by Lemma 2 the output of line k is f(ℓ_k, σ*). Every label address agrees with pass 1, so the drift check in axx (`_pass2`) passes. No error arises either, so the output file is written, and its contents are f(ℓ₁, σ*) ⋯ f(ℓ_n, σ*) = f*(S). ∎

## 7. Corollary and necessity of the assumptions

### Corollary: H6 holds automatically for fixed-length ISAs

**Claim.** Suppose the length |f(ℓ, σ)| of each line depends only on ℓ, not on σ. Build each G_i so that it emits the same number of words even for out-of-range values (pad with 0 after `.raise`). Then pass 1 converges in two iterations.

**Proof.** In iteration 1, lengths do not depend on values, so every address comes out right. Iteration 2 emits the same lengths, so the label table equals that of iteration 1. Two iterations are within the axx limit of 16. ∎

For fixed-length instruction sets such as RISC-V, MIPS, SPARC and PowerPC, H6 need not be checked separately.

### H6 cannot be dropped: an example with no consistent layout

Suppose one instruction sits at address 0, followed directly by label L. Let the encoding rule be "length 1 if L is even, length 2 if L is odd".

- With length 1, L = 1, which is odd: a contradiction.
- With length 2, L = 2, which is even: again a contradiction.

No consistent layout exists, so f*(S) itself is undefined and no assembler can produce a correct output. axx reports this case as oscillation and stops without writing output.

### Deriving H3 from a simpler condition

Take the condition "f depends only on the line with spaces removed and letters upper-cased". The axx matcher behaves as follows (`PatternMatcher.match`):

- a literal character matches one source character, ignoring case;
- spaces are skipped;
- the spelling of a capture is the corresponding part of the source with surrounding spaces and the stop character removed.

So concatenating the literals and the capture spellings in order gives the same normal form as the original line. g_i can compute f from that concatenated string, so H3 follows from the condition above.

There is one exception. Under the rule that a pattern `+` matches a source `-` (manual section 3.13), the reconstruction gives `+-5`. We additionally require f to treat `+-x` and `-x` alike.

## 8. Checks on the implementations

The behaviour of axx that the proof relies on was checked with both caxx (the C version) and paxx (the Python version). Every result was as expected, and the two implementations produced byte-identical output.

| What was checked | Input | Result |
| --- | --- | --- |
| Lemma 1: a Turing machine runs in the mini language | A machine that adds 1 to a binary number; `inc 1011`, `inc 111` | `1100`, `1000` |
| Spelling and value reach the function | `mov a,2+3` | Spelling `2+3` and value 5 were passed; output `aa 05` |
| Whitespace normalisation | `mov a , b` and `mov a,b` | Both `bb` |
| Lemma 2: any chosen pattern will do | Only `MOV A,!d`, versus that plus an overlapping `MOV A,5` | Byte-identical output |

The pattern file used to check Lemma 2 is below. Adding or removing the overlapping second line does not change the output.

```
MOV A,!d :: .call h("MOV A,",.exp(d),d)
MOV A,5  :: .call h("MOV A,","5",5)
.func h(a,b,v)
.return .call g(a+b, v)
.endfunc
.func g(s, v)
.if s == "MOV A,5" .then
.return [0xAA, 5]
.endif
.return [0xAA, v & 0xff]
.endfunc
```

## 9. Scope of the proof

Under H1–H6 the proposition holds as a theorem about the axx specification. Its core is two facts: a line can be rebuilt from its spellings, and the mini language is Turing complete.

- **Shown:** for every encoding f satisfying H1–H6, a pattern file exists that realises f exactly. The specificity score is not needed for correctness.
- **Taken as given:** the matcher and expression evaluator behave as specified. Freedom from implementation bugs is not proved; that is the job of the differential testing in `test1`.
- **To check per ISA:** H1 and H2, that is, whether the surface syntax avoids axx's conventions and is covered by axx's captures. An ISA where case changes meaning, or one that uses `;` inside instructions, fails here.
- **Implementation versus ideal:** real axx limits the mini language's resources, so strictly the scope is "ISAs whose encoding fits within those limits" (H5).

References: [fygar256/axx](https://github.com/fygar256/axx), `Technical_Manual.md` section 1.7, `axxsemantics.md` section 14.1, `mini_en.md`
