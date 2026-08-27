# axx General Assembler の表示的意味論

## ― 自由構文パターン言語から機械語生成への意味付け ―

### 要旨

本稿では、fygar256 による **axx General Assembler** を、プログラム意味論、とりわけ**表示的意味論（denotational semantics）**の観点から形式化する。

axx は、特定のプロセッサ向けに専用アセンブラを実装する方式ではなく、プロセッサ固有の命令体系を外部のパターンファイルに記述し、共通のアセンブルエンジンによってその記述を解釈する。

axx の基本的なパターンは、

**instruction :: error_patterns :: binary_list**

という構造を持つ。

したがって、axx の本質は、

> **アセンブリ言語の構文と、それに対応する機械語生成規則を、宣言的なパターンとして記述し、その意味を共通エンジンによって評価すること**

にある。

本稿では、この構造を表示的意味論として、

**Assembly Source → Pattern Matching → Environment → Binary → Object**

という意味付け関数として定式化する。

また、現行版に存在するラベル、セクション、relocation、可変長命令、relaxation についても意味論的に位置付ける。

---

# 1. はじめに

通常のアセンブラは、特定の ISA（命令セットアーキテクチャ）を前提として設計される。

例えば x86-64 アセンブラで、

```text
mov rax, rbx
```

を処理する場合、

「mov という命令は何か」

「rax はどのレジスタ番号か」

「どの opcode を生成するか」

「ModRM はどう構成するか」

といった知識がアセンブラ本体に組み込まれている。

これに対して axx は、この構造を逆転させる。

axx のアセンブルエンジン自身は特定 ISA の命令体系を知る必要がなく、ISA 固有の情報をパターンファイルに記述する。

したがって、概念的には、

**axx = 汎用アセンブルエンジン ＋ ISA パターン**

となる。

例えば、

```text
RET :: 0xc3
```

というパターンは、

```text
RET
```

というアセンブリ表現に対して、

```text
0xc3
```

という機械語を対応させる。

この構造を意味論的に見ると、パターンファイルそのものが**アセンブリ言語の意味を定義する仕様記述**になっている。

---

# 2. axx の意味論

表示的意味論では、プログラムに数学的対象を対応させる。

通常、

**⟦P⟧**

という記法によって、プログラム P の意味を表す。

axx の最も単純なモデルなら、

**⟦S⟧ₚ = B**

と表現できる。

ここで、

* S = アセンブリソース
* P = プロセッサパターン
* B = 生成された機械語

である。

しかし、実際の axx は単純な文字列変換ではない。

ラベル、セクション、location counter、relocation、alignment、relaxation などを扱うため、より適切には、

**⟦S⟧ₚ : State → State**

という状態変換として考える必要がある。

---

# 3. アセンブラ状態

axx の状態を、概念的に次のように定義する。

**State = (ρ, λ, pc, Γ, Ω, R, E)**

各要素は以下を意味する。

| 記号 | 意味               |
| -- | ---------------- |
| ρ  | パターン変数の環境        |
| λ  | ラベル環境            |
| pc | location counter |
| Γ  | セクション状態          |
| Ω  | 生成されたオブジェクト      |
| R  | relocation 情報    |
| E  | エラー・診断状態         |

特に重要なのがラベル環境 λ である。

例えば、

```text
foo:
```

というラベルがアドレス 0x100 に存在するなら、

**λ(foo) = 0x100**

となる。

---

# 4. パターンの意味

axx のパターンを、

**p = (I, E, B)**

とする。

ここで、

* I = instruction pattern
* E = error pattern
* B = binary_list

である。

例えば、

```text
ADD A,R!n :: n>7;5 :: n|0x68
```

というパターンを考える。

これは、

```text
instruction = ADD A,R!n
error pattern = n>7;5
binary list = n|0x68
```

という三つの部分から構成される。

したがって、パターンの意味は概念的に、

**Pattern × Source × Environment → Binary または Error**

という関数になる。

---

# 5. instruction pattern の意味

## 5.1 文字列

パターン中のリテラル文字は、入力アセンブリの対応する文字と照合される。

例えば、

```text
RET
```

というパターンに、

```text
RET
```

という入力が与えられれば一致する。

つまり、

**match("RET", "RET") = true**

である。

---

# 6. パターン変数

axx の特徴的な機構がパターン変数である。

例えば、

```text
MOV r,!d
```

というパターンでは、入力から `r` や `d` に対応する値を取り出すことができる。

概念的には、

```text
MOV rax,10
```

に対して、

```text
r = rax
d = 10
```

という環境が構築される。

この環境を ρ とすると、

**ρ(r) = rax**

**ρ(d) = 10**

となる。

したがって axx のパターン照合は、

**入力文字列 → 変数環境**

という意味を持つ。

これは通常のコンパイラの字句解析・構文解析とは異なる重要な特徴である。

---

# 7. 式の意味論

axx の式は、整数演算、ビット演算、比較などを表現できる。

式 e の意味を、

**⟦e⟧ρ,λ**

とする。

例えば、

```text
n|0x68
```

なら、

**⟦n|0x68⟧ρ = ρ(n) OR 0x68**

となる。

`n = 1` なら、

```text
1 OR 0x68 = 0x69
```

となる。

したがって、

```text
ADD A,R!n :: n>7;5 :: n|0x68
```

に対して、

```text
ADD A,R1
```

を入力すると、

```text
n = 1
```

なので、

```text
1 | 0x68 = 0x69
```

が生成される。

---

# 8. error pattern の意味

error pattern は、環境に対する**述語**として考えることができる。

例えば、

```text
n>7;5
```

は概念的には、

**E(n) = true ならエラーコード 5**

という意味を持つ。

したがってパターン全体は、

1. instruction pattern が一致する
2. 変数環境を得る
3. error pattern を評価する
4. エラーならエラーを生成する
5. そうでなければ binary_list を評価する

という意味を持つ。

---

# 9. binary_list の意味論

axx の機械語生成部分が binary_list である。

binary_list を、

**B = b₁, b₂, …, bₙ**

とする。

各要素を環境のもとで評価すると、

**⟦B⟧ρ = bytes(⟦b₁⟧ρ, …, ⟦bₙ⟧ρ)**

となる。

例えば、

```text
RET :: 0xc3
```

では、

**⟦0xc3⟧ = 0xc3**

なので、

```text
RET
```

の意味は、

```text
[c3]
```

という1バイトの機械語となる。

---

# 10. 条件付き出力

axx の binary_list には、値が 0 の場合に出力を抑止する `;` 修飾子がある。

概念的には、

```text
;e
```

を、

* e が 0 → 空列
* e が 0 以外 → e を出力

と解釈できる。

つまり、

**⟦;e⟧ = ε（e = 0 の場合）**

**⟦;e⟧ = [⟦e⟧]（e ≠ 0 の場合）**

となる。

この仕組みは、可変長命令の記述に利用できる。

---

# 11. optional group

axx には optional group も存在する。

例えば、

```text
INC (IX[[+!d]])
```

のようなパターンでは、

```text
INC (IX)
```

と、

```text
INC (IX+0x12)
```

の両方を表現できる。

意味論的には、

**⟦[[X]]⟧ = ε または ⟦X⟧**

と考えることができる。

ただし実際の axx では、単純な正規表現ではなく、変数束縛を伴うパターン照合として処理される。

---

# 12. パターン集合の意味

パターンファイルには多数のパターンが存在する。

これを、

**P = {p₁, p₂, …, pₙ}**

とする。

入力行 s に対して、

**Match(P, s)**

を「s に適用可能なパターンを選択する関数」とする。

axx では、パターンの記述順序に依存しないように、パターンの特異度を考慮して照合候補を決定する。

したがって概念的には、

**Pattern Set → Candidate Patterns → Best Match**

という処理になる。

これは、単純に「ファイルの上から順番に最初の一致を採用する」という方式とは異なる。

---

# 13. 一行の意味

これまでをまとめると、assembly line L の意味は、

**⟦L⟧P**

として、

```text
入力行
 ↓
パターン選択
 ↓
パターン照合
 ↓
変数環境生成
 ↓
エラー条件評価
 ↓
binary_list 評価
 ↓
機械語生成
 ↓
アセンブラ状態更新
```

という写像になる。

すなわち、

**Assembly Line × State → State**

である。

---

# 14. ラベルの意味論

ラベル環境を、

**λ : Label → Address**

とする。

例えば、

```text
foo:
    nop
```

の場合、

```text
λ(foo) = 現在のPC
```

となる。

そして、

```text
jmp foo
```

という命令では、

```text
⟦foo⟧λ = λ(foo)
```

となる。

しかし、アセンブル途中ではラベルの最終アドレスがまだ分からない場合がある。

そこで axx は、Pass 1 と Pass 2 を使って最終的なラベル値を決定する。

---

# 15. location counter

location counter を `pc` とする。

命令が n バイト生成した場合、

**pc' = pc + n**

となる。

つまり、

```text
⟦instruction⟧(pc)
    = (generated bytes, pc + length)
```

である。

`.align` のようなディレクティブでは、必要な padding を挿入して pc を次の境界まで進める。

したがって axx の意味は、単純な

**Assembly → Bytes**

ではなく、

**Assembly × State → Bytes × State**

となる。

---

# 16. セクションの意味論

axx は `.text`、`.data` などのセクションを扱う。

したがって状態 Γ は、

**Section → Fragment の列**

として考えることができる。

例えば、

```text
.text
A

.data
B

.text
C
```

なら、

```text
text = [A, C]
data = [B]
```

のような構造になる。

これは単純な「ファイル全体が一つのバイト列」という意味論よりも、ELF object generation を含む axx の実装に適している。

---

# 17. relocation の意味論

外部シンボルの場合、

```text
.extern foo
```

と宣言した時点では `foo` の最終アドレスは決定できない。

そこで axx は、

**Reference(foo, relocation type)**

という情報をオブジェクト中に残す。

最終的に linker が、

**Relocate(Bytes, Relocations, Symbol Environment)**

を実行する。

したがって、axx のアセンブル結果は単なるバイト列ではなく、

**Object = Bytes + Relocation Information + Symbol Information**

と考える必要がある。

---

# 18. relaxation の固定点意味論

axx の意味論で特に重要なのが relaxation である。

命令長がラベルとの距離によって変化する場合、

```text
ラベルのアドレス
↓
命令長
↓
後続ラベルのアドレス
↓
さらに命令長
```

という循環が発生する。

そこで axx は Pass 1 において再アセンブルを繰り返し、ラベルアドレスが変化しなくなるまで計算する。

これを数学的に表すなら、

**F : Label Environment → Label Environment**

という関数を考え、

**λ₀ → λ₁ → λ₂ → …**

と反復し、

**λ* = F(λ*)**

となる λ* を求める。

つまり、

> **axx の relaxation は、ラベル環境に対する固定点計算として解釈できる。**

これは axx の単純な「パターン置換器」という理解を超える重要な特徴である。

---

# 19. マクロ層

現行 axx にはマクロ層も存在する。

したがって全体の意味は、

```text
Assembly Source
       ↓
Macro Expansion
       ↓
Expanded Source
       ↓
Pattern Matching
       ↓
Binary Generation
       ↓
Object
```

となる。

これを意味論的に書けば、

**⟦S⟧ = ⟦A(M(S))⟧**

と考えられる。

ここで、

* M = マクロ展開
* A = axx のアセンブル意味関数

である。

重要なのは、マクロ層とパターン層が異なる意味論を持つことである。

マクロ層は主として**ソース変換**を行い、パターン層は**ソースから機械表現への意味付け**を行う。

---

# 20. axx の意味論の全体像

axx の全体をまとめると、次のようになる。

```text
              Assembly Source
                     │
                     ▼
              Macro Semantics
                     │
                     ▼
              Expanded Source
                     │
                     ▼
          Pattern Matching Semantics
                     │
                     ▼
             Variable Environment
                     │
                     ▼
             Expression Semantics
                     │
                     ▼
             Binary-list Semantics
                     │
                     ▼
              Machine Bytes
                     │
                     ▼
        State / Label / Section Update
                     │
                     ▼
          Relaxation Fixed Point
                     │
                     ▼
              ELF / Object File
```

この構造が、axx の表示的意味論を最もよく表している。

---

# 21. axx は何を意味付けしているのか

通常のプログラム意味論では、

**Program → Computation**

という対応を考える。

例えば、

**C Program → Store → Store**

というように、プログラムの実行による状態変化を意味として定義する。

しかし axx の場合は違う。

axx が意味付けしているのは、

**Assembly Language → Machine Representation**

である。

したがって axx は、

> **プログラムを実行するための意味論**

ではなく、

> **アセンブリ言語を機械表現へ解釈するための意味論**

を持つ。

この点は非常に重要である。

---

# 22. AXX の核心

axx の構造を最も簡潔に表現すると、

**Generic Assembler + Pattern Specification**

である。

従来型アセンブラでは、

```text
x86 Assembler
    ↓
x86 専用コード
```

となる。

axx では、

```text
                ┌── x86 pattern
                │
Generic axx ────┼── ARM pattern
                │
                ├── Z80 pattern
                │
                └── RISC-V pattern
```

となる。

つまり、

**アセンブラ本体が ISA を知るのではなく、パターンが ISA を記述する。**

この構造によって、同じ意味関数を異なる ISA に適用できる。

---

# 23. 表示的意味論としての最終的定式化

axx の意味論を最も簡潔にまとめるなら、

**Aₚ : AssemblyProgram → Object**

である。

ここで `p` はプロセッサパターンである。

より実装に忠実に書くなら、

**Aₚ : AssemblyProgram × State → Object × State**

となる。

そして relaxation を含めるなら、

**Aₚ(S) = Emitₚ(S, fix(Fₛ))**

と考えられる。

ここで、

* `S` = アセンブリプログラム
* `p` = プロセッサパターン
* `Fₛ` = Pass 1 における状態更新関数
* `fix(Fₛ)` = relaxation の固定点
* `Emit` = 最終的な機械語・オブジェクト生成

である。

---

# 24. 結論

本稿では axx General Assembler を表示的意味論の観点から分析した。

axx の意味論は、単純な、

**文字列 → バイト列**

ではない。

より正確には、

**アセンブリソース
→ パターン照合
→ 変数環境
→ 式評価
→ binary_list 評価
→ 機械語生成
→ ラベル・セクション状態更新
→ relaxation
→ relocation
→ オブジェクト**

という多段階の意味付けである。

特に重要なのは、axx において ISA 固有の意味がアセンブラ本体ではなく、**外部パターンに記述されている**ことである。

したがって axx は、

> **ISA の構文と機械語への写像を宣言的パターンとして記述し、その記述を共通アセンブル意味関数によって解釈するメタアセンブラ**

と位置付けることができる。

さらに relaxation を固定点として解釈すると、

> **axx は、ISA 記述の解釈・パターン照合・式評価・状態遷移・固定点計算・オブジェクト生成を組み合わせた、アセンブリ言語の意味付け系**

として理解できる。

この観点から見ると、axx の「general assembler」という名称は単に「多くの CPU に対応する」という意味ではなく、

**「アセンブリ言語そのものをパターンによって定義し、その意味を共通の意味関数によって与える」**

という、より抽象的な一般化を指していると解釈できる。

---

## 【確認できた事実】

リポジトリの `axx.py` には、パターン照合、ラベル管理、セクション管理、relaxation、relocation、ELF object 生成などの機構が実装されている。また、リポジトリ内の説明では `instruction :: error_patterns :: binary_list` というパターン形式が axx の中心的な設計として説明されている。

## 【推測・形式化】

本文中の

**Aₚ(S) = Emitₚ(S, fix(Fₛ))**

などの数式は、リポジトリにそのまま記載されている公式の形式意味論ではなく、**実装を表示的意味論の形式へ写像した本稿独自の定式化**です。

## 【情報源】

* [fygar256/axx — GitHub](https://github.com/fygar256/axx?utm_source=chatgpt.com)
* [axx.py — GitHub](https://github.com/fygar256/axx/blob/main/axx.py?utm_source=chatgpt.com)
* [README.md — GitHub](https://github.com/fygar256/axx/blob/main/README.md?utm_source=chatgpt.com)

## 回答日時

2026年8月27日
