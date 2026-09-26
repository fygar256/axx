# ELF の一般化

axx の ELF オブジェクト出力（`-o`）を、組み込みのマシン表に載っている 11 機種
から、**任意の `e_machine`** へ広げました。リロケーション型・ELF クラス・
RELA/REL・ELF ヘッダの欄を、パターンファイル側で宣言できます。

対応は `axx.py`（Paxx）と `caxx.c`（Caxx）の両実装に入っています。出力は
バイト単位で一致します。

---

## 1. 何が変わったか

これまで `-o` は、axx が再配置番号を組み込みで持つ 11 機種 — i386(3)、m68k(4)、
PowerPC(20)、PowerPC64(21)、s390x(22)、ARM(40)、SuperH(42)、SPARCV9(43)、
x86-64(62)、AArch64(183)、RISC-V(243) — だけを相手にしていました。`-m` に表に無い
番号を書くとエラーで止まります。「当てずっぽうの型番号で全部のリロケーションに
嘘のラベルを貼るよりは止まったほうがよい」という判断です。

判断そのものは正しいのですが、止める以外の道がありませんでした。そこで、
**番号を当てずっぽうにしない方法**をパターンファイル側に用意しました。型番号も
欄の幅も PC 相対性も、その機種を知っている人（パターンファイルを書く人）が
書けばよい、という形です。

前回入れた `.elftype`（型名を自分で決める）の続きにあたります。`.elftype` が
「名前 → 型番号」を決めるものだったのに対し、今回はその型を**どこで使うか**と、
**ELF をどう組むか**までを宣言できるようにしました。

---

## 2. 宣言（パターンファイル）

| 宣言 | 決めるもの |
|---|---|
| `.elfmachine::<番号>[::<名前>]` | `e_machine` の番号（と診断に出す名前） |
| `.elfclass::<32>` / `<64>` | ELF クラス（ELF32 / ELF64） |
| `.elfrela::<1>` / `<0>` | RELA（1、`rela` とも）か REL（0、`rel`）か |
| `.elftype::<名前>::<番号>[::<幅>[::<PC相対>]]` | リロケーション型（幅と PC 相対欄を追加） |
| `.elfwidth::<バイト幅>::<型>` | その幅の参照に使う既定の型 |
| `.elfextern::<型>` | `.extern` が型名を書かなかったときの既定の型 |
| `.elfdwarf::<型>` | `-g` の DWARF が書く絶対アドレス参照の型 |
| `.elfheader::<欄名>::<値>` | ELF ヘッダの欄 |

共通の決まりです。

- どの宣言も、`-m` で選んだ組み込みの表に**重ねる差分**です。表にある機種なら、
  書いた分だけが差し替わります。x86-64 に型名を 1 つ足すだけ、`e_flags` を足す
  だけ、という使い方ができます。
- `<型>` のところには、`.elftype` で決めた名前・組み込みの名前・型番号
  （10 進、`0x` 付き 16 進）のどれでも書けます。名前の大小は区別しません。
- 宣言はどこに書いても構いません。`.elftype` と同じく、パターンファイルを読み
  終えた時点でそろえられます。使う側より後ろに書いても引けます。
- `.elfwidth` のバイト幅は 1・2・4・8 のいずれかです。

### 2.1 `.elftype` の拡張

```
.elftype::abs16::2::2          /* 型番号 2、欄は 2 バイト          */
.elftype::pcrel16::4::2::1     /* 型番号 4、2 バイト、PC 相対      */
```

4 番目の欄が、その型が書き換える欄のバイト幅です。加数の計算に欄の幅が要るので、
組み込みの表を持たないマシンで `.elfwidth` や `.elfextern` から引かせる型には、
幅を書いてください。5 番目の欄は 0 以外なら「PC 相対の型」という印で、加数に
命令アドレスを足す側に回ります。どちらも省けます。

### 2.2 `.elfheader` で書ける欄

| 欄名 | ELF ヘッダの欄 | 既定値 | 範囲 |
|---|---|---|---|
| `type` | `e_type` | 1（`ET_REL`） | 0〜0xFFFF |
| `flags` | `e_flags` | 0 | 0〜0xFFFFFFFF |
| `version` | `e_version` | 1（`EV_CURRENT`） | 0〜0xFFFFFFFF |
| `entry` | `e_entry` | 0 | 0〜0x7FFFFFFFFFFFFFFF |
| `osabi` | `e_ident[EI_OSABI]` | `--osabi` の値 | 0〜0xFF |
| `abiversion` | `e_ident[EI_ABIVERSION]` | 0 | 0〜0xFF |

機種固有の `e_flags`（ARM EABI の版数、RISC-V の ABI 印など）を出すための欄です。
書かなかった欄は既定値のまま出ます。値は定数式で書けます。

---

## 3. `-m` / `-f` との関係

| | 書いたとき | 書かないとき |
|---|---|---|
| `-m` | その番号が対象（パターンの `.elfmachine` より優先） | `.elfmachine`、それも無ければ 62（x86-64） |
| `-f` | その ELF クラス | `.elfclass`、それも無ければマシンの慣習クラス |

`-m` が勝つので、同じパターンファイルを別の `e_machine` 番号で使い回せます。

`-f` の既定が変わりました。これまでは常に 64 で、32 ビット機を選ぶと
「`-f` が ELF64 を強制した」という警告付きで ELF64 が出ていました。いまは
`-m 3`（i386）なら黙って ELF32 が出ます。`-f 32` / `-f 64` を明示したときの
振る舞いは今までどおりで、慣習と違う組み合わせ（`-m 62 -f 32`、実際の x32 ABI
のレイアウト）も警告付きで受け入れます。

---

## 4. 宣言が足りないとき

**黙って壊れた `.o` を出さない**というのが全体の方針です。

- 型の決まらない参照は、当てずっぽうの型番号を書く代わりにリロケーションを
  出しません。どこを飛ばしたかは `-d` を付けると出ます。
- `-m` に組み込みの表に無い番号を書いて `-o` を出すときは、そのことを知らせる
  警告が出ます。
- `.elfwidth` / `.elfextern` / `.elfdwarf` に書いた型名が引けないときは、宣言が
  出そろった時点で 1 回だけ警告します（綴り違いを黙って読み飛ばさないため）。
- `-g` の DWARF は、`.elfdwarf`（または組み込みの表）で絶対参照の型が分かる
  ときだけ出ます。

---

## 5. 例 — EM_MSP430 (105)

axx が組み込みの表を持たないマシンの、記述の全体です。

```
.bits::8

.elfmachine::105::MSP430
.elfclass::32
.elfrela::1

.elftype::abs32::1::4
.elftype::abs16::2::2
.elftype::pcrel16::4::2::1
.elftype::abs8::3::1

.elfwidth::4::abs32
.elfwidth::2::abs16
.elfwidth::1::abs8
.elfextern::abs16
.elfdwarf::abs32

.elfheader::flags::0x2a
.elfheader::abiversion::1

CALL !t :: 0xb0,0x12,t,t>>8
.reloc::t::pcrel16
JMP !t :: 0x00,0x3c,t,t>>8
.clrreloc::t
DB !t :: t
DW !t :: t,t>>8
DD !t :: t,t>>8,t>>16,t>>24
```

ソース側は普通に書きます。

```
        .extern ext1                    ; 型は .elfextern から
        .extern ext2::abs32             ; .elftype の名前
        .global start
start:
        call    ext1
        jmp     start
        dw      start
        db      start
        dd      ext2
```

`axx elfgen.axx elfgen.s -o out.o` の結果を `readelf -r` で見たものです。

```
Relocation section '.rela.text' at offset 0x58 contains 5 entries:
 Offset     Info    Type            Sym.Value  Sym. Name + Addend
00000002  00000202 R_MSP430_ABS16    00000000   ext1 + 0
00000006  00000404 R_MSP430_PCR16    00000000   start + 6
00000008  00000402 R_MSP430_ABS16    00000000   start + 0
0000000a  00000403 R_MSP430_ABS8     00000000   start + 0
0000000b  00000301 R_MSP430_ABS32    00000000   ext2 + 0
```

ヘッダ側も宣言どおりです。

```
  Class:        ELF32
  ABI Version:  1
  Machine:      Texas Instruments msp430 microcontroller
  Flags:        0x2a
```

