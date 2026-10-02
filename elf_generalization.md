# ELF の一般化 — axx の `-o` の仕組み

axx の `-o` は、**任意の CPU** 向けにリンクできる再配置可能オブジェクト（`ET_REL`
の `.o`）を書きます。ELF の組み立てに要る知識は 2 つに分かれ、それぞれ別の場所に
書きます。

- **機種に依存するもの** — リロケーション型、ELF クラス、RELA/REL、ELF ヘッダの
  欄、セクションヘッダの属性、命令語の中の欄の形、リロケーションの対や添え物、
  `r_info` の並び、加数の単位、セクショングループ、CFI の CIE の欄。これは
  **パターンファイル**に宣言します（2 節）。
- **プログラムに依存するもの** — シンボルの型・大きさ・束縛・可視性・共通
  シンボル、関数ごとの CFI（`.cfi_*`）。これは**ソースファイル**に宣言します
  （3 節、2.14 節）。

axx は 11 機種ぶんの組み込みの表を持っていますが、表はパターンファイルの宣言を
あらかじめ書いておいたものにすぎません。ELF を書くコードには機種番号で分かれる
処理が無く、表の項目はどれも宣言で書けます（5 節）。

実装は `axx.py`（Paxx）と `caxx.c`（Caxx）の両方にあり、同じ入力に対して
バイト単位で同じ ELF を出します。

---

## 1. 仕組み

`-o` の ELF は、次の 5 段で組み立てられます。

### 1.1 マシン記述を組む

`-m` の番号（無ければ `.elfmachine`、それも無ければ 62）の組み込みの表を土台に、
パターンファイルの `.elf*` 宣言をかぶせて「実効表」を作ります。

- 同じ名前の型は宣言が表に勝ちます。表に無い型は宣言から加わります。
- `.elfbuiltin::0` なら土台は空の表で、宣言だけが残ります。
- 宣言の綴り（型名）はパターンファイルを読み終えるまで綴りのまま置き、実効表を
  組むときに型番号へ解決します。使う側より後ろに宣言を書いても引けるのはこの
  ためです。
- 実効表は「(マシン番号, 宣言の世代番号)」を鍵にして覚えます。宣言が増える
  たびに世代番号が進むので、古い表が残ることはありません。

実効表が持つもの:

| 項目 | 中身 | 宣言 |
|---|---|---|
| 名前 | 診断に出す機種名 | `.elfmachine` |
| クラス | ELF32 / ELF64 | `.elfclass` |
| RELA / REL | 加数をどこに置くか | `.elfrela` |
| 型の表 | 名前 → 番号、番号 → 欄の幅、PC 相対の型の集合 | `.elftype` |
| 幅からの推定 | 欄の幅 → 既定の型 | `.elfwidth` |
| 外部参照の既定の型 | 型名の無い `.extern` の型 | `.elfextern` |
| DWARF の型 | `-g` の絶対参照の型 | `.elfdwarf` |
| PC 相対の推定 | 絶対型を PC 相対型に取り替えるか | `.elfpcguess` |
| 命令欄 | 型 → (マスク, オフセット, シフト, 補正) | `.elffield` |
| 書き戻し関数 | 型 → 関数名（REL） | `.elfencode` |
| 添え物 | 型 → [(添える型, シンボルを持つか)] | `.elfextra` |
| ラベルの和と差 | 幅 → (足す型, 引く型)、型 → (足す型, 引く型) | `.elfdiff` |
| `r_info` 関数 | 関数名 | `.elfrinfo` |
| 単位 | byte / word | `.elfunit` |
| CFI | CIE の欄、初期命令、レジスタ名 | `.elfcfi`、`.elfcfiinit`、`.elfcfireg` |

### 1.2 参照を追跡する

パス 2 で 1 行をアセンブルするとき、axx は「どの出力ワードがどのラベルから
来たか」を記録します。

- パターンの変数（`!t` など）がソースのオペランドを取り込むとき、その式が
  参照したラベルを変数に結び付けます。ラベルが 1 つならそのラベル、2 つ以上で
  `.elfdiff` が宣言されていればラベルの和と差の候補、それ以外は「曖昧」です。
- 和と差の候補は、取り込んだ式の綴りを読んで各ラベルの符号を決めます。式が
  ラベル・数・`+`・`-`・括弧だけでできていて、どのラベルの係数も +1 か −1 なら
  和と差、そうでなければ曖昧です。括弧の前の `-` は中の符号を反転します。
  ラベルが 1 つでも符号が負なら、`.elfdiff` があれば引く項だけの和と差、無ければ
  曖昧です。
- `binary_list` の要素を評価するとき、変数が使われたらその出力ワードの位置に
  ラベルを記録します。`.reloc::<変数>::<型>` の付いた変数なら、型と
  「オペランドの値 − ラベルの値」も一緒に記録します（命令欄のヒント）。
- 照合の試行が失敗したら、その試行で記録したものはすべて巻き戻します。

行の終わりに、同じラベルを指す連続したワードを 1 つの欄にまとめます。1 つの
ワードに別々のラベルが重なる欄は曖昧として捨てます。

### 1.3 型を決める

欄ごとに型を次の順で決めます（強い順）。

| 順位 | 決めるところ | 書き方 |
|---|---|---|
| 強 | ソースファイル | `.extern`／`.global`／`.EQU`／取り込み TSV の `::<型名>`、`.reloctype` |
| 中 | パターンファイル | `.reloc::<変数>::<型名>` |
| 弱 | 既定 | 欄のバイト幅からの推定（`.elfwidth`、実効表） |

- 型名を書かない `.extern ext` の既定の型（`.elfextern`）は「ソースファイル」に
  当たりません。`.reloc` が決めた型は上書きされず、既定の型は `.reloc` の無い
  参照（データなど）にだけ使われます。
- ソースの型が `.reloc` の型に勝っても、`.reloc` が教える「値は命令語のビット欄に
  入っている」という知識と加数の求め方はそのまま使われ、型番号だけが差し替わり
  ます。
- 幅から推定した型が PC 相対なのに、欄の値がラベルの値そのものなら、同じ幅の
  絶対型に取り替えます。逆に `.elfpcguess::1` の機種では、推定した型が絶対型で
  欄の値がラベルの値と違えば、同じ幅の PC 相対型に取り替えます。取り替え先は
  実効表の型を宣言順に見て、同じ幅・逆の PC 相対性の最初の型です。
- 型が決まらない欄にはリロケーションを出しません（`-d` で報告します）。

### 1.4 加数を求める

加数はまずワードで求め、`.elfunit` の単位に直します（`byte` なら 1 ワードの
バイト数を掛け、`word` ならそのまま）。

| 欄の種類 | 加数 | 欄の中身（RELA） |
|---|---|---|
| データ（絶対型） | 欄の値 − ラベルの値 | 欄の値のまま |
| データ（PC 相対型） | 欄の値 − ラベルの値 ＋ 欄の位置（セクション先頭から） | 欄の値のまま |
| 命令欄（`.elffield` の型） | オペランドの値 − ラベルの値 ＋ 補正 | マスクのビットを 0 |
| ラベルの和と差（`.elfdiff`、幅） | 最初の足す型: 定数部、ほか: 0 | 0 |
| ラベルの和と差（`.elfdiff`、型） | 同上（定数部はオペランドの値 − 和と差） | `.elffield` があればマスクのビットを 0、無ければ組み立てた値のまま |

欄の値は、欄のワード列を対象のバイト順で 1 つの整数に読み、欄の幅で符号を
付けたものです。

### 1.5 書き出す

セクション、シンボル表、リロケーション、（`-g` なら）DWARF を組んで書きます。

- **セクション** — 属性は名前の規則（`.text` は実行、`.data`・`.bss` は書き込み、
  `.bss` は `SHT_NOBITS`、それ以外は割り当てのみ）に `.elfsection` が勝ちます。
  `sh_link` / `sh_info` は `.elflink` から。ファイル内の位置は `sh_addralign`
  （16 を下限）に合わせます。
- **セクショングループ** — `.elfgroup` のグループはセクションヘッダ表の先頭
  （メンバーより前）に置き、メンバーとそのリロケーションセクションに
  `SHF_GROUP` を立てます。
- **シンボル表** — セクションシンボル、局所シンボル、外部参照、公開シンボルの
  順。値はセクション先頭からの位置で、単位は `.elfunit` に従います。型・大きさ・
  束縛・可視性はソースの宣言（3 節）から。
- **リロケーション** — 項目ごとに、`.elfextra` の添え物を同じ位置に続けます。
  RELA なら加数を項目に書きます。REL なら加数を欄へ書き戻します。書き戻しは
  `.elfencode` の関数、無ければ `.elffield` のマスク・シフト、無ければ欄の幅ぶんの
  整数として。同じ位置に複数の項目があるときは最初の項目だけが書き戻します。
- **`r_info`** — `.elfrinfo` の関数、無ければ ELF の決まりの形
  （ELF64 は `(シンボル << 32) | 型`、ELF32 は `(シンボル << 8) | 型`）。
- **DWARF** — `.debug_info` / `.debug_abbrev` / `.debug_line` と、その
  リロケーション（`.elfdwarf` の型、`r_info` は同じ規則）。
- **CFI** — ソースの `.cfi_*` から `.eh_frame` と `.rela.eh_frame`（2.14 節）。
  リンカ緩和の機種では、表が使う局所シンボル `.Lcfi<n>` を局所シンボルの後ろに
  置きます。
- **セクションの数** — 節番号が `SHN_LORESERVE`（0xff00）以上のセクションが
  あれば、`e_shnum` / `e_shstrndx` を 0 番目のセクションヘッダに置き、シンボルの
  節番号を `.symtab_shndx`（`SHT_SYMTAB_SHNDX`）に書きます（`st_shndx` は
  `SHN_XINDEX`）。セクションの数に上限はありません。

---

## 2. 宣言（パターンファイル）

| 宣言 | 決めるもの |
|---|---|
| `.elfmachine::<番号>[::<名前>]` | `e_machine` の番号（と診断に出す名前） |
| `.elfclass::<32>` / `<64>` | ELF クラス |
| `.elfrela::<1>` / `<0>` | RELA（1、`rela`）か REL（0、`rel`）か |
| `.elftype::<名前>::<番号>[::<幅>[::<PC相対>]]` | リロケーション型 |
| `.elfwidth::<バイト幅>::<型>` | その幅の参照に使う既定の型 |
| `.elfextern::<型>` | `.extern` が型名を書かなかったときの既定の型 |
| `.elfdwarf::<型>` | `-g` の DWARF が書く絶対参照の型 |
| `.elfpcguess::<0>` / `<1>` | 幅から推定した絶対型を PC 相対型に取り替えるか |
| `.elfheader::<欄名>::<値>` | ELF ヘッダの欄 |
| `.elfsection::<名前>::<sh_flags>[::<sh_type>[::<整列>[::<要素長>]]]` | セクションヘッダの属性 |
| `.elflink::<セクション>::<sh_link>[::<sh_info>]` | セクションの `sh_link` / `sh_info` |
| `.elfgroup::<名前>::<署名>::<フラグ>::<メンバー>[,...]` | セクショングループ |
| `.elffield::<型>::<マスク>[::<オフセット>[::<シフト>[::<補正>]]]` | 命令フィールド型 |
| `.elfencode::<型>::<関数>` | REL で加数を欄へ書き戻す関数 |
| `.elfextra::<型>::<添える型>[::<シンボル>]` | 同じ位置に添えるリロケーション |
| `.elfdiff::<幅または型>::<足す型>::<引く型>` | ラベルの和と差を足す型と引く型の組で出す |
| `.elfrinfo::<関数>` | `r_info` を組む関数 |
| `.elfunit::<byte>` / `<word>` | 加数とシンボル値の単位 |
| `.elfbuiltin::<0>` / `<1>` | 組み込みの表を土台にするか |
| `.elfcfi::<戻り番地の列>::<コード整列>::<データ整列>[::<詰め>]` | CFI の CIE の欄 |
| `.elfcfiinit::<命令>` | CIE の初期命令 |
| `.elfcfireg::<名前>::<DWARF 番号>` | CFI の指令に書くレジスタ名 |

共通の決まり:

- どの宣言も、`-m` で選んだ組み込みの表に**重ねる差分**です（`.elfbuiltin::0`
  を除く）。表にある機種なら、書いた分だけが差し替わります。
- `<型>` のところには、`.elftype` で決めた名前・組み込みの名前・型番号（10 進、
  `0x` 付き 16 進）のどれでも書けます。名前の大小は区別しません。
- 宣言はどこに書いても構いません。パターンファイルを読み終えた時点でそろえられ
  ます。
- 数の欄は定数式で書けます。

### 2.1 `.elftype` — リロケーション型

```
.elftype::abs16::2::2          /* 型番号 2、欄は 2 バイト          */
.elftype::pcrel16::4::2::1     /* 型番号 4、2 バイト、PC 相対      */
```

第 4 欄がその型が書き換える欄のバイト幅（1〜8）、第 5 欄が 0 以外なら PC 相対の
型です。加数の計算に欄の幅が要るので、`.elfwidth` や `.elfextern` から引かせる型、
命令欄の型には幅を書きます。番号は 1〜2147483647 です。3 つの型を 1 項目で持つ
複合型（MIPS64）は、3 バイトを詰めた番号で書けます（2.12 節）。

### 2.2 `.elfwidth` / `.elfextern` / `.elfdwarf`

`.elfwidth` のバイト幅は 1〜8 のどれでも書けます。1 ワードが 8 ビットでない機種
（`.bits`）では参照の幅が 1 ワードのバイト数の倍数になり、8 ビット機でも 3 バイト
の欄を持つ ISA があるからです（`R_MN10300_24` など）。型に 0 と書くと「その幅には
型が無い」で、そういう参照にはリロケーションを出しません。

### 2.3 `.elfheader` — ELF ヘッダの欄

| 欄名 | ELF ヘッダの欄 | 既定値 | 範囲 |
|---|---|---|---|
| `type` | `e_type` | 1（`ET_REL`） | 0〜0xFFFF |
| `flags` | `e_flags` | 0 | 0〜0xFFFFFFFF |
| `version` | `e_version` | 1（`EV_CURRENT`） | 0〜0xFFFFFFFF |
| `entry` | `e_entry` | 0 | 0〜0x7FFFFFFFFFFFFFFF |
| `osabi` | `e_ident[EI_OSABI]` | `--osabi` の値 | 0〜0xFF |
| `abiversion` | `e_ident[EI_ABIVERSION]` | 0 | 0〜0xFF |

機種固有の `e_flags`（ARM EABI の版数、RISC-V の ABI 印、MIPS の ISA など）を
出すための欄です。

### 2.4 `.elfsection` — セクションヘッダの属性

```
.elfsection::.vectors::0x6           /* ALLOC+EXECINSTR、型は既定のまま */
.elfsection::.noinit::0x3::8         /* ALLOC+WRITE、SHT_NOBITS         */
.elfsection::.note.axx::0::7         /* 欄なし、SHT_NOTE、整列は 4      */
.elfsection::.vectors2::0x6::1::2    /* 整列を明示して 2                */
.elfsection::.rodata.str1.1::0x32::1::1::1
                                     /* ALLOC+MERGE+STRINGS、要素長 1   */
```

- セクション名は大小を区別せず丸ごと一致で引き当てます。
- `sh_type` を書かなければ名前の規則のまま残ります。`SHT_NOBITS`（8）の
  セクションは `sh_size` だけを持ち、中身をファイルに書きません。
- 第 4 欄は `sh_addralign` で、0 か 2 の冪です。書かなければ 16、ただし
  `SHT_NOTE`（7）は 4 です（note の詰め物が整列値に従い、binutils が 4 か 8 しか
  読まないため。8 が要る note は 8 と書きます）。
- 第 5 欄は `sh_entsize` です。`SHF_MERGE`（0x10）のセクションは、リンカが要素の
  幅を知るためにこれを要求します（文字列表なら 1）。

### 2.5 `.elflink` — `sh_link` と `sh_info`

```
.elfsection::.meta::0x82               /* ALLOC+LINK_ORDER  */
.elflink::.meta::.text                 /* sh_link -> .text  */
```

値はセクション名（出力するセクション、`.rela.*` / `.rel.*`、`.symtab`、`.strtab`、
`.shstrtab`、`-g` の DWARF セクション。大小を区別しない）か数（10 進か `0x` 付き
16 進）です。見つからない名前は 0 と書き、警告します。`.rela.*` と `.symtab` の
`sh_link` / `sh_info` は axx が自分で正しい番号を入れます。

### 2.6 `.elfgroup` — セクショングループ

```
.elfsection::.text.foo::0x6
.elfgroup::.group::foo::1::.text.foo   /* COMDAT、署名 foo */
```

- `<名前>` はグループのセクション名、`<署名>` は署名のシンボル名です。シンボル表に
  無く、セクション名と一致すればそのセクションシンボルを使います。
- `<フラグ>` はグループの中身の先頭の語（1 が `GRP_COMDAT`）です。
- メンバーには `SHF_GROUP`（0x200）が立ち、そのリロケーションセクションも
  グループに入ります。
- グループのセクションはセクションヘッダ表の先頭に置きます（gABI はグループを
  メンバーより前に置くことを求めます）。
- 出力に無いメンバーは警告して読み飛ばし、メンバーが残らないグループは出しません。

### 2.7 `.elffield` — 命令フィールド型

```
.elffield::<型>::<マスク>[::<オフセット>[::<シフト>[::<補正>]]]
```

値を素の連続バイトではなく命令語のビット欄に詰める型を宣言します。この型を
`.reloc::<変数>::<型>` で付けた行は、

- 加数が「オペランドの値 − ラベルの値 ＋ 補正」になります（`bl ext+8` なら 8）。
- RELA では命令語の欄は 0 で出力され、リンカが埋めます（GNU as と同じ形）。
- REL では加数を `<シフト>` ビット右へずらし、マスクの立っているビットへ下から
  順に詰めて欄に書き戻します。マスクの外（命令の残り）はそのまま残ります。
- そのオペランドの範囲・整列の検査はリンカに任されます。

欄の決まり:

- `<マスク>` はリンカが書き込むビットです。型の幅ぶんのワードを対象のバイト順で
  読んだ整数の中のビットで書きます。2 つの命令語にまたがる欄も 64 ビットのマスク
  1 つで書けます（RISC-V の `R_RISCV_CALL_PLT` は `0xfff00000fffff000`）。
- `<オフセット>`（省略時 0）は、その欄が、その行がオペランドのために出す最初の
  ワードから何バイト目に始まるかです。`r_offset` もそこを指します。
- `<シフト>`（省略時 0、0〜63）は REL の書き戻しで加数を右へずらすビット数です
  （語単位の欄なら 2）。
- `<補正>`（省略時 0）は加数に足す定数です。PC が命令の先頭より先を指す機種の
  ずれで、ARM の分岐は −8 です。
- 下から順に詰めるので、欄の中でビットの並びが入れ替わる型を REL で書き戻すには
  `.elfencode`（2.8 節）を使います。

```
.elftype::rel24::10::4::1
.elffield::rel24::0x03fffffc            /* PowerPC64 bl の LI 欄 */

.reloc::t::rel24
BL !t :: .call w4(0x48000001|((t-$$)&0x3fffffc))
.clrreloc::t
```

AArch64 の組み込みの表は、`call26`、`adrp`、`:lo12:` の型などをこの形で持って
います。

### 2.8 `.elfencode` — 書き戻し関数

```
.elfencode::<型>::<関数>
```

REL のとき、その型の加数をミニ言語の関数で欄へ書き戻します。関数は
(欄の値, 加数) を受け取り、新しい欄の値を返します。欄の値は型の幅ぶんのワードを
対象のバイト順で読んだ整数、加数は負になりえます。丸めの要る欄、ビットの並びが
入れ替わる欄、ビットが他のビットの関数になっている欄（Thumb の J1/J2）も書けます。
`.elffield` があってもこちらが書き戻しを受け持ちます。RELA では呼ばれません。

```
.elfencode::hi16::hi16enc
.func hi16enc(f, a)
.return (f & 0xffff0000) | (((a + 0x8000) >> 16) & 0xffff)
.endfunc
```

### 2.9 `.elfextra` — 添えるリロケーション

```
.elfextra::<型>::<添える型>[::<シンボル>]
```

`<型>` のリロケーションの後ろに、同じ位置で `<添える型>` を加数 0 で出します。
`<シンボル>` が 0（既定）ならシンボル番号 0、1 なら元と同じシンボルです。
RISC-V の `R_RISCV_RELAX` がこれです。

### 2.10 `.elfdiff` — ラベルの和と差

```
.elfdiff::<幅>::<足す型>::<引く型>
.elfdiff::<型>::<足す型>::<引く型>
```

値がラベルの足し引き（`a-b`、`a-b+c-d+4`、`-(a-b)`、`a-(b-c)` など）の欄に、
足されるラベルそれぞれへの `<足す型>` と、引かれるラベルそれぞれへの `<引く型>` を
同じ位置に出します。足す型を先、引く型を後に並べ、定数部は最初の足す型の加数に
置きます（足すラベルが無ければ最初の引く型の加数に符号を反転して置きます）。

- 第 1 欄が幅なら、その幅のデータの欄が対象です。RELA では欄を 0 で出します
  （この種の型は欄の中身に足し引きするため）。
- 第 1 欄が型名なら、`.reloc` でその型を付けた欄が対象です。欄の位置と幅は
  その型の `.elffield` に従い、`.elffield` が無ければ参照が出したワード列その
  もので、中身は組み立てた値のまま残します（ULEB128 のように、リンカが既存の
  長さを保って書き直す欄のため）。
- リンカがコードを縮める機種では、同じセクションの中の差もこの組で出す必要が
  あります。宣言の無い幅のラベルの和と差にはリロケーションを出しません。

### 2.11 `.elfunit` — 単位

| 値 | 加数 | `st_value` / `st_size` |
|---|---|---|
| `byte`（既定） | バイト | バイト |
| `word` | ワード | ワード |

`r_offset` と `sh_size` は常にバイトです。1 ワードが 8 ビットの機種では両者は同じ
値になります。

### 2.12 `.elfrinfo` — `r_info` の形

```
.elfrinfo::<関数>
```

関数は (シンボル番号, 型番号) を受け取り、`r_info` を返します。`-g` の DWARF の
リロケーションにも使われます。MIPS64 は型を最上位バイトに置きます。

```
.elfrinfo::rinfo64
.func rinfo64(sym, t)
.return sym | (((t >> 16) & 0xff) << 40) | (((t >> 8) & 0xff) << 48) | ((t & 0xff) << 56)
.endfunc
```

`.elfencode` と `.elfrinfo` の関数は 2 つの引数を取り、数を返します。そうでなければ
エラーです。

### 2.13 `.elfpcguess` / `.elfbuiltin`

`.elfpcguess::1` は 1.3 節の「絶対型 → PC 相対型」の取り替えを有効にします
（組み込みの表では m68k が 1）。`.elfbuiltin::0` は組み込みの表を土台にせず、
パターンファイルの宣言だけで記述を組みます。

### 2.14 CFI — `.elfcfi` / `.elfcfiinit` / `.elfcfireg` と `.cfi_*`

ソースの `.cfi_*` 指令（GNU as と同じ書き方）から `.eh_frame` を組みます。機種に
依存する部分はパターンファイルで宣言します。

```
.elfcfi::16::1::-8                     /* RA の列、コード整列、データ整列 */
.elfcfiinit::def_cfa rsp, 8            /* CIE の初期命令（書いた順）     */
.elfcfiinit::offset rip, -8
.elfcfireg::rsp::7                     /* レジスタ名 → DWARF 番号       */
.elfcfireg::rip::16
```

- 第 4 欄は CIE と FDE を詰める単位（省略時はポインタの大きさ）です。
- CIE は拡張文字列 `zR`（`.cfi_personality` で `P`、`.cfi_lsda` で `L`、
  `.cfi_signal_frame` で `S`）、FDE の番地は `DW_EH_PE_pcrel|sdata4` です。
  番地には、実効表の型を宣言順に見て最初の 4 バイトの PC 相対のデータ型
  （命令欄の型を除く）を使います。同じ設定の関数は CIE を共有します。
- 命令の位置の進みは 6 ビット・1・2・4 バイトのうち収まる最小の形、各命令は
  GNU as・llvm-mc と同じ形です。
- `.elfdiff::4` があれば（リンカ緩和の機種）、関数の長さと位置の進みを足す型・
  引く型の組で書き、そのための局所シンボル `.Lcfi<n>` を置きます。コード整列は
  1 でなければなりません。
- ソースに書ける指令: `startproc [simple]`、`endproc`、`def_cfa`、
  `def_cfa_offset`、`def_cfa_register`、`adjust_cfa_offset`、`offset`、
  `rel_offset`、`val_offset`、`restore`、`undefined`、`same_value`、`register`、
  `remember_state`、`restore_state`、`return_column`、`signal_frame`、
  `window_save`、`negate_ra_state`、`escape`、`personality`、`lsda`、
  `sections`（読み飛ばす）。

---

## 3. 宣言（ソースファイル）— シンボル表の属性

シンボル表の型・大きさ・束縛・可視性はどの機種でも同じ形の欄で、プログラムの
側の情報なのでソースに書きます。リンカはここを見て仕事を変えます。

- `STT_FUNC` でないシンボルには、ARM / AArch64 のリンカが中継命令（veneer）を
  作りません。
- 大きさが 0 のシンボルは `--gc-sections` が範囲を決められません。
- 弱いシンボル（`STB_WEAK`）で、既定の実装を上書きできるライブラリを作れます。
- `SHN_COMMON` のシンボルは、複数のオブジェクトの同じ変数をリンカが 1 つに
  まとめます。
- `st_other` の上位ビットには機種固有の意味が載ります（PowerPC64 ELFv2 の
  局所入口のずれはビット 5〜7）。

| 宣言 | 決めるもの |
|---|---|
| `.type <名前>::<種別>` | `st_info` の型欄（`STT_*`） |
| `.size <名前>::<式>` | `st_size` |
| `.weak <名前>` | 束縛を `STB_WEAK` にする |
| `.hidden <名前>` / `.protected <名前>` / `.internal <名前>` | `st_other` の可視性（`STV_*`） |
| `.other <名前>::<値>` | `st_other` のバイトそのもの |
| `.comm <名前>::<大きさ>[::<整列>]` | `SHN_COMMON` のシンボル |

- どれも `名前1::…, 名前2::…` とカンマで並べられます。
- 宣言していないシンボルは `STT_NOTYPE`、大きさ 0、可視性 `STV_DEFAULT` です。

**`.type` の種別。** 名前でも番号（0〜15）でも書けます。

| 種別 | `STT_*` | 使うところ |
|---|---|---|
| `notype` | 0 | 型を言わない（既定） |
| `object` | 1 | データ |
| `func`（`function`） | 2 | 関数の入口 |
| `section` | 3 | セクションシンボル |
| `file` | 4 | ファイル名シンボル |
| `common` | 5 | 共通シンボル |
| `tls`（`tls_object`） | 6 | スレッド局所データ |
| `gnu_ifunc`（`ifunc`） | 10 | GNU の間接関数 |

**`.size`。** 値はワード数で、`.elfunit::byte` なら 1 ワードのバイト数を掛けて
`st_size` に入ります。関数の終わりのラベルとの差で書くのが普通です
（`.size func::func_end-func`）。

**`.weak`。** このファイルで定義されていれば `.global` と同じく外へ出し、束縛だけ
弱くします。定義されていなければ型名なしの `.extern` と同じに登録するので、
`.weak maybe` だけで「解決できなければ 0 になる参照」が書けます。弱いシンボルは
必ず大域側に置きます（ELF は局所シンボルを弱くすることを許しません）。

**`.other`。** 下位 2 ビットが可視性、上位 6 ビットが機種固有です。可視性の宣言は
下位 2 ビットだけを書き換えるので、`.other` の後に書いても上位は残ります。

**`.comm`。** `st_value` が整列（バイト、既定 1）、`st_size` が大きさです。型は
`.type` が無ければ `STT_OBJECT` です。名前は外部シンボルとして登録され、参照には
リロケーションが出ます。

実例は同梱の `elfsym.axx` / `elfsym.s`（EM_MN10300）です。

---

## 4. `-m` / `-f`

| | 書いたとき | 書かないとき |
|---|---|---|
| `-m` | その番号が対象（`.elfmachine` より優先） | `.elfmachine`、それも無ければ 62（x86-64） |
| `-f` | その ELF クラス | `.elfclass`、それも無ければ実効表のクラス（表に無い機種は ELF64） |

`-m` が勝つので、同じパターンファイルを別の `e_machine` 番号で使い回せます。
慣習と違う組み合わせ（`-m 62 -f 32`、x32 ABI のレイアウト）は警告付きで受け入れ
ます。

---

## 5. 組み込みの表と `--elfdesc`

組み込みの表を持つ機種は i386(3)、m68k(4)、PowerPC(20)、PowerPC64(21)、
s390x(22)、ARM(40)、SuperH(42)、SPARCV9(43)、x86-64(62)、AArch64(183)、
RISC-V(243) です。表の項目は 1.1 節の実効表の項目そのもので、どれも宣言で
書けます。AArch64 の命令欄は `.elffield` の形、m68k の推定は `.elfpcguess` の形で
持っています。

`--elfdesc` は、いま有効な記述（`-m` の機種の表に宣言を重ねた実効表）を、先頭に
`.elfbuiltin::0` を置いた宣言の並びとして標準出力へ書き出して終わります。

```
$ axx test.axx -m 4 --elfdesc
.elfbuiltin::0
.elfmachine::4::m68k
.elfclass::32
.elfrela::1
.elftype::abs32::1::4
.elftype::abs16::2::2
.elftype::abs8::3::1
.elftype::pc32::4::4::1
.elftype::rel32::4::4::1
.elftype::pc16::5::2::1
.elftype::pc8::6::1::1
.elfwidth::1::abs8
.elfwidth::2::abs16
.elfwidth::4::pc32
.elfextern::pc32
.elfdwarf::abs32
.elfpcguess::1
.elfunit::byte
```

この出力をパターンファイルに貼れば（あるいは include すれば）、組み込みの表なしで
同じ ELF が出ます。`.elfencode` / `.elfrinfo` が名前を挙げる関数は書き出さないので、
関数を定義したパターンファイルと一緒に使います。組み込みの 11 機種、AArch64・
PowerPC64（両バイト順）・RISC-V の命令セット、同梱の ELF 系パターンファイルで、
`--elfdesc` を通した出力が元の出力とバイト単位で一致することを確かめています。

---

## 6. 宣言が足りないとき

**黙って壊れた `.o` を出さない**のが方針です。

- 型の決まらない参照、宣言の無い幅のラベル差には、リロケーションを出しません
  （`-d` で報告します）。
- `-m` に組み込みの表に無い番号を書いて `-o` を出すときは警告します。
- 宣言に書いた型名が引けないときは、宣言が出そろった時点で 1 回だけ警告します。
- `.elfencode` / `.elfrinfo` の関数が無い、引数の数が違う、数を返さないときは
  エラーです。
- CFI では、`.cfi_startproc` の外の指令、閉じていない関数、データ整列係数で
  割り切れないオフセット、`remember_state` の無い `restore_state`、知らない
  シンボルや符号化、`.elfcfi` の無いパターンファイルがエラーです。
- `-g` の DWARF は、絶対参照の型が分かるときだけ出します。
- ELF32 の既定の `r_info` は型欄が 8 ビットです。255 を超える型番号は別の型に
  化けるので、型ごとに 1 回警告します（シンボル番号が 24 ビットに入らないときも
  同じ）。`.elfrinfo` が形を決めているときは警告しません。

---

## 7. 範囲

axx が出すのは再配置可能オブジェクト（`ET_REL`）です。`binary_list` の中では、
同じセクションのラベルと `$$` をセクション先頭からの相対値で埋めます（場所は
リンカが決めるため）。実行ファイル（`ET_EXEC`）や共有ライブラリ（`ET_DYN`）を
出すには、リロケーションを型ごとの計算式で解決し、プログラムヘッダや動的リンクの
表を組む必要があり、それはリンカの仕事です。番地の決まった生のイメージは `-b` で
出せます。

---

## 8. 例

### 8.1 EM_MSP430 (105) — 表の無い機種

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

CALL !t :: 0xb0,0x12,t,t>>8
.reloc::t::pcrel16
JMP !t :: 0x00,0x3c,t,t>>8
.clrreloc::t
DB !t :: t
DW !t :: t,t>>8
DD !t :: t,t>>8,t>>16,t>>24
```

```
        .extern ext1                    ; 型は .elfextern から
        .extern ext2::abs32             ; .elftype の名前
        .global start
start:
        call    ext1                    ->  R_MSP430_ABS16   ext1 + 0
        jmp     start                   ->  R_MSP430_PCR16   start + 6
        dw      start                   ->  R_MSP430_ABS16   start + 0
        db      start                   ->  R_MSP430_ABS8    start + 0
        dd      ext2                    ->  R_MSP430_ABS32   ext2 + 0
```

同梱の `elfgen.axx` / `elfgen.s` です。優先順位の例は `elfprio.axx` /
`elfprio.s` です。

### 8.2 PowerPC64 (21) — 表に宣言を重ねる

`ppc64.axx`（ビッグエンディアン、ELFv1）と `ppc64le.axx`（リトルエンディアン、
ELFv2）はバイト順と ELF の記述だけを持つラッパーで、命令セット本体の
`ppc64_isa.axx` を取り込みます。64 ビット PowerPC ELF ABI の型を `.elftype` で、
命令欄（`REL24`、`REL14`、`ADDR16` 系、`ADDR16_DS`、`D34`、`PCREL34` など）を
`.elffield` で与えます。16 ビット欄のオフセットはビッグエンディアンで 2、
リトルエンディアンで 0 です。`.text` は `.elfsection` で 64 バイト整列です。

```
bl      ext+8           ->  R_PPC64_REL24         ext + 8
addis   3,2,msg@ha      ->  R_PPC64_ADDR16_HA     msg + 0
addi    3,3,msg@l       ->  R_PPC64_ADDR16_LO     msg + 0
ld      4,msg@l(3)      ->  R_PPC64_ADDR16_LO_DS  msg + 0
pld     5,ext@pcrel     ->  R_PPC64_PCREL34       ext + 0
.quad   ext             ->  R_PPC64_ADDR64        ext + 0
```

GNU as 2.42 とリロケーション・リンク結果が一致します。

### 8.3 ARM (40) — 表なし、REL の命令欄

`elfrel.axx` は `.elfbuiltin::0` で ARM を記述し、REL の命令欄を `.elffield` の
シフトと補正で書き戻します。

```
.elffield::call::0x00ffffff::0::2::-8  /* imm24、語単位、PC+8 */
.elffield::movw_abs_nc::0x000f0fff     /* imm4:imm12          */
```

```
bl   ext                   ->  eb fffffe   R_ARM_CALL         ((0 − 8) >> 2)
bl   ext+16                ->  eb 000002   R_ARM_CALL         ((16 − 8) >> 2)
movw r1,%lo16(dat+0x12345) ->  e302 1345   R_ARM_MOVW_ABS_NC
```

命令語・リロケーションは llvm-mc と一致し、`ld.lld -m armelf` でリンクした結果も
一致します。

### 8.4 RISC-V (243) — 命令欄、添え物、ラベル差、グループ

`riscv64.axx` は組み込みの表がデータ型しか持たない機種で、`CALL_PLT`・`BRANCH`・
`JAL`・`HI20`・`LO12_I`/`_S`・`PCREL` 対を `.elftype` と `.elffield` で与え、
`ld -m elf64lriscv` でリンクできる `.o` を出します。RISC-V には 8・16 ビットの
絶対型が無いので、`.elfwidth::1::0` と `.elfwidth::2::0` でその幅を「型なし」に
しています。

`elfpair.axx` はこれを取り込み、リンカ緩和に要るものを足します。

```
.elfextra::call::relax
.elfdiff::4::add32::sub32
.elfdiff::8::add64::sub64
.elfgroup::.group::foo::1::.text.foo
.elfsection::.meta::0x82
.elflink::.meta::.text
```

```
call  ext                ->  R_RISCV_CALL_PLT ext + 0, R_RISCV_RELAX
dword lend-_start        ->  R_RISCV_ADD32 lend + 0,   R_RISCV_SUB32 _start + 0
dword ext-_start+4       ->  R_RISCV_ADD32 ext + 4,    R_RISCV_SUB32 _start + 0
quad  foo-d0             ->  R_RISCV_ADD64 foo + 0,    R_RISCV_SUB64 d0 + 0
dword lend-_start+d0-d1+4 -> ADD32 lend + 4, ADD32 d0, SUB32 _start, SUB32 d1
dword -(lend-_start)     ->  R_RISCV_ADD32 _start + 0, R_RISCV_SUB32 lend + 0
uleb  lend-_start+300    ->  R_RISCV_SET_ULEB128 lend + 300, R_RISCV_SUB_ULEB128 _start
adv6  lend-_start        ->  R_RISCV_SET6 lend + 0,    R_RISCV_SUB6 _start
```

リロケーション・COMDAT グループ・`SHF_LINK_ORDER` のセクションヘッダは llvm-mc と
一致します。`ld.lld` のリンカ緩和で `call` が `jal` に縮んだ後も、どの差の値も
正しくなります（ULEB128 は長さを保ち、6 ビットの欄は上位ビットを保ちます）。

同じファイルは CFI も宣言していて（`.elfcfi::1::1::-8`、`R_RISCV_32_PCREL`）、
`.elfdiff::4` があるので、関数の長さと位置の進みは `.Lcfi<n>` に対する
ADD32/SUB32 で書かれます。リンク後の表は、llvm-mc の出力をリンクしたものと同じ
位置になります。

### 8.5 MIPS (8) — 書き戻し関数と `r_info`

`elfmips.axx`（MIPS32、REL）は `R_MIPS_26` と `R_MIPS_LO16` を `.elffield`、
`R_MIPS_HI16` を `.elfencode` の関数（`(加数 + 0x8000) >> 16`）で書き戻します。

```
lui   3,%hi(ext+0x18000)    ->  3c03 0002   R_MIPS_HI16
addiu 3,3,%lo(ext+0x18000)  ->  2463 8000   R_MIPS_LO16
jal   ext+8                 ->  0c00 0002   R_MIPS_26
```

命令語・リロケーションは llvm-mc と一致し、`ld.lld` でリンクした `.text` も
バイト単位で一致します。

`elfmips64.axx`（MIPS64 n64、リトルエンディアン）は `.elfrinfo` で型を `r_info` の
最上位バイトに置き、`readelf -r` が各項目を `R_MIPS_64/R_MIPS_NONE/R_MIPS_NONE`
のように llvm-mc の出力と同じに読みます。

### 8.6 x86-64 — CFI

`elfcfi.axx` は x86-64 の命令をいくつかだけ持ち、CFI を宣言します。

```
f:
        .cfi_startproc
        push    rbp
        .cfi_def_cfa_offset 16
        .cfi_offset rbp, -16
        mov     rbp,rsp
        .cfi_def_cfa_register rbp
        ...
        ret
        .cfi_endproc
```

`llvm-dwarfdump --eh-frame` が読む表（`0x1: CFA=RSP+16: RBP=[CFA-16], RIP=[CFA-8]`
など）は llvm-mc の出力と一致し、詰めを 4 にすると `.eh_frame` はバイト単位で
一致します。AArch64（`R_AARCH64_PREL32`）でも一致します。

### 8.7 1 ワード 16 ビットの機種 — 単位

`elfword.axx` は `.bits::16` の架空の機種で、`.elfunit::word` により加数と
シンボル値をワードで書きます。

```
j   f+3      ->  jmp12  f + 3      (byte なら f + 6)
dw  mid+1    ->  abs16  mid + 1    (byte なら mid + 2)
mid          st_value 1            (byte なら 2)
```

---

## 9. 実装の対応

両実装の関数は同じ規則で書かれ、互いに名前を指し合っています。

| 段 | axx.py | caxx.c |
|---|---|---|
| 実効表 | `elf_machine_table()` | `elf_machine_effective()`、`elf_field_effective()` |
| 命令欄の記述 | `insn_reloc_field_decl()` | `insn_reloc_field_decl()` |
| ビットの書き戻し | `_field_deposit()` | `field_deposit()` |
| ラベルの和と差 | `_elf_v2l_second()`、`_elf_v2l_finish()`、`_elf_diff_resolve()` | `label_get_value()`、`elf_v2l_finish()`、`elf_diff_resolve()` |
| 関数の呼び出し | `_elf_call_func()` | `elf_call_func()` |
| `r_info` | `_elf_r_info()` | `weo_rinfo()` |
| CFI の記録 | `cfi_processing()` | `adir_cfi()` |
| CFI の命令 | `_cfi_op_bytes()` | `cfi_op_bytes()` |
| `.eh_frame` | `_build_eh_frame()`、`_cfi_points()` | `build_eh_frame()`、`cfi_points()` |
| 書き出し | `write_elf_obj()` | `write_elf_obj()` |
| `--elfdesc` | `elf_desc_text()` | `elf_desc_print()` |
| 宣言の検査 | `check_elfdecls()` | `check_elfdecls()` |
