# faxx — axx の gforth 実装 (愛称 Faxx)

`axx.py` (Paxx) / `caxx.c` の全機能を Forth（gforth 0.7.3 で確認）へ写したものです。パターンファイルとソースを読み、`-b`（生のバイナリ）、`-o`（ELF オブジェクト、`-g` で DWARF）、`-e` / `-E`（エクスポート）などを書きます。

```sh
gforth faxx.fs patfile/z80.axx asmsrc/z80.s -b z80.bin
gforth faxx.fs patfile/x86_64.axx asmsrc/hello.s -o hello.o -g
```

`faxx.fs` は `faxxsrc/load.fs`（部品の読み込み順）を読んで `main` を呼ぶだけの入口です。`axx.fs` は最初に作った中核だけの版で、そのまま残してあります。

## 移した範囲

- パターンファイル: コメント、`\` 継続、`.include`（循環・深さ・開けないときの診断）、`.sub` / `.endsub`、`.func`（ミニ言語）、`.echo`、`.map`、`.enum`、`.check`、`.reloc`、`.error`、`.free`、`.unordered`、`.passthru`、`.eol`、`.textmode`、`.elf*` 宣言
- 照合: 大文字＝文字定数、小文字＝シンボル、`!x` `!!x` `!Lx`、`!F` `!D` `!Q`、`!E` `!Y` `!S{{表}}`、`[[ ]]`、`\c` 止め文字
- 式: 256 ビット整数、倍精度、`flt{}` `dbl{}` `qad{}` `enflt{}` `endbl{}`、4 倍精度（binary128）の正しい丸め
- マクロ層（`!if` `!while` `!def` `!set` ほか）、ミニ言語（`.func` / `.call`）、VLIW
- ソース: ラベル、`.equ`（`::reloctype`）、`.org` `.align` `.ascii` `.zero` `.res*`、`.section`、`.global` `.extern` `.weak` ほか、`.cfi_*`
- 出力: `-b` `-o`（ELF32/64、REL/RELA、DWARF、`.eh_frame`）`-e` `-E` `-i` `-m` `-f` `--osabi` `--elfdesc` `-v` `-V` `-P` `-p`
- パス1の緩和反復とパス2、パス1/パス2のアドレス不一致の検出

## 注意

- 引数の誤りの文面（usage など）は `axx.py`（argparse）の形です。`caxx` は短い 1 行の文面なので、この点だけは両者で異なります。
- 巨大なパターンファイル向けの速度対策はしていません。
- 辞書は gforth の既定の大きさで足ります。

## 検証

`./cmp_forth` が `test1` の `caxx` 行と同じコマンド列を `caxx`（`/tmp/caxx` として作ったもの）と `faxx.fs` の両方で実行し、出力ファイルと標準出力・標準エラーを比べます（`test1` は実行しません）。

```sh
./cmp_forth          # 全部
./cmp_forth 5 12     # 5〜12 番目だけ
```

`./test_forth` は小さな機械のパターンで `axx.py` と比べる簡易版です。
