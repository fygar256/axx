#!/bin/sh
# faxx (axx の Forth 実装) を ccforth (Forth→C コンパイラ。https://github.com/ncw/ccforth) で
# コンパイルして実行ファイルにする。
#
#   ./build_ccforth.sh [出力ファイル名 (既定: faxx)]
#
# 出来た実行ファイルは gforth faxx.fs と同じ引数を取る:
#   ./faxx patfile/z80.axx asmsrc/z80.s -b z80.bin
#
# 必要なもの: ccforth、C コンパイラ、awk
# 環境変数:
#   CCFORTH  ccforth の場所 (既定: PATH 上の ccforth)
#   CC       C コンパイラ (既定: cc)
#   CFLAGS   C コンパイラに足す引数
#   MEMSIZE  Forth のメモリの大きさ (バイト。既定: 67108864 = 64MB)
#   KEEPC    指定すると、生成した C をそのファイル名で残す

CCF=${CCFORTH:-ccforth}
CC=${CC:-cc}
MEMSIZE=${MEMSIZE:-67108864}

die() { echo "build_ccforth.sh: $*" >&2; exit 1; }

# 出力先・KEEPC は呼び出したときのカレントディレクトリから見た名前にする
abspath() { case "$1" in /*) echo "$1" ;; *) echo "$(pwd)/$1" ;; esac; }
OUT=$(abspath "${1:-faxx}")
[ -n "$KEEPC" ] && KEEPC=$(abspath "$KEEPC")

command -v "$CCF" >/dev/null 2>&1 || die "ccforth が見つかりません (CCFORTH=$CCF)"
command -v "$CC" >/dev/null 2>&1 || die "C コンパイラが見つかりません (CC=$CC)"

SRC=$(cd "$(dirname "$0")" && pwd)/faxxsrc
[ -f "$SRC/faxx-cc.fs" ] || die "$SRC/faxx-cc.fs がありません"
[ -d "$OUT" ] && die "出力先 $OUT はディレクトリです"

T=$(mktemp -d) || exit 1
trap 'rm -rf "$T"' EXIT INT TERM

# 1) Forth → C。ccforth の included はカレントディレクトリから探すので faxxsrc/ で動かす
(cd "$SRC" && "$CCF" -c -entry cc-start -memsize "$MEMSIZE" faxx-cc.fs) > "$T/raw.c" \
  || die "ccforth が失敗しました"

# 2) ccforth の出力を 2 か所直す
#    - MEM_SIZE が既定の 1MB のまま書かれるので、MEMSIZE に置き換える
#    - _alloc_ptrs が使われる場所より後ろで宣言されるので、mem[] の宣言のすぐ後ろへ前倒しする
NALLOC=$(sed -n 's/^static cell_t _alloc_ptrs\[\([0-9][0-9]*\)\];.*/\1/p' "$T/raw.c" | head -n 1)
awk -v ms="$MEMSIZE" -v na="$NALLOC" '
  !ms_done && /^#define MEM_SIZE / { sub(/MEM_SIZE [0-9]+/, "MEM_SIZE " ms); ms_done = 1 }
  { print }
  na != "" && !na_done && /^static unsigned char mem\[MEM_SIZE\];/ {
    print "static cell_t _alloc_ptrs[" na "];"; na_done = 1
  }
  END { if (!ms_done) exit 1 }
' "$T/raw.c" > "$T/out.c" || die "生成された C に MEM_SIZE の定義が見つかりません"

[ -n "$KEEPC" ] && cp "$T/out.c" "$KEEPC"

# 3) C → 実行ファイル
"$CC" $CFLAGS -std=c11 -O1 -U_FORTIFY_SOURCE -D_FORTIFY_SOURCE=0 -fwrapv -fno-strict-aliasing -w \
  -o "$OUT" "$T/out.c" -lm || die "C のコンパイルに失敗しました"
echo "built $OUT"
