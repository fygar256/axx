#!/bin/sh
# faxx を ccforth (Forth→C コンパイラ。https://github.com/ncw/ccforth) でコンパイルして実行ファイルにする。
#   ./build_ccforth.sh [出力ファイル名 (既定: faxx)]
# 必要なもの: ccforth (環境変数 CCFORTH で場所を指定。既定は PATH 上の ccforth)、C コンパイラ (cc / gcc / clang)
# 実行ファイルは gforth faxx.fs と同じ引数を取る:  ./faxx patfile/z80.axx asmsrc/z80.s -b z80.bin
OUT=${1:-faxx}
case "$OUT" in /*) ;; *) OUT=$(pwd)/$OUT ;; esac
CCF=${CCFORTH:-ccforth}
CC=${CC:-cc}
MEMSIZE=${MEMSIZE:-67108864}
R=$(cd "$(dirname "$0")" && pwd)
T=$(mktemp -d) || exit 1
trap 'rm -rf "$T"' EXIT
cd "$R/faxxsrc" || exit 1
# 1) Forth → C。ccforth の取り込み (included) はカレントディレクトリからなので faxxsrc/ で動かす
$CCF -c -entry cc-start -memsize $MEMSIZE faxx-cc.fs > "$T/out.c" || exit 1
# 2) ccforth の出力を 2 か所直す: メモリの大きさ (MEM_SIZE) と、使う前に宣言されていない _alloc_ptrs
python3 - "$T/out.c" $MEMSIZE <<'PY' || exit 1
import re,sys
p,ms=sys.argv[1],sys.argv[2]
s=open(p,encoding='utf-8',errors='surrogateescape').read()
s=s.replace('#define MEM_SIZE 1048576','#define MEM_SIZE '+ms,1)
m=re.search(r'static cell_t _alloc_ptrs\[(\d+)\];',s)
if m:
    k='static unsigned char mem[MEM_SIZE];'
    i=s.index(k)+len(k)
    s=s[:i]+'\nstatic cell_t _alloc_ptrs[%s];\n'%m.group(1)+s[i:]
open(p,'w',encoding='utf-8',errors='surrogateescape').write(s)
PY
[ -n "$KEEPC" ] && cp "$T/out.c" "$KEEPC"
# 3) C → 実行ファイル
$CC $CFLAGS -std=c11 -O1 -U_FORTIFY_SOURCE -D_FORTIFY_SOURCE=0 -fwrapv -fno-strict-aliasing -w -o "$OUT" "$T/out.c" -lm || exit 1
echo "built $OUT"
