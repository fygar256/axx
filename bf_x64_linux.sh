#!/bin/sh
#
# bf_x64_linux.sh -- AArch64 で書いた bf インタプリタ (bf_aarch64.s) を
#                    a64tox64_axx.axx で x86_64 へ翻訳し、Linux/x86_64 の
#                    実行ファイルにする（Technical_Manual 3.18 節）。
#
# 実行:
#       ./bf_x64_linux.sh                    (build_bf_linux/bf を作る)
#       ./bf_x64_linux.sh mandelbrot.bf      (作ったあとでその .bf を走らせる)
#       AXX=paxx ./bf_x64_linux.sh           (Python 版で翻訳・アセンブルする)
#
# FreeBSD の Linuxulator (linux64.ko) でも走る。FreeBSD の ld は出力に
# FreeBSD のブランドを付けるので、FreeBSD で実行したときはリンクの後で
# brandelf -t Linux を付け直す。
#

set -e

AXX=${AXX:-caxx}
LD=${LD:-ld}

# パターンファイルとアセンブリソースの置き場。リポジトリでは patfile/ と
# asmsrc/ に分かれ、作業場ではどちらも同じ階層にある（test1 と同じ判定）。
D=$(cd "$(dirname "$0")" && pwd)
P=$D/patfile; [ -d "$P" ] || P=$D
S=$D/asmsrc;  [ -d "$S" ] || S=$D

W=build_bf_linux
mkdir -p $W

# 翻訳結果の先頭にランタイムの名前の宣言 (a64ext.s) を付ける。パイプにすると
# 翻訳の失敗を set -e が拾えないので、いったんファイルに書く。
$AXX $P/a64tox64_axx.axx $S/bf_aarch64.s -V > $W/bf_x64.body
cat $S/a64ext.s $W/bf_x64.body > $W/bf_x64.s
$AXX $P/x86_64.axx $W/bf_x64.s --osabi Linux -o $W/bf.o
$AXX $P/x86_64.axx $S/a64rt_axx.s --osabi Linux -o $W/a64rt.o
$LD -static -e _start $W/bf.o $W/a64rt.o -o $W/bf

if [ "$(uname -s)" = FreeBSD ]; then
    brandelf -t Linux $W/bf
fi

echo "built $W/bf"

if [ $# -gt 0 ]; then
    $W/bf "$@"
fi
