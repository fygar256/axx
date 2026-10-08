#!/bin/sh
#
# bf_x64_freebsd.sh -- AArch64 で書いた bf インタプリタ (bf_aarch64.s) を
#                      a64tox64_axx.axx で x86_64 へ翻訳し、FreeBSD/amd64 の
#                      実行ファイルにする（Technical_Manual 3.18 節）。
#
# 実行:
#       ./bf_x64_freebsd.sh                  (build_bf_freebsd/bf を作る)
#       ./bf_x64_freebsd.sh mandelbrot.bf    (作ったあとでその .bf を走らせる)
#       ./bf_x64_freebsd.sh run              (作ったあとで同梱の mandelbrot.bf を走らせる)
#       AXX=paxx ./bf_x64_freebsd.sh         (Python 版で翻訳・アセンブルする)
#
# 入口はランタイムの __a64_start。FreeBSD/amd64 のカーネルは argc の場所を
# rdi で渡し、rsp を 8 バイトずらすので、__a64_start が rsp を合わせてから
# _start へ飛ぶ。
#

set -e

AXX=${AXX:-caxx}
# AXX に axx の置き場（ディレクトリ）を入れている環境では、そこの caxx を使う。
if [ -d "$AXX" ]; then
    AXX=$AXX/caxx
fi
LD=${LD:-ld}

# パターンファイルとアセンブリソースの置き場。リポジトリでは patfile/ と
# asmsrc/ に分かれ、作業場ではどちらも同じ階層にある（test1 と同じ判定）。
D=$(cd "$(dirname "$0")" && pwd)
P=$D/patfile; [ -d "$P" ] || P=$D
S=$D/asmsrc;  [ -d "$S" ] || S=$D

# 引数が run だけなら、作ったあとで同梱の mandelbrot.bf を走らせる。
# run のあとに .bf ファイルを書けば、それを走らせる。
if [ "$1" = run ]; then
    shift
    if [ $# -eq 0 ]; then
        set -- "$D/mandelbrot.bf"
    fi
fi

W=build_bf_freebsd
mkdir -p $W

# 翻訳結果の先頭にランタイムの名前の宣言 (a64ext.s) を付ける。パイプにすると
# 翻訳の失敗を set -e が拾えないので、いったんファイルに書く。
$AXX $P/a64tox64_axx.axx $S/bf_aarch64.s -V > $W/bf_x64.body
cat $S/a64ext.s $W/bf_x64.body > $W/bf_x64.s
$AXX $P/x86_64.axx $W/bf_x64.s --osabi FreeBSD -o $W/bf.o
$AXX $P/x86_64.axx $S/a64rt_axx_freebsd.s --osabi FreeBSD -o $W/a64rt.o
$LD -static -e __a64_start $W/bf.o $W/a64rt.o -o $W/bf

echo "built $W/bf"

if [ $# -gt 0 ]; then
    $W/bf "$@"
fi
