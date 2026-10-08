#!/bin/sh
#
# bf_aarch64_linux.sh -- AArch64 で書いた bf インタプリタ (bf_aarch64.s) を
#                        aarch64.axx でアセンブルし、Linux/AArch64 の実行
#                        ファイルにして、Linux の qemu-aarch64 (linux-user) で
#                        走らせる。
#
# 実行:
#       ./bf_aarch64_linux.sh                  (build_bf_aarch64_linux/bf を作る)
#       ./bf_aarch64_linux.sh mandelbrot.bf    (作ったあとでその .bf を走らせる)
#       ./bf_aarch64_linux.sh run              (作ったあとで同梱の mandelbrot.bf を走らせる)
#       AXX=paxx ./bf_aarch64_linux.sh         (Python 版でアセンブルする)
#       QEMU= ./bf_aarch64_linux.sh x.bf       (qemu を通さずに走らせる)
#
# qemu は qemu-aarch64-static（Debian の qemu-user-static）を探し、無ければ
# qemu-aarch64 を使う。AArch64 の Linux（Android の Termux を含む）では
# そのまま走らせる。FreeBSD の qemu-aarch64 は bsd-user で Linux の実行
# ファイルを走らせない。
#

set -e

AXX=${AXX:-caxx}
# AXX に axx の置き場（ディレクトリ）を入れている環境では、そこの caxx を使う。
if [ -d "$AXX" ]; then
    AXX=$AXX/caxx
fi
LD=${LD:-ld.lld}
HOST=$(uname -s | tr A-Z a-z)

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

# 走らせ方。ホストが AArch64 ならそのまま、違えば qemu に渡す。
case $(uname -m) in
    arm64|aarch64) Q= ;;
    *) Q=qemu-aarch64-static
       command -v $Q >/dev/null 2>&1 || Q=qemu-aarch64 ;;
esac
QEMU=${QEMU-$Q}

W=build_bf_aarch64_linux
mkdir -p $W

$AXX $P/aarch64.axx $S/bf_aarch64.s -m 183 --osabi Linux -o $W/bf.o
$LD -static -e _start -o $W/bf $W/bf.o

echo "built $W/bf (linux)"

if [ $# -gt 0 ]; then
    if [ $HOST != linux ]; then
        echo "$W/bf は linux 用なので、$HOST では走らせられない" >&2
        exit 1
    fi
    $QEMU $W/bf "$@"
fi
