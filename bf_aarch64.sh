#!/bin/sh
#
# bf_aarch64.sh -- AArch64 で書いた bf インタプリタ (bf_aarch64.s) を
#                  aarch64.axx でアセンブルし、Linux/AArch64 の実行ファイルに
#                  する。
#
# 実行:
#       ./bf_aarch64.sh                  (build_bf_aarch64/bf を作る)
#       ./bf_aarch64.sh mandelbrot.bf    (作ったあとでその .bf を走らせる)
#       AXX=paxx ./bf_aarch64.sh         (Python 版でアセンブルする)
#       QEMU= ./bf_aarch64.sh x.bf       (qemu を通さずに走らせる)
#
# bf_aarch64.s は Linux 用だけなので、走らせられるのは Linux のホストだけ:
# AArch64 ならそのまま、ほかの CPU なら qemu-aarch64（linux-user）で。
# FreeBSD の qemu-aarch64-static は bsd-user で、FreeBSD の実行ファイルしか
# 走らせない。FreeBSD では作るところまで行う。
#

set -e

AXX=${AXX:-caxx}
LD=${LD:-ld.lld}
HOST=$(uname -s | tr A-Z a-z)

# パターンファイルとアセンブリソースの置き場。リポジトリでは patfile/ と
# asmsrc/ に分かれ、作業場ではどちらも同じ階層にある（test1 と同じ判定）。
D=$(cd "$(dirname "$0")" && pwd)
P=$D/patfile; [ -d "$P" ] || P=$D
S=$D/asmsrc;  [ -d "$S" ] || S=$D

# 走らせ方。ホストが AArch64 ならそのまま、違えば qemu に渡す。
case $(uname -m) in
    arm64|aarch64) Q= ;;
    *) Q=qemu-aarch64-static
       command -v $Q >/dev/null 2>&1 || Q=qemu-aarch64 ;;
esac
QEMU=${QEMU-$Q}

W=build_bf_aarch64
mkdir -p $W

$AXX $P/aarch64.axx $S/bf_aarch64.s -m 183 -o $W/bf.o
$LD -static -e _start -o $W/bf $W/bf.o

echo "built $W/bf (linux)"

if [ $# -gt 0 ]; then
    # qemu のユーザーモードは自分と同じ OS の実行ファイルしか走らせない。
    if [ $HOST != linux ]; then
        echo "$W/bf は linux 用なので、$HOST では走らせられない" >&2
        exit 1
    fi
    $QEMU $W/bf "$@"
fi
