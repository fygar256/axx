#!/bin/sh
#
# bf_ppc64.sh -- PowerPC64 で書いた bf インタプリタ (bf_ppc64.s) を
#                ppc64.axx でアセンブルし、Linux/PowerPC64 ビッグエンディアン
#                (ELFv1) の実行ファイルにする。
#
# 実行:
#       ./bf_ppc64.sh                    (build_bf_ppc64/bf を作る)
#       ./bf_ppc64.sh mandelbrot.bf      (作ったあとでその .bf を走らせる)
#       AXX=paxx ./bf_ppc64.sh           (Python 版でアセンブルする)
#       QEMU= ./bf_ppc64.sh x.bf         (qemu を通さずに走らせる)
#
# bf_ppc64.s は Linux 用だけなので、走らせられるのは Linux のホストだけ:
# PowerPC64 ならそのまま、ほかの CPU なら qemu-ppc64（linux-user）で。
# FreeBSD の qemu-ppc64-static は bsd-user で、FreeBSD の実行ファイルしか
# 走らせない。FreeBSD では作るところまで行う。
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

# 走らせ方。ホストがビッグエンディアンの PowerPC64 ならそのまま、違えば
# qemu に渡す（ppc64le のホストでは走らない）。
case $(uname -m) in
    ppc64) Q= ;;
    *) Q=qemu-ppc64-static
       command -v $Q >/dev/null 2>&1 || Q=qemu-ppc64 ;;
esac
QEMU=${QEMU-$Q}

W=build_bf_ppc64
mkdir -p $W

$AXX $P/ppc64.axx $S/bf_ppc64.s -o $W/bf.o
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
