#!/bin/sh
#
# bf_riscv64.sh -- RISC-V で書いた bf インタプリタを riscv64full.axx で
#                  アセンブルし、RISC-V 64 の実行ファイルにする。
#                  FreeBSD 用は bf_riscv64_freebsd.s、Linux 用は bf_riscv64.s。
#
# 実行:
#       ./bfsh/bf_riscv64.sh                (build_bf_riscv64/bf を作る)
#       ./bfsh/bf_riscv64.sh mandelbrot.bf  (作ったあとでその .bf を走らせる)
#       ./bfsh/bf_riscv64.sh run            (作ったあとで同梱の mandelbrot.bf を走らせる)
#       OS=linux ./bfsh/bf_riscv64.sh       (OS を選ぶ。既定はホストの OS)
#       AXX=paxx ./bfsh/bf_riscv64.sh       (Python 版でアセンブルする)
#       QEMU= ./bfsh/bf_riscv64.sh x.bf     (qemu を通さずに走らせる)
#
# RISC-V 以外のホストでは qemu のユーザーモードで走らせる。FreeBSD の
# qemu-riscv64-static は bsd-user なので FreeBSD 用しか、Linux の
# qemu-riscv64 は Linux 用しか走らせない。
#
# ld.lld は RISC-V の実行ファイルの OS/ABI を System V にするので、FreeBSD 用は
# リンクの後で FreeBSD のブランドを付ける（FreeBSD のカーネルはブランドを見る）。
#

set -e

AXX=${AXX:-caxx}
# AXX に axx の置き場（ディレクトリ）を入れている環境では、そこの caxx を使う。
if [ -d "$AXX" ]; then
    AXX=$AXX/caxx
fi
LD=${LD:-ld.lld}
HOST=$(uname -s | tr A-Z a-z)
OS=${OS:-$HOST}

# パターンファイルとアセンブリソースの置き場。スクリプトは bfsh/ に置くので、
# その一つ上が最上位。リポジトリでは patfile/ と asmsrc/ に分かれ、作業場では
# どちらも最上位にある（test1 と同じ判定）。
D=$(cd "$(dirname "$0")/.." && pwd)
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

case $OS in
    freebsd) SRC=bf_riscv64_freebsd.s; OSABI=FreeBSD ;;
    linux)   SRC=bf_riscv64.s;         OSABI=Linux ;;
    *)       echo "OS は freebsd か linux: $OS" >&2; exit 2 ;;
esac

# 走らせ方。ホストが RISC-V ならそのまま、違えば qemu に渡す。
case $(uname -m) in
    riscv|riscv64) Q= ;;
    *) Q=qemu-riscv64-static
       command -v $Q >/dev/null 2>&1 || Q=qemu-riscv64 ;;
esac
QEMU=${QEMU-$Q}

W=build_bf_riscv64
mkdir -p $W

$AXX $P/riscv64full.axx $S/$SRC --osabi $OSABI -o $W/bf.o
$LD -m elf64lriscv -static -e _start -o $W/bf $W/bf.o

if [ $OS = freebsd ]; then
    if command -v brandelf >/dev/null 2>&1; then
        brandelf -t FreeBSD $W/bf
    else
        elfedit --output-osabi FreeBSD $W/bf
    fi
fi

echo "built $W/bf ($OS)"

if [ $# -gt 0 ]; then
    # qemu のユーザーモードは自分と同じ OS の実行ファイルしか走らせない。
    if [ $OS != $HOST ]; then
        echo "$W/bf は $OS 用なので、$HOST では走らせられない" >&2
        exit 1
    fi
    $QEMU $W/bf "$@"
fi
