#!/bin/sh
#
# bf_riscv64_freebsd.sh -- RISC-V で書いた FreeBSD 用の bf インタプリタ
#                          (bf_riscv64_freebsd.s) を riscv64full.axx で
#                          アセンブルし、FreeBSD/RISC-V 64 の実行ファイルにして、
#                          FreeBSD の qemu-riscv64 (bsd-user) で走らせる。
#                          Linux 用は bf_riscv64_linux.sh。
#
# 実行:
#       ./bfsh/bf_riscv64_freebsd.sh                (build_bf_riscv64_freebsd/bf を作る)
#       ./bfsh/bf_riscv64_freebsd.sh mandelbrot.bf  (作ったあとでその .bf を走らせる)
#       ./bfsh/bf_riscv64_freebsd.sh run            (作ったあとで同梱の mandelbrot.bf を走らせる)
#       AXX=paxx ./bfsh/bf_riscv64_freebsd.sh       (Python 版でアセンブルする)
#       QEMU= ./bfsh/bf_riscv64_freebsd.sh x.bf     (qemu を通さずに走らせる)
#
# ld.lld は RISC-V の実行ファイルの OS/ABI を System V にするので、リンクの
# 後で FreeBSD のブランドを付ける（FreeBSD のカーネルはブランドを見る）。
#

set -e

AXX=${AXX:-caxx}
# AXX に axx の置き場（ディレクトリ）を入れている環境では、そこの caxx を使う。
if [ -d "$AXX" ]; then
    AXX=$AXX/caxx
fi
LD=${LD:-ld.lld}
HOST=$(uname -s | tr A-Z a-z)

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

# 走らせ方。ホストが RISC-V ならそのまま、違えば qemu に渡す。
case $(uname -m) in
    riscv|riscv64) Q= ;;
    *) Q=qemu-riscv64-static
       command -v $Q >/dev/null 2>&1 || Q=qemu-riscv64 ;;
esac
QEMU=${QEMU-$Q}

W=build_bf_riscv64_freebsd
mkdir -p $W

$AXX $P/riscv64full.axx $S/bf_riscv64_freebsd.s --osabi FreeBSD -o $W/bf.o
$LD -m elf64lriscv -static -e _start -o $W/bf $W/bf.o

if command -v brandelf >/dev/null 2>&1; then
    brandelf -t FreeBSD $W/bf
else
    elfedit --output-osabi FreeBSD $W/bf
fi

echo "built $W/bf (freebsd)"

if [ $# -gt 0 ]; then
    # bsd-user の qemu は FreeBSD の上でしか動かない。
    if [ $HOST != freebsd ]; then
        echo "$W/bf は freebsd 用なので、$HOST では走らせられない（bf_riscv64_linux.sh を使う）" >&2
        exit 1
    fi
    $QEMU $W/bf "$@"
fi
