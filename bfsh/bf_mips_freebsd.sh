#!/bin/sh
#
# bf_mips_freebsd.sh -- MIPS で書いた FreeBSD 用の bf インタプリタ
#                       (bf_mips_freebsd.s) を mips.axx / mipsel.axx で
#                       アセンブルし、FreeBSD/MIPS32 o32 の実行ファイルにして、
#                       FreeBSD の qemu-mips-static / qemu-mipsel-static
#                       (bsd-user) で走らせる。Linux 用は bf_mips_linux.sh。
#
# 実行:
#       ./bfsh/bf_mips_freebsd.sh                (build_bf_mips_freebsd/bf を作る)
#       ./bfsh/bf_mips_freebsd.sh mandelbrot.bf  (作ったあとでその .bf を走らせる)
#       ./bfsh/bf_mips_freebsd.sh run            (作ったあとで同梱の mandelbrot.bf を走らせる)
#       ENDIAN=el ./bfsh/bf_mips_freebsd.sh      (リトルエンディアン。build_bf_mipsel_freebsd/bf)
#       AXX=paxx ./bfsh/bf_mips_freebsd.sh       (Python 版でアセンブルする)
#       QEMU= ./bfsh/bf_mips_freebsd.sh x.bf     (FreeBSD/mips で、qemu を通さずに走らせる)
#
# 入口は ld.lld の既定の __start。ld.lld はオブジェクトの OS/ABI を写すが、
# 写さないリンカのためにリンクの後で FreeBSD のブランドを付け直す。
#

set -e

AXX=${AXX:-caxx}
# AXX に axx の置き場（ディレクトリ）を入れている環境では、そこの caxx を使う。
if [ -d "$AXX" ]; then
    AXX=$AXX/caxx
fi
LD=${LD:-ld.lld}
HOST=$(uname -s | tr A-Z a-z)
ENDIAN=${ENDIAN:-eb}

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

case $ENDIAN in
    eb) ARCH=mips ;;
    el) ARCH=mipsel ;;
    *)  echo "ENDIAN は eb か el: $ENDIAN" >&2; exit 2 ;;
esac

# 走らせ方。MIPS のホストはバイト順が決まらないので、ここでは見分けず qemu に
# 渡す。そのまま走らせるときは QEMU= を空にする。
Q=qemu-$ARCH-static
command -v $Q >/dev/null 2>&1 || Q=qemu-$ARCH
QEMU=${QEMU-$Q}

W=build_bf_${ARCH}_freebsd
mkdir -p $W

$AXX $P/$ARCH.axx $S/bf_mips_freebsd.s --osabi FreeBSD -o $W/bf.o
$LD -static -o $W/bf $W/bf.o

if command -v brandelf >/dev/null 2>&1; then
    brandelf -t FreeBSD $W/bf
else
    elfedit --output-osabi FreeBSD $W/bf
fi

echo "built $W/bf (freebsd, $ARCH)"

if [ $# -gt 0 ]; then
    # bsd-user の qemu は FreeBSD の上でしか動かない。
    if [ $HOST != freebsd ]; then
        echo "$W/bf は freebsd 用なので、$HOST では走らせられない（bf_mips_linux.sh を使う）" >&2
        exit 1
    fi
    $QEMU $W/bf "$@"
fi
