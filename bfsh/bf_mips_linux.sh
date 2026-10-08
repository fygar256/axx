#!/bin/sh
#
# bf_mips_linux.sh -- MIPS で書いた Linux 用の bf インタプリタ (bf_mips.s) を
#                     mips.axx / mipsel.axx でアセンブルし、Linux/MIPS32 o32 の
#                     実行ファイルにして、Linux の qemu-mips / qemu-mipsel
#                     (linux-user) で走らせる。
#
# 実行:
#       ./bfsh/bf_mips_linux.sh                (build_bf_mips_linux/bf を作る)
#       ./bfsh/bf_mips_linux.sh mandelbrot.bf  (作ったあとでその .bf を走らせる)
#       ./bfsh/bf_mips_linux.sh run            (作ったあとで同梱の mandelbrot.bf を走らせる)
#       ENDIAN=el ./bfsh/bf_mips_linux.sh      (リトルエンディアン。build_bf_mipsel_linux/bf)
#       AXX=paxx ./bfsh/bf_mips_linux.sh       (Python 版でアセンブルする)
#       QEMU= ./bfsh/bf_mips_linux.sh x.bf     (MIPS の Linux で、qemu を通さずに走らせる)
#
# qemu は qemu-mips-static（Debian の qemu-user-static）を探し、無ければ
# qemu-mips を使う。FreeBSD では Linuxulator (linux64.ko) に入れた Linux の
# qemu (/compat/linux/usr/bin/qemu-mips) を使う（/usr/local/bin の qemu は
# bsd-user で、Linux の実行ファイルを走らせない）。
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
if [ $HOST = freebsd ]; then
    Q=/compat/linux/usr/bin/qemu-$ARCH
else
    Q=qemu-$ARCH-static
    command -v $Q >/dev/null 2>&1 || Q=qemu-$ARCH
fi
QEMU=${QEMU-$Q}

W=build_bf_${ARCH}_linux
mkdir -p $W

$AXX $P/$ARCH.axx $S/bf_mips.s --osabi Linux -o $W/bf.o
$LD -static -o $W/bf $W/bf.o

echo "built $W/bf (linux, $ARCH)"

if [ $# -gt 0 ]; then
    # FreeBSD では Linuxulator の上の Linux の qemu で走らせる。
    if [ $HOST != linux ] && [ $HOST != freebsd ]; then
        echo "$W/bf は linux 用なので、$HOST では走らせられない" >&2
        exit 1
    fi
    if [ -n "$QEMU" ] && ! command -v "$QEMU" >/dev/null 2>&1; then
        echo "$QEMU が無い（FreeBSD では Linux の qemu-user を /compat/linux に入れる）" >&2
        exit 1
    fi
    $QEMU $W/bf "$@"
fi
