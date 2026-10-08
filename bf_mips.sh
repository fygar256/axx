#!/bin/sh
#
# bf_mips.sh -- MIPS で書いた bf インタプリタを mips.axx / mipsel.axx で
#               アセンブルし、MIPS32 o32 の実行ファイルにする。
#               FreeBSD 用は bf_mips_freebsd.s、Linux 用は bf_mips.s。
#
# 実行:
#       ./bf_mips.sh                        (build_bf_mips/bf を作る)
#       ./bf_mips.sh mandelbrot.bf          (作ったあとでその .bf を走らせる)
#       ENDIAN=el ./bf_mips.sh              (リトルエンディアン。build_bf_mipsel/bf)
#       OS=linux ./bf_mips.sh               (OS を選ぶ。既定はホストの OS)
#       AXX=paxx ./bf_mips.sh               (Python 版でアセンブルする)
#       QEMU= ./bf_mips.sh x.bf             (MIPS のホストで、qemu を通さずに走らせる)
#
# 走らせるのは qemu のユーザーモード（qemu-mips / qemu-mipsel）。FreeBSD の
# qemu-mips-static は bsd-user なので FreeBSD 用しか、Linux の qemu-mips は
# Linux 用しか走らせない。入口はどちらのソースも ld.lld の既定の __start。
#

set -e

AXX=${AXX:-caxx}
LD=${LD:-ld.lld}
HOST=$(uname -s | tr A-Z a-z)
OS=${OS:-$HOST}
ENDIAN=${ENDIAN:-eb}

# パターンファイルとアセンブリソースの置き場。リポジトリでは patfile/ と
# asmsrc/ に分かれ、作業場ではどちらも同じ階層にある（test1 と同じ判定）。
D=$(cd "$(dirname "$0")" && pwd)
P=$D/patfile; [ -d "$P" ] || P=$D
S=$D/asmsrc;  [ -d "$S" ] || S=$D

case $OS in
    freebsd) SRC=bf_mips_freebsd.s; OSABI=FreeBSD ;;
    linux)   SRC=bf_mips.s;         OSABI=Linux ;;
    *)       echo "OS は freebsd か linux: $OS" >&2; exit 2 ;;
esac

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

W=build_bf_$ARCH
mkdir -p $W

$AXX $P/$ARCH.axx $S/$SRC --osabi $OSABI -o $W/bf.o
$LD -static -o $W/bf $W/bf.o

# ld.lld はオブジェクトの OS/ABI を写すが、写さないリンカのために付け直す。
if [ $OS = freebsd ]; then
    if command -v brandelf >/dev/null 2>&1; then
        brandelf -t FreeBSD $W/bf
    else
        elfedit --output-osabi FreeBSD $W/bf
    fi
fi

echo "built $W/bf ($OS, $ARCH)"

if [ $# -gt 0 ]; then
    # qemu のユーザーモードは自分と同じ OS の実行ファイルしか走らせない。
    if [ $OS != $HOST ]; then
        echo "$W/bf は $OS 用なので、$HOST では走らせられない" >&2
        exit 1
    fi
    $QEMU $W/bf "$@"
fi
