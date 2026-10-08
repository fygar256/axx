#!/bin/sh
#
# bf_x86_64.sh -- x86_64 で書いた bf インタプリタ (bf_x86_64.s) を
#                 x86_64.axx でアセンブルし、x86_64 の実行ファイルにする。
#                 bf_x86_64.s はマクロ層の `!set OS` で FreeBSD 用と Linux 用を
#                 切り替えるので、その行を選んだ OS に書き換えた写しを組む。
#
# 実行:
#       ./bf_x86_64.sh                   (build_bf_x86_64/bf を作る)
#       ./bf_x86_64.sh mandelbrot.bf     (作ったあとでその .bf を走らせる)
#       OS=linux ./bf_x86_64.sh          (OS を選ぶ。既定はホストの OS)
#       AXX=paxx ./bf_x86_64.sh          (Python 版でアセンブルする)
#
# FreeBSD で OS=linux にしたものは Linuxulator (linux64.ko) で走る。FreeBSD の
# ld は出力に FreeBSD のブランドを付けるので、リンクの後で brandelf -t Linux
# を付け直す。x86_64 以外のホストでは qemu-x86_64 で走らせる。
#

set -e

AXX=${AXX:-caxx}
# AXX に axx の置き場（ディレクトリ）を入れている環境では、そこの caxx を使う。
if [ -d "$AXX" ]; then
    AXX=$AXX/caxx
fi
LD=${LD:-ld}
HOST=$(uname -s | tr A-Z a-z)
OS=${OS:-$HOST}

# パターンファイルとアセンブリソースの置き場。リポジトリでは patfile/ と
# asmsrc/ に分かれ、作業場ではどちらも同じ階層にある（test1 と同じ判定）。
D=$(cd "$(dirname "$0")" && pwd)
P=$D/patfile; [ -d "$P" ] || P=$D
S=$D/asmsrc;  [ -d "$S" ] || S=$D

case $OS in
    freebsd) OSABI=FreeBSD ;;
    linux)   OSABI=Linux ;;
    *)       echo "OS は freebsd か linux: $OS" >&2; exit 2 ;;
esac

# 走らせ方。ホストが x86_64 ならそのまま、違えば qemu に渡す。
case $(uname -m) in
    amd64|x86_64) Q= ;;
    *) Q=qemu-x86_64-static
       command -v $Q >/dev/null 2>&1 || Q=qemu-x86_64 ;;
esac
QEMU=${QEMU-$Q}

W=build_bf_x86_64
mkdir -p $W

# `!set OS = "freebsd"` の行を選んだ OS に書き換える。書き換わらなかったときは
# 違う OS 用のまま組んでしまうので止める。
sed "s/^!set OS *= *\"[a-z]*\"/!set OS = \"$OS\"/" $S/bf_x86_64.s > $W/bf.s
grep -q "^!set OS = \"$OS\"" $W/bf.s || {
    echo "bf_x86_64.s に !set OS の行が見つからない" >&2
    exit 1
}

$AXX $P/x86_64.axx $W/bf.s --osabi $OSABI -o $W/bf.o
$LD -o $W/bf $W/bf.o

if [ $OS = linux ] && [ $HOST = freebsd ]; then
    brandelf -t Linux $W/bf
fi

echo "built $W/bf ($OS)"

if [ $# -gt 0 ]; then
    # qemu のユーザーモードは自分と同じ OS の実行ファイルしか走らせない。
    # FreeBSD の Linuxulator だけは、同じ CPU の Linux 用を走らせる。
    if [ $OS != $HOST ] && ! { [ -z "$QEMU" ] && [ $HOST = freebsd ]; }; then
        echo "$W/bf は $OS 用なので、$HOST では走らせられない" >&2
        exit 1
    fi
    $QEMU $W/bf "$@"
fi
