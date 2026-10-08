#!/bin/sh
#
# bf_x86_64_linux.sh -- x86_64 で書いた bf インタプリタ (bf_x86_64.s) を
#                       `!set OS = "linux"` に書き換えて x86_64.axx で
#                       アセンブルし、Linux/x86_64 の実行ファイルにする。
#                       x86_64 のホストではそのまま、ほかの CPU の Linux では
#                       qemu-x86_64 (linux-user) で走らせる。
#
# 実行:
#       ./bfsh/bf_x86_64_linux.sh                (build_bf_x86_64_linux/bf を作る)
#       ./bfsh/bf_x86_64_linux.sh mandelbrot.bf  (作ったあとでその .bf を走らせる)
#       ./bfsh/bf_x86_64_linux.sh run            (作ったあとで同梱の mandelbrot.bf を走らせる)
#       AXX=paxx ./bfsh/bf_x86_64_linux.sh       (Python 版でアセンブルする)
#       QEMU= ./bfsh/bf_x86_64_linux.sh x.bf     (qemu を通さずに走らせる)
#
# FreeBSD/amd64 では Linuxulator (linux64.ko) で走る。FreeBSD の ld は出力に
# FreeBSD のブランドを付けるので、リンクの後で brandelf -t Linux を付け直す。
#

set -e

AXX=${AXX:-caxx}
# AXX に axx の置き場（ディレクトリ）を入れている環境では、そこの caxx を使う。
if [ -d "$AXX" ]; then
    AXX=$AXX/caxx
fi
LD=${LD:-ld}
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

# 走らせ方。ホストが x86_64 ならそのまま、違えば qemu に渡す。
case $(uname -m) in
    amd64|x86_64) Q= ;;
    *) Q=qemu-x86_64-static
       command -v $Q >/dev/null 2>&1 || Q=qemu-x86_64 ;;
esac
QEMU=${QEMU-$Q}

W=build_bf_x86_64_linux
mkdir -p $W

# `!set OS = "freebsd"` の行を linux に書き換える。書き換わらなかったときは
# FreeBSD 用のまま組んでしまうので止める。
sed 's/^!set OS *= *"[a-z]*"/!set OS = "linux"/' $S/bf_x86_64.s > $W/bf.s
grep -q '^!set OS = "linux"' $W/bf.s || {
    echo "bf_x86_64.s に !set OS の行が見つからない" >&2
    exit 1
}

$AXX $P/x86_64.axx $W/bf.s --osabi Linux -o $W/bf.o
$LD -o $W/bf $W/bf.o

if [ $HOST = freebsd ]; then
    brandelf -t Linux $W/bf
fi

echo "built $W/bf (linux)"

if [ $# -gt 0 ]; then
    # qemu のユーザーモードは自分と同じ OS の実行ファイルしか走らせない。
    # FreeBSD の Linuxulator だけは、同じ CPU の Linux 用を走らせる。
    if [ $HOST != linux ] && ! { [ -z "$QEMU" ] && [ $HOST = freebsd ]; }; then
        echo "$W/bf は linux 用なので、$HOST では走らせられない" >&2
        exit 1
    fi
    $QEMU $W/bf "$@"
fi
