#!/bin/sh
#
# bf_sparc_linux.sh -- SPARC V9 で書いた bf インタプリタ (bf_sparc.s) を
#                      `!set OS = "linux"` で sparc.axx でアセンブルし、
#                      Linux/sparc64 の実行ファイルにして、Linux の
#                      qemu-sparc64 (linux-user) で走らせる。
#
# 実行:
#       ./bfsh/bf_sparc_linux.sh                (build_bf_sparc_linux/bf を作る)
#       ./bfsh/bf_sparc_linux.sh mandelbrot.bf  (作ったあとでその .bf を走らせる)
#       ./bfsh/bf_sparc_linux.sh run            (作ったあとで同梱の mandelbrot.bf を走らせる)
#       AXX=paxx ./bfsh/bf_sparc_linux.sh       (Python 版でアセンブルする)
#       QEMU= ./bfsh/bf_sparc_linux.sh x.bf     (qemu を通さずに走らせる)
#
# qemu は qemu-sparc64-static（Debian の qemu-user-static）を探し、無ければ
# qemu-sparc64 を使う。sparc64 の Linux ではそのまま走らせる。FreeBSD では
# Linuxulator (linux64.ko) に入れた Linux の qemu
# (/compat/linux/usr/bin/qemu-sparc64) を使う（/usr/local/bin の qemu は
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

# 走らせ方。ホストが sparc64 ならそのまま、違えば qemu に渡す。
case $(uname -m) in
    sparc64) Q= ;;
    *) if [ $HOST = freebsd ]; then
           Q=/compat/linux/usr/bin/qemu-sparc64
       else
           Q=qemu-sparc64-static
           command -v $Q >/dev/null 2>&1 || Q=qemu-sparc64
       fi ;;
esac
QEMU=${QEMU-$Q}

W=build_bf_sparc_linux
mkdir -p $W

# `!set OS = "..."` の行を linux に書き換える。書き換わらなかったときは
# 違う OS 用のまま組んでしまうので止める。
sed 's/^!set OS *= *"[a-z]*"/!set OS = "linux"/' $S/bf_sparc.s > $W/bf.s
grep -q '^!set OS = "linux"' $W/bf.s || {
    echo "bf_sparc.s に !set OS の行が見つからない" >&2
    exit 1
}

$AXX $P/sparc.axx $W/bf.s --osabi Linux -o $W/bf.o
$LD -o $W/bf $W/bf.o

echo "built $W/bf (linux)"

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
