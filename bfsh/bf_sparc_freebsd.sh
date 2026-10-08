#!/bin/sh
#
# bf_sparc_freebsd.sh -- SPARC V9 で書いた bf インタプリタ (bf_sparc.s) を
#                        `!set OS = "freebsd"` で sparc.axx でアセンブルし、
#                        FreeBSD/sparc64 の実行ファイルにして、FreeBSD の
#                        qemu-sparc64-static (bsd-user) で走らせる。
#                        Linux 用は bf_sparc_linux.sh。
#
# 実行:
#       ./bfsh/bf_sparc_freebsd.sh                (build_bf_sparc_freebsd/bf を作る)
#       ./bfsh/bf_sparc_freebsd.sh mandelbrot.bf  (作ったあとでその .bf を走らせる)
#       ./bfsh/bf_sparc_freebsd.sh run            (作ったあとで同梱の mandelbrot.bf を走らせる)
#       AXX=paxx ./bfsh/bf_sparc_freebsd.sh       (Python 版でアセンブルする)
#       QEMU= ./bfsh/bf_sparc_freebsd.sh x.bf     (FreeBSD/sparc64 で、qemu を通さずに走らせる)
#
# bf_sparc.s はマクロ層の `!set OS` で FreeBSD 用と Linux 用を切り替える。
# 書いてある値に頼らず、その行を "freebsd" に書き換えた写しを組む。
# ld.lld はオブジェクトの OS/ABI を写すが、写さないリンカのためにリンクの
# 後で FreeBSD のブランドを付け直す。
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
    *) Q=qemu-sparc64-static
       command -v $Q >/dev/null 2>&1 || Q=qemu-sparc64 ;;
esac
QEMU=${QEMU-$Q}

W=build_bf_sparc_freebsd
mkdir -p $W

# `!set OS = "..."` の行を freebsd に書き換える。書き換わらなかったときは
# 違う OS 用のまま組んでしまうので止める。
sed 's/^!set OS *= *"[a-z]*"/!set OS = "freebsd"/' $S/bf_sparc.s > $W/bf.s
grep -q '^!set OS = "freebsd"' $W/bf.s || {
    echo "bf_sparc.s に !set OS の行が見つからない" >&2
    exit 1
}

$AXX $P/sparc.axx $W/bf.s --osabi FreeBSD -o $W/bf.o
$LD -o $W/bf $W/bf.o

if command -v brandelf >/dev/null 2>&1; then
    brandelf -t FreeBSD $W/bf
else
    elfedit --output-osabi FreeBSD $W/bf
fi

echo "built $W/bf (freebsd)"

if [ $# -gt 0 ]; then
    # bsd-user の qemu は FreeBSD の上でしか動かない。
    if [ $HOST != freebsd ]; then
        echo "$W/bf は freebsd 用なので、$HOST では走らせられない（bf_sparc_linux.sh を使う）" >&2
        exit 1
    fi
    $QEMU $W/bf "$@"
fi
