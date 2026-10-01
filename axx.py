#!/usr/bin/env python3
"""axx — パターンファイル駆動の汎用アセンブラ（Python 実装、愛称 Paxx）。

普通のアセンブラは特定の命令セットをコードの中に持つが、axx は持たない。
「ニーモニックの書式 → 機械語のバイト列」という対応はすべて外部のテキスト
ファイル（`.axx` パターンファイル）にあり、これを差し替えるだけで同じエンジンが
別の ISA（x86_64 / AArch64 / Z80 / VLIW・EPIC ...）を扱う。

    axx.py <パターンファイル.axx> <ソース.s> -o <出力.o>

パターンファイルの 1 行は 3 欄でできている:

    命令の書式 :: エラー条件 :: 出力バイト列

処理の流れ（入口は Assembler.run()）:

  1. パターンファイル読み込み      PatternFileReader.readpat()
       `.INCLUDE` を再帰で展開し、各行を "::" で最大 6 欄に割る。
  2. マクロ展開                    MacroPreprocessor.expand()
       `!def` / `!if` / `!while` 等の行指向マクロを、アセンブルの前に潰す。
  3. パス1（長さの収束）           最大 MAX_RELAX 回
       可変長命令の長さが前方参照ラベルの値で決まるので、1 回では確定しない。
       前回の反復で得た値を推定値として使い、全ラベルのアドレスが前回と
       一致するまで繰り返す。これをリラクゼーションと呼ぶ。
  4. パス2（コード生成）           1 回だけ
       確定したアドレスで実際のバイト列と ELF リロケーションを作る。パス1と
       アドレスが食い違っていたら明示的にエラーにし、誤ったバイナリは出さない。
  5. 出力                          ELF オブジェクト / 生バイナリ / ラベル TSV

計算能力は 3 層に分かれており、停止性の扱いがそれぞれ違う:

  マクロ層    MacroPreprocessor  アセンブル前のテキスト変換。制限は無い
  パターン層  PatternMatcher     意図的にチューリング不完全。照合の停止性を保証
  ミニ言語    MiniInterp         `.call` で名指しされたときだけ動く。上限付き

C に移した caxx.c が同じディレクトリにあり、両者は同じ入力に対して同じバイト列を
出すことを目標に保守されている。食い違いが出たらどちらかのバグとして扱う。
"""


from decimal import Decimal, Context, localcontext, ROUND_HALF_EVEN
try:
    import readline
except ImportError:
    pass
import ast
import functools
import itertools
import struct
import sys
import os
import math
import re
import tempfile
import uuid


# パス1の反復中、「まだ一度も値が確定していない」ことを「値が 0 である」と
# 区別するための番兵。None や 0 を使うと、本当に 0 番地にあるラベルと
# 見分けが付かなくなる。
_RELAXATION_SENTINEL = object()


# いま動いている AssemblerState。状態を持たないモジュール関数の diag() が
# ここを見る。「今のパスで診断を出してよいか」の判定と had_error の管理は
# AssemblerState 側にあるので、その橋渡しとして使う。
_ACTIVE_STATE = None


def diag(text, set_error=True, force=False):
    """診断行を 1 本出す。

    set_error で had_error を立てるかを、force でパスに関わらず出すかを選ぶ。
    AssemblerState がまだ無い時期（引数解析中など）は stderr へ直接書く。
    """
    st = _ACTIVE_STATE
    if st is None:
        print(text, file=sys.stderr)
        return True
    return st.diag(text, set_error=set_error, force=force)


def diag_error(msg, force=False):
    """エラーとして 1 行出し、had_error を立てる。"""
    return diag(f" error - {msg}", set_error=True, force=force)


def diag_warning(msg, force=False):
    """警告として 1 行出す。had_error は立てないので出力は作られる。"""
    return diag(f" warning - {msg}", set_error=False, force=force)


# 式をどちらの文脈で読んでいるか。パターンファイル側とアセンブリソース側で
# 使える記法が違う（`!!!` などはパターン専用）。
EXP_PAT = 0
EXP_ASM = 1


class ExprCaps:
    """式評価器で使える項の集合を表す記述子。

    同じ評価器をパターン行・アセンブリ行・ミニ言語・マクロ層から呼ぶが、
    どこでも全部の項が意味を持つわけではない。どれを許すかをこの記述子に
    持たせ、評価器本体は呼び出し元を知らずにこれだけを見る。
    """

    __slots__ = ('name', 'patvars', 'vliw', 'labels', 'loc', 'syms')

    def __init__(self, name, patvars=False, vliw=False,
                 labels=True, loc=True, syms=True):
        self.name = name
        self.patvars = patvars
        self.vliw = vliw
        self.labels = labels
        self.loc = loc
        self.syms = syms

    def __repr__(self):
        return f"<ExprCaps {self.name}>"


# パターン行はすべて使える。アセンブリ行にはパターン変数と VLIW 計数が無い。
# ミニ言語はラベル・`$$`・`#記号` は読めるが、`.func` 本体の実行中は
# パターン変数を束縛しているものが無いので、それだけ落とす。
CAPS_PAT = ExprCaps('pattern', patvars=True, vliw=True)
CAPS_ASM = ExprCaps('assembly')
CAPS_MINI = ExprCaps('mini language')
# 式の評価モード。'i' が整数、'f' が IEEE-754 倍精度。error_patterns と
# 浮動小数点オペランドの評価で 'f' に切り替わる。
# 実際に読まれるのは AssemblerState.exp_typ のほうで、このモジュール変数は
# 現在どこからも参照されていない。
exp_typ = 'i'


# パターン中の `[[` / `]]`（省略可能グループ）を 1 文字に潰した内部表現。
# 2 文字のままだと以降の走査がすべて 2 文字先読みを強いられるので、
# 印字できない 1 文字に置き換えてから扱う。
OB = chr(0x90)
CB = chr(0x91)

# ソース行の「本物の」VLIW スロット区切り `!!` と終端 `!!!!` を 1 文字に
# 潰した内部表現。`\!\!` とエスケープされた「文字としての !!」と
# 区別するために使う。StringUtils.resolve_vliw_escapes() を参照。
VLIW_SEP = chr(0x92)
VLIW_STOP = chr(0x93)


# 未定義ラベルの値を表す番兵。None ではなく巨大な整数にしてあるのは、
# ラベル値が `label+4` や `label-$$` のように普通の算術へ流れ込むため。
# 整数にしておけば例外を出さずに「未定義性」が計算結果へ伝わっていく。
# VAR_UNDEF はパターン変数側の未束縛値で、マッチしなかった省略可能
# オペランドが 0 として読まれるのと同じ 0。
UNDEF = (1 << 1024) - 1
VAR_UNDEF = 0

# `.check` の許可リストに `""` が書かれたときに積む印。「その位置は省略可、
# 省略時は VAR_UNDEF」を意味する。シンボル名は get_symbol_word() で必ず
# 1 文字以上・大文字化されるため、空文字が実在のシンボル名と衝突しない。
CHECK_OMIT = ''

# UNDEF から算術で派生した値を「未定義由来」と判定する閾値。UNDEF そのものと
# 完全一致しなくても（`UNDEF+4` など）、この大きさなら未定義由来とみなす。
_UNDEF_DERIVED_THRESHOLD = 1 << 768


# axx は 256bit 整数・128bit 浮動小数点までを正当に扱うので、2**256 程度までは
# 本物の値でありうる。その帯に入った値については上の閾値ヒューリスティックが
# 誤判定しうることを、一度だけ警告する。
_UNDEF_SANE_CEILING = 1 << 256
_undef_ceiling_warned = False

# `*(値, 位置)` のバイト抽出でシフトさせる最大ビット数。これを超えると結果は
# 符号（0 か -1）にしかならないので、頭打ちにしても値は変わらず、巨大な
# シフト量を渡されたときの暴走だけを防げる。_SEXT_MAX_BITS は `x'bits` の
# 符号拡張幅の上限で、超えたら 0 にして警告する。
_BYTE_EXTRACT_SHIFT_MAX = 1 << 20
_SEXT_MAX_BITS = 128



def op_msb(v):
    """`@v` — 最上位の立っているビットの位置を右から数えて返す。

    ヘビマルマッタ演算子。非数・無限は 0 とする。
    """
    if isinstance(v, float):
        if v != v or v in (float('inf'), float('-inf')):
            return 0
    try:
        r = int(abs(v))
    except (OverflowError, ValueError):
        return 0
    b = 0
    while r:
        r >>= 1
        b += 1
    return b


def op_sext(x, bits):
    """`x'bits` — ビット bits-1 を符号ビットとみなした符号拡張。

    返り値は (値, 伝えるべき文言か None, 成否)。報告はせず呼び出し側に任せる。
    """
    try:
        x = int(x)
        bits = int(bits)
    except (ValueError, OverflowError):
        return 0, None, False
    if bits <= 0:
        return 0, None, True
    if bits > _SEXT_MAX_BITS:
        return 0, (f"sign-extension bit width {bits} exceeds maximum "
                   f"{_SEXT_MAX_BITS}, result set to 0"), True
    return ((x & ~((~0) << bits)) | ((~0) << bits if (x >> (bits - 1)) & 1 else 0),
            None, True)


def op_byte(x, index):
    """`*(x, index)` — 下位から数えて index バイト目より上を残した値。

    返り値は (値, 伝えるべき文言か None)。シフト量は上限で頭打ちにする。
    """
    try:
        index = int(index)
    except (OverflowError, ValueError):
        return 0, "non-finite byte-extract offset in *(expr, expr)"
    if index < 0:
        return 0, "negative byte-extract offset in *(expr, expr)"
    try:
        x = int(x)
    except (OverflowError, ValueError):
        return 0, "non-finite value in *(expr, expr) byte extract"
    return x >> min(index * 8, _BYTE_EXTRACT_SHIFT_MAX), None


def _ieee_pow(a, b):
    """`**` の浮動小数点版。IEEE-754 の定義域外の答えを C 側とそろえる。

    負の底に非整数指数を与えた定義域エラーでは、glibc の pow() が符号ビットの
    立った nan (0xfff8...) を返す。caxx.c と突き合わせて実測で確認したうえで、
    同じビットパターンになるよう copysign で符号を付けている。
    """
    a = float(a)
    b = float(b)
    if math.isnan(a) or math.isnan(b):
        return float('nan')
    if a == 0.0 and b < 0.0:
        return float('inf')
    if a < 0.0 and b != math.floor(b):
        return math.copysign(float('nan'), -1.0)
    try:
        return math.pow(a, b)
    except OverflowError:
        if a < 0.0 and int(b) % 2 != 0:
            return float('-inf')
        return float('inf')
    except ValueError:
        return math.copysign(float('nan'), -1.0)


def _is_undef_derived(v):
    """値が未定義ラベル由来かを閾値で判定する。

    _UNDEF_SANE_CEILING と閾値の間に入った値は正当な巨大値と区別が付かない
    ので、そのときだけ一度警告してから「未定義由来ではない」と答える。
    """
    global _undef_ceiling_warned
    if v == UNDEF:
        return True
    if isinstance(v, int):
        av = abs(v)
        if _UNDEF_SANE_CEILING <= av < _UNDEF_DERIVED_THRESHOLD and not _undef_ceiling_warned:
            _undef_ceiling_warned = True
            diag(" warning - a value larger than 2**256 was computed; the UNDEF-sentinel "
                 "heuristic treats it as a legitimate large value (not undefined-derived) "
                 "and may fail to detect it if it actually originated from an undefined "
                 "label.", set_error=False)
        return av >= _UNDEF_DERIVED_THRESHOLD
    return False


@functools.lru_cache(maxsize=None)
def _lead_caps(pat_text):
    """命令書式の先頭にある大文字の連なりを返す。

    パターン索引の鍵に使う。空白は読み飛ばし、大文字以外が出たところで止める。
    返り値は (大文字の連なり, その直後が索引を閉じてよい文字か)。閉じてよいのは
    次が小文字・数字・`!`・`\\`・`[` のいずれでもないとき、つまりニーモニックが
    そこで終わっているときだけで、そうでなければ前方一致の見落としが起きる。
    lru_cache にしてあるのは、同じ書式が照合のたびに何度も問われるため。
    """
    p = []
    i = 0
    n = len(pat_text)
    while i < n:
        ch = pat_text[i]
        if ch in CAPITAL:
            p.append(ch)
        elif ch == ' ':
            pass
        else:
            break
        i += 1
    nxt = pat_text[i] if i < n else ''
    closed = nxt not in _PFX_OPEN
    return ''.join(p), closed


# 行の位置によらず効き方が変わらないディレクティブ。パターンファイルの先頭に
# 並ぶこれらは、ソースを 1 行読むたびに解釈し直す必要がないので、
# _pat_hoist_scan() が「先に 1 回だけ処理してよい塊」として切り出す。
_HOIST_TEXT_ONLY = ('.check', '.clrcheck', '.reloc', '.clrreloc',
                    '.symbolc', '.passthru', '.eol', '.textmode',
                    '.elfmachine', '.elfclass', '.elfrela', '.elfwidth',
                    '.elfextern', '.elfdwarf', '.elfheader', '.elfsection',
                    '.elffield')


def _pat_text_dynamic(t):
    """欄の中身がソース行ごとに変わりうるか。

    `!` `$` `#` `@` `'` と小文字（パターン変数）のどれかを含めば、
    行をまたいで使い回せないので持ち上げの対象から外す。
    """
    for ch in t:
        if ch in "!$#@'":
            return True
        if 'a' <= ch <= 'z':
            return True
    return False


def _pat_is_name_list(t):
    """欄が「大文字の名前をカンマで並べたもの」だけで出来ているか。"""
    comma = False
    for ch in t:
        if ch == ',':
            comma = True
        elif ch in ' \t':
            pass
        elif not ('A' <= ch <= 'Z' or '0' <= ch <= '9' or ch == '_'):
            return False
    return comma


def _pat_dir_line_invariant(i):
    """このディレクティブ行を、ソースを読む前に 1 回だけ処理してよいか。

    値が定数で、評価の時点に依存しないものだけを真にする。判断に迷うものは
    必ず偽を返す（持ち上げないだけなので遅くなるだけで、結果は変わらない）。
    """
    name = i[0]
    if name == '.setsym':
        nm  = i[1] if i[1] else i[2]
        val = i[2] if i[1] else ''
        if _pat_text_dynamic(nm):
            return False
        if not val:
            return True
        v = val.lstrip(' \t')
        if v[:1] == '"':
            return True
        if v[:1] == '[':
            return False
        if _CONST_SETSYM_RE.match(val):
            return True
        return _pat_is_name_list(val)
    if name in _HOIST_TEXT_ONLY:
        for f in i[1:]:
            if f and any(ch in "!$#@" for ch in f):
                return False
        return True
    if name == '.bits':
        for f in i[1:]:
            if f and StringUtils.upper(f) not in ('BIG', 'LITTLE') \
                    and not _CONST_SETSYM_RE.match(f):
                return False
        return True
    if name in ('.padding', '.vliw'):
        for f in i[1:]:
            if f and not _CONST_SETSYM_RE.match(f):
                return False
        return True
    if name == '.error':
        return bool(_CONST_SETSYM_RE.match(i[1])) and i[2].lstrip(' \t')[:1] == '"'
    if name == '.elftype':
        if not i[1] or any(ch in "!$#@'" for ch in i[1]):
            return False
        for f in i[3:]:
            if f and not _CONST_SETSYM_RE.match(f):
                return False
        return bool(_CONST_SETSYM_RE.match(i[2]))
    return False


def _pat_hoist_scan(pat, isdir):
    """先頭から何行を事前処理に持ち上げられるかを数える。

    返り値は (持ち上げる行数, その中で設定される欄の名前の集合)。
    持ち上げた範囲が読んでいる名前を、あとの行の `.setsym` / `.clearsym` /
    `.free` が書き換えている場合は、順序依存が壊れるので持ち上げを諦める。
    """
    h = 0
    fields = set()
    while h < len(pat):
        i = pat[h]
        if i is None or not any(i):
            h += 1
            continue
        if not isdir[h] or not _pat_dir_line_invariant(i):
            break
        if i[0] == '.bits':
            fields.add('bits')
        elif i[0] == '.padding':
            fields.add('padding')
        elif i[0] == '.symbolc':
            fields.add('symbolc')
        elif i[0] == '.vliw':
            fields.add('vliw')
        h += 1
    if h <= 0 or h >= len(pat):
        return 0, fields

    reads = set()
    for row in range(h):
        i = pat[row]
        if i is None:
            continue
        for f in i[1:]:
            for tok in re.findall(r'[A-Z0-9_]+', f):
                reads.add(tok)
    for row in range(h, len(pat)):
        i = pat[row]
        if i is None or not isdir[row]:
            continue
        nm = i[0]
        if nm == '.setsym':
            if not i[1]:
                return 0, fields
            if _CONST_SETSYM_RE.match(i[2]):
                continue
            w = i[1]
        elif nm in ('.clearsym', '.free'):
            w = i[2] if i[2] else i[1]
            if not w:
                return 0, fields
        else:
            continue
        if StringUtils.upper(w) in reads:
            return 0, fields
    return h, fields


def _build_pat_index(pat, isdir):
    """先頭の大文字列をキーにしたパターン索引を作る。

    照合は全パターンを試して最良のものを選ぶ方式なので、素直に書くと 1 行あたり
    全件走査になる。ニーモニック先頭の大文字で先に絞り、どのキーにも属さない
    もの（先頭が大文字でない書式とディレクティブ）だけを always に入れて
    常に試す。これで結果を変えずに候補数を落とせる。
    """
    index = {}
    always = []
    maxkey = 0
    for row, i in enumerate(pat):
        pfx = ''
        closed = True
        if i and i[0]:
            pfx, closed = _lead_caps(i[0])
        if not pfx or isdir[row]:
            always.append(row)
            continue
        ent = index.get(pfx)
        if ent is None:
            ent = index[pfx] = ([], [])
        ent[1 if closed else 0].append(row)
        if len(pfx) > maxkey:
            maxkey = len(pfx)
    return index, always, maxkey


def _pat_candidates(index, maxkey, lin):
    """ソース行 1 行に対して、照合を試す価値のあるパターン行番号を返す。

    行の先頭から空白を飛ばしつつ大文字化した文字を積み、1 文字目・2 文字目…と
    伸ばした鍵で索引を引く。索引の片側（ent[0]）はニーモニックがそこで終わって
    いない書式なので常に候補になり、もう片側（ent[1]）はそこで終わっている
    書式なので、ソース側の次の文字が語を続ける文字でないときだけ候補にする。
    これを外すと `ADD` のパターンが `ADDS` の行に当たってしまう。
    返す番号は昇順にそろえる。パターンの採択は特異度スコアで決まるので
    順序は結果に影響しないが、診断の出る順を実装間でそろえるために並べる。
    """
    if not maxkey:
        return ()
    key = []
    nextraw = []
    for ci, ch in enumerate(lin):
        if ch == ' ':
            continue
        up = ch.upper()
        key.append(up if len(up) == 1 else '\0')
        nextraw.append(lin[ci + 1] if ci + 1 < len(lin) else '')
        if len(key) >= maxkey:
            break
    cand = []
    for k in range(1, len(key) + 1):
        ent = index.get(''.join(key[:k]))
        if ent is None:
            continue
        cand.extend(ent[0])
        if nextraw[k - 1] not in _PFX_WORD:
            cand.extend(ent[1])
    if len(cand) > 1:
        cand.sort()
    return cand


# 照合で使う文字クラス。パターンの `instruction` 欄では大文字が文字定数、
# 小文字がパターン変数という約束なので、この 2 つの区別が構文そのものを決める。
CAPITAL = "ABCDEFGHIJKLMNOPQRSTUVWXYZ"
LOWER = "abcdefghijklmnopqrstuvwxyz"
SET_OPS = "&|^+-"
DIGIT = '0123456789'
XDIGIT = "0123456789ABCDEF"
ALPHABET = LOWER + CAPITAL

# _PFX_OPEN … 先頭大文字列の直後にこれが来たら、ニーモニックはまだ続いている
#             （小文字のオペランド、`!` の式捕捉、`[[` の省略可能部分など）。
# _PFX_WORD … 語を構成する文字。ソース側で鍵の直後がこれなら語の途中なので、
#             そこで終わる書式を候補に入れてはいけない。
_PFX_OPEN = frozenset(LOWER + DIGIT + '!\\[')
_PFX_WORD = frozenset(ALPHABET + DIGIT + '_')


def _is_sub_name(s):
    """`.sub::名前` / `!S{{名前}}` に書ける名前かを見る。"""
    return bool(s) and all(c in _PFX_WORD for c in s)


def _dot_kw(s):
    """行頭のドット付きキーワードを大文字で取り出す。

    `.setsym::x::1` なら `.SETSYM`。ドットで始まらない行は空文字を返す。
    """
    t = s.strip()
    if not t.startswith('.'):
        return ''
    j = 1
    while j < len(t) and (t[j].isalnum() or t[j] == '_'):
        j += 1
    return StringUtils.upper(t[:j])


def _parse_func_header(l):
    """`.func` のヘッダを読み、(関数名, 引数名のリスト, エラー文言) を返す。

    書き方が 2 通りある。`.func 名前(引数, ...)` が現在の形で、`.func::名前::引数`
    が古い形。`.func` の直後に `::` が来るかどうかだけで選び分けるので、
    古いパターンファイルはそのまま動く。引数が無いときは `()` も省けるため、
    名前だけで行が終わる形も受ける。エラー文言は None なら成功。
    """
    t = l.strip()
    i = 1
    while i < len(t) and (t[i].isalnum() or t[i] == '_'):
        i += 1
    i = StringUtils.skipspc(t, i)

    if t[i:i + 2] == '::':
        hdr = []
        hi = 0
        while True:
            hi = StringUtils.skipspc(t, hi)
            fld = ''
            while hi < len(t):
                if t[hi:hi + 2] == '::':
                    hi += 2
                    break
                fld += t[hi]
                hi += 1
            hdr.append(fld.rstrip(' \t'))
            if len(t) <= hi:
                break
        nm = (hdr[1] if len(hdr) > 1 else '').strip()
        ps = [p.strip() for p in (hdr[2] if len(hdr) > 2 else '').split(',') if p.strip()]
        return nm, ps, None

    j = i
    while j < len(t) and (t[j].isalnum() or t[j] == '_'):
        j += 1
    nm = t[i:j]
    k = StringUtils.skipspc(t, j)

    if k >= len(t):
        return nm, [], None
    if t[k] != '(':
        return nm, [], (f" error - '.func': expected '(' or end of line after the "
                        f"name, got {t[k:]!r}")
    e = t.rfind(')')
    if e < k:
        return nm, [], " error - '.func': missing closing ')' in the parameter list."
    if t[e + 1:].strip():
        return nm, [], (f" error - '.func': trailing text after ')': "
                        f"{t[e + 1:].strip()!r}")
    ps = [p.strip() for p in t[k + 1:e].split(',') if p.strip()]
    return nm, ps, None


# ミニ言語の入れ子を数えるための開き／閉じキーワード。`.func` 本体を読む段階で
# 深さを数え、`.endfunc` がどの入れ子を閉じるのかを決めるのに使う。
_MINI_OPEN = frozenset(('.IF', '.FOR', '.WHILE'))
_MINI_CLOSE = frozenset(('.ENDIF', '.NEXT', '.ENDWHILE'))


class _MiniFunc:
    """ミニ言語の関数 1 個。`.func` から `.endfunc` までを持つ。

    lines は読み込んだ生の行で、body は MiniParser が構文木にしたもの。
    parent / children を持つのは入れ子定義のためで、呼び出し名の解決は
    内側から外側へたどる。file と line は診断にそのまま出す定義位置。
    """

    __slots__ = ('name', 'params', 'lines', 'body', 'parent', 'children',
                 'file', 'line', 'depth')

    def __init__(self, name, params, parent, file, line):
        self.name = name
        self.params = params
        self.lines = []
        self.body = None
        self.parent = parent
        self.children = {}
        self.file = file
        self.line = line
        self.depth = 0


# error_patterns の `;` のあとに書く番号から引く文言。番号 0 は使わない。
# 4 と 7 以上が空文字なのは意図したもので、エラーは起こるがメッセージは
# 出ない。パターンファイル側から `.error::n::"文言"` で追加・上書きできる。
# caxx.c の ERRORS と同じ並びでなければならない。
ERRORS = [
    "",
    "Invalid syntax.",
    "Address out of range.",
    "Value out of range.",
    "",
    "Register out of range.",
    "Port number out of range."
]


# `-o` の ELF 出力でリロケーションを書くための、マシンごとの組み込み表。
# 鍵は ELF の e_machine 値。各欄の意味:
#
#   name           診断に出す名前
#   elfclass       慣習的な ELF クラス。1 が ELF32、2 が ELF64。`-f` 未指定時の既定
#   is_rela        真なら .rela（加数をセクションに持つ）、偽なら .rel
#   width_guess    欄の幅（バイト）→ 型番号。型が明示されないラベル参照を
#                  幅から推測するときに使う。優先順位はこれが最も低い
#   pc_rel         PC 相対の型番号。加数の計算が絶対参照と変わる
#   extern_default 外部シンボル参照の既定の型
#   named          ソースの `::型名` とパターンの `.reloc` で書ける名前
#                  → (型番号, 欄の幅)
#   dwarf_abs      DWARF セクション内の絶対参照に使う型
#
# ここに無い e_machine も `-m` に書ける。そのときは型も欄もパターンファイルの
# ELF 記述（.elfmachine / .elftype / .elffield ...）から来る。RISC-V の欄が
# データ型だけで pc_rel が空なのはそのためで、CALL_PLT / BRANCH / JAL / HI20 /
# LO12 といった命令側の型は riscv64.axx が自分で宣言している。
_ELF_MACHINE_RAW = {
    3: dict(
        name='i386', elfclass=1, is_rela=False,
        width_guess={4: 2, 2: 20, 1: 22},
        pc_rel={2, 4, 13, 21, 23},
        extern_default=2,
        named={
            'abs32': (1, 4), 'pc32': (2, 4), 'rel32': (2, 4),
            'got32': (3, 4), 'plt32': (4, 4),
            'gotoff': (9, 4), 'gotpc': (10, 4),
            'abs16': (20, 2), 'pc16': (21, 2),
            'abs8': (22, 1), 'pc8': (23, 1),
        },
        dwarf_abs=1,
    ),
    4: dict(
        name='m68k', elfclass=1, is_rela=True,
        width_guess={4: 4, 2: 2, 1: 3},
        pc_rel={4, 5, 6},
        extern_default=4,
        named={
            'abs32': (1, 4), 'abs16': (2, 2), 'abs8': (3, 1),
            'pc32': (4, 4), 'rel32': (4, 4),
            'pc16': (5, 2), 'pc8': (6, 1),
        },
        dwarf_abs=1,
    ),
    20: dict(
        name='PowerPC', elfclass=1, is_rela=True,
        width_guess={4: 26, 2: 4},
        pc_rel={10, 26},
        extern_default=26,
        named={
            'abs32': (1, 4), 'abs16': (3, 2), 'abs16lo': (4, 2),
            'abs16hi': (5, 2), 'abs16ha': (6, 2),
            'pc32': (26, 4), 'rel32': (26, 4),
            'pc24': (10, 4), 'rel24': (10, 4),
        },
        dwarf_abs=1,
    ),
    21: dict(
        name='PowerPC64', elfclass=2, is_rela=True,
        width_guess={8: 38, 4: 26, 2: 4},
        pc_rel={10, 26, 44},
        extern_default=26,
        named={
            'abs64': (38, 8), 'abs32': (1, 4),
            'abs16': (3, 2), 'abs16lo': (4, 2),
            'abs16hi': (5, 2), 'abs16ha': (6, 2),
            'pc64': (44, 8), 'rel64': (44, 8),
            'pc32': (26, 4), 'rel32': (26, 4),
            'pc24': (10, 4), 'rel24': (10, 4),
        },
        dwarf_abs=38,
    ),
    22: dict(
        name='s390x', elfclass=2, is_rela=True,
        width_guess={8: 22, 4: 5, 2: 3, 1: 1},
        pc_rel={5, 16, 23},
        extern_default=5,
        named={
            'abs64': (22, 8), 'abs32': (4, 4), 'abs16': (3, 2), 'abs8': (1, 1),
            'pc64': (23, 8), 'pc32': (5, 4), 'rel32': (5, 4), 'pc16': (16, 2),
        },
        dwarf_abs=22,
    ),
    40: dict(
        name='ARM', elfclass=1, is_rela=False,
        width_guess={4: 3, 2: 5, 1: 8},
        pc_rel={1, 3},
        extern_default=3,
        named={
            'abs32': (2, 4), 'pc24': (1, 4),
            'pc32': (3, 4), 'rel32': (3, 4),
            'abs16': (5, 2), 'abs12': (6, 4), 'abs8': (8, 1),
        },
        dwarf_abs=2,
    ),
    42: dict(
        name='SuperH', elfclass=1, is_rela=True,
        width_guess={4: 2},
        pc_rel={2},
        extern_default=2,
        named={'abs32': (1, 4), 'pc32': (2, 4), 'rel32': (2, 4)},
        dwarf_abs=1,
    ),
    43: dict(
        name='SPARCV9', elfclass=2, is_rela=True,
        width_guess={8: 32, 4: 6, 2: 2, 1: 1},
        pc_rel={4, 5, 6, 46},
        extern_default=6,
        named={
            'abs64': (32, 8), 'abs32': (3, 4), 'abs16': (2, 2), 'abs8': (1, 1),
            'pc64': (46, 8), 'rel64': (46, 8),
            'pc32': (6, 4), 'rel32': (6, 4),
            'pc16': (5, 2), 'pc8': (4, 1),
        },
        dwarf_abs=32,
    ),
    62: dict(
        name='x86-64', elfclass=2, is_rela=True,
        width_guess={8: 1, 4: 2, 2: 12, 1: 14},
        pc_rel={2, 4, 9, 13, 15, 24},
        extern_default=2,
        named={
            'abs64': (1, 8), 'abs32': (10, 4), 'abs32s': (11, 4),
            'abs16': (12, 2), 'abs8': (14, 1),
            'pc32': (2, 4), 'rel32': (2, 4), 'plt32': (4, 4),
            'pc16': (13, 2), 'pc8': (15, 1), 'pc64': (24, 8),
            'got32': (3, 4), 'gotpcrel': (9, 4), 'got64': (27, 8),
        },
        dwarf_abs=1,
    ),
    183: dict(
        name='AArch64', elfclass=2, is_rela=True,
        width_guess={8: 257, 4: 261, 2: 262},
        pc_rel={260, 261, 262},
        extern_default=261,
        named={
            'abs64': (257, 8), 'abs32': (258, 4), 'abs16': (259, 2),
            'pc64': (260, 8), 'rel64': (260, 8),
            'pc32': (261, 4), 'rel32': (261, 4),
            'pc16': (262, 2), 'rel16': (262, 2),
            'movw_uabs_g0': (263, 4), 'movw_uabs_g0_nc': (264, 4),
            'movw_uabs_g1': (265, 4), 'movw_uabs_g1_nc': (266, 4),
            'movw_uabs_g2': (267, 4), 'movw_uabs_g2_nc': (268, 4),
            'movw_uabs_g3': (269, 4),
            'movw_prel_g0': (287, 4), 'movw_prel_g0_nc': (288, 4),
            'movw_prel_g1': (289, 4), 'movw_prel_g1_nc': (290, 4),
            'movw_prel_g2': (291, 4), 'movw_prel_g2_nc': (292, 4),
            'movw_prel_g3': (293, 4),
            'adr_prel_lo21': (274, 4),
            'adr_prel_pg_hi21': (275, 4), 'adrp': (275, 4),
            'adr_prel_pg_hi21_nc': (276, 4),
            'add_abs_lo12_nc': (277, 4),
            'ldst8_abs_lo12_nc': (278, 4),
            'tstbr14': (279, 4), 'condbr19': (280, 4),
            'jump26': (282, 4), 'call26': (283, 4),
            'ldst16_abs_lo12_nc': (284, 4),
            'ldst32_abs_lo12_nc': (285, 4),
            'ldst64_abs_lo12_nc': (286, 4),
            'ldst128_abs_lo12_nc': (299, 4),
            'got_ld_prel19': (309, 4),
            'got_page': (311, 4), 'adr_got_page': (311, 4),
            'got_lo12': (312, 4), 'ld64_got_lo12_nc': (312, 4),
            'ld64_gotpage_lo15': (313, 4),
        },
        dwarf_abs=257,
    ),
    243: dict(
        name='RISC-V', elfclass=2, is_rela=True,
        width_guess={8: 2, 4: 1, 2: 34, 1: 33},
        pc_rel=set(),
        extern_default=1,
        named={
            'abs64': (2, 8), 'abs32': (1, 4), 'abs16': (34, 2), 'abs8': (33, 1),
        },
        dwarf_abs=2,
    ),
}


def _build_elf_machine_tables(raw):
    """生の表から、引きやすい 3 つの写像を作る。

    named が名前 → 型番号、reloc_bytes が型番号 → 欄の幅、reverse が
    型番号 → 名前。reverse は setdefault なので、同じ型番号に別名が
    付いている場合（pc32 と rel32 など）は先に書いたほうが診断に出る。
    """
    out = {}
    for machine, entry in raw.items():
        named_types = {name: rt for name, (rt, _w) in entry['named'].items()}
        reloc_bytes = {rt: w for (rt, w) in entry['named'].values()}
        reverse = {}
        for name, rt in named_types.items():
            reverse.setdefault(rt, name)
        out[machine] = dict(entry,
                             named=named_types,
                             reloc_bytes=reloc_bytes,
                             reverse=reverse)
    return out


ELF_MACHINES = _build_elf_machine_tables(_ELF_MACHINE_RAW)


# 組み込みの表に無いマシンの土台。型が 1 つも無いので、パターンファイルが
# 何も宣言しなければ型の決まらない参照はリロケーションを出さない。
# 当てずっぽうの型番号を書いてリンカを騙すよりは、出さないほうを選ぶ。
_ELF_MACHINE_GENERIC = dict(
    name='', elfclass=2, is_rela=True, width_guess={}, pc_rel=frozenset(),
    extern_default=0, named={}, reloc_bytes={}, reverse={}, dwarf_abs=0)


def _elf_decl_type(state, named, text):
    """パターンファイルに書かれた型の綴りを型番号にする。

    数値ならそのまま、名前なら `.elftype` が宣言したもの、次に組み込みの表を
    見る。どれでもなければ None を返し、呼び出し側はその宣言を無視する。
    """
    if not text:
        return None
    s = ''.join(c for c in text if c not in ' \t')
    if not s:
        return None
    try:
        return int(s, 0)
    except ValueError:
        pass
    key = s.lower()
    rt = state.elftypes.get(key)
    if rt is None:
        rt = named.get(key)
    return rt


def elf_machine_table(state):
    """いま有効な ELF マシン記述を組み立てて返す。

    組み込みの表を土台に、パターンファイルの宣言（.elftype / .elffield /
    .elfclass / .elfrela / .elfwidth / .elfextern / .elfdwarf / .elfheader）を
    かぶせたものがここで出来る。同じ名前なら宣言のほうが組み込みに勝つ。
    これを 1 行ごとに作り直すと重いので (machine, decl_gen) を鍵にして覚える。
    decl_gen は宣言が増えるたびに進む世代番号なので、宣言を読み終えた時点で
    鍵が変わり、古い表が残ることはない。
    """
    e = state.elf
    key = (e.machine, e.decl_gen)
    if e.mach_cache_key == key:
        return e.mach_cache

    base = ELF_MACHINES.get(e.machine, _ELF_MACHINE_GENERIC)
    width_guess = dict(base['width_guess'])
    pc_rel      = set(base['pc_rel'])
    name        = base['name'] or ("machine %d" % e.machine)
    elfclass       = base['elfclass']
    is_rela        = base['is_rela']
    extern_default = base['extern_default']
    dwarf_abs      = base['dwarf_abs']

    named, reloc_bytes, reverse = {}, {}, {}
    _merged = [(nm, rt, base['reloc_bytes'].get(rt, 0))
               for nm, rt in base['named'].items() if nm not in state.elftypes]
    _merged += [(nm, rt, e.type_width.get(nm, 0)) for nm, rt in state.elftypes.items()]
    for nm, rt, w in _merged:
        named.setdefault(nm, rt)
        reverse.setdefault(rt, nm)
        if w:
            reloc_bytes.setdefault(rt, w)
    for nm in e.type_pcrel:
        rt = state.elftypes.get(nm)
        if rt is not None:
            pc_rel.add(rt)

    for nbytes, text in e.decl_width.items():
        rt = _elf_decl_type(state, named, text)
        if rt is not None:
            width_guess[nbytes] = rt
    rt = _elf_decl_type(state, named, e.decl_extern)
    if rt is not None:
        extern_default = rt
    rt = _elf_decl_type(state, named, e.decl_dwarf)
    if rt is not None:
        dwarf_abs = rt
    if e.decl_rela is not None:
        is_rela = bool(e.decl_rela)
    if e.decl_class is not None:
        elfclass = e.decl_class
    if e.decl_name and (e.decl_machine is None or e.decl_machine == e.machine):
        name = e.decl_name

    field = {}
    for text, fo in e.decl_field.items():
        rt = _elf_decl_type(state, named, text)
        if rt is not None:
            field.setdefault(rt, fo)

    tbl = dict(base, name=name, elfclass=elfclass, is_rela=is_rela,
               width_guess=width_guess, pc_rel=pc_rel,
               extern_default=extern_default, dwarf_abs=dwarf_abs,
               named=named, reloc_bytes=reloc_bytes, reverse=reverse,
               field=field)
    e.mach_cache_key = key
    e.mach_cache = tbl
    return tbl


def _reloc_same_width(mach, nbytes, want_pcrel):
    """欄の幅と PC 相対かどうかが一致する型を 1 つ探す。

    辞書を順に見て最初に当たったものを返すので、同じ幅の型が複数あるときは
    表に書いた順が結果を決める。見つからなければ None。
    """
    if not mach:
        return None
    for _nm, rt in mach['named'].items():
        if mach['reloc_bytes'].get(rt, 0) != nbytes:
            continue
        if (rt in mach['pc_rel']) == bool(want_pcrel):
            return rt
    return None


def _elf_section_attrs(state, name):
    """セクション名から (sh_flags, sh_type, 整列, 要素サイズ) を決める。

    名前の先頭を `.text` / `.data` / `.rodata` / `.bss` と照合して既定を作る。
    flags は 0x1 が WRITE、0x2 が ALLOC、0x4 が EXECINSTR。`.bss` だけ
    sh_type を 8 (SHT_NOBITS) にしてファイルに中身を持たせない。
    `.elfsection` の宣言があれば、名前からの推測を丸ごと置き換える。
    axx が名前の規則を持たないセクション（ベクタ表、note など）はこれで書く。
    """
    uname = name.upper()
    if   uname.startswith('.TEXT'):
        flags = 0x2 | 0x4
    elif uname.startswith('.DATA'):
        flags = 0x2 | 0x1
    elif uname.startswith('.RODATA'):
        flags = 0x2
    elif uname.startswith('.BSS'):
        flags = 0x2 | 0x1
    else:
        flags = 0x2
    sh_type = 8 if uname.startswith('.BSS') else 1
    align = None
    entsize = 0
    decl = state.elf.decl_sec.get(name.lower())
    if decl is not None:
        flags = decl[0]
        if decl[1] is not None:
            sh_type = decl[1]
        if len(decl) > 2 and decl[2] is not None:
            align = decl[2]
        if len(decl) > 3 and decl[3] is not None:
            entsize = decl[3]
    return flags, sh_type, align, entsize


def _elf_default_align(sh_type, is_elf64):
    """整列が書かれていないセクションの既定値。

    SHT_NOTE (7) だけ 4、ほかは 16。is_elf64 は現在使っていないが、
    caxx.c 側と呼び出し形をそろえるために残してある。
    """
    del is_elf64
    if sh_type == 7:
        return 4
    return 16



# ソースの `.type` に書ける名前 → ELF の STT_* 値。
ELF_SYM_TYPES = {
    'notype': 0, 'object': 1, 'func': 2, 'function': 2,
    'section': 3, 'file': 4, 'common': 5, 'tls': 6, 'tls_object': 6,
    'gnu_ifunc': 10, 'ifunc': 10,
}

# シンボル 1 個ぶんの属性。ソースの `.type` / `.size` / `.weak` / `.hidden` /
# `.protected` / `.internal` / `.other` / `.comm` がここに溜まる。
# 添字の名前が _SA_* で、タプルのまま持つのはシンボル数ぶん作られるため。
_SYM_ATTR_DEFAULT = (0, 0, 0, 0, 0, 0, 0)

_SA_TYPE, _SA_SIZE_SET, _SA_SIZE, _SA_OTHER, _SA_WEAK, _SA_COMMON, _SA_ALIGN = range(7)


def _sym_attr(state, name):
    """シンボルの属性を読む。無ければ既定のタプルを返す（表は増やさない）。"""
    return state.sym_attrs.get(name, _SYM_ATTR_DEFAULT)


def _sym_attr_slot(state, name):
    """シンボルの属性を書くための枠を返す。無ければリストで作って登録する。

    読むだけの _sym_attr と分けてあるのは、参照しただけのシンボルに
    属性の枠を作らせないため。
    """
    a = state.sym_attrs.get(name)
    if a is None:
        a = list(_SYM_ATTR_DEFAULT)
        state.sym_attrs[name] = a
    return a


def _sym_st_info(state, name, bind):
    """st_info を組む。`.weak` があればバインドを STB_WEAK に差し替える。"""
    a = _sym_attr(state, name)
    if a[_SA_WEAK]:
        bind = 2
    return ((bind & 0xF) << 4) | (a[_SA_TYPE] & 0xF)


def _sym_common_override(state, name, bpw, shndx, value, size):
    """`.comm` のシンボルを共通シンボルに書き換える。

    SHN_COMMON (0xfff2) に置き、st_value を整列、st_size をワード数×ワード幅に
    する。`.comm` でなければ渡された 3 つをそのまま返す。
    """
    a = _sym_attr(state, name)
    if not a[_SA_COMMON]:
        return shndx, value, size
    return 0xfff2, a[_SA_ALIGN], a[_SA_SIZE] * bpw


def _sym_size_of(state, name, bpw):
    """`.size` の値をバイト数で返す。ソースにはワード数で書くので幅をかける。"""
    a = _sym_attr(state, name)
    if not a[_SA_SIZE_SET]:
        return 0
    return a[_SA_SIZE] * bpw


def _reloc_named(state, mach, name):
    """リロケーション型の名前を番号にする。`.elftype` が組み込みの表に勝つ。"""
    if not name:
        return None
    key = name.lower()
    rt = state.elftypes.get(key)
    if rt is not None:
        return rt
    return mach['named'].get(key) if mach else None


def _reloc_reverse(state, mach, rtype):
    """リロケーション型の番号を名前にする（診断とリスティング用）。

    組み込みの表に無ければ `.elftype` の宣言を逆から探す。それも無ければ空文字。
    """
    if rtype is None:
        return ''
    nm = mach['reverse'].get(rtype, '') if mach else ''
    if nm:
        return nm
    for k, v in state.elftypes.items():
        if v == rtype:
            return k
    return ''


# AArch64 の「命令の中の欄を書き換える」リロケーションが、32bit 命令語の
# どのビットに値を置くか。各要素が (最下位ビット位置, ビット数) で、
# ADR/ADRP だけは値が 2 つの欄に分かれて入る（下位 2bit と上位 19bit）。
# 組み込みで持っているのは AArch64 のぶんだけで、他のマシンでは
# パターンファイルの `.elffield` が同じことを宣言する。
_A64_ADR_FIELDS = ((29, 2), (5, 19))
_A64_LO12_FIELD = ((10, 12),)
_A64_MOVW_FIELD = ((5, 16),)
AARCH64_INSN_RELOCS = {
    263: _A64_MOVW_FIELD, 264: _A64_MOVW_FIELD,
    265: _A64_MOVW_FIELD, 266: _A64_MOVW_FIELD,
    267: _A64_MOVW_FIELD, 268: _A64_MOVW_FIELD,
    269: _A64_MOVW_FIELD,
    287: _A64_MOVW_FIELD, 288: _A64_MOVW_FIELD,
    289: _A64_MOVW_FIELD, 290: _A64_MOVW_FIELD,
    291: _A64_MOVW_FIELD, 292: _A64_MOVW_FIELD,
    293: _A64_MOVW_FIELD,
    274: _A64_ADR_FIELDS,
    275: _A64_ADR_FIELDS, 276: _A64_ADR_FIELDS,
    277: _A64_LO12_FIELD,
    278: _A64_LO12_FIELD,
    279: ((5, 14),),
    280: ((5, 19),),
    282: ((0, 26),), 283: ((0, 26),),
    284: _A64_LO12_FIELD, 285: _A64_LO12_FIELD,
    286: _A64_LO12_FIELD, 299: _A64_LO12_FIELD,
    309: ((5, 19),),
    311: _A64_ADR_FIELDS,
    312: _A64_LO12_FIELD,
    313: _A64_LO12_FIELD,
}


def insn_reloc_field_decl(state, rtype):
    """`.elffield` で宣言された命令欄の記述を引く。無ければ None。"""
    if state is None or not state.elf.decl_field:
        return None
    return elf_machine_table(state)['field'].get(rtype)


def insn_reloc_field_mask(rtype, machine=183, state=None):
    """その型が命令語のどのビットを使うかのマスク。

    `.elffield` の宣言が最優先。無ければ AArch64 の組み込み表だけを見る。
    どちらも無ければ None で、「命令の中の欄ではない」ふつうのデータ
    リロケーションとして扱われる。
    """
    _fd = insn_reloc_field_decl(state, rtype)
    if _fd is not None:
        return _fd[0]
    if machine != 183:
        return None
    fields = AARCH64_INSN_RELOCS.get(rtype)
    if fields is None:
        return None
    mask = 0
    for lo, nbits in fields:
        mask |= ((1 << nbits) - 1) << lo
    return mask


class VLIWState:
    """`.vliw` の宣言と、組み立て中のバンドルの状態。

    bits がバンドル全体のビット数、instbits が命令 1 個のビット数、
    templatebits がテンプレート欄のビット数（0 なら非 EPIC、負なら左端に置く）、
    nop が隙間を埋める NOP、slotset が `EPIC::` 行で宣言されたスロットの
    組み合わせ、cnt が `!!` で結合された命令の数、stop がストップビット。
    """

    def __init__(self):
        self.instbits = 41
        self.nop = []
        self.bits = 128
        self.slotset = []
        self.flag = False
        self.templatebits = 0x00
        self.stop = 0
        self.cnt = 1


class ElfState:
    """`-o` の ELF 出力に関わる状態をまとめたもの。

    decl_* はパターンファイルの ELF 記述（.elfmachine / .elfclass / .elfrela /
    .elfwidth / .elfextern / .elfdwarf / .elfheader / .elfsection / .elffield）が
    書き込む先で、組み込みの表にかぶせて elf_machine_table() が実表を作る。
    decl_gen はそのキャッシュを捨てるための世代番号。
    """

    def __init__(self):
        self.osabi: int = 0
        self.objfile: str = ""
        self.machine: int = 62
        self.elf_class: int | None = None

        # パターンファイルの ELF 記述。読んだ時点では綴りのまま置いておき、
        # 型番号への解決は elf_machine_table() まで遅らせる。`.elftype` の
        # 宣言より先に `.reloc` が現れても解けるようにするため。
        self.decl_machine = None
        self.decl_name = ''
        self.decl_class = None
        self.decl_rela = None
        self.decl_width = {}
        self.decl_extern = ''
        self.decl_dwarf = ''
        self.decl_hdr = {}
        self.decl_field = {}
        self.decl_sec = {}
        self.type_width = {}
        self.type_pcrel = set()
        self.decl_gen = 0
        self.machine_from_cli = False
        self.mach_cache = None
        self.mach_cache_key = None

        # パス2で集まるリロケーション。tracking 中に式評価器がラベル参照を
        # 見つけると label_refs_seen に積まれ、どの出力ワードのどの変数から
        # 来たか（current_word_idx / var_to_label / capturing_var）を頼りに
        # 型と位置を決める。命令の中の欄に入る型は insn_reloc_hint で伝える。
        self.relocations = []
        self.tracking = False
        self.label_refs_seen = []
        self.current_word_idx: int = -1
        self.var_to_label: dict = {}
        self.capturing_var: str | None = None
        self.insn_reloc_hint: dict = {}

        # `-g` の DWARF 出力。line_map が .debug_line を作るための
        # 「アドレス ↔ ソース行」の対応。
        self.gen_debug: bool = False
        self.line_map: list = []

        self.reloctype_override: dict = {}


class RelaxationState:
    """パス1の反復（リラクゼーション）に属する状態。

    可変長命令の長さが前方参照ラベルの値で決まるため、1 回読んだだけでは
    アドレスが確定しない。前回の反復の値を推定値として使い、全ラベルの
    アドレスが前回と一致するまで繰り返す。繰り返しの上限は Assembler 側の
    MAX_RELAX (16) で、収束しなければ出力を書かずに中断する。
    """

    def __init__(self):
        # 現在のパス。0 が対話モード、1 が長さの収束、2 がコード生成。
        # 診断を出してよいのは 0 と 2 だけ（should_report_errors）。
        # パス1は推定値で動いているので、そこで出る「範囲外」は本物とは限らない。
        self.pas = 0

        # パス1で長さだけを知りたい区間。ここでは診断を抑える。
        self.pass1_size_mode = False

        # 前回の反復で得たラベル → アドレス。番兵のままなら反復は未実施。
        self.pass1_prev_label_pcs = _RELAXATION_SENTINEL

        # 前回の反復での値。今回の反復で前方参照の推定値として読む。
        self.relax_prev_values = {}

        # 最初の反復（relax_iter == 0）だけ真。まだ何も分かっていない段階で
        # 未定義ラベルを楽観的に扱い、短い符号化から試させるためのもの。
        self.relax_optimistic = False

        # 組み合わせ数の上限に当たったことを行ごとに一度だけ警告するための印。
        self.combo_budget_warned = set()


class AssemblerState:
    """アセンブル中の状態すべて。

    もともと平らな属性の集まりだったものを、VLIW / ELF / リラクゼーションの
    3 群だけ下位オブジェクトへ切り出してある。古い平らな名前は末尾の
    _FORWARDED_ATTRS が生成するプロパティで今も通るので、呼び出し側は
    どちらの綴りでも書ける。

    生成時に自分をモジュール変数 _ACTIVE_STATE へ入れる。状態を持たない
    モジュール関数の diag() がそこを見て診断の宛先を知る。
    """

    def __init__(self):
        global _ACTIVE_STATE
        _ACTIVE_STATE = self

        self._diag_pending = None

        self.outfile = ""
        self.expfile = ""
        self.expfile_elf = ""
        self.impfile = ""

        self.pc = 0
        self.padding = 0

        self.pc_instr_start = 0
        self.pc_instr_end = 0
        self._in_binary_list = False

        # ラベルとシンボルに使える文字。`.labelc` / `.symbolc` で広げられる。
        # シンボル側に `-` が入っているのが、`(IX-5)` のような負の変位を
        # シンボルの続きとして一度試してから後退できる理由。
        self.lwordchars = DIGIT + ALPHABET + "_."
        self.swordchars = DIGIT + ALPHABET + "_%$-~&|"

        self.current_section = ".text"
        self.current_file = ""

        # ラベル・シンボルの各表。patsymbols はパターンファイルが定義した
        # シンボルで、ソースのラベルと名前が衝突したらエラーにする。
        # pat / pat_isdir が読み込んだパターン行とそれがディレクティブかの印、
        # pat_index / pat_always / pat_maxkey が照合を絞るための索引、
        # hoist_* が「ソースを読む前に 1 回だけ処理してよい先頭の塊」。
        self.labels = {}
        self.extern_untyped = set()
        self.sym_attrs = {}
        self.sections = {}
        self.symbols = {}
        self.patsymbols = {}
        self.export_labels = {}
        self.pat = []
        self.pat_isdir = []
        self.pat_index = {}
        self.pat_always = []
        self.pat_maxkey = 0
        self.pat_dirfn = []
        self.hoist_rows = 0
        self.hoist_fields = set()
        self.hoist_first_ai = 0
        self.hdrsnap = None
        self.diag_count = 0

        self.vliw = VLIWState()

        # いまどちらの文脈の式を読んでいるか。expcaps がそれに対応する
        # 使える項の集合で、評価器はこの 2 つだけを見る。
        self.expmode = EXP_PAT
        self.expcaps = CAPS_PAT

        self.error_undefined_label = False

        self.reported_label_errors = set()

        self.had_error = False

        self._in_match_attempt = False

        # 出力ワードの形。bts が 1 ワードのビット数（`.bits`）、endian が
        # バイト順、align と padding が `.align` の既定値と詰め物の値。
        self.align = 16
        self.bts = 8
        self.endian = 'little'
        self.byte = 'yes'
        self.debug = False

        # いま処理している行とその位置。fnstack / lnstack は `.include` で
        # 入れ子になったファイル名と行番号で、診断にそのまま出す。
        self.cl = ""
        self.ln = 0
        self.fnstack = []
        self.lnstack = []

        # パターン変数の束縛。vars_undef が「この行では束縛されなかった」印、
        # vars_text が `!L` が覚えたソースに書かれていたままの綴り。
        self.vars = {}

        self.vars_undef = {}

        self.vars_text = {}

        self.deb1 = ""
        self.deb2 = ""

        self.exp_typ: str = 'i'

        self.relax = RelaxationState()

        self.verbose: bool = False
        self.text_output: bool = False
        self.asmtext = None
        self.asmtext_disp = None
        self.label_text = ''
        self.comment_text = ''
        self.indent_text = ''
        self.strsymbols = {}
        self.arrsymbols = {}
        self.arrgen = 0
        self.elftypes = {}
        self.passthru = 0
        self.eol = 0
        self.textmode = 0

        self.stdin_tmp_path: str | None = None

        self.elf = ElfState()

        self.init_func: str | None = None
        self.fini_func: str | None = None

        self.varnames: set = set()
        self.check_constraints: dict = {}

        self.reloc_constraints: dict = {}
        self._reloc_badname_seen: set = set()

        self.enum_defs: dict = {}

        self.enum_bindings: list | None = None

        self.sub_defs: dict = {}
        self.freed_subs: set = set()

        self.func_defs: dict = {}

        self.errors: list = list(ERRORS)

        self.section_ranges: list = []

        self._equ_sections_touched = None

        self._macro_label_values = None
        self._macro_label_names = None
        self._macro_line_pcs = None
        self._macro_line_pcs_cur: dict = {}


    def diag(self, text, set_error=True, force=False):
        """診断を 1 行出す。出すかどうかはパスと照合の状況で決まる。

        照合の試行中は、その試行が採択されるとは限らないので溜めるだけにする
        （diag_capture_begin / take / replay）。報告してよいパスでなければ
        捨てる。force はその両方を無視して必ず出す。
        """
        self.diag_count += 1
        if not force:
            if self._in_match_attempt:
                if self._diag_pending is not None:
                    self._diag_pending.append((text, set_error))
                return False
            if not self.should_report_errors():
                return False
        print(text, file=sys.stderr)
        if set_error:
            self.had_error = True
        return True

    def diag_capture_begin(self):
        """以降の診断を溜め始める（照合の試行に入るとき）。"""
        self._diag_pending = []

    def diag_capture_take(self):
        """溜めた診断を取り出して、溜めるのをやめる。"""
        out = self._diag_pending if self._diag_pending is not None else []
        self._diag_pending = None
        return out

    def diag_replay(self, items):
        """溜めた診断を出す。採択されたパターンのぶんだけ流すために使う。"""
        for text, set_error in items:
            if self.should_report_errors():
                print(text, file=sys.stderr)
                if set_error:
                    self.had_error = True

    def diag_error(self, msg, force=False):
        """エラーとして 1 行出し、had_error を立てる。"""
        return self.diag(f" error - {msg}", set_error=True, force=force)

    def diag_warning(self, msg, force=False):
        """警告として 1 行出す。had_error は立てない。"""
        return self.diag(f" warning - {msg}", set_error=False, force=force)

    def should_report_errors(self):
        """いま診断を出してよいパスか。パス2と対話モードだけ真。

        パス1は推定値で動いているので、そこで出る「範囲外」は本物とは限らない。
        """
        return self.pas == 2 or self.pas == 0

    # 下位オブジェクトへ切り出した属性の、古い平らな名前。
    # 下の内包でそれぞれ property を作るので、state.vliwbits のような
    # 既存の書き方が state.vliw.bits として通り続ける。読み書きの両方が通る。
    _FORWARDED_ATTRS = {
        'pas':                   ('relax', 'pas'),
        '_pass1_size_mode':      ('relax', 'pass1_size_mode'),
        '_pass1_prev_label_pcs': ('relax', 'pass1_prev_label_pcs'),
        '_relax_prev_values':    ('relax', 'relax_prev_values'),
        '_relax_optimistic':     ('relax', 'relax_optimistic'),
        '_combo_budget_warned':  ('relax', 'combo_budget_warned'),

        'vliwinstbits':     ('vliw', 'instbits'),
        'vliwnop':          ('vliw', 'nop'),
        'vliwbits':         ('vliw', 'bits'),
        'vliwset':          ('vliw', 'slotset'),
        'vliwflag':         ('vliw', 'flag'),
        'vliwtemplatebits': ('vliw', 'templatebits'),
        'vliwstop':         ('vliw', 'stop'),
        'vcnt':             ('vliw', 'cnt'),

        'osabi':                  ('elf', 'osabi'),
        'elf_objfile':            ('elf', 'objfile'),
        'elf_machine':            ('elf', 'machine'),
        'elf_class':              ('elf', 'elf_class'),
        'relocations':            ('elf', 'relocations'),
        '_elf_tracking':          ('elf', 'tracking'),
        '_elf_label_refs_seen':   ('elf', 'label_refs_seen'),
        '_elf_current_word_idx':  ('elf', 'current_word_idx'),
        '_elf_var_to_label':      ('elf', 'var_to_label'),
        '_elf_capturing_var':     ('elf', 'capturing_var'),
        '_elf_insn_reloc_hint':   ('elf', 'insn_reloc_hint'),
        'gen_debug':              ('elf', 'gen_debug'),
        'line_map':               ('elf', 'line_map'),
        'reloctype_override':     ('elf', 'reloctype_override'),
    }
    for _old_name, (_sub_name, _sub_attr) in _FORWARDED_ATTRS.items():
        def _make_forward(_sub_name=_sub_name, _sub_attr=_sub_attr):
            def _getter(self):
                return getattr(getattr(self, _sub_name), _sub_attr)

            def _setter(self, value):
                setattr(getattr(self, _sub_name), _sub_attr, value)
            return property(_getter, _setter)
        locals()[_old_name] = _make_forward()
    del _old_name, _sub_name, _sub_attr, _make_forward


class StringUtils:
    """行とトークンの文字列処理。どれも状態を持たない。

    ここに集めてあるのは、アセンブリ行・パターン行・マクロ行のどこからでも
    同じ意味で呼べる必要があるものだけ。文字列リテラル `"..."` と文字定数
    `'c'` の中は触らない、という規則を全員が共有している点が要。`'` は
    符号拡張演算子でもあるので、文字定数かどうかの判定は 1 か所
    (skip_squote_literal) に閉じてある。
    """

    _ASCII_UPPER = str.maketrans(LOWER, CAPITAL)

    _upper_cache = {}

    @staticmethod
    def upper(s):
        """ASCII だけを大文字にする。

        str.upper() を使わないのは、非 ASCII まで畳むと caxx.c の toupper() と
        結果が食い違うため。照合のたびに呼ばれるので表を引く形にし、
        短い文字列だけを上限付きで覚える（溢れたら捨てて作り直す）。
        """
        c = StringUtils._upper_cache
        v = c.get(s)
        if v is None:
            v = s.translate(StringUtils._ASCII_UPPER)
            if len(s) <= 64:
                if len(c) >= 65536:
                    c.clear()
                c[s] = v
        return v

    @staticmethod
    def join_backslash_continuations(raw_lines):
        """行末の `\\` で続く行をつなぐ。

        つないだぶんだけ空行を残すので、行数が入力と変わらない。診断に出す
        行番号をソースの見た目と合わせるために、詰めずに空行を置いている。
        """
        out = []
        pending = ''
        for raw in raw_lines:
            body, ending = raw, ''
            if body.endswith('\r\n'):
                body, ending = body[:-2], '\r\n'
            elif body.endswith('\n') or body.endswith('\r'):
                body, ending = body[:-1], body[-1]
            if body.endswith('\\'):
                pending += body[:-1]
                out.append('')
            else:
                out.append(pending + body + ending)
                pending = ''
        if pending:
            out.append(pending)
        return out

    @staticmethod
    def q(s, t, idx):
        """s の idx の位置に t があるか（大文字小文字を区別しない）。"""
        return StringUtils.upper(s[idx:idx + len(t)]) == StringUtils.upper(t)

    @staticmethod
    def skipspc(s, idx):
        """空白とタブを飛ばした位置を返す。"""
        while idx < len(s) and s[idx] in ' \t':
            idx += 1
        return idx

    @staticmethod
    def skip_squote_literal(s, i):
        """i の `'` が文字定数なら、その直後の位置を返す。

        `'c'` `'\\n'` `'\\xHH'` を認める。文字定数でなければ i+1 を返すので、
        呼び出し側はその `'` をふつうの 1 文字（符号拡張演算子）として読む。
        この判定を 1 か所に閉じてあるので、どの層でも同じ切り分けになる。
        """
        j = i + 1
        if j < len(s) and s[j] == '\\' and j + 1 < len(s):
            esc_char = s[j + 1]
            if esc_char in 'xX':
                k = j + 2
                hex_digits = 0
                while k < len(s) and s[k] in '0123456789abcdefABCDEF' and hex_digits < 2:
                    k += 1
                    hex_digits += 1
                if k < len(s) and s[k] == '\'':
                    return k + 1
            elif j + 2 < len(s) and s[j + 2] == '\'':
                return j + 3
        elif j < len(s) and j + 1 < len(s) and s[j + 1] == '\'':
            return j + 2
        return i + 1

    @staticmethod
    def parse_hex_char_literal(s, idx):
        """`'\\xHH'` を読む。返り値は (読めたか, 値, 次の位置)。"""
        if not (idx + 3 <= len(s) and s[idx] == "'" and s[idx + 1] == '\\'
                and s[idx + 2] in 'xX'):
            return False, 0, idx
        j = idx + 3
        hex_digits = ''
        while j < len(s) and s[j] in '0123456789abcdefABCDEF' and len(hex_digits) < 2:
            hex_digits += s[j]
            j += 1
        if hex_digits and j < len(s) and s[j] == "'":
            return True, int(hex_digits, 16), j + 1
        return False, 0, idx

    _SPACE_RUNS = re.compile(r'\s{2,}')

    @staticmethod
    def reduce_spaces(text):
        """空白の連なりを 1 個に潰す。リテラルの中身も区別せず潰す。

        中身を守る必要があるところでは normalize_ws() を使う。
        """
        return StringUtils._SPACE_RUNS.sub(' ', text)

    @staticmethod
    def normalize_ws(l):
        """空白の連なりを 1 個に潰す。ただし `"..."` と `'c'` の中は触らない。

        照合は空白の数を問わないので先に潰しておくが、文字列テンプレートが
        出すテキストは書いたままでなければならない。その両立のための版。
        """
        out = []
        in_dquote = False
        in_ws = False
        i = 0
        n = len(l)
        while i < n:
            ch = l[i]

            if in_dquote:
                if ch == '\\' and i + 1 < n:
                    out.append(l[i:i + 2])
                    i += 2
                    continue
                if ch == '"':
                    in_dquote = False
                out.append(ch)
                i += 1
                continue

            if ch == '"':
                in_dquote = True
                in_ws = False
                out.append(ch)
                i += 1
                continue

            if ch == '\'':
                j = StringUtils.skip_squote_literal(l, i)
                out.append(l[i:j])
                in_ws = False
                i = j
                continue

            if ch in ' \t\n\r':
                if not in_ws:
                    out.append(' ')
                    in_ws = True
                i += 1
                continue

            out.append(ch)
            in_ws = False
            i += 1
        return ''.join(out)

    @staticmethod
    def remove_comment(l, in_comment=False):
        """パターンファイルの `/* ... */` を落とす。

        返り値は (落としたあとの行, まだコメントの中か)。複数行にまたがる
        コメントは呼び出し側がこの第 2 返り値を次の行へ渡して続ける。
        「`/*` だけ並べた古い書き方ではコメントを次行へ延長しない」という
        後方互換の判断は PatternFileReader 側にあり、ここは素の状態機械。
        """
        out = []
        i = 0
        n = len(l)
        while i < n:
            if in_comment:
                if l[i:i + 2] == '*/':
                    in_comment = False
                    i += 2
                    continue
                i += 1
                continue
            if l[i:i + 2] == '/*':
                in_comment = True
                i += 2
                continue
            out.append(l[i])
            i += 1
        return ''.join(out), in_comment

    @staticmethod
    def split_comment_asm(l):
        """アセンブリ行を (コード, `;` コメント) に割る。

        `"..."` と `'c'` の中の `;` は区切らない。`\\;` は文字としての `;` で、
        ここで `;` 1 文字に開かれる。コメントを捨てずに返すのは、テキスト置換
        モードが書かれていたままの綴りで出力に残すため。
        """
        in_dquote = False
        out = []
        i = 0
        n = len(l)
        while i < n:
            ch = l[i]

            if ch == '\\' and in_dquote:
                if i + 1 < n:
                    out.append(l[i:i + 2])
                    i += 2
                else:
                    out.append(ch)
                    i += 1
                continue

            if not in_dquote and ch == '\\' and i + 1 < n and l[i + 1] == ';':
                out.append(';')
                i += 2
                continue

            if ch == '"':
                in_dquote = not in_dquote
            elif ch == '\'' and not in_dquote:
                j = StringUtils.skip_squote_literal(l, i)
                out.append(l[i:j])
                i = j
                continue
            elif ch == ';' and not in_dquote:
                return ''.join(out).rstrip(), l[i:].rstrip()

            out.append(ch)
            i += 1
        if in_dquote:
            diag(f" warning - unterminated string literal in line: {l!r}", set_error=False)
        return ''.join(out).rstrip(), ''

    @staticmethod
    def resolve_vliw_escapes(l):
        """ソース行の `!!` と `!!!!` を 1 文字の内部表現に置き換える。

        `\\!` は文字としての `!` なので、先に `!` 1 文字へ開いてから見る。
        これで「スロット区切り」と「エスケープされた !!」が以降は
        1 文字か 2 文字かだけで区別できる。文字列の中は触らない。
        """
        out = []
        in_dquote = False
        i = 0
        n = len(l)
        while i < n:
            ch = l[i]

            if ch == '\\' and in_dquote:
                if i + 1 < n:
                    out.append(l[i:i + 2])
                    i += 2
                else:
                    out.append(ch)
                    i += 1
                continue

            if not in_dquote and ch == '\\' and i + 1 < n and l[i + 1] == '!':
                out.append('!')
                i += 2
                continue

            if ch == '"':
                in_dquote = not in_dquote
                out.append(ch)
                i += 1
                continue
            if ch == '\'' and not in_dquote:
                j = StringUtils.skip_squote_literal(l, i)
                out.append(l[i:j])
                i = j
                continue

            if not in_dquote and l[i:i + 4] == '!!!!':
                out.append(VLIW_STOP)
                i += 4
                continue
            if not in_dquote and l[i:i + 2] == '!!':
                out.append(VLIW_SEP)
                i += 2
                continue

            out.append(ch)
            i += 1
        return ''.join(out)

    @staticmethod
    def get_param_to_spc(s, idx):
        """空白か VLIW スロット境界まで読む。返り値は (読んだ文字, 次の位置)。"""
        t = ""
        idx = StringUtils.skipspc(s, idx)
        while idx < len(s) and s[idx] != ' ' and s[idx] not in (VLIW_SEP, VLIW_STOP):
            t += s[idx]
            idx += 1
        return t, idx

    @staticmethod
    def get_param_to_eon(s, idx):
        """VLIW スロット境界まで読む（空白は含めて読む）。"""
        t = ""
        idx = StringUtils.skipspc(s, idx)
        while idx < len(s) and s[idx] not in (VLIW_SEP, VLIW_STOP):
            t += s[idx]
            idx += 1
        return t, idx

    @staticmethod
    def get_string(l2):
        """ダブルクォートの文字列リテラルを 1 個読んで、中身を返す。

        エスケープは `\\n` `\\t` `\\r` `\\\\` `\\"` と `\\xHH`、`\\uXXXX`、
        `\\UXXXXXXXX`。桁が足りない・多い場合は警告して、書かれた文字を
        そのまま採る（エラーにして止めない）。閉じられていない場合も警告だけ。
        """
        idx = 0
        idx = StringUtils.skipspc(l2, idx)
        if l2 == '' or idx >= len(l2) or l2[idx] != '"':
            return ""
        idx += 1
        s = ""
        while idx < len(l2):
            if l2[idx] == '\\' and idx + 1 < len(l2):
                next_char = l2[idx + 1]
                if next_char == '"':
                    s += '"'
                    idx += 2
                elif next_char == '\\':
                    s += '\\'
                    idx += 2
                elif next_char == 'n':
                    s += '\n'
                    idx += 2
                elif next_char == 't':
                    s += '\t'
                    idx += 2
                elif next_char == 'r':
                    s += '\r'
                    idx += 2
                elif next_char in 'xX':
                    idx += 2
                    hex_str = ''
                    while idx < len(l2) and l2[idx] in '0123456789abcdefABCDEF' and len(hex_str) < 2:
                        hex_str += l2[idx]
                        idx += 1
                    if idx < len(l2) and l2[idx] in '0123456789abcdefABCDEF':
                        diag(f" warning - '\\x' escape takes at most 2 hex digits; "
                             f"extra digit(s) treated as literal characters in: {l2!r}", set_error=False)
                    if hex_str:
                        s += chr(int(hex_str, 16))
                    else:
                        diag(f" warning - '\\x' escape requires at least one hex digit; "
                             f"treated as literal 'x' in: {l2!r}", set_error=False)
                        s += 'x'
                elif next_char in 'uU':

                    _ndigits = 4 if next_char == 'u' else 8
                    idx += 2
                    hex_str = ''
                    while idx < len(l2) and l2[idx] in '0123456789abcdefABCDEF' and len(hex_str) < _ndigits:
                        hex_str += l2[idx]
                        idx += 1
                    if len(hex_str) == _ndigits:
                        try:
                            s += chr(int(hex_str, 16))
                        except (ValueError, OverflowError):
                            diag(f" warning - invalid \\{next_char} escape in: {l2!r}", set_error=False)
                            s += next_char
                    else:
                        diag(f" warning - '\\{next_char}' escape requires {_ndigits} hex digits; "
                             f"treated as literal characters in: {l2!r}", set_error=False)
                        s += next_char + hex_str
                else:
                    s += next_char
                    idx += 2
            elif l2[idx] == '"':
                return s
            else:
                s += l2[idx]
                idx += 1
        diag(f" warning - unterminated string literal: {l2!r}", set_error=False)
        return s


class Parser:
    """行から 1 個ずつトークンを切り出す低位の読み取り器。

    どのメソッドも (読んだもの, 次の位置) を返し、読めなければ位置を動かさない。
    照合は後退しながら何度も試すので、失敗が副作用を残さないことが要。
    使える文字の集合は state の lwordchars / swordchars から引くため、
    `.labelc` / `.symbolc` の拡張がそのまま効く。
    """

    def __init__(self, state):
        self.state = state

    def get_intstr(self, s, idx):
        """続く 10 進数字を綴りのまま取る。"""
        fs = ''
        while idx < len(s) and s[idx] in DIGIT:
            fs += s[idx]
            idx += 1
        return fs, idx

    def get_floatstr(self, s, idx):
        """浮動小数点の綴りを取る。`inf` / `-inf` / `nan` も読む。

        指数部は `e` のあとに数字が無ければ指数ではないので、`e` の前まで
        巻き戻す。`1e` で終わる行や、`1eax` のような続きがある場合のため。
        """
        if s[idx:idx + 4] == '-inf':
            return '-inf', idx + 4
        elif s[idx:idx + 3] == 'inf':
            return 'inf', idx + 3
        elif s[idx:idx + 3] == 'nan':
            return 'nan', idx + 3
        else:
            fs = ''
            while idx < len(s) and s[idx] in "0123456789.":
                fs += s[idx]
                idx += 1
            if idx < len(s) and s[idx] in "eE":
                saved_idx = idx
                saved_fs  = fs
                fs += s[idx]
                idx += 1
                if idx < len(s) and s[idx] in "+-":
                    fs += s[idx]
                    idx += 1
                digits_start = idx
                while idx < len(s) and s[idx] in "0123456789":
                    fs += s[idx]
                    idx += 1
                if idx == digits_start:
                    fs  = saved_fs
                    idx = saved_idx
            return fs, idx

    def isfloatstr(self, s, idx):
        """その位置から浮動小数点として読めるか（位置は動かさない）。"""
        sidx = idx
        v, idx = self.get_floatstr(s, idx)
        if idx == sidx:
            return False
        else:
            return True

    def get_curlb(self, s, idx):
        """`{ ... }` の中身を取る。返り値は (あったか, 中身, 次の位置)。

        閉じ括弧が無ければ診断を出し、行の末尾まで消費したことにする。
        """
        idx = StringUtils.skipspc(s, idx)
        f = False
        t = ''

        if idx < len(s) and s[idx] == '{':
            idx += 1
            idx = StringUtils.skipspc(s, idx)
            while idx < len(s) and s[idx] != '}':
                t += s[idx]
                idx += 1
            t = t.rstrip(' \t\r\n\x00')
            if idx >= len(s):
                if self.state.should_report_errors():
                    self.state.diag(f" error - missing closing '}}' in expression: '{{{t}'",
                                    set_error=True, force=True)
                return False, '', len(s)
            idx += 1
            f = True

        return f, t, idx

    def get_symbol_word(self, s, idx):
        """シンボル名を 1 個取り、大文字化して返す。

        数字で始まる綴りはシンボルではない。使える文字は `.symbolc` 次第。
        """
        t = ""
        if idx < len(s) and s[idx] not in DIGIT and s[idx] in self.state.swordchars:
            t = s[idx]
            idx += 1
            while idx < len(s) and s[idx] in self.state.swordchars:
                t += s[idx]
                idx += 1
        return StringUtils.upper(t), idx

    def get_label_word(self, s, idx, eat_colon=True):
        """ラベル名を 1 個取る。大文字化はしない（ラベルは区別する）。

        定義側の `label:` の `:` まで食べるのが既定だが、`:=`（代入）の
        `:` は食べない。参照側で `:` を残したいときは eat_colon を偽にする。
        """
        t = ""
        if idx < len(s) and (s[idx] == '.' or (s[idx] not in DIGIT and s[idx] in self.state.lwordchars)):
            t = s[idx]
            idx += 1
            while idx < len(s) and s[idx] in self.state.lwordchars:
                t += s[idx]
                idx += 1

            if (eat_colon and idx < len(s) and s[idx] == ':'
                    and (idx + 1 >= len(s) or s[idx + 1] != '=')):
                idx += 1

        return t, idx

    def get_params1(self, l, idx):
        """`::` までを 1 欄として取る。パターン行とディレクティブ行の分解に使う。"""
        idx = StringUtils.skipspc(l, idx)

        if idx >= len(l):
            return "", idx

        s = ""
        while idx < len(l):
            if l[idx:idx + 2] == '::':
                idx += 2
                break
            else:
                s += l[idx]
                idx += 1
        return s.rstrip(' \t'), idx


def enfloat(a):
    """32bit の整数ビットパターンを、同じビットの float として読み直す。

    `!F` で捕らえた値を式の中で数として扱うときの逆方向。壊れた入力では
    例外を投げずに 0.0 を返し、診断は呼び出し側に任せる。
    """
    try:
        float_value = struct.unpack('f', struct.pack('I', int(a) & 0xFFFFFFFF))[0]
    except (struct.error, OverflowError, ValueError):
        float_value = 0.0
    return float_value


def endouble(a):
    """64bit の整数ビットパターンを、同じビットの double として読み直す。"""
    try:
        double_value = struct.unpack('d', struct.pack('Q', int(a) & 0xFFFFFFFFFFFFFFFF))[0]
    except (struct.error, OverflowError, ValueError):
        double_value = 0.0
    return double_value


enflt = enfloat
endbl = endouble


class IEEE754Converter:
    """10 進表記 → IEEE-754 のビットパターン（16 進文字列）。

    32bit と 64bit は struct に任せられるが、128bit は Python に型が無いので
    Decimal で手で組む。パターンの `!Q` と `.float` がこれを通る。
    inf / nan / -0.0 の形まで caxx.c（strtoflt128）と一致させる必要がある。
    """

    @staticmethod
    def decimal_to_ieee754_32bit_hex(a):
        """`!F` 用。32bit 単精度のビットパターンを 16 進 8 桁で返す。"""
        if a == 'inf':
            return "0x7F800000"
        elif a == '-inf':
            return "0xFF800000"
        elif a == 'nan':
            return "0x7FC00000"

        try:
            fval = float(Decimal(a))
        except Exception as _e:
            raise ValueError(f"decimal_to_ieee754_32bit_hex: invalid input {a!r}") from _e
        try:
            bits = struct.unpack('I', struct.pack('f', fval))[0]
        except (struct.error, OverflowError) as _e:
            raise ValueError(f"decimal_to_ieee754_32bit_hex: cannot pack {fval!r}") from _e
        return f"0x{bits:08X}"

    @staticmethod
    def decimal_to_ieee754_64bit_hex(a):
        """`!D` 用。64bit 倍精度のビットパターンを 16 進 16 桁で返す。"""
        if a == 'inf':
            return "0x7FF0000000000000"
        elif a == '-inf':
            return "0xFFF0000000000000"
        elif a == 'nan':
            return "0x7FF8000000000000"

        try:
            fval = float(Decimal(a))
        except Exception as _e:
            raise ValueError(f"decimal_to_ieee754_64bit_hex: invalid input {a!r}") from _e
        try:
            bits = struct.unpack('Q', struct.pack('d', fval))[0]
        except (struct.error, OverflowError) as _e:
            raise ValueError(f"decimal_to_ieee754_64bit_hex: cannot pack {fval!r}") from _e
        return f"0x{bits:016X}"

    @staticmethod
    def decimal_to_ieee754_128bit_hex(a):
        """`!Q` 用。128bit 四倍精度のビットパターンを 16 進 32 桁で返す。

        Decimal の精度を 60 桁に上げた文脈で実装を呼ぶ。既定の 28 桁では
        112bit の仮数を丸めきれない。
        """
        with localcontext() as _ctx:
            _ctx.prec = 60
            return IEEE754Converter._decimal_to_ieee754_128bit_hex_impl(a)

    @staticmethod
    def _decimal_to_ieee754_128bit_hex_impl(a):
        """128bit 変換の本体。符号・指数・仮数を自分で組む。

        指数の初期推定を 10 進桁数から作り、1 <= 仮数 < 2 になるまで 2 で
        掛け割りして正規化する。推定が外れても収束するはずだが、壊れた入力で
        回り続けないよう反復数に上限を置き、超えたら例外にする。
        指数が上に溢れたら無限、下に溢れたら非正規化数として詰める。
        丸めは偶数丸め。0 は符号付きゼロを保つ。
        """
        BIAS = 16383
        SIGNIFICAND_BITS = 112
        EXPONENT_BITS = 15

        if a == 'inf':
            a = 'Infinity'
        elif a == '-inf':
            a = '-Infinity'
        elif a == 'nan':
            a = 'NaN'
        d = Decimal(a)

        if d.is_nan():
            sign = 0
            exponent = (1 << EXPONENT_BITS) - 1
            fraction = 1 << (SIGNIFICAND_BITS - 1)
        elif d == Decimal('Infinity'):
            sign = 0
            exponent = (1 << EXPONENT_BITS) - 1
            fraction = 0
        elif d == Decimal('-Infinity'):
            sign = 1
            exponent = (1 << EXPONENT_BITS) - 1
            fraction = 0
        elif d == 0:
            sign = 1 if d.is_signed() else 0
            exponent = 0
            fraction = 0
        else:
            sign = 0 if d >= 0 else 1
            d = abs(d)

            two = Decimal(2)

            exp_unbiased = int(d.adjusted() * math.log2(10))

            scale = two ** exp_unbiased
            normalized = d / scale

            _NORM_MAX_ITERS = 1000
            _norm_iters = 0
            while normalized >= 2:
                exp_unbiased += 1
                normalized /= 2
                _norm_iters += 1
                if _norm_iters > _NORM_MAX_ITERS:
                    raise ValueError(
                        "decimal_to_ieee754_128bit_hex: failed to normalize "
                        f"{d!r} (exponent estimate did not converge)")
            while normalized < 1:
                exp_unbiased -= 1
                normalized *= 2
                _norm_iters += 1
                if _norm_iters > _NORM_MAX_ITERS:
                    raise ValueError(
                        "decimal_to_ieee754_128bit_hex: failed to normalize "
                        f"{d!r} (exponent estimate did not converge)")

            biased_exp = exp_unbiased + BIAS

            _MAX_EXP = (1 << EXPONENT_BITS) - 1
            if biased_exp >= _MAX_EXP:
                sign_bit = sign
                exponent = _MAX_EXP
                fraction = 0
                bits = (sign_bit << 127) | (exponent << SIGNIFICAND_BITS) | fraction
                return f"0x{bits:032X}"

            if biased_exp <= 0:
                exponent = 0
                shift = two ** (1 - BIAS - SIGNIFICAND_BITS)
                fraction = int((d / shift).to_integral_value(rounding=ROUND_HALF_EVEN))
                if fraction >= (1 << SIGNIFICAND_BITS):
                    exponent = 1
                    fraction = 0
            else:
                exponent = biased_exp
                fraction = int(((normalized - 1) * (two ** SIGNIFICAND_BITS)).to_integral_value(rounding=ROUND_HALF_EVEN))
                if fraction >= (1 << SIGNIFICAND_BITS):
                    fraction = 0
                    exponent += 1

            fraction &= (1 << SIGNIFICAND_BITS) - 1

        bits = (sign << 127) | (exponent << SIGNIFICAND_BITS) | fraction
        return f"0x{bits:032X}"

    @staticmethod
    def decimal_eval_expr(text):
        """128bit 精度のまま浮動小数点式を評価し、ビットパターンを返す。

        `qad{...}` の中身がここを通る。途中を double に落とさないので、
        34 桁の有効数字が最後まで残る。
        """
        with localcontext() as _ctx:
            _ctx.prec = 60
            return IEEE754Converter._decimal_eval_expr_impl(text)

    @staticmethod
    def _decimal_eval_expr_impl(text):
        """上の本体。Decimal 上の再帰下降で `+ - * / // %` と括弧を解く。

        `//` は C と同じゼロ方向ではなく負の無限方向へ丸める（下の補正）。
        入れ子が深すぎる式は RecursionError を拾って文言に変える。
        """
        text = text.strip()

        def skip(s, i):
            while i < len(s) and s[i] in ' \t':
                i += 1
            return i

        def parse_number(s, i):
            i = skip(s, i)
            neg = False
            if i < len(s) and s[i] == '-':
                neg = True
                i += 1
                i = skip(s, i)
            for kw, dval in (('inf', Decimal('Infinity')), ('nan', Decimal('NaN'))):
                if s[i:i + len(kw)] == kw:
                    v = dval.copy_negate() if neg else dval
                    return v, i + len(kw)
            if i >= len(s) or s[i] not in '0123456789.':
                raise ValueError(f"expected number at {i!r}")
            start = i
            while i < len(s) and s[i] in '0123456789.':
                i += 1
            if i < len(s) and s[i] in 'eE':
                i += 1
                if i < len(s) and s[i] in '+-':
                    i += 1
                while i < len(s) and s[i] in '0123456789':
                    i += 1
            try:
                v = Decimal(s[start:i])
            except Exception as _e:
                raise ValueError(f"invalid decimal literal: {s[start:i]!r}") from _e
            return (v.copy_negate() if neg else v), i

        def parse_factor(s, i):
            i = skip(s, i)
            if i < len(s) and s[i] == '(':
                try:
                    v, i = parse_expr(s, i + 1)
                except RecursionError:
                    raise ValueError("decimal_eval_expr: expression nesting too deep")
                i = skip(s, i)
                if i < len(s) and s[i] == ')':
                    i += 1
                return v, i
            if i < len(s) and s[i] == '-':
                try:
                    v, i = parse_factor(s, i + 1)
                except RecursionError:
                    raise ValueError("decimal_eval_expr: expression nesting too deep")
                return v.copy_negate(), i
            if i < len(s) and s[i] == '+':
                try:
                    return parse_factor(s, i + 1)
                except RecursionError:
                    raise ValueError("decimal_eval_expr: expression nesting too deep")
            return parse_number(s, i)

        def parse_term(s, i):
            v, i = parse_factor(s, i)
            while True:
                i = skip(s, i)
                if i < len(s) and s[i] == '*':
                    t, i = parse_factor(s, i + 1)
                    v *= t
                elif i + 1 < len(s) and s[i] == '/' and s[i + 1] == '/':
                    t, i = parse_factor(s, i + 2)
                    if t == 0:
                        raise ZeroDivisionError("floor division by zero in qad{}")
                    tq = v // t
                    if tq * t != v and (v < 0) != (t < 0):
                        tq -= 1
                    v = Decimal(int(tq))
                elif i < len(s) and s[i] == '/' and (i + 1 >= len(s) or s[i + 1] != '/'):
                    t, i = parse_factor(s, i + 1)
                    if t == 0:
                        raise ZeroDivisionError("division by zero in qad{}")
                    v /= t
                elif i < len(s) and s[i] == '%':
                    t, i = parse_factor(s, i + 1)
                    if t == 0:
                        raise ZeroDivisionError("modulo by zero in qad{}")
                    v = Decimal(int(v) % int(t))
                else:
                    break
            return v, i

        def parse_expr(s, i):
            v, i = parse_term(s, i)
            while True:
                i = skip(s, i)
                if i < len(s) and s[i] == '+':
                    t, i = parse_term(s, i + 1)
                    v += t
                elif i < len(s) and s[i] == '-':
                    t, i = parse_term(s, i + 1)
                    v -= t
                else:
                    break
            return v, i

        val, _ = parse_expr(text, 0)
        return IEEE754Converter.decimal_to_ieee754_128bit_hex(str(val))


class VariableManager:
    """パターン変数の束縛を読み書きする。

    変数は小文字で始まり小文字・数字・`_` が続く綴りで、長さは問わない。
    綴りがそれに合わないものは変数ではないので、読めば VAR_UNDEF、
    書けば黙って捨てる。束縛はパターン行ごとに消えるため、マッチしなかった
    省略可能オペランドは 0 として読まれる。
    """

    def __init__(self, state):
        self.state = state

    @staticmethod
    def _index(s):
        """変数名を正規の鍵（小文字）にする。変数名でなければ None。"""
        if not s:
            return None
        u = s.lower()
        if not u.isascii() or not ('a' <= u[0] <= 'z'):
            return None
        for ch in u[1:]:
            if not ('a' <= ch <= 'z' or ch.isdigit() or ch == '_'):
                return None
        return u

    def get(self, s):
        """変数の値。未束縛・名前でない場合は VAR_UNDEF。"""
        i = self._index(s)
        if i is None:
            return VAR_UNDEF
        return self.state.vars.get(i, VAR_UNDEF)

    def is_undef(self, s):
        """その変数が未定義ラベル由来の値を持っているか。"""
        i = self._index(s)
        if i is None:
            return False
        return self.state.vars_undef.get(i, False)

    def put(self, s, v):
        """変数に値を束縛する（未定義由来の印は付けない）。"""
        self.put_tagged(s, v, False)

    def put_tagged(self, s, v, is_undef):
        """変数に値と「未定義由来か」の印を束縛する。

        Decimal と float は、整数で表せるなら int に落として入れる。
        以降の演算とリスティングの見え方を caxx.c とそろえるため、
        「整数になる値は整数で持つ」を入口で揃えておく。
        """
        c = self._index(s)
        if c is None:
            return
        self.state.varnames.add(c)
        if isinstance(v, Decimal):
            if not v.is_finite():
                self.state.vars[c] = float(v)
            elif v == v.to_integral_value():
                self.state.vars[c] = int(v)
            else:
                self.state.vars[c] = float(v)
        elif isinstance(v, float) and not v.is_integer():
            self.state.vars[c] = v
        else:
            try:
                self.state.vars[c] = int(v)
            except (OverflowError, ValueError):
                self.state.vars[c] = v
        self.state.vars_undef[c] = bool(is_undef)


class LabelManager:
    """ラベルの定義と参照。リラクゼーションとリロケーションの要。

    参照のたびに、いまが何パスか・パターン照合の途中かによって答えを変える。
    パス1では値が未確定でも止まれないので推定値を返し、パス2では確定値を
    返す。`-o` のとき参照そのものを ElfState に記録するのもここ。
    """

    def __init__(self, state):
        self.state = state

    def _section_relative_offset(self, name, word_pc):
        """絶対のワードアドレスを、そのセクション先頭からの相対位置に直す。

        セクションはソース中で何度も開き直せるので、同じ名前の範囲を書かれた
        順にたどって累積する。範囲に入らなければ None。
        """
        ranges = [(rs, rl) for (rn, rs, rl) in self.state.section_ranges if rn == name]
        cum = 0
        for rs, rl in ranges:
            if rs <= word_pc < rs + rl:
                return cum + (word_pc - rs)
            cum += rl
        entry = self.state.sections.get(name)
        if entry:
            entry_pc = entry[2] if len(entry) > 2 else entry[0]
            if word_pc >= entry_pc:
                return cum + (word_pc - entry_pc)
        return None

    def get_section(self, k):
        """ラベルが属するセクション名。未定義なら UNDEF を返して印を立てる。"""
        try:
            v = self.state.labels[k][1]
        except (KeyError, IndexError):
            v = UNDEF
            self.state.error_undefined_label = True
        return v

    def get_value(self, k):
        """ラベルの値を読む。パスごとに「未確定」の扱いが変わる。

        未定義のときの答えは、
          - パス1で前回の反復の値があればそれ（収束のための推定値）、
          - パス1の最初の反復なら現在の PC（楽観的に短い符号化から試す）、
          - 長さだけ見ている区間なら 0、
          - それ以外は UNDEF。
        診断を出すのは、照合の試行中ではなく、かつ報告してよいパスのときだけ。
        照合は失敗する試行を何度も通るので、そこで出すと嘘の診断が溢れる。

        `-o` の追跡中は、この参照がどの変数・どの出力ワードから来たかを
        ElfState に積む。あとでリロケーションの型と位置を決めるのに使う。
        `.equ` のラベルは再配置情報を失う定数なので、型が付いている場合を
        除いて積まない。
        """
        try:
            v = self.state.labels[k][0]
        except (KeyError, IndexError):
            if self.state.pas == 1 and k in self.state._relax_prev_values:
                return self.state._relax_prev_values[k]
            if self.state.pas == 1 and self.state._relax_optimistic:
                self.state.error_undefined_label = True
                return self.state.pc
            if self.state._pass1_size_mode:
                return 0
            v = UNDEF
            self.state.error_undefined_label = True
            if not self.state._in_match_attempt and (self.state.should_report_errors()):
                _fn = self.state.current_file or ""
                _ln = self.state.ln
                self.state.diag(f" error - Label undefined: '{k}'"
                     f"  [{_fn}:{_ln}]", set_error=True)
            return v
        _sec = self.state.labels[k][1]
        if self.state._equ_sections_touched is not None:
            self.state._equ_sections_touched.add(_sec)

            _adj = self._section_relative_offset(_sec, v)
            if _adj is not None:
                v = _adj
        elif self.state._in_binary_list and _sec == self.state.current_section:

            _adj = self._section_relative_offset(_sec, v)
            if _adj is not None:
                v = _adj

        _is_equ = len(self.state.labels[k]) > 2 and self.state.labels[k][2]
        _equ_has_reloc = _is_equ and len(self.state.labels[k]) > 4 and self.state.labels[k][4] is not None
        if self.state._elf_tracking and not self.state.error_undefined_label and (not _is_equ or _equ_has_reloc):
            if self.state._elf_capturing_var is not None:
                cv = self.state._elf_capturing_var
                if cv not in self.state._elf_var_to_label:
                    self.state._elf_var_to_label[cv] = (k, v)
                else:
                    self.state._elf_var_to_label[cv] = None
            elif self.state._elf_current_word_idx >= 0:
                self.state._elf_label_refs_seen.append(
                    (k, v, self.state._elf_current_word_idx))
        return v

    def _report_definition_error(self, key, msg):
        """ラベル定義のエラーを、同じ原因について 1 回だけ出す。

        パス1とパス2で同じ行を 2 回通るので、鍵で重複を抑える。
        """
        self.state.had_error = True
        if key in self.state.reported_label_errors:
            return
        self.state.reported_label_errors.add(key)
        _fn = self.state.current_file or ""
        self.state.diag(f" error - {msg}  [{_fn}:{self.state.ln}]",
                        set_error=True, force=True)

    def put_value(self, k, v, s, is_equ=False, reloc_type=None):
        """ラベルを定義する。定義できたかを返す。

        弾くのは、同じ名前の二重定義（インポートされたものの上書きは可）、
        パス1に無くパス2で現れた名前、パターンファイルのシンボルとの衝突。
        リロケーション型が渡されなければ、前の定義が持っていた型を引き継ぐ。
        """
        if self.state.pas == 1 or self.state.pas == 0:
            if k in self.state.labels:
                existing = self.state.labels[k]
                old_is_imported = len(existing) > 3 and existing[3]
                if not old_is_imported:
                    self._report_definition_error(
                        ('dup', k), f"label '{k}' is already defined.")
                    return False
        elif self.state.pas == 2:
            if k not in self.state.labels:
                self._report_definition_error(
                    ('pass1', k), f"label '{k}' not defined in pass 1.")
                return False

        if StringUtils.upper(k) in self.state.patsymbols:
            self._report_definition_error(
                ('patsym', k), f"'{k}' is a pattern file symbol.")
            return False

        is_imported = False

        entry = [v, s, is_equ, is_imported]
        if reloc_type is None:
            _old = self.state.labels.get(k)
            if _old is not None and len(_old) > 4 and _old[4] is not None:
                reloc_type = _old[4]
        if reloc_type is not None:
            entry.append(reloc_type)

        self.state.labels[k] = entry
        return True

    def printlabels(self):
        """ラベル表を標準エラーへ並べる。プロンプトモードの `?` の中身。"""
        result = {}
        for key, value in self.state.labels.items():
            num = value[0]
            section = value[1]
            if num == UNDEF:
                num_str = "UNDEF"
            elif isinstance(num, float):
                num_str = repr(num)
            else:
                try:
                    num_str = hex(int(num))
                except (TypeError, ValueError, OverflowError):
                    num_str = repr(num)
            result[key] = [num_str, section]
        for k, v in sorted(result.items()):
            print(f"  {k:40s}  {v[0]}  ({v[1]})", file=sys.stderr)


class SymbolManager:
    """パターンファイルが定義したシンボルを引く。名前は大文字で正規化する。"""

    def __init__(self, state):
        self.state = state

    def get(self, w):
        """シンボルの値。無ければ空文字を返す。"""
        w = StringUtils.upper(w)
        return self.state.symbols.get(w, "")


_ENUM_WORD_CHARS = set(DIGIT + ALPHABET + '_')


def _enum_name_at(s, idx, names):
    """その位置にある `.enum` の要素名を最長一致で読む。

    返り値は (要素の番号, 次の位置)。無ければ (-1, idx)。名前の直後が
    英数字・下線なら語の途中なので一致とみなさない。
    """
    best = -1
    best_end = idx
    for k, nm in enumerate(names):
        n = len(nm)
        if n <= best_end - idx:
            continue
        if StringUtils.upper(s[idx:idx + n]) != nm:
            continue
        e = idx + n
        if e < len(s) and s[e] in _ENUM_WORD_CHARS:
            continue
        best = k
        best_end = e
    return best, best_end


def _symset_item_at(s, idx, items):
    """その位置にある集合の項目名を最長一致で読む（`!Y` の照合）。

    返り値は (項目の番号, 次の位置)。数値の項目は名前を持たないので候補外。
    `A,AX,AL` に対して `al` が `A` ではなく `AL` に当たるのは最長一致のため。
    """
    best = -1
    best_end = idx
    for k, it in enumerate(items):
        if not isinstance(it, str):
            continue
        n = len(it)
        if n <= best_end - idx:
            continue
        if StringUtils.upper(s[idx:idx + n]) != StringUtils.upper(it):
            continue
        e = idx + n
        if e < len(s) and s[e] in _ENUM_WORD_CHARS:
            continue
        best = k
        best_end = e
    return best, best_end


class ExpressionEvaluator:
    """式評価器。優先順位ごとに 1 メソッドの再帰下降。

    どのメソッドも (値, 次の位置) を返し、読めなければ位置を動かさない。
    アセンブリ行・パターン行・ミニ言語・マクロ層がすべてこの 1 つを通るので、
    どの層でも同じ式が同じ値になる。使える項の違いは state.expcaps
    (ExprCaps) だけで表し、評価器は呼び出し元を知らない。
    state.exp_typ が 'f' のときは浮動小数点として計算する。

    優先順位（緩いものが外側、Python に倣う）:

      term11   ?:
      term10   ||
      term9    &&
      term8    （段を空けてある。下へ素通し）
      term7    <= < >= > == !=
      term6    '   符号拡張
      term5    ^
      term4    |
      term3    &
      term2    << >>
      term1    + -
      term0    * / // %
      term0_0  **
      factor   単項 - ~ @、`*(x,y)`、`!!!` `!!!!`
      factor1  項そのもの（数値・ラベル・シンボル・変数・`$$` ...）
    """

    def __init__(self, state, var_manager, label_manager, symbol_manager, parser):
        self.state = state
        self.var_manager = var_manager
        self.label_manager = label_manager
        self.symbol_manager = symbol_manager
        self.parser = parser

    def nbit(self, l):
        """`@` 演算子。最上位の立っているビットの位置。"""
        return op_msb(l)

    def err(self, m):
        """文言を標準エラーへ出して -1 を返す。"""
        print(m, file=sys.stderr)
        return -1

    def factor(self, s, idx):
        """単項演算子と括弧つきの組み込み項を処理し、残りを factor1 に渡す。

        扱うのは `-` `~` `@`、バイト抽出 `*(x,y)`、VLIW の `!!!`（結合された
        命令の数）と `!!!!`（ストップビット）。VLIW の 2 つは expcaps が
        許していなければ読まない。再帰が深すぎる式は RecursionError を拾って
        診断にする。factor1 が 1 文字も進めず、しかも区切り文字でもない
        ときだけ「読めない字」の警告を出す（照合の試行中は出さない）。
        """
        idx = StringUtils.skipspc(s, idx)
        x = 0

        if idx + 4 <= len(s) and s[idx:idx + 4] == '!!!!' and self.state.expcaps.vliw:
            x = self.state.vliwstop
            idx += 4
        elif idx + 3 <= len(s) and s[idx:idx + 3] == '!!!' and self.state.expcaps.vliw:
            x = self.state.vcnt
            idx += 3
        elif idx < len(s) and s[idx] == '-':
            try:
                x, idx = self.factor(s, idx + 1)
            except RecursionError:
                self.state.diag(" error - expression nesting too deep (RecursionError) in unary '-'.", set_error=True)
                return 0, idx
            x = -x
        elif idx < len(s) and s[idx] == '~':
            try:
                x, idx = self.factor(s, idx + 1)
            except RecursionError:
                self.state.diag(" error - expression nesting too deep (RecursionError) in unary '~'.", set_error=True)
                return 0, idx
            try:
                x = ~int(x)
            except (OverflowError, ValueError):
                self.state.diag(" error - cannot apply bitwise NOT (~) to non-finite float value.", set_error=True)
                x = 0
        elif idx < len(s) and s[idx] == '@':
            try:
                x, idx = self.factor(s, idx + 1)
            except RecursionError:
                self.state.diag(" error - expression nesting too deep (RecursionError) in unary '@'.", set_error=True)
                return 0, idx
            x = self.nbit(x)
        elif idx < len(s) and s[idx] == '*':
            if idx + 1 < len(s) and s[idx + 1] == '(':
                x, idx = self.expression(s, idx + 2)
                if idx < len(s) and s[idx] == ',':
                    x2, idx = self.expression(s, idx + 1)
                    if idx < len(s) and s[idx] == ')':
                        idx += 1
                        x, _err = op_byte(x, x2)
                        if _err:
                            self.state.diag(f" error - {_err}.", set_error=True)
                    else:
                        self.state.diag(" error - missing ')' in *(expr, expr) expression.", set_error=True)
                        x = 0
                else:
                    self.state.diag(" error - missing ',' in *(expr, expr) expression.", set_error=True)
                    x = 0
            else:
                self.state.diag(" error - expected '(' after '*' in *(expr,expr) expression.", set_error=True)
                idx += 1
        else:
            prev_idx = idx
            x, idx = self.factor1(s, idx)
            if (idx == prev_idx
                    and idx < len(s)
                    and s[idx] not in (chr(0), ',', ')', ']', CB, ' ', '\t')
                    and not self.state._in_match_attempt
                    and (self.state.should_report_errors())):
                self.state.diag(f" warning - unrecognized token at position {idx} in expression: "
                     f"{s[idx:idx + 8]!r} (treated as 0)", set_error=False)
        idx = StringUtils.skipspc(s, idx)
        return x, idx

    def xeval(self, x, _=None):
        """`:ラベル` を含む Python 構文の式を、安全に評価する。

        eval() は使わない。ラベル参照を衝突しない placeholder に置き換えてから
        ast で解析し、許可した節と演算子だけを自分で畳む。呼べる関数は
        enfloat / endouble とその別名の 4 つだけで、それ以外の名前・呼び出し・
        節はすべて拒否する。べき乗とシフトには上限も掛ける。
        ラベル名をそのまま式に埋めないのは、名前が Python の構文に化けるのを
        防ぐため。現在このメソッドはどこからも呼ばれていない。
        """
        def _cc_escape(chars):
            out = []
            for c in chars:
                if c == '\\':
                    out.append('\\\\')
                elif c == ']':
                    out.append('\\]')
                elif c == '^':
                    out.append('\\^')
                elif c == '-':
                    out.append('\\-')
                else:
                    out.append(re.escape(c))
            return ''.join(out)

        escaped = _cc_escape(self.state.lwordchars)
        pattern = rf":([{escaped}]+)(?=[^{escaped}]|$)"

        _tag = "_AXXLBL_" + uuid.uuid4().hex
        _label_values = {}

        def replacer(match):
            label_name = match.group(1)
            placeholder = f"{_tag}{len(_label_values)}"
            try:
                val = self.state.labels[label_name][0]
            except (KeyError, IndexError):
                self.state.error_undefined_label = True
                _label_values[placeholder] = 0
                return placeholder
            if _is_undef_derived(val):
                self.state.error_undefined_label = True
                _label_values[placeholder] = 0
                return placeholder
            _is_equ = (len(self.state.labels.get(label_name, [])) > 2
                       and self.state.labels[label_name][2])
            if self.state._elf_tracking and not _is_equ:
                if self.state._elf_capturing_var is not None:
                    cv = self.state._elf_capturing_var
                    if cv not in self.state._elf_var_to_label:
                        self.state._elf_var_to_label[cv] = (label_name, val)
                    else:
                        self.state._elf_var_to_label[cv] = None
                elif self.state._elf_current_word_idx >= 0:
                    self.state._elf_label_refs_seen.append(
                        (label_name, val, self.state._elf_current_word_idx))
            try:
                _label_values[placeholder] = int(val)
            except (TypeError, ValueError, OverflowError):
                self.state.error_undefined_label = True
                _label_values[placeholder] = 0
            return placeholder

        s = re.sub(pattern, replacer, x)

        _ALLOWED_FUNCS = {
            "enfloat": enfloat, "endouble": endouble,
            "enflt": enflt, "endbl": endbl,
        }

        try:
            tree = ast.parse(s, mode='eval')
        except SyntaxError as e:
            raise ValueError(f"xeval: parse error in '{s}': {e}")

        def _ev(node):
            if isinstance(node, ast.Expression):
                return _ev(node.body)
            if isinstance(node, ast.Constant):
                if isinstance(node.value, (int, float, bool)):
                    return node.value
                raise ValueError(f"xeval: disallowed constant {node.value!r} in '{s}'")
            if isinstance(node, ast.BinOp):
                l = _ev(node.left)
                r = _ev(node.right)
                op = node.op
                if isinstance(op, ast.Add):
                    return l + r
                if isinstance(op, ast.Sub):
                    return l - r
                if isinstance(op, ast.Mult):
                    return l * r
                if isinstance(op, ast.Div):
                    return l / r
                if isinstance(op, ast.FloorDiv):
                    return l // r
                if isinstance(op, ast.Mod):
                    return l % r
                if isinstance(op, ast.Pow):
                    if isinstance(r, int) and r > 1024:
                        raise ValueError("xeval: exponent exceeds 1024")
                    return l ** r
                if isinstance(op, ast.BitAnd):
                    return l & r
                if isinstance(op, ast.BitOr):
                    return l | r
                if isinstance(op, ast.BitXor):
                    return l ^ r
                if isinstance(op, ast.LShift):
                    if isinstance(r, int) and r > 65536:
                        raise ValueError("xeval: shift count exceeds 65536")
                    return l << r
                if isinstance(op, ast.RShift):
                    return l >> r
                raise ValueError(f"xeval: disallowed operator {type(op).__name__} in '{s}'")
            if isinstance(node, ast.UnaryOp):
                v = _ev(node.operand)
                op = node.op
                if isinstance(op, ast.UAdd):
                    return +v
                if isinstance(op, ast.USub):
                    return -v
                if isinstance(op, ast.Invert):
                    return ~v
                raise ValueError(f"xeval: disallowed unary operator {type(op).__name__} in '{s}'")
            if isinstance(node, ast.BoolOp):
                if isinstance(node.op, ast.And):
                    res = True
                    for vn in node.values:
                        res = _ev(vn)
                        if not res:
                            return res
                    return res
                if isinstance(node.op, ast.Or):
                    res = False
                    for vn in node.values:
                        res = _ev(vn)
                        if res:
                            return res
                    return res
                raise ValueError(f"xeval: disallowed bool operator in '{s}'")
            if isinstance(node, ast.Compare):
                left = _ev(node.left)
                for cop, comp in zip(node.ops, node.comparators):
                    right = _ev(comp)
                    if   isinstance(cop, ast.Eq):
                        ok = left == right
                    elif isinstance(cop, ast.NotEq):
                        ok = left != right
                    elif isinstance(cop, ast.Lt):
                        ok = left <  right
                    elif isinstance(cop, ast.LtE):
                        ok = left <= right
                    elif isinstance(cop, ast.Gt):
                        ok = left >  right
                    elif isinstance(cop, ast.GtE):
                        ok = left >= right
                    else:
                        raise ValueError(f"xeval: disallowed comparison in '{s}'")
                    if not ok:
                        return False
                    left = right
                return True
            if isinstance(node, ast.IfExp):
                return _ev(node.body) if _ev(node.test) else _ev(node.orelse)
            if isinstance(node, ast.Call):
                if (not isinstance(node.func, ast.Name)
                        or node.func.id not in _ALLOWED_FUNCS):
                    raise ValueError(f"xeval: disallowed function call in '{s}'")
                if node.keywords:
                    raise ValueError(f"xeval: keyword arguments not allowed in '{s}'")
                args = [_ev(a) for a in node.args]
                return _ALLOWED_FUNCS[node.func.id](*args)
            if isinstance(node, ast.Name):
                if node.id in _label_values:
                    return _label_values[node.id]
                raise ValueError(f"xeval: disallowed name '{node.id}' in '{s}'")
            raise ValueError(
                f"xeval: disallowed AST node {type(node).__name__} in '{s}'")

        result = _ev(tree)
        if not isinstance(result, (int, float, bool)):
            raise ValueError(f"xeval: unsafe result type {type(result)}")
        return result

    def factor1(self, s, idx):
        """項そのものを 1 個読む。

        数値（10 進・16 進・2 進・浮動小数点）、文字定数、ラベル、`#シンボル`、
        パターン変数、`$$`／`$.`、`%%`、括弧、`:=` の代入、配列シンボルの
        添字引き、`.enum` や集合の項目など、式の葉になるものすべて。
        どれにも当たらなければ位置を動かさず 0 を返し、判断は factor に任せる。
        """
        x = 0
        idx = StringUtils.skipspc(s, idx)

        if idx >= len(s):
            return x, idx

        _enum_hit = None
        if self.state.enum_bindings is not None:
            _enames, _evals = self.state.enum_bindings
            _ek, _eend = _enum_name_at(s, idx, _enames)
            if _ek >= 0:
                _enum_hit = (_evals[_ek], _eend)

        if s[idx] == '(':
            x, idx = self.expression(s, idx + 1)
            if idx < len(s) and s[idx] == ')':
                idx += 1
            else:
                self.state.diag(" error - missing closing ')' in expression.", set_error=True)
        elif idx + 4 <= len(s) and s[idx:idx + 4] == "'\\t'":
            x = 0x09
            idx += 4
        elif idx + 4 <= len(s) and s[idx:idx + 4] == "'\\''":
            x = ord("'")
            idx += 4
        elif idx + 4 <= len(s) and s[idx:idx + 4] == "'\\\\'":
            x = ord("\\")
            idx += 4
        elif idx + 4 <= len(s) and s[idx:idx + 4] == "'\\n'":
            x = 0x0a
            idx += 4
        elif idx + 4 <= len(s) and s[idx:idx + 4] == "'\\0'":
            x = 0x00
            idx += 4
        elif idx + 4 <= len(s) and s[idx:idx + 4] == "'\\r'":
            x = 0x0d
            idx += 4
        elif idx + 4 <= len(s) and s[idx:idx + 4] == "'\\a'":
            x = 0x07
            idx += 4
        elif idx + 4 <= len(s) and s[idx:idx + 4] == "'\\b'":
            x = 0x08
            idx += 4
        elif idx + 4 <= len(s) and s[idx:idx + 4] == "'\\f'":
            x = 0x0c
            idx += 4
        elif idx + 4 <= len(s) and s[idx:idx + 4] == "'\\v'":
            x = 0x0b
            idx += 4
        elif (_hexlit := StringUtils.parse_hex_char_literal(s, idx))[0]:
            x, idx = _hexlit[1], _hexlit[2]
        elif idx + 3 <= len(s) and s[idx] == '\'' and s[idx + 1] != '\\' and s[idx + 2] == '\'':
            x = ord(s[idx + 1])
            idx += 3
        elif StringUtils.q(s, '$$', idx):
            idx += 2
            _raw = self.state.pc_instr_start if self.state._in_binary_list else self.state.pc

            if self.state._in_binary_list or self.state._equ_sections_touched is not None:
                _adj = self.label_manager._section_relative_offset(self.state.current_section, _raw)
                x = _adj if _adj is not None else _raw
            else:
                x = _raw
        elif StringUtils.q(s, '$.', idx):
            idx += 2
            _raw = self.state.pc_instr_end
            if self.state._in_binary_list or self.state._equ_sections_touched is not None:
                _adj = self.label_manager._section_relative_offset(self.state.current_section, _raw)
                x = _adj if _adj is not None else _raw
            else:
                x = _raw
        elif StringUtils.q(s, '#', idx):
            idx += 1
            t, idx = self.parser.get_symbol_word(s, idx)
            _akey = StringUtils.upper(t)
            _arr = self.state.arrsymbols.get(_akey)
            if _arr is not None and idx < len(s) and s[idx] == '[':
                _iv, idx = self.expression_pat(s, idx + 1)
                if idx < len(s) and s[idx] == ']':
                    idx += 1
                else:
                    self.state.diag(f" error - '#{_akey}[': missing ']'.",
                                    set_error=True)
                _n = int(_iv)
                if _n < 0 or _n >= len(_arr):
                    self.state.diag(f" error - index {_n} is out of range for array "
                                    f"symbol '{_akey}' (0..{len(_arr) - 1}).",
                                    set_error=True)
                    x = 0
                elif isinstance(_arr[_n], str):
                    self.state.diag(f" error - '#{_akey}[{_n}]' is a string item and "
                                    f"has no numeric value.", set_error=True)
                    x = 0
                else:
                    x = _arr[_n]
            else:
                _sym_val = self.symbol_manager.get(t)
                if _sym_val == "":
                    self.state.diag(f" error - undefined symbol: '#{t}'", set_error=True)
                    x = 0
                else:
                    x = _sym_val
        elif StringUtils.q(s, '0b', idx):
            idx += 2
            while idx < len(s) and s[idx] in "01":
                x = 2 * x + int(s[idx], 2)
                idx += 1
        elif StringUtils.q(s, '0x', idx):
            idx += 2
            while idx < len(s) and StringUtils.upper(s[idx]) in XDIGIT:
                x = 16 * x + int(s[idx].lower(), 16)
                idx += 1
        elif (idx + 3 <= len(s) and s[idx:idx + 3] == 'qad'
              and (lambda _j=StringUtils.skipspc(s, idx + 3): _j < len(s) and s[_j] == '{')()):
            idx += 3
            idx = StringUtils.skipspc(s, idx)
            if idx < len(s) and s[idx] == '{':
                f, t, idx = self.parser.get_curlb(s, idx)
                if not f:
                    pass
                elif t in ('nan', 'inf', '-inf'):
                    x = int(IEEE754Converter.decimal_to_ieee754_128bit_hex(t), 16)
                else:
                    try:
                        h = IEEE754Converter.decimal_eval_expr(t)
                    except (ValueError, ZeroDivisionError):
                        try:
                            v = self.xeval(t, None)
                        except (ValueError, TypeError, OverflowError, ZeroDivisionError):

                            self.state.diag(f" error - qad{{}}: cannot evaluate expression '{t}'; using 0.", set_error=True)
                            h = '0' * 32
                        else:
                            if isinstance(v, int) or (
                                    isinstance(v, float) and v.is_integer()):
                                h = IEEE754Converter.decimal_to_ieee754_128bit_hex(
                                        str(int(v)))
                            else:
                                h = IEEE754Converter.decimal_to_ieee754_128bit_hex(
                                        str(Decimal(repr(float(v)))))
                    if (int(h, 16) >> 112) & 0x7fff == 0x7fff:
                        self.state.diag(f" error - qad{{}}: cannot evaluate expression '{t}'; using 0.", set_error=True)
                        h = '0' * 32
                    x = int(h, 16)
        elif (idx + 3 <= len(s) and s[idx:idx + 3] == 'dbl'
              and (lambda _j=StringUtils.skipspc(s, idx + 3): _j < len(s) and s[_j] == '{')()):
            idx += 3
            f, t, idx = self.parser.get_curlb(s, idx)
            if f:
                if t == 'nan':
                    x = 0x7ff8000000000000
                elif t == 'inf':
                    x = 0x7ff0000000000000
                elif t == '-inf':
                    x = 0xfff0000000000000
                else:
                    try:
                        v = float(self.xeval(t, None))
                        if v != v or v in (float('inf'), float('-inf')):
                            raise OverflowError('non-finite')
                        x = int.from_bytes(struct.pack('>d', v), "big")
                    except (OverflowError, ValueError, TypeError, struct.error, ZeroDivisionError):
                        self.state.diag(" error - dbl{}: cannot convert expression to float64; using 0.", set_error=True)
                        x = 0
        elif (idx + 3 <= len(s) and s[idx:idx + 3] == 'flt'
              and (lambda _j=StringUtils.skipspc(s, idx + 3): _j < len(s) and s[_j] == '{')()):
            idx += 3
            f, t, idx = self.parser.get_curlb(s, idx)
            if f:
                if t == 'nan':
                    x = 0x7fc00000
                elif t == 'inf':
                    x = 0x7f800000
                elif t == '-inf':
                    x = 0xff800000
                else:
                    try:
                        v = float(self.xeval(t, None))
                        if v != v or v in (float('inf'), float('-inf')):
                            raise OverflowError('non-finite')
                        x = int.from_bytes(struct.pack('>f', v), "big")
                    except (OverflowError, ValueError, TypeError, struct.error, ZeroDivisionError):
                        self.state.diag(" error - flt{}: cannot convert expression to float32; using 0.", set_error=True)
                        x = 0
        elif (idx + 5 <= len(s) and s[idx:idx + 5] == 'enflt'
              and (lambda _j=StringUtils.skipspc(s, idx + 5): _j < len(s) and s[_j] == '{')()):
            idx += 5
            f, t, idx = self.parser.get_curlb(s, idx)
            if f:
                _outer_undef = self.state.error_undefined_label
                self.state.error_undefined_label = False
                v, _ = self.expression(t + chr(0), 0)
                _inner_undef = self.state.error_undefined_label
                self.state.error_undefined_label = _outer_undef or _inner_undef
                if _inner_undef:
                    self.state.diag(" error - enflt{}: expression contains undefined label.", set_error=True)
                    x = enflt(0)
                else:
                    try:
                        x = enflt(int(v) & 0xFFFFFFFF)
                    except (OverflowError, ValueError):
                        self.state.diag(" error - enflt{}: non-finite float value; using 0.", set_error=True)
                        x = enflt(0)
        elif (idx + 5 <= len(s) and s[idx:idx + 5] == 'endbl'
              and (lambda _j=StringUtils.skipspc(s, idx + 5): _j < len(s) and s[_j] == '{')()):
            idx += 5
            f, t, idx = self.parser.get_curlb(s, idx)
            if f:
                _outer_undef = self.state.error_undefined_label
                self.state.error_undefined_label = False
                v, _ = self.expression(t + chr(0), 0)
                _inner_undef = self.state.error_undefined_label
                self.state.error_undefined_label = _outer_undef or _inner_undef
                if _inner_undef:
                    self.state.diag(" error - endbl{}: expression contains undefined label.", set_error=True)
                    x = endbl(0)
                else:
                    try:
                        x = endbl(int(v) & 0xFFFFFFFFFFFFFFFF)
                    except (OverflowError, ValueError):
                        self.state.diag(" error - endbl{}: non-finite float value; using 0.", set_error=True)
                        x = endbl(0)
        elif idx + 4 <= len(s) and s[idx:idx + 4] == 'not(':
            x, idx = self.expression(s, idx + 4)
            idx = StringUtils.skipspc(s, idx)
            if idx < len(s) and s[idx] == ')':
                idx += 1
            else:
                self.state.diag(" error - missing closing ')' in not(...) expression.", set_error=True)
            x = 0 if x else 1
        elif self.state.exp_typ == 'i' and idx < len(s) and s[idx] in DIGIT:
                fs, idx = self.parser.get_intstr(s, idx)
                x = int(fs)
        elif self.state.exp_typ == 'f' and idx < len(s) and (self.parser.isfloatstr(s, idx)):
                fs, idx = self.parser.get_floatstr(s, idx)
                try:
                    x = float(fs) if fs else 0.0
                except ValueError:
                    x = 0.0
        elif _enum_hit is not None:
            x, idx = _enum_hit
        elif (idx < len(s) and self.state.expcaps.patvars
              and self._patvar_len_at(s, idx) > 0):
            _vnl = self._patvar_len_at(s, idx)
            ch = s[idx:idx + _vnl]
            if idx + _vnl + 2 <= len(s) and s[idx + _vnl:idx + _vnl + 2] == ':=':
                _assign_prior = self.state.error_undefined_label
                self.state.error_undefined_label = False
                x, idx = self.expression(s, idx + _vnl + 2)
                _assign_undef = self.state.error_undefined_label
                self.state.error_undefined_label = _assign_prior or _assign_undef
                self.var_manager.put_tagged(ch, x, _assign_undef)
            else:
                x = self.var_manager.get(ch)
                idx += _vnl
                if (not self.state._in_match_attempt
                        and not self.state._pass1_size_mode
                        and (self.state.should_report_errors())
                        and (self.var_manager.is_undef(ch) or _is_undef_derived(x))):
                    self.state.error_undefined_label = True
                    self.state.diag(f" error - Label undefined: variable '{ch}' contains undefined value"
                         f"  [{self.state.current_file}:{self.state.ln}]", set_error=False)
                if (self.state._elf_tracking
                        and self.state._elf_current_word_idx >= 0):
                    entry = self.state._elf_var_to_label.get(ch)
                    if entry is not None:
                        lname, lval = entry
                        self.state._elf_label_refs_seen.append(
                            (lname, lval, self.state._elf_current_word_idx))
                        _rt = self.state.reloc_constraints.get(ch)
                        if _rt is not None and not _is_undef_derived(x):
                            self.state._elf_insn_reloc_hint.setdefault(
                                self.state._elf_current_word_idx, (_rt, int(x) - int(lval)))
        elif idx < len(s) and s[idx] in self.state.lwordchars:
            w, idx_new = self.parser.get_label_word(s, idx, eat_colon=False)
            if idx != idx_new:
                idx = idx_new
                x = self.label_manager.get_value(w)

        idx = StringUtils.skipspc(s, idx)
        return x, idx

    def term0_0(self, s, idx):
        """`**`。桁が溢れないよう指数と結果のビット数に上限を置く。

        浮動小数点モードでは _ieee_pow に渡して C 版と同じ nan を作る。
        整数モードでは、負の指数・1024 を超える指数・結果が 256bit の帯を
        超える場合をエラーにして 0 にする。連鎖した `**` で爆発させないため。
        """
        x, idx = self.factor(s, idx)
        while idx < len(s) and StringUtils.q(s, '**', idx):
            t, idx = self.factor(s, idx + 2)

            if self.state.exp_typ == 'f':
                x = _ieee_pow(x, t)
                continue

            _EXP_MAX = 1024
            _EXP_RESULT_MAX_BITS = _UNDEF_SANE_CEILING.bit_length() - 1

            try:
                t_int = int(t)
            except (ValueError, OverflowError):
                t_int = 0
            if t_int < 0:
                self.state.diag(" error - Negative exponent in ** expression; result set to 0.", set_error=True)
                x = 0
                break
            if t_int > _EXP_MAX:
                self.state.diag(f" error - Exponent {t_int} exceeds maximum {_EXP_MAX} in ** expression; result set to 0.", set_error=True)
                x = 0
                break

            if t_int == 0:
                x = 1
                continue
            if t_int == 1:
                continue

            try:
                _base_bits = abs(x).bit_length() if isinstance(x, int) else 1024
            except (TypeError, ValueError, OverflowError):
                _base_bits = 1024
            if _base_bits * t_int > _EXP_RESULT_MAX_BITS:
                self.state.diag(f" error - ** result would exceed {_EXP_RESULT_MAX_BITS} bits "
                         f"(chained exponentiation); result set to 0.", set_error=True)
                x = 0
                break
            try:
                x = x ** t_int
            except OverflowError:
                self.state.diag(" error - ** result is too large to represent as a float; result set to 0.", set_error=True)
                x = 0
                break
            if isinstance(x, float) and x.is_integer():
                x = int(x)
        return x, idx

    def term0(self, s, idx):
        """`*` `/` `//` `%`。

        整数モードの `/` はゼロ方向へ切り捨てる（`-7/3 == -2`）。`%` は Python と
        同じで結果が除数の符号に従う（`-7%3 == 2`）ので、両者のあいだに
        `a == (a/b)*b + a%b` は成り立たない。ミニ言語とマクロ層の `%` は C と
        同じ被除数の符号なので、層をまたいで式を写すときは負の値に注意。
        """
        x, idx = self.term0_0(s, idx)
        while idx < len(s):
            if s[idx] == '*' and (idx + 1 >= len(s) or s[idx + 1] != '*'):
                t, idx = self.term0_0(s, idx + 1)
                x *= t
            elif StringUtils.q(s, '//', idx):
                t, idx = self.term0_0(s, idx + 2)
                if t == 0:
                    self.state.diag(" error - Division by 0 error.", set_error=True)
                    x = 0
                    break
                else:
                    x //= t
            elif s[idx] == '/':
                t, idx = self.term0_0(s, idx + 1)
                if t == 0:
                    self.state.diag(" error - Division by 0 error.", set_error=True)
                    x = 0
                    break
                else:
                    if (self.state.exp_typ == 'i'
                            and isinstance(x, int) and isinstance(t, int)):
                        q = abs(x) // abs(t)
                        x = -q if (x < 0) != (t < 0) else q
                    else:
                        x = x / t
            elif s[idx] == '%':
                t, idx = self.term0_0(s, idx + 1)
                if t == 0:
                    self.state.diag(" error - Division by 0 error.", set_error=True)
                    x = 0
                    break
                else:
                    x = x % t
            else:
                break
        return x, idx

    def term1(self, s, idx):
        """`+` `-`。"""
        x, idx = self.term0(s, idx)
        while idx < len(s):
            if s[idx] == '+':
                t, idx = self.term0(s, idx + 1)
                x += t
            elif s[idx] == '-':
                t, idx = self.term0(s, idx + 1)
                x -= t
            else:
                break
        return x, idx

    def term2(self, s, idx):
        """`<<` `>>`。負のシフト量と 65536 を超えるシフト量はエラーにする。"""
        x, idx = self.term1(s, idx)
        _SHIFT_MAX = 65536
        while idx < len(s):
            if StringUtils.q(s, '<<', idx):
                t, idx = self.term1(s, idx + 2)
                try:
                    x = int(x)
                    t = int(t)
                except (ValueError, OverflowError):
                    x = 0
                    break
                if t < 0:
                    self.state.diag(f" error - negative shift count ({t}) in << expression.", set_error=True)
                    x = 0
                    break
                if t > _SHIFT_MAX:
                    self.state.diag(f" error - shift count {t} exceeds maximum {_SHIFT_MAX} in << expression.", set_error=True)
                    x = 0
                    break
                x <<= t
            elif StringUtils.q(s, '>>', idx):
                t, idx = self.term1(s, idx + 2)
                try:
                    x = int(x)
                    t = int(t)
                except (ValueError, OverflowError):
                    x = 0
                    break
                if t < 0:
                    self.state.diag(f" error - negative shift count ({t}) in >> expression.", set_error=True)
                    x = 0
                    break
                if t > _SHIFT_MAX:
                    self.state.diag(f" error - shift count {t} exceeds maximum {_SHIFT_MAX} in >> expression.", set_error=True)
                    x = 0
                    break
                x >>= t
            else:
                break
        return x, idx

    def _safe_int(self, v, op_name):
        """ビット演算の前に整数へ落とす。非有限値は警告して 0 にする。"""
        try:
            return int(v)
        except (OverflowError, ValueError):
            if self.state.should_report_errors():
                self.state.diag(f" error - non-finite value {v!r} in bitwise '{op_name}' operation; treated as 0.", set_error=False)
                self.state.had_error = True
            return 0

    def term3(self, s, idx):
        """`&`。`&&` は論理積なのでここでは食べない。"""
        x, idx = self.term2(s, idx)
        while idx < len(s) and s[idx] == '&' and (idx + 1 >= len(s) or s[idx + 1] != '&'):
            t, idx = self.term2(s, idx + 1)
            x = self._safe_int(x, '&') & self._safe_int(t, '&')
        return x, idx

    def term4(self, s, idx):
        """`|`。`||` は論理和なのでここでは食べない。"""
        x, idx = self.term3(s, idx)
        while idx < len(s) and s[idx] == '|' and (idx + 1 >= len(s) or s[idx + 1] != '|'):
            t, idx = self.term3(s, idx + 1)
            x = self._safe_int(x, '|') | self._safe_int(t, '|')
        return x, idx

    def term5(self, s, idx):
        """`^`。"""
        x, idx = self.term4(s, idx)
        while idx < len(s) and s[idx] == '^':
            t, idx = self.term4(s, idx + 1)
            x = self._safe_int(x, '^') ^ self._safe_int(t, '^')
        return x, idx

    def term6(self, s, idx):
        """`'` — 符号拡張。

        `'` は文字定数の引用符でもあるので、直後が数字か `(` のときだけ
        演算子として読む。そうでなければ手を付けず上の層に残す。
        """
        x, idx = self.term5(s, idx)
        while idx < len(s) and s[idx] == '\'':
            next_idx = idx + 1
            next_idx = StringUtils.skipspc(s, next_idx)
            if next_idx >= len(s) or (s[next_idx] not in DIGIT and s[next_idx] != '('):
                break
            t, idx = self.term5(s, idx + 1)
            x, _warn, _go = op_sext(x, t)
            if _warn:
                self.state.diag(f" warning - {_warn}.", set_error=False)
            if not _go:
                break
        return x, idx

    def term7(self, s, idx):
        """比較 `<=` `<` `>=` `>` `==` `!=`。結果は 1 か 0。"""
        x, idx = self.term6(s, idx)
        while idx < len(s):
            if StringUtils.q(s, '<=', idx):
                t, idx = self.term6(s, idx + 2)
                x = 1 if x <= t else 0
            elif s[idx] == '<':
                t, idx = self.term6(s, idx + 1)
                x = 1 if x < t else 0
            elif StringUtils.q(s, '>=', idx):
                t, idx = self.term6(s, idx + 2)
                x = 1 if x >= t else 0
            elif s[idx] == '>':
                t, idx = self.term6(s, idx + 1)
                x = 1 if x > t else 0
            elif StringUtils.q(s, '==', idx):
                t, idx = self.term6(s, idx + 2)
                x = 1 if x == t else 0
            elif StringUtils.q(s, '!=', idx):
                t, idx = self.term6(s, idx + 2)
                x = 1 if x != t else 0
            else:
                break
        return x, idx

    def term8(self, s, idx):
        """空けてある段。term7 へ素通しする。

        caxx.c と段の番号をそろえておくために残してある。
        """
        return self.term7(s, idx)

    def term9(self, s, idx):
        """`&&`。結果は 1 か 0。"""
        x, idx = self.term8(s, idx)
        while idx < len(s) and StringUtils.q(s, '&&', idx):
            t, idx = self.term8(s, idx + 2)
            x = 1 if x and t else 0
        return x, idx

    def term10(self, s, idx):
        """`||`。結果は 1 か 0。"""
        x, idx = self.term9(s, idx)
        while idx < len(s) and StringUtils.q(s, '||', idx):
            t, idx = self.term9(s, idx + 2)
            x = 1 if x or t else 0
        return x, idx

    @staticmethod
    def _skip_subexpr(s, idx):
        """括弧の対応を数えながら、部分式 1 個を読み飛ばした位置を返す。"""
        paren = brack = ob = 0
        n = len(s)
        while idx < n and s[idx] != chr(0):
            c = s[idx]
            if c == '(':
                paren += 1
                idx += 1
            elif c == ')':
                if paren <= 0:
                    break
                paren -= 1
                idx += 1
            elif c == '[':
                brack += 1
                idx += 1
            elif c == ']':
                if brack <= 0:
                    break
                brack -= 1
                idx += 1
            elif c == OB:
                ob += 1
                idx += 1
            elif c == CB:
                if ob <= 0:
                    break
                ob -= 1
                idx += 1
            elif paren == 0 and brack == 0 and ob == 0 and c in '?,;':
                break
            elif (paren == 0 and brack == 0 and ob == 0 and c == ':'
                    and (idx + 1 >= n or s[idx + 1] != '=')):
                break
            else:
                idx += 1
        return idx

    @classmethod
    def _skip_ternary_expr(cls, s, idx):
        """三項演算子の、選ばれなかった側を読み飛ばす。"""
        n = len(s)
        idx = cls._skip_subexpr(s, idx)
        if idx < n and s[idx] == '?' and (idx + 1 >= n or s[idx + 1] != '='):
            idx = StringUtils.skipspc(s, idx + 1)
            idx = cls._skip_ternary_expr(s, idx)
            idx = StringUtils.skipspc(s, idx)
            if idx < n and s[idx] == ':' and (idx + 1 >= n or s[idx + 1] != '='):
                idx = StringUtils.skipspc(s, idx + 1)
                idx = cls._skip_ternary_expr(s, idx)
        return idx

    def term11(self, s, idx):
        """`?:` — 三項演算子。

        選ばれなかった側は評価せずに読み飛ばす。副作用（`:=` の代入）が
        走らないようにするためで、`:` の直後が `=` のときは代入演算子なので
        三項の区切りとは読まない。
        """
        x, idx = self.term10(s, idx)
        n = len(s)
        if idx < n and s[idx] == '?':
            idx = StringUtils.skipspc(s, idx + 1)
            if x == 0:
                skip_end = self._skip_ternary_expr(s, idx)
                if (skip_end < n and s[skip_end] == ':'
                        and (skip_end + 1 >= n or s[skip_end + 1] != '=')):
                    x, idx = self.term11(s, StringUtils.skipspc(s, skip_end + 1))
                else:
                    idx = skip_end
                    x = 0
            else:
                x, idx = self.term11(s, idx)
                idx = StringUtils.skipspc(s, idx)
                if idx < n and s[idx] == ':' and (idx + 1 >= n or s[idx + 1] != '='):
                    idx = self._skip_ternary_expr(s, StringUtils.skipspc(s, idx + 1))
        return x, idx

    def expression(self, s, idx):
        """式を 1 個評価する。優先順位の一番上から入る。"""
        try:
            idx0 = StringUtils.skipspc(s, idx)
            x, idx0 = self.term11(s, idx0)
            return x, idx0
        except RecursionError:
            self.state.diag(" error - expression nesting too deep (RecursionError).", set_error=True)
            return 0, idx

    def _terminate(self, s):
        """末尾に NUL を足して、式の終わりを確定させる。"""
        if not s or s[-1] != chr(0):
            return s + chr(0)
        return s

    def _patvar_len_at(self, s, idx):
        """その位置のパターン変数名の長さ。直後がラベル文字なら変数ではない。"""
        n = PatternMatcher._var_name_at(s, idx)
        if n == 0:
            return 0
        if idx + n < len(s) and s[idx + n] in self.state.lwordchars:
            return 0
        return n

    def expression_pat(self, s, idx):
        """パターン行の式として評価する（すべての項が使える）。"""
        return self._expression_in(s, idx, EXP_PAT, CAPS_PAT)

    def expression_caps(self, s, idx, caps):
        """使える項を明示して評価する（ミニ言語などが自分の制限で呼ぶ）。"""
        return self._expression_in(s, idx, EXP_PAT, caps)

    def _expression_in(self, s, idx, mode, caps):
        """文脈を差し替えて評価し、必ず元に戻す。

        評価中に例外が出ても finally で戻すので、文脈が漏れて次の行の
        解釈を変えることはない。
        """
        prev = self.state.expmode
        prev_caps = self.state.expcaps
        self.state.expmode = mode
        self.state.expcaps = caps
        try:
            return self.expression(self._terminate(s), idx)
        finally:
            self.state.expmode = prev
            self.state.expcaps = prev_caps

    def expression_asm(self, s, idx):
        """アセンブリ行の式として評価する（パターン変数と VLIW 計数は使えない）。"""
        return self._expression_in(s, idx, EXP_ASM, CAPS_ASM)

    def expression_esc(self, s, idx, stopchar):
        """入れ子の外側にある stopchar までを 1 つの式として評価する。

        `(` `[` `[[` の対応を数えるので、括弧の内側にある stopchar では
        切らない。パターンの欄が `,` などで区切られているところで使う。
        """
        result = list(s[:idx])

        OPEN_TO_CLOSE = {'(': ')', '[': ']', OB: CB}
        CLOSE_CHARS   = set(OPEN_TO_CLOSE.values())

        stack = []

        for ch in s[idx:]:
            if not stack and ch == stopchar:
                result.append(chr(0))
                break
            elif ch in OPEN_TO_CLOSE:
                stack.append(ch)
                result.append(ch)
            elif ch in CLOSE_CHARS:
                if stack:
                    stack.pop()
                result.append(ch)
            else:
                result.append(ch)

        replaced = ''.join(result)
        return self.expression(self._terminate(replaced), idx)

    def expression_esc_float(self, s, idx, stopchar):
        """expression_esc の浮動小数点版。評価後に必ずモードを戻す。"""
        prev_typ  = self.state.exp_typ
        prev_mode = self.state.expmode
        prev_caps = self.state.expcaps
        self.state.exp_typ = 'f'
        try:
            v, idx = self.expression_esc(s, idx, stopchar)
        finally:
            self.state.exp_typ  = prev_typ
            self.state.expmode  = prev_mode
            self.state.expcaps  = prev_caps
        return (v, idx)


class BinaryWriter:
    """出力ワードを溜めて、`-b` の生バイナリを書く。

    溜め方が連続した配列ではなく「位置 → ワード」の辞書なのは、`.org` で
    いくらでも飛べるため。間が空いたところは書き出すときに `.padding` で
    埋める。1 ワードのビット数は `.bits` 次第で 8 とは限らない。
    """

    def __init__(self, state):
        self.state = state
        self._buffer = {}

    def _store(self, position, word_val):
        """1 ワードを溜める。ワード幅で切り、負の位置は捨てる。"""
        if self.state.bts <= 0:
            return
        if position < 0:
            return
        mask = (1 << self.state.bts) - 1
        self._buffer[position] = word_val & mask

    def flush(self):
        """溜めたワードを `-b` のファイルへ書き出す。

        最大位置までを 1 枚の配列にするので、`.org` の飛び先が極端だと
        巨大なファイルになる。1GB を超えたら、書く代わりに `.org` を
        疑うよう促してやめる。隙間は `.padding` の値で埋め、各ワードは
        `.bits` から決まるバイト数で、`.bits::big/little` の順に並べる。

        `-o` と併用されているときは、リンカのために 0 のまま残した命令欄が
        あればそれを警告する。その生バイナリはリンク後にしか正しくない。
        """
        if not self.state.outfile:
            return

        if self.state.bts <= 0:
            self.state.diag(f" error - flush: bts={self.state.bts} is invalid (<=0); "
                 f"no output written to '{self.state.outfile}'.", set_error=True)
            return

        if not self._buffer:
            return

        valid_buffer = {k: v for k, v in self._buffer.items() if k >= 0}
        if not valid_buffer:
            return

        max_word_pos = max(valid_buffer.keys())

        word_bits = self.state.bts
        bytes_per_word = (word_bits + 7) // 8

        total_size = (max_word_pos + 1) * bytes_per_word

        if total_size <= 0:
            return

        _MAX_OUTPUT_BYTES = 1 << 30
        if total_size > _MAX_OUTPUT_BYTES:
            self.state.diag(f" error - output size {total_size} bytes exceeds maximum "
                            f"{_MAX_OUTPUT_BYTES}. Check for incorrect .ORG or address "
                            f"values.", set_error=True, force=True)
            return

        pad_val = int(self.state.padding) & ((1 << word_bits) - 1)
        if pad_val != 0:
            tmp = pad_val
            if self.state.endian == 'little':
                pad_bytes = bytes([(tmp >> (8 * i)) & 0xff for i in range(bytes_per_word)])
            else:
                pad_bytes = bytes([(tmp >> (8 * (bytes_per_word - 1 - i))) & 0xff
                                   for i in range(bytes_per_word)])
            data = bytearray(pad_bytes * (max_word_pos + 1))
        else:
            data = bytearray(total_size)

        for pos, val in valid_buffer.items():
            base_idx = pos * bytes_per_word

            temp_val = val
            if self.state.endian == 'little':
                for i in range(bytes_per_word):
                    if base_idx + i < total_size:
                        data[base_idx + i] = temp_val & 0xff
                        temp_val >>= 8
            else:
                for i in range(bytes_per_word - 1, -1, -1):
                    if base_idx + i < total_size:
                        data[base_idx + i] = temp_val & 0xff
                        temp_val >>= 8

        try:
            with open(self.state.outfile, 'wb') as f:
                f.write(data)
        except OSError as e:
            self.state.diag(f" error - cannot write '{self.state.outfile}': {e}",
                            set_error=True)
            return
        print(f"wrote raw binary {self.state.outfile} ({len(data)} bytes)", file=sys.stderr)

        if self.state.elf_objfile:
            _zeroed = [r for r in self.state.relocations
                       if insn_reloc_field_mask(r[3], self.state.elf_machine, self.state) is not None]
            if _zeroed:
                _where = ', '.join(f"{r[0]}+0x{r[1]:x}" for r in _zeroed[:4])
                if len(_zeroed) > 4:
                    _where += ', ...'
                self.state.diag(
                    f" warning - {len(_zeroed)} instruction field(s) were left 0 for the"
                    f" linker ({_where}); this raw binary is only correct after linking"
                    f" {self.state.elf_objfile}. Drop -o to have axx fill them in.",
                    set_error=False, force=True)

    def fwrite(self, position, x, prt):
        """1 ワードを溜める。prt が真ならリスティング用に 16 進でも出す。"""
        if self.state.bts <= 0:
            return 0
        mask = (1 << self.state.bts) - 1
        val = x & mask

        if prt:
            b = self.state.bts
            colm = (b + 3) // 4
            print(f" 0x{val:0{colm}x}", end='')

        self._store(position, val)
        return 1

    def outbin2(self, a, x):
        """1 ワードを溜める（リスティングには出さない）。"""
        if self.state.should_report_errors():
            try:
                self.fwrite(a, int(x), 0)
            except (OverflowError, ValueError):
                self.state.diag(f" error - non-finite value {x!r} cannot be written as binary word.", set_error=True)

    def outbin(self, a, x):
        """1 ワードを溜め、`-v` のパス2か対話モードならリスティングにも出す。"""
        if self.state.should_report_errors():
            _prt = 1 if ((self.state.pas == 2 and self.state.verbose) or self.state.pas == 0) else 0
            try:
                self.fwrite(a, int(x), _prt)
            except (OverflowError, ValueError):
                self.state.diag(f" error - non-finite value {x!r} cannot be written as binary word.", set_error=True)

    def align_(self, addr):
        """アドレスを現在の `.align` の倍数まで繰り上げる。"""
        if self.state.align <= 0:
            return addr
        a = addr % self.state.align
        if a == 0:
            return addr
        return addr + self.state.align - a


class DirectiveProcessor:
    """パターンファイル側のディレクティブを処理する。

    各ハンドラは「自分の担当でなければ False、処理したら True」を返す決まりで、
    呼び出し側は順に試す。ディレクティブは書かれた位置から効くので
    （`.check` も `.setsym` も後のものが前を上書きする）、ここでの処理は
    パターン行の照合とは違って順序に依存する。
    """

    def __init__(self, state, expr_eval, binary_writer, symbol_manager=None, parser=None):
        self.state = state
        self.expr_eval = expr_eval
        self.binary_writer = binary_writer
        self.symbol_manager = symbol_manager
        self.parser = parser

    def add_avoiding_dup(self, l, e):
        """リストに無ければ足す。"""
        if e not in l:
            l.append(e)
        return l

    def clear_symbol(self, i):
        """`.clearsym` — 名前を 1 つ、または引数なしで全部のシンボルを消す。"""
        if len(i) == 0 or i[0] != '.clearsym':
            return False

        if len(i) >= 3 and i[2] != '':
            key = StringUtils.upper(i[2])
            self.state.symbols.pop(key, None)
            self.state.strsymbols.pop(key, None)
            self.state.arrsymbols.pop(key, None)
            self.state.arrgen += 1
        else:
            self.state.symbols = {}
            self.state.strsymbols = {}
            self.state.arrsymbols = {}
            self.state.arrgen += 1

        return True

    _const_setsym_cache = {}
    _upper_key_cache = {}
    _check_cache = {}
    _elftype_cache = {}
    _elfdecl_cache = {}

    def set_symbol(self, i):
        """`.setsym` — あらゆる種類のシンボルを定義する。

        どの種類になるかは値欄の見た目で決まる。`"..."` が文字列シンボル、
        `[...]` が配列シンボル、名前をカンマで並べたものが集合、集合式
        (`a&b` など) が計算された集合、裸の名前がコピーかその名前を保持する
        文字列シンボル、どれでもなければ数値式。特殊形の判定が数値解釈より
        先に来るが、集合になりえない欄は必ず数値解釈へ譲るので、以前
        アセンブルできていたものの意味は変わらない。
        """
        if len(i) == 0 or i[0] != '.setsym':
            return False

        if i[1]:
            value_field = i[2]
            if _PLAIN_NUM_RE.match(value_field):
                _uc = DirectiveProcessor._upper_key_cache
                key = _uc.get(i[1])
                if key is None:
                    key = StringUtils.upper(i[1])
                    if len(_uc) >= 65536:
                        _uc.clear()
                    _uc[i[1]] = key
                _c = DirectiveProcessor._const_setsym_cache
                v = _c.get(value_field, _SETSYM_MISS)
                if v is _SETSYM_MISS:
                    v, _idx = self.expr_eval.expression_pat(value_field, 0)
                    if len(_c) >= 65536:
                        _c.clear()
                    _c[value_field] = v
                self.state.symbols[key] = v
                return True
            key = StringUtils.upper(i[1])
        elif i[2]:
            key = StringUtils.upper(i[2])
            value_field = ''
        else:
            self.state.diag(" error - .setsym directive requires at least a symbol name", set_error=True)
            return False

        _vf = value_field.lstrip(' \t')
        if _vf.startswith('"'):
            self.state.strsymbols[key] = ObjectGenerator._txt_template_inner(_vf)
            return True
        if _vf.startswith('['):
            self.state.arrsymbols[key] = arr_items_from_text(self.expr_eval, _vf)
            self.state.arrgen += 1
            return True
        if symbol_copy_from_name(self.state, key, _vf):
            return True
        if symbol_set_from_text(self.state, key, value_field):
            return True
        if value_field:
            _c = DirectiveProcessor._const_setsym_cache
            v = _c.get(value_field, _SETSYM_MISS)
            if v is _SETSYM_MISS:
                v, idx = self.expr_eval.expression_pat(value_field, 0)
                if _CONST_SETSYM_RE.match(value_field):
                    if len(_c) >= 65536:
                        _c.clear()
                    _c[value_field] = v
        else:
            v = 0
        self.state.symbols[key] = v
        return True

    def bits(self, i):
        """`.bits` — 出力ワードのビット数とバイト順を決める。"""
        if len(i) == 0 or i[0] != '.bits':
            return False

        fields = []
        if len(i) >= 2 and i[1] != '':
            fields.append(i[1])
        if len(i) >= 3 and i[2] != '':
            fields.append(i[2])

        wf = ''
        for f in fields:
            fl = f.lower()
            if fl == 'big':
                self.state.endian = 'big'
            elif fl == 'little':
                self.state.endian = 'little'
            elif wf == '':
                wf = f
            else:
                self.state.diag(f" error - .bits: multiple word-width fields given "
                                f"({wf!r} and {f!r}).", set_error=True)

        if wf:
            self.state.error_undefined_label = False
            v, _idx = self.expr_eval.expression_pat(wf, 0)
            ok = not self.state.error_undefined_label and not _is_undef_derived(v)
            nb = 0
            if ok:
                try:
                    nb = int(v)
                except (OverflowError, ValueError, TypeError):
                    ok = False
                else:
                    ok = (nb == v) and 1 <= nb <= 64
            if ok:
                self.state.bts = nb
            else:
                self.state.diag(f" error - .bits: word width must be an integer in "
                                f"1..64, got {wf!r}.", set_error=True)
            self.state.error_undefined_label = False
        return True

    def paddingp(self, i):
        """`.padding` — 隙間を埋める値。"""
        if len(i) == 0 or i[0] != '.padding':
            return False

        if len(i) >= 3 and i[2] != '':
            v, idx = self.expr_eval.expression_pat(i[2], 0)
        elif len(i) >= 2 and i[1] != '':
            v, idx = self.expr_eval.expression_pat(i[1], 0)
        else:
            v = 0
        try:
            self.state.padding = int(v)
        except (OverflowError, ValueError):
            self.state.diag(" error - .padding: non-finite or invalid value; padding unchanged.", set_error=True)
        return True

    def symbolc(self, i):
        """`.symbolc` — シンボルに使える文字を増やす。"""
        if len(i) == 0 or i[0] != '.symbolc':
            return False

        if len(i) > 2 and i[2] != '':
            self.state.swordchars = ALPHABET + DIGIT + i[2]
        return True

    def vliwp(self, i):
        """`.vliw` — バンドル幅・命令幅・テンプレート幅・NOP を宣言する。"""
        if len(i) == 0 or i[0] != ".vliw":
            return False

        if len(i) < 5:
            self.state.diag(f" error - .vliw directive requires 4 parameters (vliwbits, vliwinstbits, vliwtemplatebits, nop_value), got {len(i) - 1}", set_error=True)
            return False

        v1, idx = self.expr_eval.expression_pat(i[1], 0)
        v2, idx = self.expr_eval.expression_pat(i[2], 0)
        v3, idx = self.expr_eval.expression_pat(i[3], 0)
        v4, idx = self.expr_eval.expression_pat(i[4], 0)

        try:
            self.state.vliwbits        = int(v1)
            self.state.vliwinstbits    = int(v2)
            self.state.vliwtemplatebits = int(v3)
        except (OverflowError, ValueError):
            self.state.diag(" error - .vliw: non-finite parameter value.", set_error=True)
            return True

        try:
            v4 = int(v4) & 0xFFFFFFFFFFFFFFFF
        except (OverflowError, ValueError):
            self.state.diag(" error - .vliw: non-finite nop value.", set_error=True)
            return True

        _VLIW_INSTBITS_MAX = 8192
        if not (0 <= self.state.vliwinstbits <= _VLIW_INSTBITS_MAX):
            self.state.diag(f" error - .vliw: vliwinstbits {self.state.vliwinstbits} is out of range "
                 f"(must be 0-{_VLIW_INSTBITS_MAX}).", set_error=True)
            return True

        self.state.vliwflag = True

        l = []
        for _byte_idx in range(self.state.vliwinstbits // 8 + (0 if self.state.vliwinstbits % 8 == 0 else 1)):
            l += [v4 & 0xff]
            v4 >>= 8
        self.state.vliwnop = l
        return True

    def epic(self, i):
        """`EPIC::` — インデックスコードの組み合わせごとにテンプレートを宣言する。"""
        if len(i) == 0 or StringUtils.upper(i[0]) != "EPIC":
            return False

        if len(i) <= 1 or i[1] == '':
            return False

        if len(i) < 3:
            self.state.diag(f" error - EPIC directive requires 2 parameters (indices, pattern), got {len(i) - 1}", set_error=True)
            return False

        s = i[1]
        idxs = []
        idx = 0
        while True:
            v, idx = self.expr_eval.expression_pat(s, idx)
            idxs += [v]
            if idx < len(s) and s[idx] == ',':
                idx += 1
                continue
            break

        s2 = i[2]
        self.state.vliwset = self.add_avoiding_dup(self.state.vliwset, [idxs, s2])
        return True

    def _cond_tests_relocated_var(self, cond_src):
        """そのエラー条件が、リンカが埋める変数を見ているか。

        `-o` では命令欄に入る値をまだ 0 にしてあるので、その変数に対する
        範囲検査は今の時点では意味を持たない。ここで真になった条件は
        報告しない。そうしないと、リンク後には正しいコードが
        「範囲外」で落ちてしまう。名前は語として一致したときだけ数える。
        """
        if not self.state.elf_objfile or not self.state.reloc_constraints:
            return False
        for var, rtype in self.state.reloc_constraints.items():
            if insn_reloc_field_mask(rtype, self.state.elf_machine, self.state) is None:
                continue
            for m in re.finditer(re.escape(var), cond_src):
                b, e = m.start(), m.end()
                if b > 0 and (cond_src[b - 1].isalnum() or cond_src[b - 1] == '_'):
                    continue
                if e < len(cond_src) and (cond_src[e].isalnum() or cond_src[e] == '_'):
                    continue
                return True
        return False

    def error(self, s):
        """error_patterns 欄を評価する。返り値は (発生したか, エラーコード)。

        `条件;コード` をカンマで並べたものを順に見る。評価は浮動小数点モードで
        行う（ビット演算とシフトは内部で補正するので、書いたとおりに読める）。
        リンカが埋める変数を見ている条件は _cond_tests_relocated_var で外す。
        """
        ss = s.replace(' ', '')
        if ss == "":
            return False, 0

        s += chr(0)
        idx = 0
        error_code = 0
        triggered = False

        while True:
            ch = s[idx] if idx < len(s) else chr(0)
            if ch == chr(0):
                break
            if ch == ',':
                idx += 1
                continue

            idx_before = idx
            prev_typ = self.expr_eval.state.exp_typ
            self.expr_eval.state.exp_typ = 'f'
            try:
                u, idxn = self.expr_eval.expression_pat(s, idx)
                idx = idxn
                if idx < len(s) and s[idx] == ';':
                    idx += 1
                t, idx = self.expr_eval.expression_pat(s, idx)
            finally:
                self.expr_eval.state.exp_typ = prev_typ

            if idx <= idx_before:
                break

            if (self.state.should_report_errors()) and u \
                    and not self._cond_tests_relocated_var(s[idx_before:idx]):
                try:
                    t_int = int(t)
                except (OverflowError, ValueError):
                    t_int = 0
                print(f"Line {self.state.ln} Error code {t_int} ", end="", file=sys.stderr)
                if 0 <= t_int < len(self.state.errors):
                    print(f"{self.state.errors[t_int]}", end='', file=sys.stderr)
                print(": ", file=sys.stderr)
                error_code = t_int
                triggered = True
                self.state.had_error = True

        return triggered, error_code

    def _dir_var(self, field):
        """ディレクティブの変数名欄を正規化する。変数名でなければ None。"""
        v = (field or '').strip().lower()
        if not v or not v.isascii() or not ('a' <= v[0] <= 'z'):
            return None
        for ch in v[1:]:
            if not ('a' <= ch <= 'z' or ch.isdigit() or ch == '_'):
                return None
        self.state.varnames.add(v)
        return v

    def elem_list_expand(self, text):
        """要素リストを展開する。配列シンボルの名前はその中身に開く。

        `""` は省略可能の印（CHECK_OMIT）として空文字で残す。これで
        レジスタ名の並びを一度書いて `.check` / `.enum` / `.map` で使い回せる。
        """
        out = []
        for tok in (text or '').split(','):
            tok = StringUtils.upper(tok.strip())
            if tok in ('', '""', "''"):
                out.append('')
                continue
            arr = self.state.arrsymbols.get(tok)
            if arr is None:
                out.append(tok)
                continue
            for v in arr:
                out.append(StringUtils.upper(v) if isinstance(v, str)
                           else ObjectGenerator._txt_radix(v, 10))
        return out

    def check_processing(self, i):
        """`.check` — その変数が捕らえてよいシンボルを制限する。"""
        if len(i) == 0 or i[0] != '.check':
            return False
        if i[1].strip():
            var_field, syms_field = i[1], i[2]
        elif i[2].strip():
            var_field, syms_field = i[2], ''
        else:
            self.state.diag(" error - .check: variable name is not specified.", set_error=True)
            return True
        var = self._dir_var(var_field)
        if var is None:
            self.state.diag(f" error - .check: variable should be a lower case name ('{var_field}').", set_error=True)
            return True
        _ck = (var, syms_field)
        _ce = DirectiveProcessor._check_cache.get(_ck)
        if _ce is not None and _ce[0] == self.state.arrgen:
            self.state.check_constraints[var] = _ce[1]
            return True
        syms = []
        for nm in self.elem_list_expand(syms_field):
            if nm == '':
                if CHECK_OMIT not in syms:
                    syms.append(CHECK_OMIT)
                continue
            syms.append(nm)
        if len(DirectiveProcessor._check_cache) >= 65536:
            DirectiveProcessor._check_cache.clear()
        DirectiveProcessor._check_cache[_ck] = (self.state.arrgen, syms)
        self.state.check_constraints[var] = syms
        return True

    def elftype_processing(self, i):
        """`.elftype` — リロケーション型の名前と番号を自分で決める。"""
        if len(i) == 0 or i[0] != '.elftype':
            return False
        name_field = i[1] if i[1] else i[2]
        value_field = i[2] if i[1] else ''
        nm = ''.join(c for c in name_field if c not in ' \t').lower()
        if not nm:
            self.state.diag(" error - .elftype: type name is not specified.", set_error=True)
            return True
        if not value_field:
            self.state.diag(f" error - .elftype: type number is not specified ('{nm}').",
                            set_error=True)
            return True

        _c = DirectiveProcessor._elftype_cache
        v = _c.get(value_field, _SETSYM_MISS)
        if v is _SETSYM_MISS:
            self.state.error_undefined_label = False
            v, _idx = self.expr_eval.expression_pat(value_field, 0)
            try:
                v = int(v)
            except (OverflowError, ValueError):
                v = None
            if self.state.error_undefined_label or v is None \
                    or v < 1 or v > 2147483647:
                self.state.diag(" error - .elftype: type number must be an integer in "
                                f"1..2147483647, got '{value_field}'.", set_error=True)
                self.state.error_undefined_label = False
                v = None
            self.state.error_undefined_label = False
            if len(_c) >= 65536:
                _c.clear()
            _c[value_field] = v
        if v is None:
            return True
        _e = self.state.elf
        _w = None
        if len(i) > 3 and i[3] and i[3].strip():
            _w = self._elf_decl_num('.elftype', i[3], 1, 8)
            if _w is None:
                return True
        _pc = None
        if len(i) > 4 and i[4] and i[4].strip():
            _pc = self._elf_decl_num('.elftype', i[4], 0, 1)
            if _pc is None:
                return True
        if self.state.elftypes.get(nm) != v \
                or _e.type_width.get(nm) != _w \
                or ((nm in _e.type_pcrel) != bool(_pc)):
            self.state.elftypes[nm] = v
            if _w is None:
                _e.type_width.pop(nm, None)
            else:
                _e.type_width[nm] = _w
            if _pc:
                _e.type_pcrel.add(nm)
            else:
                _e.type_pcrel.discard(nm)
            _e.decl_gen += 1
        return True


    @staticmethod
    def _elf_decl_fields(i):
        """ELF 宣言の欄を (値, 名前) に整える。欄の詰め方の違いを吸収する。"""
        f1 = i[1] if len(i) > 1 and i[1] and i[1].strip() else ''
        f2 = i[2] if len(i) > 2 and i[2] else ''
        return (f1, f2) if f1 else (f2, '')

    def _elf_decl_num(self, dname, field, lo, hi):
        """ELF 宣言の数値欄を lo..hi の整数として読む。範囲外なら None。

        同じ綴りが何度も現れるので結果を覚える。未定義ラベルを含む式は
        エラーにし、覚えた印 (error_undefined_label) は呼び出しの前後で
        必ず落として、関係のない行へ漏らさない。
        """
        text = field.strip() if field else ''
        if not text:
            self.state.diag(f" error - {dname}: a number is required.", set_error=True)
            return None
        _c = DirectiveProcessor._elfdecl_cache
        key = (text, lo, hi)
        v = _c.get(key, _SETSYM_MISS)
        if v is not _SETSYM_MISS:
            if v is None:
                self.state.diag(f" error - {dname}: value must be an integer in "
                                f"{lo}..{hi}, got '{text}'.", set_error=True)
            return v
        self.state.error_undefined_label = False
        v, _idx = self.expr_eval.expression_pat(text, 0)
        try:
            v = int(v)
        except (OverflowError, ValueError):
            v = None
        if self.state.error_undefined_label or v is None or v < lo or v > hi:
            self.state.diag(f" error - {dname}: value must be an integer in "
                            f"{lo}..{hi}, got '{text}'.", set_error=True)
            v = None
        self.state.error_undefined_label = False
        if len(_c) >= 65536:
            _c.clear()
        _c[key] = v
        return v

    def _elf_decl_set(self, attr, value):
        """ELF 宣言を書き込む。実際に変わったときだけ世代番号を進める。

        elf_machine_table() のキャッシュはこの世代番号で捨てられる。
        """
        e = self.state.elf
        if getattr(e, attr) != value:
            setattr(e, attr, value)
            e.decl_gen += 1

    def elfmachine_processing(self, i):
        """`.elfmachine` — e_machine の既定値（`-m` より弱い）。"""
        if len(i) == 0 or i[0] != '.elfmachine':
            return False
        _num, _nm = self._elf_decl_fields(i)
        v = self._elf_decl_num('.elfmachine', _num, 0, 65535)
        if v is None:
            return True
        nm = _nm.strip()
        self._elf_decl_set('decl_machine', v)
        self._elf_decl_set('decl_name', nm)
        e = self.state.elf
        if not e.machine_from_cli and e.machine != v:
            e.machine = v
            e.decl_gen += 1
        return True

    def elfclass_processing(self, i):
        """`.elfclass` — ELF32 / ELF64 の既定値（`-f` より弱い）。"""
        if len(i) == 0 or i[0] != '.elfclass':
            return False
        text = self._elf_decl_fields(i)[0].strip()
        if text == '32':
            self._elf_decl_set('decl_class', 1)
        elif text == '64':
            self._elf_decl_set('decl_class', 2)
        else:
            self.state.diag(f" error - .elfclass: value must be 32 or 64, got '{text}'.",
                            set_error=True)
        return True

    def elfrela_processing(self, i):
        """`.elfrela` — .rela（加数を欄に持つ）か .rel かを決める。"""
        if len(i) == 0 or i[0] != '.elfrela':
            return False
        text = self._elf_decl_fields(i)[0].strip().lower()
        if text in ('1', 'rela'):
            self._elf_decl_set('decl_rela', 1)
        elif text in ('0', 'rel'):
            self._elf_decl_set('decl_rela', 0)
        else:
            self.state.diag(f" error - .elfrela: value must be 1/rela or 0/rel, "
                            f"got '{text}'.", set_error=True)
        return True

    def elfwidth_processing(self, i):
        """`.elfwidth` — 欄の幅から型を推測するときの対応を宣言する。

        幅は 2 のべき乗でなくてもよい（`.elfwidth::3` など）。
        """
        if len(i) == 0 or i[0] != '.elfwidth':
            return False
        _wf, _tf = self._elf_decl_fields(i)
        w = self._elf_decl_num('.elfwidth', _wf, 1, 8)
        if w is None:
            return True
        t = _tf.strip()
        if not t:
            self.state.diag(" error - .elfwidth: relocation type is not specified.",
                            set_error=True)
            return True
        e = self.state.elf
        if e.decl_width.get(w) != t:
            e.decl_width[w] = t
            e.decl_gen += 1
        return True

    def elfextern_processing(self, i):
        """`.elfextern` — 外部シンボル参照に使う既定の型。"""
        if len(i) == 0 or i[0] != '.elfextern':
            return False
        t = self._elf_decl_fields(i)[0].strip()
        if not t:
            self.state.diag(" error - .elfextern: relocation type is not specified.",
                            set_error=True)
            return True
        self._elf_decl_set('decl_extern', t)
        return True

    def elfdwarf_processing(self, i):
        """`.elfdwarf` — DWARF セクション内の絶対参照に使う型。"""
        if len(i) == 0 or i[0] != '.elfdwarf':
            return False
        t = self._elf_decl_fields(i)[0].strip()
        if not t:
            self.state.diag(" error - .elfdwarf: relocation type is not specified.",
                            set_error=True)
            return True
        self._elf_decl_set('decl_dwarf', t)
        return True

    _ELF_HDR_FIELDS = {
        'type':       (0, 0xFFFF),
        'flags':      (0, 0xFFFFFFFF),
        'version':    (0, 0xFFFFFFFF),
        'entry':      (0, 0x7FFFFFFFFFFFFFFF),
        'osabi':      (0, 0xFF),
        'abiversion': (0, 0xFF),
    }

    def elfheader_processing(self, i):
        """`.elfheader` — ELF ヘッダの欄（e_flags など）を直接書く。"""
        if len(i) == 0 or i[0] != '.elfheader':
            return False
        _ff, _vf = self._elf_decl_fields(i)
        fld = ''.join(c for c in _ff if c not in ' \t').lower()
        rng = DirectiveProcessor._ELF_HDR_FIELDS.get(fld)
        if rng is None:
            self.state.diag(f" error - .elfheader: unknown field '{fld}' (type, flags, "
                            f"version, entry, osabi, abiversion).", set_error=True)
            return True
        v = self._elf_decl_num('.elfheader', _vf, rng[0], rng[1])
        if v is None:
            return True
        e = self.state.elf
        if e.decl_hdr.get(fld) != v:
            e.decl_hdr[fld] = v
            e.decl_gen += 1
        return True

    def elffield_processing(self, i):
        """`.elffield` — 命令語の中のどのビットに値が入るかを宣言する。

        AArch64 だけは組み込みの表を持っているが、ほかのマシンで
        命令欄リロケーションを使うにはこの宣言が要る。
        """
        if len(i) == 0 or i[0] != '.elffield':
            return False
        _tf, _mf = self._elf_decl_fields(i)
        t = _tf.strip()
        if not t:
            self.state.diag(" error - .elffield: relocation type is not specified.",
                            set_error=True)
            return True
        m = self._elf_decl_num('.elffield', _mf, 1, 0xFFFFFFFFFFFFFFFF)
        if m is None:
            return True
        off = 0
        if len(i) > 3 and i[3] and i[3].strip():
            off = self._elf_decl_num('.elffield', i[3], 0, 255)
            if off is None:
                return True
        e = self.state.elf
        if e.decl_field.get(t) != (m, off):
            e.decl_field[t] = (m, off)
            e.decl_gen += 1
        return True

    def elfsection_processing(self, i):
        """`.elfsection` — 名前から推測できないセクションの属性を宣言する。

        sh_flags / sh_type / 整列 / 要素サイズ。ベクタ表、`.bss` ではない
        未初期化領域、note セクションなどのため。
        """
        if len(i) == 0 or i[0] != '.elfsection':
            return False
        _nf, _ff = self._elf_decl_fields(i)
        nm = _nf.strip()
        if not nm:
            self.state.diag(" error - .elfsection: section name is not specified.",
                            set_error=True)
            return True
        fl = self._elf_decl_num('.elfsection', _ff, 0, 0xFFFFFFFF)
        if fl is None:
            return True
        ty = None
        if len(i) > 3 and i[3] and i[3].strip():
            ty = self._elf_decl_num('.elfsection', i[3], 0, 0xFFFFFFFF)
            if ty is None:
                return True
        al = None
        if len(i) > 4 and i[4] and i[4].strip():
            al = self._elf_decl_num('.elfsection', i[4], 0, 0x40000000)
            if al is None:
                return True
            if al & (al - 1):
                self.state.diag(" error - .elfsection: alignment must be 0 or a "
                                f"power of two, got '{al}'.", set_error=True)
                return True
        es = None
        if len(i) > 5 and i[5] and i[5].strip():
            es = self._elf_decl_num('.elfsection', i[5], 0, 0xFFFFFFFF)
            if es is None:
                return True
        e = self.state.elf
        key = nm.lower()
        if e.decl_sec.get(key) != (fl, ty, al, es):
            e.decl_sec[key] = (fl, ty, al, es)
            e.decl_gen += 1
        return True

    def reloc_processing(self, i):
        """`.reloc` — その変数が捕らえたラベル参照に使う型を宣言する。"""
        if len(i) == 0 or i[0] != '.reloc':
            return False
        if i[1].strip():
            var_field, type_field = i[1], (i[2] if len(i) > 2 else '')
        else:
            self.state.diag(" error - .reloc: variable name is not specified.", set_error=True)
            return True
        var = self._dir_var(var_field)
        if var is None:
            self.state.diag(f" error - .reloc: variable should be a lower case name ('{var_field}').", set_error=True)
            return True
        tname = type_field.strip()
        if not tname:
            self.state.diag(" error - .reloc: relocation type is not specified.", set_error=True)
            return True
        if not self.state.elf_objfile:
            return True
        mach = elf_machine_table(self.state)
        rtype = _reloc_named(self.state, mach, tname)
        if rtype is None:
            _mname = mach['name']
            _key = (tname.lower(), self.state.elf_machine)
            if _key not in self.state._reloc_badname_seen:
                self.state._reloc_badname_seen.add(_key)
                self.state.diag(
                    f" error - .reloc: unknown relocation type '{tname}' for {_mname}.",
                    set_error=True)
            return True
        self.state.reloc_constraints[var] = rtype
        return True

    def clrreloc_processing(self, i):
        """`.clrreloc` — `.reloc` の宣言を外す（引数なしで全部）。"""
        if len(i) == 0 or i[0] != '.clrreloc':
            return False
        var_field = i[2].strip() if len(i) >= 3 and i[2] else ''
        if not var_field and len(i) >= 2 and i[1]:
            var_field = i[1].strip()
        if var_field:
            var = self._dir_var(var_field)
            if var is not None:
                self.state.reloc_constraints.pop(var, None)
            else:
                self.state.diag(f" error - .clrreloc: variable should be a lower case name ('{var_field}').", set_error=True)
        else:
            self.state.reloc_constraints.clear()
        return True

    def clrcheck_processing(self, i):
        """`.clrcheck` — `.check` の制限を外す（引数なしで全部）。"""
        if len(i) == 0 or i[0] != '.clrcheck':
            return False
        var_field = i[2].strip() if len(i) >= 3 and i[2] else ''
        if var_field:
            var = self._dir_var(var_field)
            if var is not None:
                self.state.check_constraints.pop(var, None)
            else:
                self.state.diag(f" error - .clrcheck: variable should be a lower case name ('{var_field}').", set_error=True)
        else:
            self.state.check_constraints.clear()
        return True

    def map_apply(self, i, into=None, set_check=True):
        """`.map` の本体。名前の並びに値を与え、同時に `.check` も設定する。

        値欄は 2 通りに読める。1 つの式なら、その中の変数は「リスト中の
        その名前の位置」（0 起点）に置き換わる。カンマで区切った複数項目なら
        名前と 1 対 1 で対応し、長さが違えば何も定義せずにエラーにする。
        `""` の位置は値も名前も消費せずに番号だけ進め、`.check` では
        省略可能の印として積む。
        """
        var_str = i[1].strip() if len(i) >= 2 else ''
        syms_str = i[2] if len(i) >= 3 else ''
        expr_str = i[3] if (len(i) >= 4 and i[3].strip()) else var_str
        var = self._dir_var(var_str)
        if var is None:
            return
        target = self.state.symbols if into is None else into

        elems = self.elem_list_expand(syms_str)
        vals = split_top_commas(expr_str)
        if len(vals) > 1 and len(vals) != len(elems):
            self.state.diag(f" error - .map: the value list has {len(vals)} items "
                            f"but the name list has {len(elems)}.", set_error=True)
            return
        for n, nm in enumerate(elems):
            if nm == '':
                continue
            src = vals[n] if len(vals) > 1 else expr_str
            val = PatternFileReader._map_subst_index(src, var, n)
            v, _ = self.expr_eval.expression_pat(val, 0)
            target[nm] = v
        if set_check:
            syms = []
            for nm in elems:
                if nm == '':
                    if CHECK_OMIT not in syms:
                        syms.append(CHECK_OMIT)
                    continue
                syms.append(nm)
            self.state.check_constraints[var] = syms

    def map_processing(self, i):
        """`.map` — シンボル表とそのチェックを 1 行で書く。"""
        if len(i) == 0 or i[0] != '.map':
            return False
        self.map_apply(i)
        return True

    def free_processing(self, i):
        """`.free` — 名前をすべての表から外して、作り直せるようにする。

        消すのは `.setsym` の各種シンボル、`.sub` 表、`.check` の候補、
        そしてその名前が変数として読めるならその `.check` / `.enum` / `.reloc`。
        位置依存なので、上のパターンからはまだ見える。
        """
        if len(i) == 0 or i[0] != '.free':
            return False
        names = (i[2] if len(i) >= 3 and i[2] else (i[1] if len(i) >= 2 else ''))
        if not names.strip():
            self.state.diag(" error - .free: needs '.free::<name,name,...>'.",
                            set_error=True)
            return True
        for nm in names.split(','):
            nm = nm.strip()
            if not nm:
                continue
            key = StringUtils.upper(nm)
            self.state.symbols.pop(key, None)
            self.state.strsymbols.pop(key, None)
            self.state.arrsymbols.pop(key, None)
            self.state.arrgen += 1
            self.state.freed_subs.add(key)
            for var, syms in self.state.check_constraints.items():
                self.state.check_constraints[var] = [x for x in syms if x != key]
            _v = nm.lower()
            if _v and PatternMatcher._var_name_at(_v, 0) == len(_v):
                self.state.check_constraints.pop(_v, None)
                self.state.reloc_constraints.pop(_v, None)
                self.state.enum_defs.pop(_v, None)
        return True

    def echo_processing(self, i):
        """`.echo` — 本文行から標準エラーへ印字する。ワードは出さない。"""
        if len(i) == 0 or i[0] != '.echo':
            return False
        st = self.state
        if not st.should_report_errors() or st._pass1_size_mode:
            return True
        items, err = _echo_items_cached(i[1])
        if err is not None:
            return True
        parts = []
        for k, v in items:
            if k == 's':
                parts.append(v)
            else:
                val, _idx = self.expr_eval.expression_pat(v, 0)
                parts.append(_mini_signed(val))
        _echo_write(parts)
        return True

    def passthru_processing(self, i):
        """`.passthru` — どのパターンにも当たらない行を、エラーにせず素通しする。"""
        if len(i) == 0 or i[0] != '.passthru':
            return False
        arg = ''
        for f in i[1:]:
            if f and f.strip():
                arg = StringUtils.upper(f.strip())
                break
        if arg in ('', 'ON'):
            self.state.passthru = 1
        elif arg == 'OFF':
            self.state.passthru = 0
        else:
            self.state.diag(f" error - .passthru: expected 'on' or 'off' "
                            f"('{arg}').", set_error=True)
        return True

    def eol_processing(self, i):
        """`.eol` — 1 ソース行につき 1 行の改行を自動で入れる。"""
        if len(i) == 0 or i[0] != '.eol':
            return False
        arg = ''
        for f in i[1:]:
            if f and f.strip():
                arg = StringUtils.upper(f.strip())
                break
        if arg in ('', 'ON'):
            self.state.eol = 1
        elif arg == 'OFF':
            self.state.eol = 0
        else:
            self.state.diag(f" error - .eol: expected 'on' or 'off' ('{arg}').",
                            set_error=True)
        return True

    def textmode_processing(self, i):
        """`.textmode` — テキスト置換モードに切り替える。

        ラベル・式・`;` コメント・行頭の字下げを、書かれていたままの綴りで
        出力に残す。ソース間トランスレータを書くためのモード。
        """
        if len(i) == 0 or i[0] != '.textmode':
            return False
        arg = ''
        for f in i[1:]:
            if f and f.strip():
                arg = StringUtils.upper(f.strip())
                break
        if arg in ('', 'ON'):
            self.state.textmode = 1
            self.state.passthru = 1
            self.state.eol = 1
        elif arg == 'OFF':
            self.state.textmode = 0
            self.state.passthru = 0
            self.state.eol = 0
        else:
            self.state.diag(f" error - .textmode: expected 'on' or 'off' "
                            f"('{arg}').", set_error=True)
        return True

    def enum_processing(self, i):
        """`.enum` — 要素のリストを取る位置を宣言する（68000 の MOVEM など）。"""
        if len(i) == 0 or i[0] != '.enum':
            return False
        var_field = i[1].strip() if len(i) >= 2 else ''
        names_field = i[2] if len(i) >= 3 else ''
        expr_field = i[3] if len(i) >= 4 else ''
        var = self._dir_var(var_field)
        if var is None:
            self.state.diag(f" error - .enum: variable should be a lower case name ('{var_field}').", set_error=True)
            return True
        names = []
        for nm in self.elem_list_expand(names_field):
            if nm and nm not in names:
                names.append(nm)
        if not names:
            self.state.diag(" error - .enum: no enumeration element is given.", set_error=True)
            return True
        if not expr_field.strip():
            self.state.diag(" error - .enum: the value expression is missing.", set_error=True)
            return True
        self.state.enum_defs[var] = (tuple(names), expr_field)
        return True

    def clrenum_processing(self, i):
        """`.clrenum` — `.enum` の宣言を外す（引数なしで全部）。"""
        if len(i) == 0 or i[0] != '.clrenum':
            return False
        var_field = i[2].strip() if len(i) >= 3 and i[2] else ''
        if var_field:
            var = self._dir_var(var_field)
            if var is not None:
                self.state.enum_defs.pop(var, None)
            else:
                self.state.diag(f" error - .clrenum: variable should be a lower case name ('{var_field}').", set_error=True)
        else:
            self.state.enum_defs.clear()
        return True

    def errmsg_processing(self, i):
        """`.error` — エラーコードの文言を足す・上書きする。

        これがあるので、実装のソースを触らずに自分の文言を持てる。
        """
        if len(i) == 0 or i[0] != '.error':
            return False

        n_field = i[1].strip() if len(i) >= 2 else ''
        msg_field = i[2] if len(i) >= 3 else ''

        if not n_field:
            self.state.diag(" error - .error directive requires an error code (number).", set_error=True)
            return True

        self.state.error_undefined_label = False
        n, _idx = self.expr_eval.expression_pat(n_field, 0)
        bad = self.state.error_undefined_label or _is_undef_derived(n)
        self.state.error_undefined_label = False

        n_int = None
        if not bad:
            try:
                n_int = int(n)
            except (OverflowError, ValueError, TypeError):
                n_int = None
        _ERROR_CODE_MAX = 1000000
        if (n_int is None or n_int != n or n_int < 0
                or n_int > _ERROR_CODE_MAX):
            self.state.diag(f" error - .error: error code must be a non-negative integer "
                            f"(0-{_ERROR_CODE_MAX}), got {n_field!r}.", set_error=True)
            return True

        if not msg_field.strip().startswith('"'):
            self.state.diag(f" error - .error: message must be a double-quoted string, got {msg_field!r}.", set_error=True)
            return True
        msg = StringUtils.get_string(msg_field.strip())

        if n_int >= len(self.state.errors):
            self.state.errors.extend([''] * (n_int + 1 - len(self.state.errors)))
        self.state.errors[n_int] = msg
        return True


_SYM_CORE = set(DIGIT + ALPHABET + '_')

_PAT_DIRECTIVES = frozenset((
    '.setsym', '.clearsym', '.padding', '.bits', '.symbolc', '.vliw',
    '.check', '.clrcheck', '.reloc', '.clrreloc', '.map', '.free',
    '.passthru', '.eol', '.textmode', '.enum', '.clrenum', '.error',
    '.echo',
    '.elftype', '.elfmachine', '.elfclass', '.elfrela', '.elfwidth',
    '.elfextern', '.elfdwarf', '.elfheader', '.elfsection', '.elffield'))


_CONST_SETSYM_RE = re.compile(r"^[\s0-9+\-*/%()<>|&^~]+$|^\s*0[xX][0-9a-fA-F]+\s*$")

_PLAIN_NUM_RE = re.compile(r"^\s*(?:0[xX][0-9a-fA-F]+|[0-9]+)\s*$")

_SETSYM_MISS = object()


def _pat_is_directive(i):
    """そのパターン行がディレクティブか。`EPIC::` も含める。"""
    if not i:
        return False
    i0 = i[0]
    if not i0:
        return False
    if i0 in _PAT_DIRECTIVES:
        return True
    return len(i0) == 4 and (i0[0] == 'E' or i0[0] == 'e') \
        and StringUtils.upper(i0) == 'EPIC'

# テキスト置換モードで、バイトを出さずに綴りだけ通すべき組み込みディレクティブ。
_TEXTMODE_TEXT_ONLY_DIRS = frozenset((
    '.ORG', '.ALIGN', '.ZERO', '.ASCII', '.ASCIZ',
    '.RESB', '.RESW', '.RESD', '.RESQ'))


def _expects_expr(t, idx):
    """その位置でパターンが式捕捉 `!` を待っているか。"""
    while idx < len(t) and t[idx] in ' \t':
        idx += 1
    return idx < len(t) and t[idx] == '!'


class PatternMatcher:
    """アセンブリ行とパターンの `instruction` 欄を照合する。

    照合は 3 段に分かれている。

      match0          `!S{{表}}` のサブ表参照を実際の選択肢に展開して試す
      match0_brackets `[[ ]]` の省略可能部分を、組み合わせを変えて試す
      match           1 文字ずつ突き合わせる本体。スコアを付ける

    axx は最初に当たったパターンで止まらない。すべて試し、当たったものに
    特異度スコア (n_expr, -n_lit, n_sym) を付け、**最小**のものを採る:
    式捕捉が少ないもの、同点ならリテラル一致が多いもの、同点ならシンボル
    捕捉が少ないもの。これによりパターンファイル中の行の順序が結果に
    影響しない。特殊形を一般形の前に並べる手作業が要らないのはこのため。

    失敗した試行が状態を汚さないことが要。変数の束縛と、`-o` 用に積んだ
    ラベル参照は、試行ごとに保存して失敗時に巻き戻す。
    """

    def __init__(self, state, expr_eval, var_manager, symbol_manager, parser):
        self.state = state
        self.expr_eval = expr_eval
        self.var_manager = var_manager
        self.symbol_manager = symbol_manager
        self.parser = parser
        self.last_score = None
        self.last_match_score = None

    def remove_brackets(self, s, l):
        """指定した番号の `[[ ]]` 群を、中身ごと取り除く。

        番号は開き括弧の出現順（1 起点）。入れ子の対応は数えて取る。
        """
        serial = 0
        stack = []
        bracket_pairs = {}

        for i, char in enumerate(s):
            if char == OB:
                serial += 1
                stack.append((serial, i))
            elif char == CB:
                if stack:
                    ser, open_pos = stack.pop()
                    bracket_pairs[ser] = (open_pos, i)

        result = list(s)
        for index in l:
            if index in bracket_pairs:
                start_pos, end_pos = bracket_pairs[index]
                for j in range(start_pos, end_pos + 1):
                    result[j] = ''

        return ''.join(result)

    @staticmethod
    def _var_name_at(t, i):
        """その位置のパターン変数名の長さ。変数名でなければ 0。"""
        if i >= len(t) or not ('a' <= t[i] <= 'z'):
            return 0
        n = 1
        while i + n < len(t) and ('a' <= t[i + n] <= 'z'
                                  or t[i + n].isdigit() or t[i + n] == '_'):
            n += 1
        return n

    def _var_declare(self, name):
        """変数名を「この行で使われた名前」として登録する。"""
        if name:
            self.state.varnames.add(name)
        return name

    def _enum_capture(self, s, idx, edef):
        """`!E` の位置で、要素のリストをソースから読む。

        `,` と `/` がどちらも区切りで、`first-last` は列挙順序の範囲。
        逆順の範囲 (`a2-a0`) は範囲として読まず、`-` をパターンに委ねる。
        区切り文字は次の要素が続くときだけ消費するので、リストの後ろで
        パターンが `,` を使い続けられる。返り値は (値, 次の位置) か None。
        """
        names = edef[0]
        present = set()
        k1, e1 = _enum_name_at(s, StringUtils.skipspc(s, idx), names)
        if k1 < 0:
            return None
        while True:
            pos = e1
            pr = StringUtils.skipspc(s, e1)
            if pr < len(s) and s[pr] == '-':
                k2, e2 = _enum_name_at(s, StringUtils.skipspc(s, pr + 1), names)
                if k2 >= k1:
                    present.update(range(k1, k2 + 1))
                    pos = e2
                else:
                    present.add(k1)
            else:
                present.add(k1)
            ps = StringUtils.skipspc(s, pos)
            if ps < len(s) and s[ps] in ',/':
                k3, e3 = _enum_name_at(s, StringUtils.skipspc(s, ps + 1), names)
                if k3 >= 0:
                    k1, e1 = k3, e3
                    continue
            break
        v = self._enum_eval(edef, present)
        if v is None:
            return None
        return v, pos

    def _enum_eval(self, edef, present):
        """`.enum` の式を、現れた要素だけ値を持つ状態で評価する。

        現れなかった要素は 0。`.setsym` 定義を持たない要素があれば None を
        返してパターンを不一致にする（黙って 0 を寄与させない）。
        """
        names, expr = edef
        values = []
        for k, nm in enumerate(names):
            if k not in present:
                values.append(0)
                continue
            v = self.symbol_manager.get(nm)
            if v == "":
                return None
            values.append(v)
        prev = self.state.enum_bindings
        self.state.enum_bindings = (names, values)
        try:
            v, _ = self.expr_eval.expression_pat(expr, 0)
        finally:
            self.state.enum_bindings = prev
        return v

    def match(self, s, t):
        """ソース行 s とパターン t を 1 文字ずつ突き合わせる本体。

        トークナイザは無い。大文字・数字・記号は文字定数、小文字の名前は
        シンボル、`!x` は式、`!!x` は因子、`!F/!D/!Q` は浮動小数点、`!L` は
        式とその綴り、`!E` は列挙リスト、`!Y集合[変数]` は集合の項目番号。
        当たるたびに値を変数へ束縛し、同時に n_expr / n_lit / n_sym を数えて
        last_score に特異度スコアを残す。
        """
        self.state.deb1 = s
        self.state.deb2 = t

        n_expr = 0
        n_sym = 0
        n_lit = 0

        t = t.replace(OB, '').replace(CB, '')
        idx_s = 0
        idx_t = 0
        idx_s = StringUtils.skipspc(s, idx_s)
        idx_t = StringUtils.skipspc(t, idx_t)
        s += chr(0)
        t += chr(0)

        prev_alnum = False

        while True:

            s_sp = idx_s < len(s) and s[idx_s] in ' \t'
            t_sp = idx_t < len(t) and t[idx_t] in ' \t'
            idx_s = StringUtils.skipspc(s, idx_s)
            idx_t = StringUtils.skipspc(t, idx_t)

            word_break = s_sp and not t_sp
            b = s[idx_s]
            a = t[idx_t]

            if a == chr(0) and b == chr(0):
                self.last_score = (n_expr, -n_lit, n_sym)
                return True

            if a == '\\':
                idx_t += 1
                if idx_t < len(t) - 1 and t[idx_t] == b:
                    lit_alnum = t[idx_t].isalnum()
                    if lit_alnum and prev_alnum and word_break:
                        return False
                    idx_t += 1
                    idx_s += 1
                    n_lit += 1
                    prev_alnum = lit_alnum
                    continue
                else:
                    return False
            elif a in CAPITAL:
                if a == b.upper():

                    if prev_alnum and word_break:
                        return False
                    idx_s += 1
                    idx_t += 1
                    n_lit += 1
                    prev_alnum = True
                    continue
                else:
                    return False
            elif a == '!':
                prev_alnum = False
                n_expr += 1
                idx_t += 1
                if idx_t >= len(t):
                    return False
                a = t[idx_t]
                idx_t += 1
                if a == chr(0):
                    return False
                if a == 'F':
                    if idx_t >= len(t):
                        return False
                    _nl = self._var_name_at(t, idx_t)
                    if _nl == 0:
                        return False
                    a = self._var_declare(t[idx_t:idx_t + _nl])
                    idx_t = StringUtils.skipspc(t, idx_t + _nl)
                    if idx_t < len(t) and t[idx_t] == '\\':
                        idx_t += 1
                        stopchar = t[idx_t] if idx_t < len(t) else chr(0)
                        idx_t += 1
                    else:
                        stopchar = chr(0)

                    try:
                        v, idx_s = self.expr_eval.expression_esc_float(s, idx_s, stopchar)
                    finally:
                        self.state._elf_capturing_var = None
                    try:
                        v = float(v)
                        v = int.from_bytes(struct.pack('>f', v), "big")
                    except (OverflowError, ValueError, struct.error):
                        self.state.diag(" error - !F: cannot convert value to float32; using 0.", set_error=True)
                        v = 0
                    self.var_manager.put(a, v)
                    if stopchar != chr(0) and idx_s < len(s) and s[idx_s] == stopchar:
                        idx_s += 1
                    continue
                elif a == 'D':
                    if idx_t >= len(t):
                        return False
                    _nl = self._var_name_at(t, idx_t)
                    if _nl == 0:
                        return False
                    a = self._var_declare(t[idx_t:idx_t + _nl])
                    idx_t = StringUtils.skipspc(t, idx_t + _nl)
                    if idx_t < len(t) and t[idx_t] == '\\':
                        idx_t += 1
                        stopchar = t[idx_t] if idx_t < len(t) else chr(0)
                        idx_t += 1
                    else:
                        stopchar = chr(0)

                    try:
                        v, idx_s = self.expr_eval.expression_esc_float(s, idx_s, stopchar)
                    finally:
                        self.state._elf_capturing_var = None
                    try:
                        v = float(v)
                        v = int.from_bytes(struct.pack('>d', v), "big")
                    except (OverflowError, ValueError, struct.error):
                        self.state.diag(" error - !D: cannot convert value to float64; using 0.", set_error=True)
                        v = 0
                    self.var_manager.put(a, v)
                    if stopchar != chr(0) and idx_s < len(s) and s[idx_s] == stopchar:
                        idx_s += 1
                    continue
                elif a == 'Q':
                    if idx_t >= len(t):
                        return False
                    _nl = self._var_name_at(t, idx_t)
                    if _nl == 0:
                        return False
                    a = self._var_declare(t[idx_t:idx_t + _nl])
                    idx_t = StringUtils.skipspc(t, idx_t + _nl)
                    if idx_t < len(t) and t[idx_t] == '\\':
                        idx_t += 1
                        stopchar = t[idx_t] if idx_t < len(t) else chr(0)
                        idx_t += 1
                    else:
                        stopchar = chr(0)

                    idx_s_q_start = idx_s

                    try:
                        v, idx_s_after = self.expr_eval.expression_esc_float(s, idx_s, stopchar)
                    finally:
                        self.state._elf_capturing_var = None

                    raw_text = s[idx_s_q_start:idx_s_after]
                    if stopchar != chr(0) and raw_text.endswith(stopchar):
                        raw_text = raw_text[:-1]
                    raw_text = raw_text.strip()

                    if raw_text.startswith('qad{') and raw_text.endswith('}'):
                        raw_text = raw_text[4:-1].strip()

                    try:
                        h = IEEE754Converter.decimal_eval_expr(raw_text)
                    except (ValueError, ZeroDivisionError):
                        if isinstance(v, int) or (
                                isinstance(v, float) and v.is_integer()):
                            h = IEEE754Converter.decimal_to_ieee754_128bit_hex(
                                    str(int(v)))
                        else:
                            h = IEEE754Converter.decimal_to_ieee754_128bit_hex(
                                    repr(float(v)))

                    x = int(h, 16)
                    self.var_manager.put(a, x)
                    idx_s = idx_s_after
                    if stopchar != chr(0) and idx_s < len(s) and s[idx_s] == stopchar:
                        idx_s += 1
                    continue
                elif a == 'L':
                    if idx_t >= len(t):
                        return False
                    _nl = self._var_name_at(t, idx_t)
                    if _nl == 0:
                        return False
                    a = self._var_declare(t[idx_t:idx_t + _nl])
                    idx_t = StringUtils.skipspc(t, idx_t + _nl)
                    if idx_t < len(t) and t[idx_t] == '\\':
                        idx_t += 1
                        stopchar = t[idx_t] if idx_t < len(t) else chr(0)
                        idx_t += 1
                    else:
                        stopchar = chr(0)

                    idx_s_text_start = idx_s
                    self.state._elf_capturing_var = a
                    _cap_prior = self.state.error_undefined_label
                    self.state.error_undefined_label = False
                    try:
                        v, idx_s = self.expr_eval.expression_esc(s, idx_s, stopchar)
                    finally:
                        self.state._elf_capturing_var = None
                    _cap_undef = self.state.error_undefined_label

                    raw_text = s[idx_s_text_start:idx_s]
                    if stopchar != chr(0) and raw_text.endswith(stopchar):
                        raw_text = raw_text[:-1]
                    self.state.vars_text[a] = raw_text.strip(' \t' + chr(0))

                    if self.state.textmode:
                        self.state.error_undefined_label = _cap_prior
                        if _cap_undef or _is_undef_derived(v):
                            v = 0
                        self.var_manager.put_tagged(a, v, False)
                    else:
                        self.state.error_undefined_label = _cap_prior or _cap_undef
                        self.var_manager.put_tagged(a, v, _cap_undef)
                    if stopchar != chr(0) and idx_s < len(s) and s[idx_s] == stopchar:
                        idx_s += 1
                    continue
                elif a == 'E':
                    if idx_t >= len(t):
                        return False
                    _nl = self._var_name_at(t, idx_t)
                    if _nl == 0:
                        return False
                    a = self._var_declare(t[idx_t:idx_t + _nl])
                    idx_t += _nl
                    edef = self.state.enum_defs.get(a)
                    if edef is None:
                        return False
                    hit = self._enum_capture(s, idx_s, edef)
                    if hit is None:
                        return False
                    v, idx_s = hit
                    self.var_manager.put(a, v)
                    continue
                elif a == 'Y':
                    if idx_t >= len(t):
                        return False
                    _sl = self._var_name_at(t, idx_t)
                    if _sl == 0:
                        return False
                    setkey = StringUtils.upper(t[idx_t:idx_t + _sl])
                    idx_t += _sl
                    if idx_t >= len(t) or t[idx_t] != '[':
                        return False
                    idx_t += 1
                    _nl = self._var_name_at(t, idx_t)
                    if _nl == 0:
                        return False
                    a = self._var_declare(t[idx_t:idx_t + _nl])
                    idx_t += _nl
                    if idx_t >= len(t) or t[idx_t] != ']':
                        return False
                    idx_t += 1
                    arr = self.state.arrsymbols.get(setkey)
                    if not arr:
                        return False
                    _yk, _yend = _symset_item_at(s, idx_s, arr)
                    if _yk < 0:
                        return False
                    idx_s = _yend
                    self.var_manager.put(a, _yk)
                    n_expr -= 1
                    n_sym += 1
                    continue
                elif a == '!':
                    if idx_t >= len(t):
                        return False
                    _nl = self._var_name_at(t, idx_t)
                    if _nl == 0:
                        return False
                    a = self._var_declare(t[idx_t:idx_t + _nl])
                    idx_t += _nl
                    self.state._elf_capturing_var = a
                    _cap_prior = self.state.error_undefined_label
                    self.state.error_undefined_label = False
                    try:
                        v, idx_s = self.expr_eval.factor(s, idx_s)
                    finally:
                        self.state._elf_capturing_var = None
                    _cap_undef = self.state.error_undefined_label
                    self.state.error_undefined_label = _cap_prior or _cap_undef
                    self.var_manager.put_tagged(a, v, _cap_undef)
                    continue
                else:
                    _nl = self._var_name_at(t, idx_t - 1)
                    if _nl == 0:
                        return False
                    a = self._var_declare(t[idx_t - 1:idx_t - 1 + _nl])
                    idx_t += _nl - 1
                    idx_t = StringUtils.skipspc(t, idx_t)
                    if idx_t < len(t) and t[idx_t] == '\\':
                        idx_t += 1
                        stopchar = t[idx_t] if idx_t < len(t) else chr(0)
                        idx_t += 1
                    else:
                        stopchar = chr(0)

                    self.state._elf_capturing_var = a
                    _cap_prior = self.state.error_undefined_label
                    self.state.error_undefined_label = False
                    try:
                        v, idx_s = self.expr_eval.expression_esc(s, idx_s, stopchar)
                    finally:
                        self.state._elf_capturing_var = None
                    _cap_undef = self.state.error_undefined_label
                    self.state.error_undefined_label = _cap_prior or _cap_undef
                    self.var_manager.put_tagged(a, v, _cap_undef)
                    if stopchar != chr(0) and idx_s < len(s) and s[idx_s] == stopchar:
                        idx_s += 1
                    continue
            elif a in LOWER:
                prev_alnum = False
                _nl = self._var_name_at(t, idx_t)
                a = self._var_declare(t[idx_t:idx_t + _nl])
                idx_t += _nl
                prev_idx_s = idx_s
                allowed = self.state.check_constraints.get(a)
                allow_omit = allowed is not None and CHECK_OMIT in allowed
                w, idx_s = self.parser.get_symbol_word(s, idx_s)
                v = self.symbol_manager.get(w)
                if v == "":
                    for _cut in range(len(w) - 1, 0, -1):
                        if w[_cut] in _SYM_CORE:
                            continue
                        _v = self.symbol_manager.get(w[:_cut])
                        if _v != "":
                            w = w[:_cut]
                            v = _v
                            idx_s = prev_idx_s + _cut
                            break
                ok = v != "" and idx_s != prev_idx_s
                if ok and allowed is not None and w not in allowed:
                    ok = False
                if not ok and allowed:
                    _best = ''
                    for _nm in allowed:
                        if not _nm or len(_nm) <= len(_best):
                            continue
                        if StringUtils.upper(s[prev_idx_s:prev_idx_s + len(_nm)]) == _nm:
                            _best = _nm
                    if _best:
                        _v = self.symbol_manager.get(_best)
                        if _v != "":
                            w = _best
                            v = _v
                            idx_s = prev_idx_s + len(_best)
                            ok = True
                if not ok:
                    if not allow_omit:
                        return False
                    idx_s = prev_idx_s
                    self.var_manager.put(a, VAR_UNDEF)
                    n_sym += 1
                    continue
                self.var_manager.put(a, v)
                n_sym += 1
                continue
            elif a == '+' and b == '-' and _expects_expr(t, idx_t + 1):
                idx_t += 1
                n_lit += 1
                prev_alnum = False
                continue
            elif a == b:

                lit_alnum = a.isalnum()
                if lit_alnum and prev_alnum and word_break:
                    return False
                idx_t += 1
                idx_s += 1
                n_lit += 1
                prev_alnum = lit_alnum
                continue
            else:
                return False

    _MAX_COMBINATIONS = 1 << 16
    _SUB_MAX_DEPTH = 8

    @staticmethod
    def _find_sub_ref(t, start=0):
        """パターン中の最初の `!S{{表}}変数` を探す。

        返り値は (開始, 終了, 表の名前, 変数名) か None。`\\` で逃がされた
        ものは飛ばす。表の名前として読めない綴りや、変数名が続かないものも
        参照とみなさない。
        """
        i = start
        while True:
            i = t.find('!S{{', i)
            if i < 0:
                return None
            j = t.find('}}', i + 4)
            if j < 0:
                return None
            if i > 0 and t[i - 1] == '\\':
                i = j + 2
                continue
            name = t[i + 4:j]
            k = j + 2
            vl = PatternMatcher._var_name_at(t, k)
            if _is_sub_name(name) and vl > 0:
                return i, k + vl, name, t[k:k + vl]
            i = j + 2

    def _sub_variants(self, t, depth=0):
        """サブ表参照を実際の選択肢に展開し、(パターン, 束縛) を順に生む。

        エントリのパターンがさらに別の表を参照していれば再帰する。これが
        入れ子の表し方で、`.sub` を `.sub` の中に書くことはできない。
        連鎖は 8 段まで。未知の表名はパターンファイルを読むときに報告する。
        内側の変数が先に束縛されるので、外側の値リストはそれを使える。
        """
        ref = self._find_sub_ref(t)
        if ref is not None:
            self._var_declare(ref[3])
        if ref is None:
            yield t, ()
            return
        start, end, name, var = ref
        ref_text = '!S{{' + name + '}}'
        if depth >= self._SUB_MAX_DEPTH:
            self.state.diag(f" error - {ref_text}: sub table expansion exceeds "
                            f"maximum depth {self._SUB_MAX_DEPTH}.", set_error=True)
            return
        entries = self.state.sub_defs.get(name)
        if StringUtils.upper(name) in self.state.freed_subs:
            entries = None
        if entries is None:
            self.state.diag(f" error - {ref_text}: no sub table named {name!r} "
                            f"(define it with '.sub::{name} ... .return').",
                            set_error=True)
            return
        for ent_pat, ent_val in entries:
            nt = t[:start] + ent_pat + t[end:]
            for vt, binds in self._sub_variants(nt, depth + 1):
                yield vt, ((var, ent_val),) + binds

    def _sub_value(self, expr_text):
        """サブ表エントリの値リストを 1 つの値にまとめる。

        2 要素以上なら、最初が最上位になるよう `.bits` 幅ずつ詰める。
        単一要素はその値そのもの。
        """
        s = expr_text + chr(0)
        idx = 0
        vals = []
        while idx < len(s) and s[idx] != chr(0):
            if s[idx] == ',':
                idx += 1
                continue
            v, idx = self.expr_eval.expression_pat(s, idx)
            vals.append(v)
            if idx < len(s) and s[idx] == ',':
                idx += 1
                continue
            break
        if not vals:
            return 0
        if len(vals) == 1:
            return vals[0]
        bts = self.state.bts if self.state.bts > 0 else 8
        mask = (1 << bts) - 1
        acc = 0
        for v in vals:
            acc = (acc << bts) | (int(v) & mask)
        return acc

    def match0(self, s, t):
        """サブ表の選択肢を順に試す。当たったら変数へ値を束縛して True。

        失敗した試行のぶんは、変数の束縛と ELF のラベル参照をすべて
        巻き戻す。巻き戻さないと、当たらなかった選択肢が出力に化けて出る。
        """
        for vt, binds in self._sub_variants(t):
            saved_vars = dict(self.state.vars)
            saved_vars_undef = dict(self.state.vars_undef)
            saved_vars_text = dict(self.state.vars_text)
            saved_refs_len = len(self.state._elf_label_refs_seen)
            saved_v2l = dict(self.state._elf_var_to_label)
            saved_hint = dict(self.state._elf_insn_reloc_hint)
            if self.match0_brackets(s, vt):
                for var, ent_val in reversed(binds):
                    self.var_manager.put(var, self._sub_value(ent_val))
                return True
            self.state.vars = saved_vars
            self.state.vars_undef = saved_vars_undef
            self.state.vars_text = saved_vars_text
            del self.state._elf_label_refs_seen[saved_refs_len:]
            self.state._elf_var_to_label = saved_v2l
            self.state._elf_insn_reloc_hint = saved_hint
        return False

    def match0_brackets(self, s, t):
        """`[[ ]]` の省略可能部分を、組み合わせを変えて試す。

        取り除く群の数を 0 個から増やしていくので、省略可能部分は
        「できるだけ残す」方向から試される。群の数は 20 までで、
        それを超えたぶんは常に含める。組み合わせの総数にも上限 (65536) が
        あり、超えたパターンは不一致として扱い、行ごとに一度だけ警告する。
        組み合わせ爆発でアセンブルが止まらなくなるのを防ぐため。
        ここも試行ごとに状態を保存して巻き戻す。
        """
        if '[[' not in t and ']]' not in t:
            if self.match(s, t):
                self.last_match_score = self.last_score
                return True
            return False

        t = t.replace('[[', OB).replace(']]', CB)
        cnt = t.count(OB)
        sl = [_ + 1 for _ in range(cnt)]

        _MAX_OPT_GROUPS = 20
        if cnt > _MAX_OPT_GROUPS:
            self.state.diag(f" warning - pattern has {cnt} optional groups (max {_MAX_OPT_GROUPS}); "
                     f"first {_MAX_OPT_GROUPS} are treated as optional, "
                     f"remainder are always included.", set_error=False)
            sl = sl[:_MAX_OPT_GROUPS]
            cnt = _MAX_OPT_GROUPS

        _tried = 0
        for i in range(len(sl) + 1):

            for j in itertools.combinations(sl, i):
                _tried += 1
                if _tried > self._MAX_COMBINATIONS:

                    _warn_key = (getattr(self.state, 'current_file', None),
                                 getattr(self.state, 'ln', None), t)
                    if (self.state.should_report_errors()
                            and _warn_key not in self.state._combo_budget_warned):
                        self.state._combo_budget_warned.add(_warn_key)
                        self.state.diag(f" warning - a pattern with {cnt} optional group(s) exceeded the "
                             f"{self._MAX_COMBINATIONS}-combination match budget and was treated "
                             f"as non-matching; consider splitting it into multiple explicit "
                             f"pattern entries.", set_error=False)
                    return False
                lt = self.remove_brackets(t, list(j))
                saved_vars = dict(self.state.vars)
                saved_vars_undef = dict(self.state.vars_undef)
                saved_vars_text = dict(self.state.vars_text)
                saved_refs_len = len(self.state._elf_label_refs_seen)
                saved_v2l      = dict(self.state._elf_var_to_label)
                saved_hint     = dict(self.state._elf_insn_reloc_hint)
                if self.match(s, lt):
                    self.last_match_score = self.last_score
                    return True
                self.state.vars = saved_vars
                self.state.vars_undef = saved_vars_undef
                self.state.vars_text = saved_vars_text
                del self.state._elf_label_refs_seen[saved_refs_len:]
                self.state._elf_var_to_label = saved_v2l
                self.state._elf_insn_reloc_hint = saved_hint
        return False


class PatternFileReader:
    """パターンファイルを読んで、行を欄に割った表にする。

    `.INCLUDE` を再帰で展開し、各行をマクロ層に通してから `::` で最大 6 欄に
    割る。`.sub` ブロックと `.func` ブロックはここで本文を集めて別に持つので、
    その中の行が普通のパターン行として照合されることはない。
    """

    def __init__(self, parser, macro_proc=None):
        self.parser = parser
        self.macro_proc = macro_proc if macro_proc is not None \
            else MacroPreprocessor(None, pat_mode=True)
        self.subs = {}
        self.funcs = {}

    def readpat(self, fn, base_dir=None, _depth=0, _chain=None):
        """パターンファイル 1 つを読み、パターン行の表を返す。

        `.INCLUDE` は 50 段まで。同じ実パスが連鎖に現れたら循環として
        報告して飛ばす。相対パスはそのファイルのある場所から解決する。

        コメントの扱いに後方互換の規則がある。`/*` は本来ブロックコメントを
        開くが、コメント行すべての先頭に `/*` を書く古い書き方のために、
        「すぐ次の行も `/*` で始まる」か「以降どこにも `*/` が無い」ときは
        自分の行を超えて延長しない。後者を先に知る必要があるので、
        rest_has_close で後ろから `*/` の有無を数えておく。
        """
        if fn == '':
            return []

        _MAX_PAT_DEPTH = 50
        if _depth > _MAX_PAT_DEPTH:
            diag(f" error - pattern .INCLUDE nesting exceeds {_MAX_PAT_DEPTH}: '{fn}'", set_error=True)
            return []

        if base_dir and not os.path.isabs(fn):
            fn = os.path.join(base_dir, fn)

        _real = os.path.realpath(fn)
        if _chain is None:
            _chain = frozenset()
        if _real in _chain:
            diag(f" error - circular pattern .INCLUDE detected: '{fn}' "
                 f"(already in include chain). Skipped.", set_error=True)
            return []
        _chain = _chain | {_real}

        this_dir = os.path.dirname(os.path.abspath(fn))

        p = []
        w = []

        if _depth == 0:
            self.macro_proc.reset_pass()
            self.subs = {}
            self.funcs = {}

        try:
            with open(fn, "rt", encoding="utf-8", errors="surrogateescape") as f:
                raw_lines = f.readlines()
        except OSError as e:
            diag(f" error - cannot open pattern file '{fn}': {e}", set_error=True)
            return []
        except UnicodeDecodeError as e:
            diag(f" error - pattern file '{fn}' is not valid UTF-8: {e}", set_error=True)
            return []
        raw_lines = StringUtils.join_backslash_continuations(raw_lines)

        expanded = list(self.macro_proc.expand(raw_lines, fn))
        rest_has_close = [False] * (len(expanded) + 1)
        for i in range(len(expanded) - 1, -1, -1):
            rest_has_close[i] = rest_has_close[i + 1] or ('*/' in expanded[i][0])

        def _starts_with_open_comment(s):
            return s.lstrip(' \t').startswith('/*')

        in_block_comment = False
        legacy_chain = False
        cur_sub = None
        func_stack = []
        for _li, (l, _mfile, _mln) in enumerate(expanded):

            was_in_comment = in_block_comment
            l, in_block_comment = StringUtils.remove_comment(l, in_block_comment)
            if not in_block_comment:
                legacy_chain = False
            elif not was_in_comment:
                this_is_bare_open = _starts_with_open_comment(expanded[_li][0])
                if legacy_chain and this_is_bare_open:
                    treat_as_legacy = True
                else:
                    next_looks_legacy = (_li + 1 < len(expanded)
                                          and _starts_with_open_comment(expanded[_li + 1][0]))
                    treat_as_legacy = next_looks_legacy or not rest_has_close[_li + 1]
                if treat_as_legacy:
                    in_block_comment = False
                    legacy_chain = this_is_bare_open
                else:
                    legacy_chain = False
            l = l.replace('\t', ' ')
            l = l.replace(chr(13), '')
            l = l.replace('\n', '')
            l = StringUtils.reduce_spaces(l)

            _dk = _dot_kw(l)
            if func_stack or _dk == '.FUNC':
                if _dk == '.FUNC':
                    _nm, _ps, _hdr_err = _parse_func_header(l)
                    parent = func_stack[-1] if func_stack else None
                    if _hdr_err is not None:
                        diag(_hdr_err, set_error=True)
                        _nm = None
                    elif not _is_sub_name(_nm):
                        diag(f" error - '.func' needs a name made of letters, digits "
                             f"and '_': {_nm!r}", set_error=True)
                        _nm = None
                    else:
                        for _p in _ps:
                            if not _is_sub_name(_p):
                                diag(f" error - '.func {_nm}': bad parameter name {_p!r}",
                                     set_error=True)
                                _nm = None
                                break
                    if _nm is not None:
                        _fn_obj = _MiniFunc(_nm, _ps, parent, fn, _mln)
                        target = parent.children if parent else self.funcs
                        if _nm in target:
                            diag(f" warning - function {_nm!r} is defined more than "
                                 f"once; the later definition wins.", set_error=False)
                        target[_nm] = _fn_obj
                        func_stack.append(_fn_obj)
                    else:
                        func_stack.append(_MiniFunc('?', [], parent, fn, _mln))
                    continue
                cur = func_stack[-1]
                if _dk == '.ENDFUNC':
                    if cur.depth != 0:
                        diag(f" error - '.func {cur.name}': '.endfunc' while a block "
                             f"('.if'/'.while'/'.for') is still open.", set_error=True)
                    func_stack.pop()
                    continue
                if _dk in _MINI_OPEN:
                    cur.depth += 1
                elif _dk in _MINI_CLOSE:
                    cur.depth -= 1
                    if cur.depth < 0:
                        diag(f" error - '.func::{cur.name}': {_dk.lower()} without a "
                             f"matching block opener.", set_error=True)
                        cur.depth = 0
                if l.strip():
                    cur.lines.append((l, fn, _mln))
                continue

            if _dk == '.ECHO':
                if cur_sub is not None:
                    diag(f" error - '.echo' cannot be written inside "
                         f"'.sub::{cur_sub}'.", set_error=True)
                    continue
                _args = l.strip()[5:]
                _it, _err = _echo_items_cached(_args)
                if _err is not None:
                    diag(f" error - '.echo': {_err}", set_error=True)
                w.append(['.echo', _args, '', '', '', ''])
                continue

            ww = self.include_pat(l, this_dir, _depth=_depth + 1, _chain=_chain)
            if ww is not None:
                w = w + ww
                continue
            else:
                r = []
                idx = 0
                while True:
                    s, idx = self.parser.get_params1(l, idx)
                    r += [s]
                    if len(l) <= idx:
                        break
                l = r

                _kw = StringUtils.upper(l[0].strip())
                if _kw == '.SUB':
                    _nm = (l[1] if len(l) > 1 else '').strip()
                    if cur_sub is not None:
                        diag(f" error - '.sub' inside '.sub::{cur_sub}': sub tables "
                             f"cannot be nested.", set_error=True)
                    elif not _is_sub_name(_nm):
                        diag(f" error - '.sub' needs a table name made of letters, "
                             f"digits and '_': {_nm!r}", set_error=True)
                    else:
                        if _nm in self.subs:
                            diag(f" warning - sub table {_nm!r} is defined more than "
                                 f"once; the later definition wins.", set_error=False)
                        cur_sub = _nm
                        self.subs[_nm] = []
                    continue
                if _kw == '.RETURN' or _kw == '.ENDSUB':
                    if cur_sub is None:
                        diag(f" error - '{_kw.lower()}' without a matching '.sub'.",
                             set_error=True)
                    cur_sub = None
                    continue
                if cur_sub is not None:
                    if len(l) < 2:
                        if l[0].strip() != '':
                            diag(f" error - sub table {cur_sub!r}: entry has no '::' "
                                 f"field separator: {l[0]!r}", set_error=True)
                        continue
                    self.subs[cur_sub].append((l[0], l[-1]))
                    continue

                if _kw == '.MAP':
                    var_str = l[1].strip() if len(l) > 2 else ''
                    if len(l) < 3 or var_str == '':
                        diag(" error - .map: needs '.map::<variable>::"
                             "<name,name,...>[::<expression in the variable>]'.",
                             set_error=True)
                    elif self._dir_var_name(var_str) is None:
                        diag(f" error - .map: variable should be a lower case "
                             f"name ({var_str!r}).", set_error=True)

                if len(l) == 1:
                    if l[0].strip() != '' and _kw not in ('.PASSTHRU', '.EOL',
                                                         '.TEXTMODE'):
                        diag(f" warning - pattern line has no '::' field separator "
                             f"and can never match (a pattern file has no line-"
                             f"continuation mechanism, so this is likely a stray "
                             f"line left over from a multi-line comment, or a "
                             f"binary_list/error_patterns that was continued onto "
                             f"the next physical line): {l[0]!r}", set_error=False)
                    p = [l[0], '', '', '', '', '']
                elif len(l) == 2:
                    p = [l[0], '', l[1], '', '', '']
                elif len(l) == 3:
                    p = [l[0], l[1], l[2], '', '', '']
                elif len(l) == 4:
                    p = [l[0], l[1], l[2], l[3], '', '']
                elif len(l) == 5:
                    p = [l[0], l[1], l[2], l[3], l[4], '']
                elif len(l) == 6:
                    p = [l[0], l[1], l[2], l[3], l[4], l[5]]
                else:
                    diag(f" warning - pattern line has more than 6 fields "
                         f"(extra fields ignored): {l[6:]!r}", set_error=False)
                    p = [l[0], l[1], l[2], l[3], l[4], l[5]]
                w.append(p)

        if in_block_comment:
            diag(f" warning - pattern file '{fn}' ends while a /* ... */ comment "
                 f"is still open (missing closing '*/').", set_error=False)
        if cur_sub is not None:
            diag(f" error - pattern file '{fn}' ends while sub table {cur_sub!r} "
                 f"is still open (missing '.return' or '.endsub').", set_error=True)
        while func_stack:
            _f = func_stack.pop()
            diag(f" error - pattern file '{fn}' ends while function {_f.name!r} "
                 f"is still open (missing '.endfunc').", set_error=True)

        if _depth == 0:
            self.check_sub_refs(w)
            self.compile_funcs()

        return w

    @staticmethod
    def _dir_var_name(field):
        """ディレクティブの変数名欄を読む（読み込み時用の軽い版）。"""
        v = (field or '').strip().lower()
        if not v or not v.isascii() or not ('a' <= v[0] <= 'z'):
            return None
        for ch in v[1:]:
            if not ('a' <= ch <= 'z' or ch.isdigit() or ch == '_'):
                return None
        return v

    @staticmethod
    def _map_subst_index(expr, var, i):
        """`.map` の式の中の変数を、その名前の位置 i に置き換える。

        括弧で包んで入れるので演算子の優先順位は変わらない。置き換えるのは
        変数が単語として現れた箇所だけなので、`0xff` の `x` は無事。
        """
        num = '(%d)' % i
        vl = len(var)
        out = []
        k = 0
        while k < len(expr):
            if expr[k:k + vl].lower() == var:
                prev = expr[k - 1] if k > 0 else ''
                nxt = expr[k + vl] if k + vl < len(expr) else ''
                if not (prev.isalnum() or prev == '_') and \
                   not (nxt.isalnum() or nxt == '_'):
                    out.append(num)
                    k += vl
                    continue
            out.append(expr[k])
            k += 1
        return ''.join(out)

    def compile_funcs(self):
        """集めた `.func` の本文を構文木にする（ミニ言語の構文解析）。"""
        saved_reclimit = sys.getrecursionlimit()
        if saved_reclimit < _MINI_RECLIMIT:
            sys.setrecursionlimit(_MINI_RECLIMIT)
        try:
            def walk(table):
                for f in table.values():
                    try:
                        f.body = MiniParser(f).parse_body()
                    except MiniLangError as e:
                        diag(f" error - {e}", set_error=True)
                        f.body = []
                    except RecursionError:
                        diag(f" error - {f.file}:{f.line}: '.func::{f.name}' nests "
                             f"too deeply to parse.", set_error=True)
                        f.body = []
                    walk(f.children)
            walk(self.funcs)
        finally:
            sys.setrecursionlimit(saved_reclimit)

    def check_sub_refs(self, pat):
        """`!S{{表}}` の参照が解決できるかを、読み込み時に一度だけ検査する。

        表は使用箇所より後に定義してよいので、ファイル全体を読んでから見る。
        未知の表名と循環参照をここで報告しておけば、照合中に毎行
        同じ診断が出ることはない。
        """
        def refs(t):
            out, i = [], 0
            while True:
                r = PatternMatcher._find_sub_ref(t, i)
                if r is None:
                    return out
                out.append(r[2])
                i = r[1]

        def check_unknown(where, t):
            for nm in refs(t):
                if nm not in self.subs:
                    diag(f" error - !S{{{{{nm}}}}} in {where}: no sub table named "
                         f"{nm!r} (define it with '.sub::{nm} ... .return').",
                         set_error=True)

        for p in pat:
            if p[0]:
                check_unknown('pattern', p[0])
        for nm, entries in self.subs.items():
            for ent_pat, _ in entries:
                check_unknown(f"sub table {nm!r}", ent_pat)

        mark = {}

        def walk(nm, stack):
            if mark.get(nm) == 'done':
                return
            if mark.get(nm) == 'open':
                diag(f" error - sub table {nm!r} is circular "
                     f"({' -> '.join(stack + [nm])}); expansion would not terminate.",
                     set_error=True)
                return
            mark[nm] = 'open'
            for ent_pat, _ in self.subs.get(nm, ()):
                for r in refs(ent_pat):
                    if r in self.subs:
                        walk(r, stack + [nm])
            mark[nm] = 'done'

        for nm in self.subs:
            walk(nm, [])

    def include_pat(self, l, base_dir=None, _depth=0, _chain=None):
        """`.INCLUDE` の行を処理して、読み込んだ表を返す。"""
        idx = StringUtils.skipspc(l, 0)
        i = l[idx:idx + 8]
        i = i.upper()
        if i != ".INCLUDE":
            return None
        s = StringUtils.get_string(l[idx + 8:])
        if s == "":
            raw = l[idx + 8:].strip()
            if raw:
                fallback, _ = StringUtils.get_param_to_spc(raw, 0)
                if fallback:
                    diag(f" warning - .INCLUDE filename not quoted: {fallback!r}. "
                         "Please use double quotes.", set_error=False)
                    s = fallback
                else:
                    diag(f" error - .INCLUDE directive has no filename: {l!r}", set_error=True)
                    return []
            else:
                diag(f" error - .INCLUDE directive has no filename: {l!r}", set_error=True)
                return []
        w = self.readpat(s, base_dir, _depth=_depth, _chain=_chain)
        return w


class MiniLangError(Exception):
    """ミニ言語の実行時エラー。行と桁を文言に持つ。"""
    pass


class _MiniBreak(Exception):
    """`.break` を外側のループへ伝えるための内部例外。"""

    __slots__ = ()


class _MiniContinue(Exception):
    """`.continue` を外側のループへ伝えるための内部例外。"""

    __slots__ = ()


class _MiniReturn(Exception):
    """`.return` を呼び出し元へ伝えるための内部例外。値を持つことがある。"""

    __slots__ = ('value',)

    def __init__(self, value=None):
        super().__init__()
        self.value = value


_MINI_RECLIMIT = 20000

# ミニ言語の整数は 256bit で回り込む。Python 側は多倍長なので自然には
# 回らないため、演算のたびにマスクして caxx.c と同じ結果にそろえる。
_MINI_BITS = 256
_MINI_MASK = (1 << _MINI_BITS) - 1


def _mini_wrap(v):
    """値を 256bit に丸める（符号なしの表現）。"""
    return int(v) & _MINI_MASK


def _mini_signed(v):
    """値を 256bit の符号付きとして読み直す。"""
    v = int(v) & _MINI_MASK
    return v - (1 << _MINI_BITS) if v >> (_MINI_BITS - 1) else v


# ミニ言語の字句。2 文字の演算子を 1 文字より先に試す必要がある。
_MINI_OPS2 = ('**', '<<', '>>', '<=', '>=', '==', '!=', '&&', '||')
_MINI_OPS1 = frozenset('+-*/%&|^~<>!()[]:,=')

_MINI_ESC = {'\\': '\\', '"': '"', 'n': '\n', 't': '\t'}


def _mini_lex(text, pos):
    """ミニ言語の 1 行をトークンに割る。

    返す各トークンは種類と値と位置を持ち、位置は診断にそのまま出る。
    """
    toks = []
    t = text
    i = 0
    n = len(t)
    while i < n:
        c = t[i]
        if c in ' \t':
            i += 1
            continue
        if c.isdigit():
            if c == '0' and i + 1 < n and t[i + 1] in 'xX':
                j = i + 2
                while j < n and (t[j] in '0123456789abcdefABCDEF_'):
                    j += 1
                if j == i + 2:
                    raise MiniLangError(f"{pos[0]}:{pos[1]}: malformed hex number")
                toks.append(('num', int(t[i + 2:j].replace('_', ''), 16)))
            elif c == '0' and i + 1 < n and t[i + 1] in 'bB':
                j = i + 2
                while j < n and t[j] in '01_':
                    j += 1
                if j == i + 2:
                    raise MiniLangError(f"{pos[0]}:{pos[1]}: malformed binary number")
                toks.append(('num', int(t[i + 2:j].replace('_', ''), 2)))
            else:
                j = i
                while j < n and (t[j].isdigit() or t[j] == '_'):
                    j += 1
                toks.append(('num', int(t[i:j].replace('_', ''))))
            i = j
            continue
        if c.isalpha() or c == '_':
            j = i
            while j < n and (t[j].isalnum() or t[j] == '_'):
                j += 1
            toks.append(('name', t[i:j]))
            i = j
            continue
        if c == '.':
            j = i + 1
            while j < n and (t[j].isalnum() or t[j] == '_'):
                j += 1
            if j == i + 1:
                raise MiniLangError(f"{pos[0]}:{pos[1]}: stray '.'")
            toks.append(('dot', StringUtils.upper(t[i:j])))
            i = j
            continue
        if c == '$':
            if t[i:i + 2] in ('$$', '$.'):
                toks.append(('core', t[i:i + 2]))
                i += 2
                continue
            raise MiniLangError(f"{pos[0]}:{pos[1]}: '$' must be written "
                                f"'$$' (location counter) or '$.' "
                                f"(start of the next instruction)")
        if c == '#':
            j = i + 1
            while j < n and (t[j].isalnum() or t[j] in '_.$'):
                j += 1
            if j == i + 1:
                raise MiniLangError(f"{pos[0]}:{pos[1]}: '#' needs a symbol name")
            toks.append(('core', t[i:j]))
            i = j
            continue
        if c == '"':
            j = i + 1
            buf = []
            while True:
                if j >= n:
                    raise MiniLangError(f"{pos[0]}:{pos[1]}: unterminated string")
                ch = t[j]
                if ch == '"':
                    j += 1
                    break
                if ch == '\\':
                    if j + 1 >= n:
                        raise MiniLangError(f"{pos[0]}:{pos[1]}: unterminated string")
                    e = t[j + 1]
                    if e not in _MINI_ESC:
                        raise MiniLangError(f"{pos[0]}:{pos[1]}: unknown escape "
                                            f"'\\{e}' in a string")
                    buf.append(_MINI_ESC[e])
                    j += 2
                    continue
                buf.append(ch)
                j += 1
            toks.append(('str', ''.join(buf)))
            i = j
            continue
        if t[i:i + 2] in _MINI_OPS2:
            toks.append(('op', t[i:i + 2]))
            i += 2
            continue
        if c in _MINI_OPS1:
            toks.append(('op', c))
            i += 1
            continue
        raise MiniLangError(f"{pos[0]}:{pos[1]}: unexpected character {c!r}")
    return toks


class _MiniExprParser:
    """ミニ言語の式を構文木にする。優先順位ごとに 1 メソッドの再帰下降。

    演算子は C に倣う（本体の式評価器とは `%` の符号などが違う）。
    構文木を作るだけで、評価は MiniInterp が行う。
    """

    def __init__(self, toks, pos):
        self.toks = toks
        self.i = 0
        self.pos = pos

    def fail(self, msg):
        """現在位置を添えて構文エラーにする。"""
        raise MiniLangError(f"{self.pos[0]}:{self.pos[1]}: {msg}")

    def peek(self):
        """次のトークンを消費せずに見る。"""
        return self.toks[self.i] if self.i < len(self.toks) else ('end', None)

    def at_op(self, *ops):
        """次がこれらの演算子のどれかか。"""
        k, v = self.peek()
        return k == 'op' and v in ops

    def eat_op(self, op):
        """次がその演算子なら消費して真。"""
        if self.at_op(op):
            self.i += 1
            return True
        return False

    def expect_op(self, op):
        """その演算子を必ず 1 つ消費する。無ければ構文エラー。"""
        if not self.eat_op(op):
            k, v = self.peek()
            self.fail(f"expected {op!r}, found {v if k != 'end' else 'end of line'!r}")

    def at_end(self):
        """トークンを読み切ったか。"""
        return self.i >= len(self.toks)

    def parse(self):
        """式を 1 個解析する。優先順位の一番上から入る。"""
        e = self.or_()
        if not self.at_end():
            k, v = self.peek()
            self.fail(f"unexpected {v!r} in expression")
        return e

    def or_(self):
        """`||`。"""
        e = self.and_()
        while self.at_op('||'):
            self.i += 1
            e = ('bin', '||', e, self.and_())
        return e

    def and_(self):
        """`&&`。"""
        e = self.not_()
        while self.at_op('&&'):
            self.i += 1
            e = ('bin', '&&', e, self.not_())
        return e

    def not_(self):
        """単項 `!`。"""
        if self.at_op('!'):
            self.i += 1
            return ('un', '!', self.not_())
        return self.cmp_()

    def cmp_(self):
        """比較 `== != < <= > >=`。"""
        e = self.bitor_()
        while self.at_op('==', '!=', '<=', '>=', '<', '>'):
            op = self.peek()[1]
            self.i += 1
            e = ('bin', op, e, self.bitor_())
        return e

    def bitor_(self):
        """`|`。"""
        e = self.bitxor_()
        while self.at_op('|'):
            self.i += 1
            e = ('bin', '|', e, self.bitxor_())
        return e

    def bitxor_(self):
        """`^`。"""
        e = self.bitand_()
        while self.at_op('^'):
            self.i += 1
            e = ('bin', '^', e, self.bitand_())
        return e

    def bitand_(self):
        """`&`。"""
        e = self.shift_()
        while self.at_op('&'):
            self.i += 1
            e = ('bin', '&', e, self.shift_())
        return e

    def shift_(self):
        """`<<` `>>`。"""
        e = self.add_()
        while self.at_op('<<', '>>'):
            op = self.peek()[1]
            self.i += 1
            e = ('bin', op, e, self.add_())
        return e

    def add_(self):
        """`+` `-`。"""
        e = self.mul_()
        while self.at_op('+', '-'):
            op = self.peek()[1]
            self.i += 1
            e = ('bin', op, e, self.mul_())
        return e

    def mul_(self):
        """`*` `/` `%`。"""
        e = self.unary_()
        while self.at_op('*', '/', '%'):
            op = self.peek()[1]
            self.i += 1
            e = ('bin', op, e, self.unary_())
        return e

    def unary_(self):
        """単項 `-` `+` `~`。"""
        if self.at_op('-', '+', '~'):
            op = self.peek()[1]
            self.i += 1
            return ('un', op, self.unary_())
        return self.power_()

    def power_(self):
        """`**`。"""
        e = self.postfix_()
        if self.at_op('**'):
            self.i += 1
            return ('bin', '**', e, self.unary_())
        return e

    def postfix_(self):
        """後置の添字 `名前[式]`。"""
        e = self.primary_()
        while self.at_op('['):
            self.i += 1
            lo = None if self.at_op(':') else self.or_()
            if self.eat_op(':'):
                hi = None if self.at_op(']') else self.or_()
                self.expect_op(']')
                e = ('slice', e, lo, hi)
            else:
                self.expect_op(']')
                if lo is None:
                    self.fail("empty subscript")
                e = ('index', e, lo)
        return e

    def primary_(self):
        """項そのもの。数値、名前、`(式)`、配列リテラル、`.call`、組み込み。"""
        k, v = self.peek()
        if k == 'str':
            self.fail("a string can only be used in '.echo'")
        if k == 'core':
            self.i += 1
            return ('core', v)
        if k == 'num':
            self.i += 1
            return ('num', _mini_wrap(v))
        if k == 'name':
            self.i += 1
            return ('var', v)
        if k == 'dot':
            if v == '.LEN':
                self.i += 1
                self.expect_op('(')
                e = self.or_()
                self.expect_op(')')
                return ('len', e)
            if v == '.CALL':
                self.i += 1
                k2, v2 = self.peek()
                if k2 != 'name':
                    self.fail("'.call' needs a function name")
                self.i += 1
                self.expect_op('(')
                args = []
                if not self.at_op(')'):
                    args.append(self.or_())
                    while self.eat_op(','):
                        args.append(self.or_())
                self.expect_op(')')
                return ('callexpr', v2, args)
            self.fail(f"{v.lower()!r} cannot be used in an expression")
        if k == 'op' and v == '(':
            self.i += 1
            e = self.or_()
            self.expect_op(')')
            return e
        if k == 'op' and v == '[':
            self.i += 1
            items = []
            if not self.at_op(']'):
                items.append(self.or_())
                while self.eat_op(','):
                    items.append(self.or_())
            self.expect_op(']')
            return ('arr', items)
        self.fail(f"expected a value, found {v if k != 'end' else 'end of line'!r}")

    def parse_list(self):
        """カンマ区切りの式の並びを解析する（引数と配列リテラル）。"""
        items = []
        if self.at_end():
            return items
        items.append(self.or_())
        while self.eat_op(','):
            items.append(self.or_())
        if not self.at_end():
            k, v = self.peek()
            self.fail(f"unexpected {v!r} after expression list")
        return items


class MiniParser:
    """`.func` の本文を文の構文木にする。

    `.if` / `.elif` / `.else` / `.endif`、`.while` / `.endwhile`、`.for` / `.next`
    の対応をここで取る。入れ子は行の並びから数える（字下げは見ない）。
    """

    _ENDERS = frozenset(('.ELIF', '.ELSE', '.ENDIF', '.NEXT', '.ENDWHILE'))

    def __init__(self, func):
        self.func = func
        self.lines = func.lines
        self.loopdepth = 0

    def parse_body(self):
        """関数本体を丸ごと解析する。"""
        body, i = self._block(0, ())
        if i < len(self.lines):
            text, f, ln = self.lines[i]
            raise MiniLangError(f"{f}:{ln}: '{text.strip()}' has no matching opener")
        return body

    def _block(self, i, enders):
        """enders のどれかが現れるまでを 1 ブロックとして解析する。"""
        out = []
        while i < len(self.lines):
            text, f, ln = self.lines[i]
            pos = (f, ln)
            kw = _dot_kw(text)
            if kw in enders:
                return out, i
            if kw in self._ENDERS:
                raise MiniLangError(f"{f}:{ln}: '{kw.lower()}' without a matching opener")
            if kw == '.IF':
                node, i = self._if_chain(i)
                out.append(node)
                i += 1
                continue
            if kw == '.WHILE':
                toks = _mini_lex(text, pos)
                cond = _MiniExprParser(toks[1:], pos).parse()
                self.loopdepth += 1
                body, i = self._block(i + 1, ('.ENDWHILE',))
                self.loopdepth -= 1
                if i >= len(self.lines):
                    raise MiniLangError(f"{f}:{ln}: '.while' is never closed with '.endwhile'")
                out.append(('while', cond, body, pos))
                i += 1
                continue
            if kw == '.FOR':
                var, args = self._for_header(text, pos)
                self.loopdepth += 1
                body, i = self._block(i + 1, ('.NEXT',))
                self.loopdepth -= 1
                if i >= len(self.lines):
                    raise MiniLangError(f"{f}:{ln}: '.for' is never closed with '.next'")
                out.append(('for', var, args, body, pos))
                i += 1
                continue
            out.append(self._simple(text, pos))
            i += 1
        return out, i

    def _if_chain(self, i):
        """`.if` / `.elif` / `.else` / `.endif` の連なりを解析する。"""
        text, f, ln = self.lines[i]
        pos = (f, ln)
        kw = _dot_kw(text)
        toks = _mini_lex(text, pos)
        if not toks or toks[-1] != ('dot', '.THEN'):
            raise MiniLangError(f"{f}:{ln}: '{kw.lower()}' must end with '.then'")
        cond = _MiniExprParser(toks[1:-1], pos).parse()
        then_b, i = self._block(i + 1, ('.ELIF', '.ELSE', '.ENDIF'))
        if i >= len(self.lines):
            raise MiniLangError(f"{f}:{ln}: '.if' is never closed with '.endif'")
        else_b = []
        nkw = _dot_kw(self.lines[i][0])
        if nkw == '.ELIF':
            node, i = self._if_chain(i)
            else_b = [node]
        elif nkw == '.ELSE':
            epos = (self.lines[i][1], self.lines[i][2])
            rest = _mini_lex(self.lines[i][0], epos)[1:]
            if rest:
                raise MiniLangError(f"{epos[0]}:{epos[1]}: unexpected text after '.else'")
            else_b, i = self._block(i + 1, ('.ENDIF',))
            if i >= len(self.lines):
                raise MiniLangError(f"{f}:{ln}: '.if' is never closed with '.endif'")
        return ('if', cond, then_b, else_b, pos), i

    def _for_header(self, text, pos):
        """`.for` のヘッダ（変数と範囲）を解析する。"""
        toks = _mini_lex(text, pos)
        f, ln = pos
        if len(toks) < 4 or toks[1][0] != 'name':
            raise MiniLangError(f"{f}:{ln}: '.for' needs 'variable in range(...)'")
        var = toks[1][1]
        if toks[2] != ('name', 'in') or toks[3] != ('name', 'range'):
            raise MiniLangError(f"{f}:{ln}: '.for {var}' must be followed by 'in range(...)'")
        p = _MiniExprParser(toks[4:], pos)
        p.expect_op('(')
        args = []
        if not p.at_op(')'):
            args.append(p.or_())
            while p.eat_op(','):
                args.append(p.or_())
        p.expect_op(')')
        if not p.at_end():
            raise MiniLangError(f"{f}:{ln}: unexpected text after 'range(...)'")
        if not 1 <= len(args) <= 3:
            raise MiniLangError(f"{f}:{ln}: range() takes 1 to 3 arguments, got {len(args)}")
        return var, args

    def _simple(self, text, pos):
        """単純文 1 個を解析する。代入、`.emit`、`.echo`、`.raise`、`.return` など。"""
        f, ln = pos
        toks = _mini_lex(text, pos)
        if not toks:
            raise MiniLangError(f"{f}:{ln}: empty statement")
        k, v = toks[0]
        if k == 'dot':
            if v == '.RETURN':
                if len(toks) > 1:
                    return ('return', _MiniExprParser(toks[1:], pos).parse(), pos)
                return ('return', None, pos)
            if v == '.RAISE':
                if len(toks) <= 1:
                    raise MiniLangError(f"{f}:{ln}: '.raise' needs an error code")
                return ('raise', _MiniExprParser(toks[1:], pos).parse(), pos)
            if v == '.EMIT':
                p = _MiniExprParser(toks[1:], pos)
                p.expect_op('(')
                args = []
                if not p.at_op(')'):
                    args.append(p.or_())
                    while p.eat_op(','):
                        args.append(p.or_())
                p.expect_op(')')
                if not p.at_end():
                    raise MiniLangError(f"{f}:{ln}: unexpected text after '.emit(...)'")
                if not args:
                    raise MiniLangError(f"{f}:{ln}: '.emit' needs at least one value")
                return ('emit', args, pos)
            if v == '.ECHO':
                p = _MiniExprParser(toks[1:], pos)
                p.expect_op('(')
                items = []
                if not p.at_op(')'):
                    while True:
                        k2, v2 = p.peek()
                        if k2 == 'str':
                            p.i += 1
                            items.append(('s', v2))
                        else:
                            items.append(('e', p.or_()))
                        if not p.eat_op(','):
                            break
                p.expect_op(')')
                if not p.at_end():
                    raise MiniLangError(f"{f}:{ln}: unexpected text after '.echo(...)'")
                return ('echo', items, pos)
            if v in ('.BREAK', '.CONTINUE'):
                low = v.lower()
                if len(toks) != 1:
                    raise MiniLangError(f"{f}:{ln}: unexpected text after '{low}'")
                if self.loopdepth <= 0:
                    raise MiniLangError(f"{f}:{ln}: '{low}' must be inside a "
                                        f"'.while' or '.for' loop")
                return (low[1:], pos)
            if v == '.CALL':
                name, args = self._call_tail(toks, pos)
                return ('call', name, args, pos)
            if v == '.NONLOCAL':
                names = []
                j = 1
                while j < len(toks):
                    if toks[j][0] != 'name':
                        raise MiniLangError(f"{f}:{ln}: '.nonlocal' needs variable names")
                    names.append(toks[j][1])
                    j += 1
                    if j < len(toks):
                        if toks[j] != ('op', ','):
                            raise MiniLangError(f"{f}:{ln}: '.nonlocal' names must be "
                                                f"separated by ','")
                        j += 1
                if not names:
                    raise MiniLangError(f"{f}:{ln}: '.nonlocal' needs variable names")
                return ('nonlocal', names, pos)
            raise MiniLangError(f"{f}:{ln}: unknown statement {v.lower()!r}")
        if k != 'name':
            raise MiniLangError(f"{f}:{ln}: statement must be a directive or an assignment")
        name = v
        p = _MiniExprParser(toks[1:], pos)
        idx = None
        if p.at_op('['):
            p.i += 1
            idx = p.or_()
            p.expect_op(']')
        p.expect_op('=')
        rest = p.toks[p.i:]
        if rest and rest[0] == ('dot', '.CALL'):
            fname, args = self._call_tail(rest, pos)
            return ('callassign', name, idx, fname, args, pos)
        val = _MiniExprParser(rest, pos).parse()
        return ('assign', name, idx, val, pos)

    def _call_tail(self, toks, pos):
        """`.call 名前(引数, ...)` の引数部を解析する。"""
        f, ln = pos
        if len(toks) < 2 or toks[1][0] != 'name':
            raise MiniLangError(f"{f}:{ln}: '.call' needs a function name")
        name = toks[1][1]
        p = _MiniExprParser(toks[2:], pos)
        p.expect_op('(')
        args = []
        if not p.at_op(')'):
            args.append(p.or_())
            while p.eat_op(','):
                args.append(p.or_())
        p.expect_op(')')
        if not p.at_end():
            raise MiniLangError(f"{f}:{ln}: unexpected text after '.call'")
        return name, args


class MiniInterp:
    """ミニ言語の評価器。`.call` から呼ばれて出力ワードを作る。

    この言語はチューリング完全なので、バグのあるパターンファイルが
    そのままではアセンブラを止められなくしてしまう。4 つの上限がそれを防ぎ、
    代わりに問題の行を報告する。未定義ラベルから来た引数は 0 として渡るので、
    前方参照が最初のパスでループ回数を吹き飛ばすこともない。
    パターン変数はここでは使えない（`.func` 本体の実行中はそれを束縛して
    いるものが無い）。必要なら `.call` の引数として渡す。
    """

    # 1 回の `.call` で実行する文の数、呼び出しの入れ子、出力ワード数、
    # 配列長の上限。超えたらその行をエラーにして止める。
    MAX_STEPS = 4_000_000
    MAX_DEPTH = 128
    MAX_EMIT = 1 << 20
    MAX_ARRAY = 1 << 20

    def __init__(self, state, expr_eval=None):
        self.state = state
        self.expr_eval = expr_eval
        self.out = []
        self.steps = 0
        self.frames = []

    @staticmethod
    def _is_arr(v):
        """値が配列か。"""
        return isinstance(v, list)

    @classmethod
    def _echo_value(cls, v):
        """`.echo` に出す形に整える。"""
        if cls._is_arr(v):
            return [_mini_signed(e) for e in v]
        return _mini_signed(v)

    def _need_int(self, v, pos, what):
        """整数を要求する。配列が来たらエラーにする。"""
        if self._is_arr(v):
            raise MiniLangError(f"{pos[0]}:{pos[1]}: {what} must be a number, not an array")
        return _mini_wrap(v)

    def _frame_for(self, name):
        """その名前を持つスコープを探す。`.nonlocal` なら外側へたどる。"""
        top = self.frames[-1]
        if name not in top['nonlocal']:
            return top
        for fr in reversed(self.frames[:-1]):
            if name in fr['vars']:
                return fr
        return None

    def _core_eval(self, text, pos):
        """本体の式評価器に委譲する（ラベル・`$$`・`#記号` を読むため）。

        未定義ラベル由来の値は 0 にする。巨大な番兵をミニ言語の演算へ
        流し込まないため。
        """
        if self.expr_eval is None:
            raise MiniLangError(f"{pos[0]}:{pos[1]}: {text!r} is not available here")
        v, _ = self.expr_eval.expression_caps(text, 0, CAPS_MINI)
        if _is_undef_derived(v):
            return 0
        return _mini_wrap(v)

    def _core_name(self, name):
        """その名前が、本体側（ラベル・シンボル・前回の反復の値）にあるか。"""
        st = self.state
        if st is None:
            return False
        if name in st.labels:
            return True
        if StringUtils.upper(name) in st.symbols:
            return True
        return name in st._relax_prev_values

    def _get(self, name, pos):
        """変数を読む。無ければ本体側の名前として解決を試みる。

        パス2で本体側にも無い名前は「設定前に使われた」エラーにする。
        パス1ではまだ値が無いのが普通なので、そこでは通す。
        """
        fr = self._frame_for(name)
        if fr is None:
            raise MiniLangError(f"{pos[0]}:{pos[1]}: '.nonlocal {name}' found no "
                                f"enclosing definition of {name!r}")
        if name not in fr['vars']:
            if self.expr_eval is not None and self.state is not None \
                    and (self._core_name(name) or self.state.pas != 2):
                return self._core_eval(name, pos)
            raise MiniLangError(f"{pos[0]}:{pos[1]}: {name!r} is used before it is set")
        return fr['vars'][name]

    def _set(self, name, value, pos):
        """変数へ代入する。"""
        fr = self._frame_for(name)
        if fr is None:
            raise MiniLangError(f"{pos[0]}:{pos[1]}: '.nonlocal {name}' found no "
                                f"enclosing definition of {name!r}")
        fr['vars'][name] = value

    def eval(self, e, pos):
        """式の構文木を評価する。"""
        k = e[0]
        if k == 'num':
            return e[1]
        if k == 'core':
            return self._core_eval(e[1], pos)
        if k == 'var':
            return self._get(e[1], pos)
        if k == 'arr':
            return [self._need_int(self.eval(x, pos), pos, 'an array element')
                    for x in e[1]]
        if k == 'callexpr':
            fn = self._lookup(e[1], pos)
            vals = [self.eval(a, pos) for a in e[2]]
            ret = self.call(fn, vals, pos)
            if ret is None:
                raise MiniLangError(f"{pos[0]}:{pos[1]}: {e[1]!r} returned no value; "
                                    f"give it a '.return <expression>'")
            return ret
        if k == 'len':
            v = self.eval(e[1], pos)
            if not self._is_arr(v):
                raise MiniLangError(f"{pos[0]}:{pos[1]}: '.len' needs an array")
            return _mini_wrap(len(v))
        if k == 'index':
            base = self.eval(e[1], pos)
            idx = _mini_signed(self._need_int(self.eval(e[2], pos), pos, 'an index'))
            if not self._is_arr(base):
                raise MiniLangError(f"{pos[0]}:{pos[1]}: only an array can be indexed")
            if idx < 0 or idx >= len(base):
                return 0
            return base[idx]
        if k == 'slice':
            base = self.eval(e[1], pos)
            if not self._is_arr(base):
                raise MiniLangError(f"{pos[0]}:{pos[1]}: only an array can be sliced")
            n = len(base)
            lo = 0 if e[2] is None else _mini_signed(
                self._need_int(self.eval(e[2], pos), pos, 'a slice bound'))
            hi = n if e[3] is None else _mini_signed(
                self._need_int(self.eval(e[3], pos), pos, 'a slice bound'))
            lo = max(0, min(lo, n))
            hi = max(lo, min(hi, n))
            return base[lo:hi]
        if k == 'un':
            op = e[1]
            v = self._need_int(self.eval(e[2], pos), pos, 'an operand')
            if op == '-':
                return _mini_wrap(-_mini_signed(v))
            if op == '+':
                return v
            if op == '~':
                return _mini_wrap(~v)
            return 1 if _mini_signed(v) == 0 else 0
        if k == 'bin':
            return self._binop(e, pos)
        raise MiniLangError(f"{pos[0]}:{pos[1]}: bad expression")

    def _binop(self, e, pos):
        """二項演算を評価する。`/` と `%` は C と同じゼロ方向の切り捨て。"""
        op = e[1]
        if op == '&&':
            if _mini_signed(self._need_int(self.eval(e[2], pos), pos, 'an operand')) == 0:
                return 0
            return 1 if _mini_signed(
                self._need_int(self.eval(e[3], pos), pos, 'an operand')) != 0 else 0
        if op == '||':
            if _mini_signed(self._need_int(self.eval(e[2], pos), pos, 'an operand')) != 0:
                return 1
            return 1 if _mini_signed(
                self._need_int(self.eval(e[3], pos), pos, 'an operand')) != 0 else 0
        a = self._need_int(self.eval(e[2], pos), pos, 'an operand')
        b = self._need_int(self.eval(e[3], pos), pos, 'an operand')
        sa, sb = _mini_signed(a), _mini_signed(b)
        if op == '+':
            return _mini_wrap(sa + sb)
        if op == '-':
            return _mini_wrap(sa - sb)
        if op == '*':
            return _mini_wrap(sa * sb)
        if op == '/':
            if sb == 0:
                raise MiniLangError(f"{pos[0]}:{pos[1]}: division by zero")
            q = abs(sa) // abs(sb)
            return _mini_wrap(-q if (sa < 0) != (sb < 0) else q)
        if op == '%':
            if sb == 0:
                raise MiniLangError(f"{pos[0]}:{pos[1]}: division by zero")
            r = abs(sa) % abs(sb)
            return _mini_wrap(-r if sa < 0 else r)
        if op == '**':
            if sb < 0:
                raise MiniLangError(f"{pos[0]}:{pos[1]}: negative exponent")
            return _mini_wrap(pow(sa, sb, 1 << _MINI_BITS))
        if op == '<<':
            if sb < 0 or sb >= _MINI_BITS:
                return 0
            return _mini_wrap(a << sb)
        if op == '>>':
            if sb < 0:
                return 0
            if sb >= _MINI_BITS:
                return _mini_wrap(-1) if sa < 0 else 0
            return _mini_wrap(sa >> sb)
        if op == '&':
            return a & b
        if op == '|':
            return a | b
        if op == '^':
            return a ^ b
        if op == '<':
            return 1 if sa < sb else 0
        if op == '>':
            return 1 if sa > sb else 0
        if op == '<=':
            return 1 if sa <= sb else 0
        if op == '>=':
            return 1 if sa >= sb else 0
        if op == '==':
            return 1 if sa == sb else 0
        return 1 if sa != sb else 0

    def _store(self, name, idx, v, pos):
        """変数か配列要素へ代入する。配列は必要なら伸ばす（上限あり）。"""
        if idx is None:
            self._set(name, list(v) if self._is_arr(v) else _mini_wrap(v), pos)
            return
        i = _mini_signed(self._need_int(self.eval(idx, pos), pos, 'an index'))
        if i < 0:
            raise MiniLangError(f"{pos[0]}:{pos[1]}: negative index {i} in assignment")
        if i >= self.MAX_ARRAY:
            raise MiniLangError(f"{pos[0]}:{pos[1]}: array index {i} exceeds the "
                                f"maximum length {self.MAX_ARRAY}")
        arr = self._get(name, pos)
        if not self._is_arr(arr):
            raise MiniLangError(f"{pos[0]}:{pos[1]}: {name!r} is not an array")
        if i >= len(arr):
            arr.extend([0] * (i + 1 - len(arr)))
        arr[i] = self._need_int(v, pos, 'an array element')

    def _tick(self, pos):
        """実行した文を 1 つ数える。上限を超えたらエラーにする。"""
        self.steps += 1
        if self.steps > self.MAX_STEPS:
            raise MiniLangError(f"{pos[0]}:{pos[1]}: mini language ran more than "
                                f"{self.MAX_STEPS} statements; assuming a runaway loop")

    def exec_block(self, body):
        """文の並びを順に実行する。"""
        for st in body:
            self._exec(st)

    def _exec(self, st):
        """文 1 個を実行する。"""
        kind = st[0]
        pos = st[-1]
        self._tick(pos)
        if kind == 'assign':
            _, name, idx, val, _ = st
            self._store(name, idx, self.eval(val, pos), pos)
            return
        if kind == 'callassign':
            _, name, idx, fname, args, _ = st
            fn = self._lookup(fname, pos)
            vals = [self.eval(a, pos) for a in args]
            ret = self.call(fn, vals, pos)
            if ret is None:
                raise MiniLangError(f"{pos[0]}:{pos[1]}: {fname!r} returned no value; "
                                    f"give it a '.return <expression>'")
            self._store(name, idx, ret, pos)
            return
        if kind == 'emit':
            for x in st[1]:
                v = self.eval(x, pos)
                if self._is_arr(v):
                    raise MiniLangError(f"{pos[0]}:{pos[1]}: '.emit' needs numbers, "
                                        f"not an array")
                if len(self.out) >= self.MAX_EMIT:
                    raise MiniLangError(f"{pos[0]}:{pos[1]}: '.emit' produced more than "
                                        f"{self.MAX_EMIT} words")
                self.out.append(v)
            return
        if kind == 'raise':
            v = self.eval(st[1], pos)
            if self._is_arr(v):
                raise MiniLangError(f"{pos[0]}:{pos[1]}: '.raise' needs a number, "
                                    f"not an array")
            if (self.state is not None
                    and self.state.should_report_errors()
                    and not self.state._pass1_size_mode):
                _lo = int(v) & 0xFFFFFFFFFFFFFFFF
                code = _lo - (1 << 64) if _lo >> 63 else _lo
                print(f"Line {self.state.ln} Error code {code} ", end="",
                      file=sys.stderr)
                if 0 <= code < len(self.state.errors):
                    print(f"{self.state.errors[code]}", end='', file=sys.stderr)
                print(": ", file=sys.stderr)
                self.state.had_error = True
            return
        if kind == 'echo':
            parts = [x if k2 == 's' else self._echo_value(self.eval(x, pos))
                     for k2, x in st[1]]
            if (self.state is not None
                    and self.state.should_report_errors()
                    and not self.state._pass1_size_mode):
                _echo_write(parts)
            return
        if kind == 'call':
            _, name, args, _ = st
            fn = self._lookup(name, pos)
            vals = [self.eval(a, pos) for a in args]
            self.call(fn, vals, pos)
            return
        if kind == 'break':
            raise _MiniBreak()
        if kind == 'continue':
            raise _MiniContinue()
        if kind == 'return':
            raise _MiniReturn(None if st[1] is None else self.eval(st[1], pos))
        if kind == 'nonlocal':
            top = self.frames[-1]
            for nm in st[1]:
                if nm in top['vars']:
                    raise MiniLangError(f"{pos[0]}:{pos[1]}: {nm!r} is already local; "
                                        f"'.nonlocal' must come before it is set")
                top['nonlocal'].add(nm)
            return
        if kind == 'if':
            _, cond, then_b, else_b, _ = st
            if _mini_signed(self._need_int(self.eval(cond, pos), pos, 'a condition')) != 0:
                self.exec_block(then_b)
            else:
                self.exec_block(else_b)
            return
        if kind == 'while':
            _, cond, body, _ = st
            while _mini_signed(
                    self._need_int(self.eval(cond, pos), pos, 'a condition')) != 0:
                self._tick(pos)
                try:
                    self.exec_block(body)
                except _MiniContinue:
                    pass
                except _MiniBreak:
                    break
            return
        if kind == 'for':
            _, var, args, body, _ = st
            vs = [_mini_signed(self._need_int(self.eval(a, pos), pos, 'a range bound'))
                  for a in args]
            if len(vs) == 1:
                start, stop, step = 0, vs[0], 1
            elif len(vs) == 2:
                start, stop, step = vs[0], vs[1], 1
            else:
                start, stop, step = vs
            if step == 0:
                raise MiniLangError(f"{pos[0]}:{pos[1]}: range() step must not be zero")
            i = start
            while (i < stop) if step > 0 else (i > stop):
                self._tick(pos)
                self._set(var, _mini_wrap(i), pos)
                try:
                    self.exec_block(body)
                except _MiniContinue:
                    pass
                except _MiniBreak:
                    break
                i += step
            return
        raise MiniLangError(f"{pos[0]}:{pos[1]}: bad statement")

    def _lookup(self, name, pos):
        """呼び出す関数を名前で探す。内側の定義から外側へたどる。"""
        fn = self.frames[-1]['func'] if self.frames else None
        while fn is not None:
            if name in fn.children:
                return fn.children[name]
            fn = fn.parent
        fn = self.state.func_defs.get(name)
        if fn is None:
            raise MiniLangError(f"{pos[0]}:{pos[1]}: no function named {name!r}")
        return fn

    def call(self, func, args, pos):
        """関数を 1 回呼ぶ。新しいスコープを積み、入れ子の深さを検査する。"""
        if len(self.frames) >= self.MAX_DEPTH:
            raise MiniLangError(f"{pos[0]}:{pos[1]}: call nesting deeper than "
                                f"{self.MAX_DEPTH}; assuming runaway recursion")
        if len(args) != len(func.params):
            raise MiniLangError(f"{pos[0]}:{pos[1]}: {func.name!r} takes "
                                f"{len(func.params)} argument(s), got {len(args)}")
        frame = {'vars': {}, 'nonlocal': set(), 'func': func}
        for nm, v in zip(func.params, args):
            frame['vars'][nm] = list(v) if self._is_arr(v) else _mini_wrap(v)
        self.frames.append(frame)
        ret = None
        try:
            self.exec_block(func.body or [])
        except _MiniReturn as r:
            ret = r.value
        finally:
            self.frames.pop()
        return ret

    def run(self, func, args, pos):
        """`.call` の入口。関数を走らせ、出力ワードの並びを返す。"""
        self.out = []
        self.steps = 0
        self.frames = []
        ret = self.call(func, args, pos)
        return self.out, ret


_TXT_ESCAPES = {'n': '\n', 't': '\t', 'r': '\r', '\\': '\\', '"': '"'}

_ASMTEXT_SHOW = {'\n': '\\n', '\t': '\\t', '\r': '\\r', '\\': '\\\\', '"': '\\"'}


def asmtext_escaped(s):
    """テキストを 1 行の診断に収まる形にエスケープする（改行を `\\n` に）。"""
    return ''.join(_ASMTEXT_SHOW.get(c, c) for c in s)


class ObjectGenerator:
    """`binary_list`（出力欄）から、その行のワード列を作る。

    欄の要素はカンマ区切りで、数値式のほか、文字列テンプレート `"..."`、
    繰り返し `@@[n,...]`、ミニ言語の呼び出し `.call f(...)` が書ける。
    要素の頭の `;` はその値が 0 なら出力を抑え、`;;` は評価だけして捨てる。
    空要素はアラインメントになる。
    """

    def __init__(self, state, expr_eval, binary_writer):
        self.state = state
        self.expr_eval = expr_eval
        self.binary_writer = binary_writer

    def replace_percent_with_index(self, s):
        """`%%` を繰り返しインデックスの値に、`%0` をその 0 復帰に置き換える。

        文字列リテラルの中は触らない。
        """
        count = 0
        result = []
        i = 0
        while i < len(s):
            if s[i] == '"':
                result.append(s[i])
                i += 1
                while i < len(s):
                    if s[i] == '\\' and i + 1 < len(s):
                        result.append(s[i:i + 2]); i += 2; continue
                    ch = s[i]
                    result.append(ch); i += 1
                    if ch == '"':
                        break
                continue
            if i + 1 < len(s) and s[i:i + 2] == '%%':
                result.append(str(count))
                count += 1
                i += 2
            elif i + 1 < len(s) and s[i:i + 2] == "%0":
                count = 0
                i += 2
            else:
                result.append(s[i])
                i += 1
        return ''.join(result)

    def e_p(self, pattern):
        """`@@[n, 中身]` の繰り返しを展開する。返り値は (展開後, 失敗したか)。

        入れ子と文字列リテラルを数えながら対応する `]` を探す。
        """
        result = []
        has_content = False
        i = 0
        while i < len(pattern):
            if i + 3 <= len(pattern) and pattern[i:i + 3] == '@@[':
                i += 3
                depth = 1
                expr_start = i
                comma_pos = -1

                while i < len(pattern) and depth > 0:
                    if pattern[i] == '"':
                        i += 1
                        while i < len(pattern):
                            if pattern[i] == '\\' and i + 1 < len(pattern):
                                i += 2; continue
                            if pattern[i] == '"':
                                i += 1; break
                            i += 1
                        continue
                    if pattern[i] == '[':
                        depth += 1
                    elif pattern[i] == ']':
                        depth -= 1
                        if depth == 0:
                            break
                    elif pattern[i] == ',' and depth == 1 and comma_pos == -1:
                        comma_pos = i
                    i += 1

                if comma_pos >= 0 and comma_pos >= expr_start:
                    expr = pattern[expr_start:comma_pos]
                    rep_pattern = pattern[comma_pos + 1:i]

                    _rep_prior = self.state.error_undefined_label
                    self.state.error_undefined_label = False
                    n, idx = self.expr_eval.expression_pat(expr, 0)
                    _rep_undef = self.state.error_undefined_label
                    self.state.error_undefined_label = _rep_prior or _rep_undef
                    _N_MAX = 1 << 24
                    if _rep_undef or _is_undef_derived(n):
                        n = 0
                    try:
                        n_int = int(n)
                    except (ValueError, OverflowError):
                        n_int = 0
                    if n_int > _N_MAX:
                        self.state.diag(f" error - @@[n,...]: repeat count {n_int} exceeds maximum {_N_MAX}.", set_error=True)
                        n_int = 0
                    if n_int > 0:
                        n = n_int
                        has_content = True
                        expanded_rep, _ = self.e_p(rep_pattern)
                        for j in range(int(n)):
                            if j > 0:
                                result.append(',')
                            result.append(expanded_rep)

                    i += 1
                else:
                    self.state.diag(" error - @@[...]: missing ',' separating count and pattern.", set_error=True)
                    result.append('@@[')
                    has_content = True
            elif pattern[i] == '"':
                result.append(pattern[i]); i += 1
                has_content = True
                while i < len(pattern):
                    if pattern[i] == '\\' and i + 1 < len(pattern):
                        result.append(pattern[i:i + 2]); i += 2; continue
                    ch = pattern[i]
                    result.append(ch); i += 1
                    if ch == '"':
                        break
            else:
                result.append(pattern[i])
                has_content = True
                i += 1

        return ''.join(result), not has_content

    def _mini_diag(self, msg):
        """ミニ言語からのエラーを診断として出す。"""
        if not self.state._pass1_size_mode:
            self.state.diag(msg, set_error=True)

    def mini_call(self, s, idx):
        """`.call 名前(引数, ...)` を実行し、生まれたワード列を返す。

        引数は呼び出し側（パターン行）の式なので、ここでパターン変数が
        解決されてから関数へ渡る。関数の内側ではそれが引数になる。
        """
        idx += 5
        idx = StringUtils.skipspc(s, idx)
        j = idx
        while j < len(s) and s[j] in _SYM_CORE:
            j += 1
        name = s[idx:j]
        idx = StringUtils.skipspc(s, j)
        if not name or idx >= len(s) or s[idx] != '(':
            self._mini_diag(" error - '.call' needs 'name(argument, ...)'.")
            return [], len(s)
        depth = 0
        k = idx
        while k < len(s) and s[k] != chr(0):
            if s[k] in '([':
                depth += 1
            elif s[k] in ')]':
                depth -= 1
                if depth == 0:
                    break
            k += 1
        if depth != 0 or k >= len(s):
            self._mini_diag(f" error - '.call {name}': unbalanced parentheses.")
            return [], len(s)
        arg_text = s[idx + 1:k]
        idx = k + 1

        fn = self.state.func_defs.get(name)
        if fn is None:
            self._mini_diag(f" error - '.call': no function named {name!r} "
                            f"(define it with '.func::{name}:: ... .endfunc').")
            return [], idx

        args = []
        a = 0
        arg_text_z = arg_text + chr(0)
        while True:
            a = StringUtils.skipspc(arg_text_z, a)
            if a >= len(arg_text_z) or arg_text_z[a] == chr(0):
                break
            if arg_text_z[a] == ',':
                a += 1
                continue
            if arg_text_z[a] == '[':
                v, a = self._mini_arg_array(arg_text_z, a, name)
                if v is None:
                    return [], idx
                args.append(v)
            else:
                v, a = self.expr_eval.expression_pat(arg_text_z, a)
                args.append(0 if _is_undef_derived(v) else v)
            a = StringUtils.skipspc(arg_text_z, a)
            if a < len(arg_text_z) and arg_text_z[a] == ',':
                a += 1
                continue
            break

        saved_reclimit = sys.getrecursionlimit()
        if saved_reclimit < _MINI_RECLIMIT:
            sys.setrecursionlimit(_MINI_RECLIMIT)
        try:
            words, ret = MiniInterp(self.state, self.expr_eval).run(
                fn, args, (fn.file, fn.line))
        except MiniLangError as e:
            self._mini_diag(f" error - {e}")
            return [], idx
        except RecursionError:
            self._mini_diag(f" error - '.call {name}': expression nesting too deep.")
            return [], idx
        finally:
            sys.setrecursionlimit(saved_reclimit)
        if ret is not None:
            words = words + (list(ret) if isinstance(ret, list) else [ret])
        return words, idx

    def _mini_arg_array(self, t, a, name):
        """`[e1, e2, ...]` と書かれた引数を配列として評価する。"""
        depth = 0
        k = a
        while k < len(t) and t[k] != chr(0):
            if t[k] in '([':
                depth += 1
            elif t[k] in ')]':
                depth -= 1
                if depth == 0:
                    break
            k += 1
        if depth != 0 or k >= len(t) or t[k] != ']':
            self._mini_diag(f" error - '.call {name}': unbalanced '[' in the "
                            f"argument list.")
            return None, len(t)
        inner = t[a + 1:k] + chr(0)
        out = []
        i = 0
        while True:
            i = StringUtils.skipspc(inner, i)
            if i >= len(inner) or inner[i] == chr(0):
                break
            if inner[i] == ',':
                i += 1
                continue
            v, i = self.expr_eval.expression_pat(inner, i)
            out.append(_mini_wrap(0 if _is_undef_derived(v) else v))
            i = StringUtils.skipspc(inner, i)
            if i < len(inner) and inner[i] == ',':
                i += 1
                continue
            break
        return out, k + 1

    _TXT_CONVS = (('float', 3), ('hex', 0), ('dec', 1), ('bin', 2))

    @staticmethod
    def _arr_split(q):
        """配列リテラルをトップレベルのカンマで項目に割る。

        `"..."` の中や入れ子の括弧・ブラケットの中のカンマでは割らない。
        """
        items = []
        i = 1
        n = len(q)
        while i < n:
            while i < n and q[i] in ' \t':
                i += 1
            if i >= n or q[i] == ']':
                break
            b = i
            depth = 0
            inq = False
            while i < n:
                c = q[i]
                if inq:
                    if c == '\\' and i + 1 < n:
                        i += 1
                    elif c == '"':
                        inq = False
                elif c == '"':
                    inq = True
                elif c in '[(':
                    depth += 1
                elif c == ')':
                    depth -= 1
                elif c == ']':
                    if depth == 0:
                        break
                    depth -= 1
                elif c == ',' and depth == 0:
                    break
                i += 1
            items.append(q[b:i].rstrip(' \t'))
            if i < n and q[i] == ',':
                i += 1
            else:
                break
        return items

    @staticmethod
    def _txt_template_inner(q):
        """文字列テンプレートの外側のダブルクォートを外す。"""
        out = []
        i = 1
        while i < len(q):
            if q[i] == '\\' and i + 1 < len(q):
                out.append(q[i]); out.append(q[i + 1]); i += 2; continue
            if q[i] == '"':
                break
            out.append(q[i]); i += 1
        return ''.join(out)

    @staticmethod
    def _txt_radix(v, radix):
        """値をその基数の数字だけで書く（基数プレフィックスは付けない）。"""
        n = int(v)
        neg = n < 0
        if neg:
            n = -n
        if n == 0:
            body = '0'
        else:
            digits = '0123456789abcdef'
            body = ''
            while n:
                body = digits[n % radix] + body
                n //= radix
        return ('-' + body) if neg else body

    _TXT_FLOAT_PREC = 34

    @classmethod
    def _txt_float_parts(cls, neg, digits, exp10):
        """`.float` の出力を、符号・数字列・指数から組み立てる。"""
        digits = digits.rstrip('0') or '0'
        n = len(digits)
        if -6 <= exp10 < cls._TXT_FLOAT_PREC:
            if exp10 >= n - 1:
                body = digits + '0' * (exp10 - (n - 1)) + '.0'
            elif exp10 >= 0:
                body = digits[:exp10 + 1] + '.' + digits[exp10 + 1:]
            else:
                body = '0.' + '0' * (-exp10 - 1) + digits
        else:
            frac = digits[1:] if n > 1 else '0'
            body = '%s.%se%s%02d' % (digits[0], frac,
                                     '-' if exp10 < 0 else '+', abs(exp10))
        return ('-' + body) if neg else body

    @classmethod
    def _txt_float(cls, v):
        """`{{.float(x)}}` — 値を 10 進 128bit 浮動小数点として書く。

        有効数字 34 桁、偶数丸め。小数部が無い値にも小数部を付けるので
        `16` は `16.0` になる。34 桁を超える場合と極端に小さい値では
        指数形式に切り替わる。両実装が同じテキストを出す必要がある。
        """
        prec = cls._TXT_FLOAT_PREC
        if isinstance(v, float):
            if v != v or v in (float('inf'), float('-inf')):
                return 'nan' if v != v else ('inf' if v > 0 else '-inf')
            d = Context(prec=prec).create_decimal(Decimal(v))
        else:
            d = Context(prec=prec).create_decimal(Decimal(int(v)))
        sign, digits, dexp = d.as_tuple()
        digits = ''.join(str(x) for x in digits) or '0'
        return cls._txt_float_parts(sign == 1, digits, len(digits) - 1 + dexp)

    @staticmethod
    def _txt_close_paren(s, i):
        """対応する `)` の位置を返す。"""
        depth = 0
        while i < len(s):
            if s[i] == '(':
                depth += 1
            elif s[i] == ')':
                depth -= 1
                if depth == 0:
                    return i
            i += 1
        return -1

    @classmethod
    def _txt_conv_name(cls, s):
        """`{{ }}` の中の変換名（`.hex` `.dec` `.bin` `.float` ...）を読む。"""
        u = StringUtils.upper(s)
        for name, kind in cls._TXT_CONVS:
            if u.startswith(StringUtils.upper(name)) and s[len(name):len(name) + 1] == '(':
                return len(name), kind
        return 0, -1

    def _txt_emit_expr(self, parts, expr, kind):
        """`{{ }}` の 1 個を評価して、テキストとして積む。"""
        saved_undef = self.state.error_undefined_label
        self.state.error_undefined_label = False
        v, _ = self.expr_eval.expression_pat(expr, 0)
        if self.state.error_undefined_label:
            saved_undef = True
        self.state.error_undefined_label = saved_undef

        if kind == 0:
            parts.append(self._txt_radix(v, 16))
        elif kind == 2:
            parts.append(self._txt_radix(v, 2))
        elif kind == 3:
            parts.append(self._txt_float(v))
        else:
            parts.append(self._txt_radix(v, 10))

    def _txt_render(self, s):
        """文字列テンプレートを展開して、出来上がったテキストを返す。

        置き換えるのは `{{ }}` の中だけで、それ以外はバックスラッシュ
        エスケープを除いて書いたままの文字が出る。`{{ }}` の中に単独で
        書かれた名前は、文字列シンボル → 配列シンボル → 式の順で解決する。
        数値の `.setsym` シンボルは 1 番目では引かないので、ただの単語が
        黙って数値に化けることはない（欲しいときは `{{#NAME}}`）。
        """
        parts = []
        i = 0
        while i < len(s):
            c = s[i]
            if c == '\\' and i + 1 < len(s):
                parts.append(_TXT_ESCAPES.get(s[i + 1], s[i + 1])); i += 2; continue
            if s.startswith('{{', i):
                e = s.find('}}', i + 2)
                if e < 0:
                    parts.append(c); i += 1; continue
                inner = s[i + 2:e]
                j = 0
                while j < len(inner) and inner[j] == ' ':
                    j += 1
                done = False
                if inner[j:j + 1] == '.':
                    en = self._txt_exp_call(inner[j + 1:])
                    if en is not None:
                        parts.append(self._txt_exp_text(en))
                        done = True
                if not done and inner[j:j + 1] == '.':
                    nm, ix = self._txt_index_call(inner[j + 1:])
                    if nm is not None:
                        parts.append(self._txt_index_text(nm, ix))
                        done = True
                if not done and inner[j:j + 1] == '.':
                    nl, kind = self._txt_conv_name(inner[j + 1:])
                    if nl:
                        cp = self._txt_close_paren(inner, j + 1 + nl)
                        if cp > 0:
                            self._txt_emit_expr(parts, inner[j + 1 + nl + 1:cp], kind)
                            done = True
                if not done:
                    nm, ix = self._txt_bare_indexed(inner)
                    if nm is not None:
                        parts.append(self._txt_indexed_text(nm, ix))
                        done = True
                if not done:
                    bare = self._txt_bare_name(inner)
                    if bare is not None and (bare in self.state.strsymbols
                                             or bare in self.state.arrsymbols):
                        parts.append(self._txt_name_text(bare))
                        done = True
                if not done:
                    self._txt_emit_expr(parts, inner, -1)
                i = e + 2
                continue
            parts.append(c)
            i += 1
        return ''.join(parts)

    @classmethod
    def _txt_bare_indexed(cls, inner):
        """`{{名前[式]}}` の形か調べて、名前と添字に割る。"""
        t = inner.strip()
        if not t.isascii() or not t[:1].isalpha() and t[:1] != '_':
            return None, None
        i = 1
        while i < len(t) and (t[i].isalnum() or t[i] == '_'):
            i += 1
        name = t[:i]
        while i < len(t) and t[i] in ' \t':
            i += 1
        if i >= len(t) or t[i] != '[':
            return None, None
        cb = cls._txt_close_bracket(t, i)
        if cb < 0 or t[cb + 1:].strip() != '':
            return None, None
        return name, t[i + 1:cb]

    @staticmethod
    def _txt_bare_name(inner):
        """`{{名前}}` の形か調べて、その名前を返す。"""
        t = inner.strip()
        if not t.isascii() or not (t[:1].isalpha() or t[:1] == '_'):
            return None
        for ch in t[1:]:
            if not (ch.isalnum() or ch == '_'):
                return None
        return StringUtils.upper(t)

    def _txt_name_text(self, name):
        """`{{名前}}` を解決してテキストにする。"""
        key = StringUtils.upper(name)
        if key in self.state.strsymbols:
            return self.state.strsymbols[key]
        if key in self.state.arrsymbols:
            return ','.join(v if isinstance(v, str) else self._txt_radix(v, 10)
                            for v in self.state.arrsymbols[key])
        _v = name.lower()
        if _v == name and _v in self.state.varnames:
            return self._txt_radix(self.state.vars.get(_v, VAR_UNDEF), 10)
        return name

    @staticmethod
    def _txt_close_bracket(s, i):
        """対応する `]` の位置を返す。"""
        depth = 0
        while i < len(s):
            if s[i] == '[':
                depth += 1
            elif s[i] == ']':
                depth -= 1
                if depth == 0:
                    return i
            i += 1
        return -1

    def _txt_indexed_text(self, name, idxtext):
        """`{{配列[添字]}}` を解決してテキストにする。"""
        key = StringUtils.upper(name)
        if key not in self.state.arrsymbols:
            self.state.diag(f" error - '{key}' is not an array symbol; "
                            f"'{key}[...]' needs '.setsym::{key}::[...]'.",
                            set_error=True)
            return ''
        n = self._arr_index_of(key, idxtext)
        if n is None:
            return ''
        arr = self.state.arrsymbols[key]
        return arr[n] if isinstance(arr[n], str) else self._txt_radix(arr[n], 10)

    @classmethod
    def _txt_index_call(cls, s):
        """`{{.index 名前[添字]}}` と `{{.index(名前[添字])}}` の両方を読む。"""
        if StringUtils.upper(s[:5]) != 'INDEX':
            return None, None
        rest = s[5:]
        if rest[:1] not in (' ', '\t', '('):
            return None, None
        rest = rest.strip()
        if rest.startswith('('):
            cp = cls._txt_close_paren(rest, 0)
            if cp < 0 or rest[cp + 1:].strip() != '':
                return None, None
            rest = rest[1:cp]
        return cls._txt_bare_indexed(rest)

    def _txt_index_text(self, name, idxtext):
        """`{{.index 配列[添字]}}` — 項目ではなく添字そのものを 10 進で書く。

        添字の解決は項目を引くときと同じ規則（文字列シンボル → パターン変数
        → その配列の項目名、無ければ同名の数値シンボル → ふつうの式）。
        名前から番号への引き当てがこれで書ける。
        """
        key = StringUtils.upper(name)
        if key not in self.state.arrsymbols:
            self.state.diag(f" error - '{key}' is not an array symbol; "
                            f"'.index {key}[...]' needs '.setsym::{key}::[...]'.",
                            set_error=True)
            return ''
        n = self._arr_index_of(key, idxtext)
        return '' if n is None else self._txt_radix(n, 10)

    @classmethod
    def _txt_exp_call(cls, s):
        """`{{.exp(変数)}}` の形を読む。"""
        if StringUtils.upper(s[:3]) != 'EXP':
            return None
        rest = s[3:]
        if rest[:1] not in (' ', '\t', '('):
            return None
        rest = rest.strip()
        if rest[:1] != '(':
            return None
        cb = cls._txt_close_paren(rest, 0)
        if cb < 0 or rest[cb + 1:].strip() != '':
            return None
        nm = rest[1:cb].strip()
        if not nm or PatternMatcher._var_name_at(nm, 0) != len(nm):
            return None
        return nm

    def _txt_exp_text(self, name):
        """`{{.exp(変数)}}` — `!L` が覚えた綴りを、ソースに書かれていたまま出す。"""
        if name not in self.state.varnames:
            self.state.diag(f" error - '{name}' is not a pattern variable; "
                            f"'.exp({name})' needs '!L{name}' in the "
                            f"instruction field.", set_error=True)
            return ''
        return self.state.vars_text.get(name, '')

    @staticmethod
    def _txt_quoted_text(t):
        """添字に書かれた文字列リテラルを、その中身に開く。

        これがあるので `arrb["CX"]` は `arrb[CX]` と同じに読まれる。
        """
        if t.startswith('\\"'):
            delim = '\\"'
        elif t.startswith('"'):
            delim = '"'
        else:
            return None
        out = []
        i = len(delim)
        while i < len(t):
            if t.startswith(delim, i):
                return ''.join(out) if t[i + len(delim):].strip() == '' else None
            if t[i] == '\\' and i + 1 < len(t):
                out.append(_TXT_ESCAPES.get(t[i + 1], t[i + 1])); i += 2; continue
            out.append(t[i]); i += 1
        return None

    def _arr_index_of(self, key, idxtext):
        """配列の添字を解決して整数にする。

        順序は、文字列シンボルの名前（中身を添字として読み直す）、
        パターン変数（その値）、その配列の項目名（その位置）、無ければ
        同名の `.setsym` / `.map` の数値シンボル、どれでもなければ式。
        """
        arr = self.state.arrsymbols[key]
        t = (idxtext or '').strip()
        _q = self._txt_quoted_text(t)
        if _q is not None:
            t = _q.strip()
        nm = self._txt_bare_name(t)
        if nm is not None and nm in self.state.strsymbols:
            t = self.state.strsymbols[nm].strip()
            nm = self._txt_bare_name(t)
        _v = t.lower()
        is_var = (_v == t and _v in self.state.varnames)
        if nm is not None and not is_var:
            for k, v in enumerate(arr):
                if isinstance(v, str) and StringUtils.upper(v) == nm:
                    return k
            if nm in self.state.symbols:
                return self._arr_index_check(key, arr, self.state.symbols[nm])
        saved_undef = self.state.error_undefined_label
        self.state.error_undefined_label = False
        v, _ = self.expr_eval.expression_pat(t, 0)
        if self.state.error_undefined_label:
            saved_undef = True
        self.state.error_undefined_label = saved_undef
        return self._arr_index_check(key, arr, v)

    def _arr_index_check(self, key, arr, v):
        """添字が範囲内かを検査する。範囲外はエラーとして報告する。"""
        try:
            n = int(v)
        except (OverflowError, ValueError, TypeError):
            n = -1
        if n < 0 or n >= len(arr):
            self.state.diag(f" error - index {n} is out of range for array symbol "
                            f"'{key}' (0..{len(arr) - 1}).", set_error=True)
            return None
        return n

    def makeobj(self, s):
        """`binary_list` を評価して、その行のワード列を返す。

        先に `@@[]` の繰り返しと `%%` の添字を展開し、残りをカンマで 1 要素ずつ
        見る。要素はダブルクォートならテキストテンプレート（UTF-8 の 1 バイトが
        1 ワードになる。ワード幅を超えるバイトは警告して切る）、`.call` なら
        ミニ言語、空ならアラインメント、ほかは式。`;` 付きは値が 0 のとき、
        文字列なら描画結果が空のときに飛ばし、`;;` 付きは評価して捨てる。
        """
        _txtacc = []
        _dispacc = []

        s, z = self.e_p(s)
        s = self.replace_percent_with_index(s)

        s += chr(0)
        idx = 0
        objl = []

        if z:
            return objl

        self.state._in_binary_list = True
        _prior_undef = self.state.error_undefined_label
        self.state.error_undefined_label = False
        try:
            while True:
                if idx >= len(s) or s[idx] == chr(0):
                    break

                if s[idx] == ',':
                    idx += 1
                    continue

                semicolon = False
                drop = False
                if s[idx] == ';':
                    semicolon = True
                    idx += 1
                    if idx < len(s) and s[idx] == ';':
                        drop = True
                        idx += 1

                _qs = idx
                while _qs < len(s) and s[_qs] in ' \t':
                    _qs += 1
                if _qs < len(s) and s[_qs] == '"':
                    _src = s[_qs:]
                    _nul = _src.find(chr(0))
                    if _nul >= 0:
                        _src = _src[:_nul]
                    _txt = self._txt_render(self._txt_template_inner(_src))
                    if not (drop or (semicolon and _txt == '')):
                        _word_mask = (1 << self.state.bts) - 1 if self.state.bts > 0 else 0xFF
                        _vals = list(_txt.encode('utf-8', errors='surrogateescape'))
                        if (any(_v > _word_mask for _v in _vals)
                                and not self.state._pass1_size_mode
                                and self.state.should_report_errors()):
                            self.state.diag(f" warning - text template: one or more bytes exceed "
                                 f"the output word width ({self.state.bts} bit(s)) and were "
                                 f"truncated (high bits discarded): {_txt!r}", set_error=False)
                        objl += _vals
                        _txtacc.append(_txt)
                        _dispacc.append('"%s"' % asmtext_escaped(_txt))
                    _closed = False
                    idx = _qs + 1
                    while idx < len(s) and s[idx] != chr(0):
                        if s[idx] == '\\' and idx + 1 < len(s):
                            idx += 2; continue
                        if s[idx] == '"':
                            idx += 1; _closed = True; break
                        idx += 1
                    if (not _closed and not self.state._pass1_size_mode
                            and self.state.should_report_errors()):
                        self.state.diag(f" warning - unterminated string literal in pattern "
                             f"encoding field: {_src!r}", set_error=False)
                    while idx < len(s) and s[idx] in ' \t':
                        idx += 1
                    if idx < len(s) and s[idx] == ',':
                        idx += 1
                        continue
                    break

                if StringUtils.upper(s[idx:idx + 5]) == '.CALL' and (
                        idx + 5 >= len(s) or s[idx + 5] not in _SYM_CORE):
                    self.state._elf_current_word_idx = len(objl)
                    words, idx = self.mini_call(s, idx)
                    if drop or (semicolon and len(words) == 1 and words[0] == 0):
                        words = []
                    if not words:
                        _wi = self.state._elf_current_word_idx
                        self.state._elf_label_refs_seen = [
                            e for e in self.state._elf_label_refs_seen if e[2] != _wi
                        ]
                        self.state._elf_insn_reloc_hint.pop(_wi, None)
                    objl += words
                    self.state._elf_current_word_idx = -1
                    if idx < len(s) and s[idx] == ',':
                        idx += 1
                        continue
                    break

                self.state._elf_current_word_idx = len(objl)

                if self.state.pas == 1:
                    self.state._pass1_size_mode = True
                x, idx = self.expr_eval.expression_pat(s, idx)
                if self.state.pas == 1:
                    self.state._pass1_size_mode = False
                    self.state.error_undefined_label = False

                if not drop and (not semicolon or x != 0):
                    objl += [x]
                else:
                    self.state._elf_label_refs_seen = [
                        e for e in self.state._elf_label_refs_seen
                        if e[2] != self.state._elf_current_word_idx
                    ]

                if idx < len(s) and s[idx] == ',':
                    idx += 1
                    continue
                break
        finally:
            self.state._elf_current_word_idx = -1
            self.state._in_binary_list = False
            if self.state.pas == 1:
                self.state._pass1_size_mode = False
            self.state.error_undefined_label = self.state.error_undefined_label or _prior_undef
            if _txtacc:
                self.state.asmtext = ''.join(_txtacc)
                self.state.asmtext_disp = ','.join(_dispacc)

        return objl



def bare_name_of(text):
    """欄が「裸の名前」1 個だけなら、その綴りを返す。でなければ None。

    綴りはそのまま保つ（大文字化しない）。配列シンボルの項目が書かれた
    ままの綴りで残るのはこれが理由。
    """
    t = (text or '').strip()
    if not t.isascii() or not (t[:1].isalpha() or t[:1] == '_'):
        return None
    for ch in t[1:]:
        if not (ch.isalnum() or ch == '_'):
            return None
    return t


def arr_items_from_text(expr_eval, q):
    """`[...]` の中身を配列シンボルの項目リストにする。

    `"..."` は文字列、裸の名前は綴りのままの文字列、それ以外は式として
    評価した数値。空の項目は 0。
    """
    out = []
    for item in ObjectGenerator._arr_split(q):
        if item.startswith('"'):
            out.append(ObjectGenerator._txt_template_inner(item))
            continue
        nm = bare_name_of(item)
        if nm is not None:
            out.append(nm)
        elif item:
            v, _ = expr_eval.expression_pat(item, 0)
            out.append(v)
        else:
            out.append(0)
    return out



def split_top_commas(text):
    """トップレベルのカンマだけで割る。括弧・ブラケットの中では割らない。"""
    items = []
    buf = []
    depth = 0
    for ch in text:
        if ch in '([{':
            depth += 1
        elif ch in ')]}':
            if depth > 0:
                depth -= 1
        elif ch == ',' and depth == 0:
            items.append(''.join(buf).strip())
            buf = []
            continue
        buf.append(ch)
    items.append(''.join(buf).strip())
    return items


def _set_name_token(t):
    """集合リストの 1 項目として読める名前か。読めれば大文字化して返す。"""
    t = t.strip()
    if not t or not t.isascii() or t[0] in DIGIT:
        return None
    for ch in t:
        if ch in ' \t':
            return None
    return StringUtils.upper(t)


def set_items_dedupe(items):
    """順序を保ったまま重複を落とす。最初に現れた位置が残る。"""
    out = []
    for it in items:
        if it not in out:
            out.append(it)
    return out


def set_literal_from_text(state, text):
    """`r0,r1,r2` の形を集合として読む。

    項目がそれ自体集合（配列シンボル）ならその場で展開する。名前でない項目が
    1 つでもあれば None を返し、数値解釈へ譲る。2 項目以上ないと集合にしない
    ので、単一の名前はコピーとして扱われる。
    """
    parts = split_top_commas(text)
    if len(parts) < 2:
        return None
    items = []
    for p in parts:
        nm = _set_name_token(p)
        if nm is None:
            return None
        arr = state.arrsymbols.get(nm)
        if arr is not None:
            items.extend(arr)
        else:
            items.append(nm)
    return set_items_dedupe(items)


def _set_operand(state, t):
    """集合式のオペランドを読む。既存の集合を指す裸の識別子のみ。

    `-` `&` `|` はシンボル名の中にも現れうるので、文字・数字・`_` だけで
    綴られている場合に限って集合と認める。
    """
    t = t.strip()
    if not t or not t.isascii():
        return None
    if not (t[0].isalpha() or t[0] == '_'):
        return None
    for ch in t[1:]:
        if not (ch.isalnum() or ch == '_'):
            return None
    arr = state.arrsymbols.get(StringUtils.upper(t))
    return None if arr is None else set_items_dedupe(list(arr))


def set_expr_from_text(state, text):
    """集合式 `a&b` `a|b` `a^b` `a+b` `a-b` を計算する。

    演算子に固有の優先順位は無く、左から右へ適用するので `a&b|c` は
    `(a&b)|c`。結果は毎回新しいリストなので、あとで `a` を再定義しても
    影響せず、`.setsym::a::a|b` のような自己参照も安全。
    集合として読めなければ None を返し、数値解釈へ譲る。
    """
    toks = []
    cur = []
    for ch in text:
        if ch in SET_OPS:
            toks.append(''.join(cur))
            toks.append(ch)
            cur = []
        else:
            cur.append(ch)
    toks.append(''.join(cur))
    if len(toks) < 3:
        return None
    acc = _set_operand(state, toks[0])
    if acc is None:
        return None
    k = 1
    while k + 1 < len(toks):
        op = toks[k]
        rhs = _set_operand(state, toks[k + 1])
        if rhs is None:
            return None
        if op == '&':
            acc = [x for x in acc if x in rhs]
        elif op in '|+':
            acc = acc + [x for x in rhs if x not in acc]
        elif op == '^':
            acc = ([x for x in acc if x not in rhs]
                   + [x for x in rhs if x not in acc])
        else:
            acc = [x for x in acc if x not in rhs]
        k += 2
    return acc


def symbol_set_from_text(state, dst_upper, value_field):
    """値欄を集合として解釈し、配列シンボルとして登録する。

    中身が変わったときだけ世代番号を進める。`.check` の名前一覧は配列
    シンボルを参照するので、無駄に進めるとそのキャッシュが無意味に落ちる。
    """
    items = set_expr_from_text(state, value_field)
    if items is None:
        items = set_literal_from_text(state, value_field)
    if items is None:
        return False
    if state.arrsymbols.get(dst_upper) == items:
        return True
    state.arrsymbols[dst_upper] = items
    state.arrgen += 1
    return True


def symbol_copy_from_name(state, dst_upper, value_field):
    """値欄が裸の名前のときの `.setsym`。

    その名前が配列シンボルか文字列シンボルならコピーし（独立したコピーなので
    元を再定義しても変わらない）、どちらでもなければ「その名前を保持する
    文字列シンボル」にする。名前を持ち回って添字に使えるのはこれのため。
    """
    t = bare_name_of(value_field)
    if t is None:
        return False
    src = StringUtils.upper(t)
    if src in state.arrsymbols:
        if src != dst_upper:
            state.arrsymbols[dst_upper] = list(state.arrsymbols[src])
            state.arrgen += 1
        return True
    if src in state.strsymbols:
        if src != dst_upper:
            state.strsymbols[dst_upper] = state.strsymbols[src]
        return True
    state.strsymbols[dst_upper] = t
    return True


class VLIWProcessor:
    """VLIW / EPIC のバンドルを組み立てる。

    ソースで `!!` で結合された命令をスロットに詰め、テンプレート欄と
    ストップビットを付けてバンドル 1 個ぶんのワード列にする。
    埋まらないスロットは `.vliw` で宣言した NOP で埋める。
    """

    def __init__(self, state, expr_eval, binary_writer):
        self.state = state
        self.expr_eval = expr_eval
        self.binary_writer = binary_writer

    def vliwprocess(self, line, idxs, objl, flag, idx, lineassemble2_func):
        """1 バンドルを組み立てて出力する。

        各スロットを lineassemble2_func で個別にアセンブルし、得られた
        インデックスコードの並びで `EPIC::` の宣言を引いてテンプレートを決める。
        テンプレート幅が正なら右端、負なら絶対値を幅として左端に置く。
        バイト順は `.bits::big/little` に従う。
        """
        objs = [objl]
        idxlst = [idxs]
        self.state.vliwstop = 0

        while True:
            idx = StringUtils.skipspc(line, idx)
            if idx < len(line) and line[idx] == VLIW_STOP:
                idx += 1
                self.state.vliwstop = 1
                continue
            elif idx < len(line) and line[idx] == VLIW_SEP:
                idx += 1

                _slot_peek = line[idx:].lstrip()
                if _slot_peek.startswith('.'):
                    self.state.diag(" error - directives (e.g. .section/.endsection/.INCLUDE) "
                             "are not allowed inside VLIW slots (the packet's PC has not "
                             "advanced yet at this point in the packet).", set_error=True)
                    return False
                idxs, objl, flag, idx = lineassemble2_func(line, idx)
                if not flag:
                    return False
                objs += [objl]
                idxlst += [idxs]
                continue
            else:
                break

        if self.state.vliwtemplatebits == 0:
            self.state.vliwset = [[[0], "0"]]

        vbits = abs(self.state.vliwbits)

        if self.state.vliwinstbits == 0:
            self.state.diag(" error - vliwinstbits is zero; cannot compute instruction slots.", set_error=True)
            return False
        for k in self.state.vliwset:
            if list(k[0]) == list(idxlst) or self.state.vliwtemplatebits == 0:
                im = 2 ** self.state.vliwinstbits - 1
                tm = 2 ** abs(self.state.vliwtemplatebits) - 1
                pm = 2 ** vbits - 1
                _tmpl_prior_undef = self.state.error_undefined_label
                self.state.error_undefined_label = False
                x, idx = self.expr_eval.expression_pat(k[1], 0)
                if self.state.error_undefined_label and self.state.should_report_errors():
                    self.state.had_error = True
                self.state.error_undefined_label = _tmpl_prior_undef or self.state.error_undefined_label
                templ = x & tm

                values = []
                ibyte = self.state.vliwinstbits // 8 + (0 if self.state.vliwinstbits % 8 == 0 else 1)
                noi = (vbits - abs(self.state.vliwtemplatebits)) // self.state.vliwinstbits

                if noi <= 0:
                    self.state.diag(f" error - .vliw: vliwtemplatebits ({self.state.vliwtemplatebits}) "
                             f"leaves no room for instruction slots in a {vbits}-bit packet "
                             f"(vliwinstbits={self.state.vliwinstbits}).", set_error=True)
                    return False

                for j in objs:
                    for m in j:
                        values += [m]

                target_len = ibyte * noi
                if len(values) > target_len:
                    self.state.diag(f"warning-VLIW:{len(values)} values exceed slot capacity {target_len},truncating.", set_error=False)
                    values = values[:target_len]
                else:
                    _deficit = target_len - len(values)
                    _full_nops, _remainder = divmod(_deficit, ibyte) if ibyte > 0 else (0, _deficit)
                    for _ in range(_full_nops):
                        values += self.state.vliwnop
                    if _remainder > 0:
                        values += (self.state.vliwnop + [0] * _remainder)[:_remainder]

                v1 = []
                cnt = 0

                for j in range(noi):
                    vv = 0
                    if self.state.endian == 'little':
                        for i in range(ibyte):
                            if len(values) > cnt:
                                vv |= (values[cnt] & 0xff) << (8 * i)
                            cnt += 1
                    else:
                        for i in range(ibyte):
                            vv <<= 8
                            if len(values) > cnt:
                                vv |= values[cnt] & 0xff
                            cnt += 1
                    v1 += [vv & im]

                r = 0
                for v in v1:
                    r = (r << self.state.vliwinstbits) | v
                r = r & pm

                if self.state.vliwtemplatebits < 0:
                    res = r | (templ << (vbits - abs(self.state.vliwtemplatebits)))
                else:
                    res = (r << self.state.vliwtemplatebits) | templ

                q = 0
                if vbits < 8:
                    self.binary_writer.outbin(self.state.pc, res & ((1 << vbits) - 1))
                    q = 1
                elif self.state.endian == 'little':
                    total_bytes = (vbits + 7) // 8
                    for cnt in range(total_bytes):
                        self.binary_writer.outbin(self.state.pc + cnt, res & 0xff)
                        res >>= 8
                        q += 1
                else:
                    total_bytes = (vbits + 7) // 8
                    for cnt in range(total_bytes):
                        shift = (total_bytes - 1 - cnt) * 8
                        self.binary_writer.outbin(self.state.pc + cnt, (res >> shift) & 0xff)
                        q += 1

                self.state.pc += q
                break
        else:
            self.state.diag(" error - No vliw instruction-set defined.", set_error=True)
            return False
        return True


class AssemblyDirectiveProcessor:
    """アセンブリソース側のディレクティブを処理する。

    パターンファイルに関係なく常に使えるのはここにあるものだけで、`DB` の
    ようなバイト出力ニーモニックは組み込みではない（パターンファイルが
    定義したときだけ存在する）。
    """

    def __init__(self, state, expr_eval, binary_writer, label_manager, parser):
        self.state = state
        self.expr_eval = expr_eval
        self.binary_writer = binary_writer
        self.label_manager = label_manager
        self.parser = parser

    def labelc_processing(self, l, ll):
        """`.labelc` — ラベルに使える文字を増やす。"""
        if l.upper() != '.LABELC':
            return False
        if ll:
            self.state.lwordchars = ALPHABET + DIGIT + ll
        return True

    def label_processing(self, l):
        """行頭の `label:` と `.equ` を処理する。

        `.equ` で定義したラベルは再配置情報を失い、定数として扱われる。
        """
        if l == "":
            return ""

        label, idx = self.parser.get_label_word(l, 0)
        lidx = idx

        if label != "" and idx > 0 and l[idx - 1] == ':':
            idx = StringUtils.skipspc(l, idx)
            e, idx = StringUtils.get_param_to_spc(l, idx)

            if e.upper() == '.EQU':
                reloc_type = None
                expr_part = l[idx:].strip()
                if '::' in expr_part:
                    parts = [p.strip() for p in expr_part.split('::', 1)]
                    expr_part = parts[0]
                    rt_str = parts[1].lower()

                    _mach_tbl = elf_machine_table(self.state)
                    reloc_type = _reloc_named(self.state, _mach_tbl, rt_str)
                    if reloc_type is None:
                        self.state.diag(f" warning - unknown reloctype '{rt_str}' in .EQU"
                             f" for machine {self.state.elf_machine}", set_error=False)

                self.state.error_undefined_label = False
                saved_mode = self.state._pass1_size_mode
                if self.state.pas == 1:
                    self.state._pass1_size_mode = True

                _track_sections = reloc_type is None
                if _track_sections:
                    self.state._equ_sections_touched = set()
                try:
                    u, _ = self.expr_eval.expression_asm(expr_part, 0)
                finally:
                    self.state._pass1_size_mode = saved_mode
                    _touched = self.state._equ_sections_touched
                    self.state._equ_sections_touched = None
                if (_track_sections and _touched and len(_touched) > 1
                        and self.state.should_report_errors()):
                    self.state.diag(f" warning - .EQU '{label}': expression combines labels from "
                         f"multiple sections ({', '.join(sorted(_touched))}) without an "
                         f"explicit ::reloctype; the resulting constant assumes a specific "
                         f"section layout and will NOT be relocated by the linker.", set_error=False)
                if self.state.error_undefined_label and self.state.should_report_errors():
                    self.state.diag(f" error - .EQU '{label}': expression contains undefined label.", set_error=True)
                ok = self.label_manager.put_value(label, u, self.state.current_section, is_equ=True, reloc_type=reloc_type)
                if self.state.textmode:
                    self.state.label_text = l[:lidx]
                    return l[lidx:]
                return ""
            else:
                ok = self.label_manager.put_value(label, self.state.pc, self.state.current_section, is_equ=False)
                if ok is False:
                    return ""
                self.state.label_text = l[:lidx]
                return l[lidx:]
        return l

    def asciistr(self, l2):
        """`.ascii` / `.asciz` の文字列をバイト列にする。"""
        idx = 0
        if l2 == '' or l2[idx] != '"':
            return False
        idx += 1

        _word_mask = (1 << self.state.bts) - 1 if self.state.bts > 0 else 0xFF
        _truncated = False

        while idx < len(l2) and not l2[idx] == '"':
            ch = None
            _is_literal = False
            if l2[idx:idx + 2] == '\\0':
                idx += 2
                ch = chr(0)
            elif l2[idx:idx + 2] == '\\t':
                idx += 2
                ch = '\t'
            elif l2[idx:idx + 2] == '\\n':
                idx += 2
                ch = '\n'
            elif l2[idx:idx + 2] == '\\r':
                idx += 2
                ch = '\r'
            elif l2[idx:idx + 2] == '\\\\':
                idx += 2
                ch = '\\'
            elif l2[idx:idx + 2] == '\\"':
                idx += 2
                ch = '"'
            elif l2[idx:idx + 2] in ('\\x', '\\X'):
                idx += 2
                hex_str = ''
                while idx < len(l2) and l2[idx] in '0123456789abcdefABCDEF' and len(hex_str) < 2:
                    hex_str += l2[idx]
                    idx += 1
                if hex_str:
                    ch = chr(int(hex_str, 16))
                else:
                    self.state.diag(f" error - '\\x' escape requires at least one hex digit in string: {l2!r}", set_error=False)
                    return False
            elif l2[idx:idx + 2] in ('\\u', '\\U'):
                _ndigits = 4 if l2[idx:idx + 2] == '\\u' else 8
                idx += 2
                hex_str = ''
                while idx < len(l2) and l2[idx] in '0123456789abcdefABCDEF' and len(hex_str) < _ndigits:
                    hex_str += l2[idx]
                    idx += 1
                if len(hex_str) == _ndigits:
                    try:
                        ch = chr(int(hex_str, 16))
                    except (ValueError, OverflowError):
                        self.state.diag(f" error - invalid \\u/\\U escape in string: {l2!r}", set_error=False)
                        return False
                else:
                    self.state.diag(f" error - '\\{'u' if _ndigits == 4 else 'U'}' escape requires "
                         f"{_ndigits} hex digits in string: {l2!r}", set_error=False)
                    return False
            else:
                ch = l2[idx]
                idx += 1
                _is_literal = True
            if ch is not None:
                if _is_literal:
                    _vals = list(ch.encode('utf-8', errors='surrogateescape'))
                else:
                    _vals = [ord(ch)]
                for _v in _vals:
                    if _v > _word_mask:
                        _truncated = True
                    self.binary_writer.outbin(self.state.pc, _v)
                    self.state.pc += 1
        if idx >= len(l2):
            self.state.diag(f" warning - unterminated string literal in .ASCII/.ASCIZ: {l2!r}", set_error=False)
        if _truncated and self.state.should_report_errors():
            self.state.diag(f" warning - .ASCII/.ASCIZ: one or more characters exceed the output word "
                 f"width ({self.state.bts} bit(s)) and were truncated (high bits discarded): "
                 f"{l2!r}", set_error=False)
        return True

    def export_processing(self, l1, l2):
        """ラベルを TSV にエクスポートする指定を処理する。"""
        _l1u = StringUtils.upper(l1)
        if _l1u != ".EXPORT" and _l1u != ".GLOBAL":
            return False
        if not (self.state.should_report_errors()):
            return True

        idx = 0
        l2 += chr(0)
        while idx < len(l2) and l2[idx] != chr(0):
            idx = StringUtils.skipspc(l2, idx)
            s, idx = self.parser.get_label_word(l2, idx)
            if s == "":
                break
            if idx > 0 and l2[idx - 1] == ':' and idx < len(l2) and l2[idx] == ':':
                idx -= 1
            if idx < len(l2) and l2[idx:idx + 2] == '::':
                idx += 2
                _rt_start = idx
                while idx < len(l2) and l2[idx] not in ' \t,:' + chr(0):
                    idx += 1
                _rt_str = l2[_rt_start:idx].strip().lower()
                if _rt_str:
                    _mach_tbl_g = elf_machine_table(self.state)
                    _rtype_g = _reloc_named(self.state, _mach_tbl_g, _rt_str)
                    if _rtype_g is None:
                        self.state.diag(f" warning - unknown reloc type '{_rt_str}' in .GLOBAL"
                                        f" for machine {self.state.elf_machine}", set_error=False)
                    else:
                        _ent_g = self.state.labels.get(s)
                        if _ent_g is not None:
                            while len(_ent_g) < 5:
                                _ent_g.append(None)
                            _ent_g[4] = _rtype_g
            if idx < len(l2) and l2[idx] == ':':
                idx += 1
            v = self.label_manager.get_value(s)
            sec = self.label_manager.get_section(s)
            _lentry = self.state.labels.get(s, [])
            is_equ = len(_lentry) > 2 and _lentry[2]
            self.state.export_labels[s] = [v, sec, is_equ]
            idx = StringUtils.skipspc(l2, idx)
            if idx < len(l2) and l2[idx] == ',':
                idx += 1
        return True

    _RES_UNITS = {'.RESB': 1, '.RESW': 2, '.RESD': 4, '.RESQ': 8}

    def resb_processing(self, l1, l2):
        """`.resb` / `.resw` / `.resd` / `.resq` — バイトを出さず領域だけ予約する。"""
        _directive = StringUtils.upper(l1)
        _mul = self._RES_UNITS.get(_directive)
        if _mul is None:
            return False
        self.state.error_undefined_label = False
        x, idx = self.expr_eval.expression_asm(l2, 0)
        if self.state.error_undefined_label:
            self.state.diag(f" error - {_directive} argument contains undefined label.", set_error=True)
            return True
        try:
            x = int(x)
        except (OverflowError, ValueError):
            self.state.diag(f" error - {_directive} argument is non-finite or invalid.", set_error=True)
            return True
        if x < 0:
            self.state.diag(f" error - {_directive} requires a non-negative count, got {x}.", set_error=True)
            return True
        _RESB_MAX = 1 << 28
        if x > _RESB_MAX // _mul:
            self.state.diag(f" error - {_directive} count {x} (x{_mul}) exceeds maximum "
                     f"{_RESB_MAX} words.", set_error=True)
            return True
        self.state.pc += x * _mul
        return True

    def zero_processing(self, l1, l2):
        """`.zero` — ゼロバイトを並べる。"""
        if StringUtils.upper(l1) != ".ZERO":
            return False
        self.state.error_undefined_label = False
        x, idx = self.expr_eval.expression_asm(l2, 0)
        if self.state.error_undefined_label:
            self.state.diag(" error - .ZERO argument contains undefined label.", set_error=True)
            return True
        try:
            x = int(x)
        except (OverflowError, ValueError):
            self.state.diag(" error - .ZERO argument is non-finite or invalid.", set_error=True)
            return True
        if x < 0:
            self.state.diag(f" error - .ZERO requires a non-negative count, got {x}.", set_error=True)
            return True
        _ZERO_MAX = 1 << 28
        if x > _ZERO_MAX:
            self.state.diag(f" error - .ZERO count {x} exceeds maximum {_ZERO_MAX}.", set_error=True)
            return True
        for i in range(x):
            self.binary_writer.outbin2(self.state.pc, 0x00)
            self.state.pc += 1
        return True

    def ascii_processing(self, l1, l2):
        """`.ascii` — 文字列のバイト列を出す。"""
        if StringUtils.upper(l1) != ".ASCII":
            return False
        return self.asciistr(l2)

    def asciiz_processing(self, l1, l2):
        """`.asciz` — 文字列のバイト列と末尾の 0 を出す。"""
        if StringUtils.upper(l1) != ".ASCIZ":
            return False
        if not self.asciistr(l2):
            self.state.diag(" error - .ASCIZ requires a quoted string.", set_error=True)
            return False
        self.binary_writer.outbin(self.state.pc, 0x00)
        self.state.pc += 1
        return True

    def section_processing(self, l1, l2):
        """`.section` / `.segment` — セクションを切り替える。

        これがセクションを切り替える唯一の方法で、`.text` のような短縮形は
        組み込みではない（単独で書けば構文エラー）。
        """
        if StringUtils.upper(l1) != ".SECTION" and StringUtils.upper(l1) != ".SEGMENT":
            return False

        if l2 != '':
            old_sec = self.state.current_section
            if old_sec not in self.state.sections:
                self.state.sections[old_sec] = [0, 0, 0, False]
            old_entry = self.state.sections[old_sec]
            _entry_pc = old_entry[2] if len(old_entry) > 2 else old_entry[0]
            tentative = self.state.pc - _entry_pc
            if tentative > 0:
                old_entry[1] += tentative
                self.state.section_ranges.append((old_sec, _entry_pc, tentative))

            self.state.current_section = l2
            if l2 not in self.state.sections:
                self.state.sections[l2] = [self.state.pc, 0, self.state.pc, False]
            else:
                existing_start     = self.state.sections[l2][0]
                existing_size      = self.state.sections[l2][1]
                existing_confirmed = len(self.state.sections[l2]) > 3 and self.state.sections[l2][3]
                if existing_size == 0 and not existing_confirmed:
                    new_start = self.state.pc
                else:
                    new_start = min(existing_start, self.state.pc)

                self.state.sections[l2] = [new_start, existing_size, self.state.pc, False]
        return True

    def align_processing(self, l1, l2):
        """`.align` — 整列する。引数なしなら前回（または既定）の値を使う。"""
        if StringUtils.upper(l1) != ".ALIGN":
            return False

        if l2 != '':
            self.state.error_undefined_label = False
            u, idx = self.expr_eval.expression_asm(l2, 0)
            if self.state.error_undefined_label:
                self.state.diag(" error - .ALIGN argument contains undefined label.", set_error=True)
                return True
            try:
                u_int = int(u)
            except (OverflowError, ValueError):
                self.state.diag(" error - .ALIGN argument is non-finite or invalid.", set_error=True)
                return True
            if u_int <= 0:
                self.state.diag(f" error - .ALIGN requires a positive value, got {u_int}.", set_error=True)
                return True
            self.state.align = u_int

        _sec_rel = self.label_manager._section_relative_offset(
            self.state.current_section, self.state.pc)
        _base = _sec_rel if _sec_rel is not None else self.state.pc
        _padding = self.binary_writer.align_(_base) - _base
        self.state.pc += _padding
        return True

    def endsection_processing(self, l1, l2):
        """`.endsection` / `.endsegment` — セクションを閉じる。"""
        if StringUtils.upper(l1) != ".ENDSECTION" and StringUtils.upper(l1) != ".ENDSEGMENT":
            return False
        if self.state.current_section not in self.state.sections:
            self.state.diag(f" error - .ENDSECTION without matching .SECTION for '{self.state.current_section}'.", set_error=True)
            return True
        entry = self.state.sections[self.state.current_section]
        start = entry[0]
        entry_pc = entry[2] if len(entry) > 2 else start
        block_size = self.state.pc - entry_pc
        if block_size < 0:
            self.state.diag(f" warning - ENDSECTION: computed block size {block_size} < 0 for "
                 f"'{self.state.current_section}'; keeping previous size.", set_error=False)
            return True
        new_size = entry[1] + block_size
        if block_size > 0:
            self.state.section_ranges.append((self.state.current_section, entry_pc, block_size))
        self.state.sections[self.state.current_section] = [start, new_size, self.state.pc, True]
        return True

    def extern_processing(self, l1, l2):
        """`.extern` / `.global` — シンボルを外部と結び付ける。"""
        if StringUtils.upper(l1) != ".EXTERN":
            return False

        idx = 0
        l2 = l2 + chr(0)
        while idx < len(l2) and l2[idx] != chr(0):
            idx = StringUtils.skipspc(l2, idx)
            label_part, idx = self.parser.get_label_word(l2, idx)
            if not label_part:
                break

            if idx > 0 and l2[idx - 1] == ':' and idx < len(l2) and l2[idx] == ':':
                idx -= 1

            _em_ext = self.state.elf_machine
            _mach_tbl_ext = elf_machine_table(self.state)
            reloc_type = _mach_tbl_ext['extern_default']
            explicit_reloc_type = False
            if idx < len(l2) and l2[idx:idx + 2] == '::':
                idx += 2
                rt_start = idx
                while idx < len(l2) and l2[idx] not in ' \t,:' + chr(0):
                    idx += 1
                rt_str = l2[rt_start:idx].strip().lower()

                if rt_str:
                    reloc_type = _reloc_named(self.state, _mach_tbl_ext, rt_str)
                    if reloc_type is None:
                        self.state.diag(f" warning - unknown reloc type '{rt_str}' in .EXTERN"
                             f" for machine {_em_ext}", set_error=False)
                    else:
                        explicit_reloc_type = True

            if idx < len(l2) and l2[idx] == ':':
                idx += 1

            existing = self.state.labels.get(label_part)

            if explicit_reloc_type:
                self.state.extern_untyped.discard(label_part)
            elif existing is None:
                self.state.extern_untyped.add(label_part)

            if existing is None:
                self.state.labels[label_part] = [0, '.text', False, True, reloc_type]
            elif len(existing) > 3 and existing[3]:

                if len(existing) >= 5 and explicit_reloc_type:
                    existing[4] = reloc_type
            else:
                self.state.diag(f" warning - .EXTERN: '{label_part}' is already defined"
                     f" locally; ignoring extern declaration", set_error=False)

            idx = StringUtils.skipspc(l2, idx)
            if idx < len(l2) and l2[idx] == ',':
                idx += 1

        return True


    def _sym_decl_scan(self, l2, nfields):
        """シンボル属性ディレクティブの欄を切り出す。"""
        out = []
        idx = 0
        buf = l2 + chr(0)
        while idx < len(buf) and buf[idx] != chr(0):
            idx = StringUtils.skipspc(buf, idx)
            name, idx = self.parser.get_label_word(buf, idx)
            if not name:
                break
            if idx > 0 and buf[idx - 1] == ':' and idx < len(buf) and buf[idx] == ':':
                idx -= 1
            fields = []
            while len(fields) < nfields and buf[idx:idx + 2] == '::':
                idx += 2
                _s = idx
                while idx < len(buf) and buf[idx] not in ' \t,:' + chr(0):
                    idx += 1
                fields.append(buf[_s:idx].strip())
            while len(fields) < nfields:
                fields.append('')
            if idx < len(buf) and buf[idx] == ':':
                idx += 1
            out.append((name, fields))
            idx = StringUtils.skipspc(buf, idx)
            if idx < len(buf) and buf[idx] == ',':
                idx += 1
        return out

    def _sym_decl_num(self, dname, name, text, lo, hi):
        """シンボル属性の数値欄を lo..hi の整数として読む。"""
        if not text:
            self.state.diag(f" error - {dname}: a number is required for '{name}'.",
                            set_error=True)
            return None
        self.state.error_undefined_label = False
        v, _idx = self.expr_eval.expression_asm(text, 0)
        _undef = _is_undef_derived(v)
        try:
            v = int(v)
        except (OverflowError, ValueError):
            v = None
        if self.state.error_undefined_label or _undef or v is None \
                or v < lo or v > hi:
            self.state.diag(f" error - {dname}: value for '{name}' must be an integer "
                            f"in {lo}..{hi}, got '{text}'.", set_error=True)
            v = None
        self.state.error_undefined_label = False
        return v

    def _sym_declare_extern(self, name):
        """その名前を外部シンボルとして登録する。"""
        if name in self.state.labels:
            return
        reloc_type = elf_machine_table(self.state)['extern_default']
        self.state.extern_untyped.add(name)
        self.state.labels[name] = [0, '.text', False, True, reloc_type]

    def type_processing(self, l1, l2):
        """`.type` — ELF シンボルの種別（STT_*）を書く。"""
        if StringUtils.upper(l1) != ".TYPE":
            return False
        if not self.state.should_report_errors():
            return True
        for name, f in self._sym_decl_scan(l2, 1):
            kind = f[0].lower()
            if not kind:
                self.state.diag(f" error - .TYPE: a symbol type is required for "
                                f"'{name}'.", set_error=True)
                continue
            v = ELF_SYM_TYPES.get(kind)
            if v is None:
                v = self._sym_decl_num('.TYPE', name, kind, 0, 15)
                if v is None:
                    continue
            _sym_attr_slot(self.state, name)[_SA_TYPE] = v
        return True

    def size_processing(self, l1, l2):
        """`.size` — シンボルの大きさを書く。値はワード数で、出力時に幅をかける。"""
        if StringUtils.upper(l1) != ".SIZE":
            return False
        if not self.state.should_report_errors():
            return True
        for name, f in self._sym_decl_scan(l2, 1):
            v = self._sym_decl_num('.SIZE', name, f[0], 0, 0x7FFFFFFFFFFFFFFF)
            if v is None:
                continue
            a = _sym_attr_slot(self.state, name)
            a[_SA_SIZE_SET] = 1
            a[_SA_SIZE] = v
        return True

    def weak_processing(self, l1, l2):
        """`.weak` — 弱シンボルにする（バインドが STB_WEAK になる）。"""
        if StringUtils.upper(l1) != ".WEAK":
            return False
        _record = self.state.should_report_errors()
        for name, _f in self._sym_decl_scan(l2, 0):
            self._sym_declare_extern(name)
            if not _record:
                continue
            _sym_attr_slot(self.state, name)[_SA_WEAK] = 1
            _lentry = self.state.labels.get(name, [])
            _is_imported = len(_lentry) > 3 and _lentry[3]
            if not _is_imported:
                v = self.label_manager.get_value(name)
                sec = self.label_manager.get_section(name)
                is_equ = len(_lentry) > 2 and _lentry[2]
                self.state.export_labels[name] = [v, sec, is_equ]
        return True

    _VIS_DIRS = {'.HIDDEN': 2, '.PROTECTED': 3, '.INTERNAL': 1}

    def visibility_processing(self, l1, l2):
        """`.hidden` / `.protected` / `.internal` — 可視性を書く。"""
        vis = self._VIS_DIRS.get(StringUtils.upper(l1))
        if vis is None:
            return False
        if not self.state.should_report_errors():
            return True
        for name, _f in self._sym_decl_scan(l2, 0):
            a = _sym_attr_slot(self.state, name)
            a[_SA_OTHER] = (a[_SA_OTHER] & ~0x03) | vis
        return True

    def other_processing(self, l1, l2):
        """`.other` — st_other バイトを丸ごと置き換える。"""
        if StringUtils.upper(l1) != ".OTHER":
            return False
        if not self.state.should_report_errors():
            return True
        for name, f in self._sym_decl_scan(l2, 1):
            v = self._sym_decl_num('.OTHER', name, f[0], 0, 255)
            if v is None:
                continue
            _sym_attr_slot(self.state, name)[_SA_OTHER] = v
        return True

    def comm_processing(self, l1, l2):
        """`.comm` — 共通シンボル（SHN_COMMON）にする。"""
        if StringUtils.upper(l1) != ".COMM":
            return False
        _record = self.state.should_report_errors()
        for name, f in self._sym_decl_scan(l2, 2):
            self._sym_declare_extern(name)
            if not _record:
                continue
            sz = self._sym_decl_num('.COMM', name, f[0], 0, 0x7FFFFFFFFFFFFFFF)
            if sz is None:
                continue
            al = 1
            if f[1]:
                al = self._sym_decl_num('.COMM', name, f[1], 0, 0x40000000)
                if al is None:
                    continue
                if al & (al - 1):
                    self.state.diag(" error - .COMM: alignment must be 0 or a power "
                                    f"of two, got '{al}' for '{name}'.", set_error=True)
                    continue
            a = _sym_attr_slot(self.state, name)
            a[_SA_COMMON] = 1
            a[_SA_SIZE_SET] = 1
            a[_SA_SIZE] = sz
            a[_SA_ALIGN] = al
            if a[_SA_TYPE] == 0:
                a[_SA_TYPE] = 1
        return True

    def reloctype_processing(self, l1, l2):
        """`.reloctype` — このソースでの幅推測リロケーション型を上書きする。"""
        if StringUtils.upper(l1) != ".RELOCTYPE":
            return False

        _mach_tbl_rt = elf_machine_table(self.state)
        if not _mach_tbl_rt['named']:
            self.state.diag(f" warning - .RELOCTYPE: no relocation type is known for "
                 f"machine {self.state.elf_machine}; declare them with .elftype", set_error=False)
            return True

        _widths = (1, 2, 4, 8)
        _parts = l2.split(',') if l2 else []
        for _i, _raw_name in enumerate(_parts):
            if _i >= len(_widths):
                self.state.diag(" warning - .RELOCTYPE: too many arguments (only "
                     "4 widths -- 8/16/32/64-bit -- are supported)", set_error=False)
                break
            _name = _raw_name.strip().lower()
            if not _name:
                continue
            _rtype = _reloc_named(self.state, _mach_tbl_rt, _name)
            if _rtype is None:
                self.state.diag(f" warning - unknown reloc type '{_name}' in "
                     f".RELOCTYPE for machine {self.state.elf_machine}", set_error=False)
                continue
            _expected_width = _widths[_i]
            _actual_width = _mach_tbl_rt['reloc_bytes'].get(_rtype)
            if _actual_width is not None and _actual_width != _expected_width:
                self.state.diag(f" warning - .RELOCTYPE: '{_name}' is a "
                     f"{_actual_width * 8}-bit relocation type, but was given "
                     f"in the {_expected_width * 8}-bit position; ignored", set_error=False)
                continue
            self.state.reloctype_override[_expected_width] = _rtype

        return True

    def org_processing(self, l1, l2):
        """`.org` — ロケーションカウンタを設定する。

        `,p` を付けると、カウンタが目標より下にある場合その隙間を埋める。
        """
        if StringUtils.upper(l1) != ".ORG":
            return False
        self.state.error_undefined_label = False
        u, idx = self.expr_eval.expression_asm(l2, 0)
        if self.state.error_undefined_label:
            self.state.diag(" error - .ORG argument contains undefined label.", set_error=True)
            return True
        try:
            u = int(u)
        except (OverflowError, ValueError):
            self.state.diag(" error - .ORG argument is non-finite or invalid.", set_error=True)
            return True
        if u < 0:
            self.state.diag(f" error - .ORG address must be non-negative, got {u}.", set_error=True)
            return True
        if idx + 2 <= len(l2) and l2[idx:idx + 2].upper() == ',P':
            if u > self.state.pc:
                _ORG_FILL_MAX = 1 << 28
                fill_count = u - self.state.pc
                if fill_count > _ORG_FILL_MAX:
                    self.state.diag(f" error - .ORG ,P fill count {fill_count} exceeds maximum {_ORG_FILL_MAX}.", set_error=True)
                    return True
                for i in range(fill_count):
                    self.binary_writer.outbin2(i + self.state.pc, self.state.padding)
        self.state.pc = u
        return True




_MACRO_MAX_DEPTH = 200
_MACRO_MAX_ITER = 1000000
_MACRO_MAX_LINES = 2000000
_MACRO_MAX_INCLUDE_DEPTH = 64

_MACRO_KEYWORDS = frozenset((
    'if', 'then', 'else', 'elif', 'while', 'def', 'return', 'set', 'local',
    'break', 'continue', 'error', 'warning', 'echo', 'include', 'undef',
))


class MacroError(Exception):
    """マクロ展開中のエラー。位置を含む文言を持つ。"""

    def __init__(self, msg):
        super().__init__(msg)
        self.msg = msg


class _MacroBreak(Exception):
    """`!break` を `!while` へ伝えるための内部例外。"""
    pass


class _MacroContinue(Exception):
    """`!continue` を `!while` へ伝えるための内部例外。"""
    pass


class _MacroReturn(Exception):
    """`!return` を呼び出し元へ伝えるための内部例外。値を持つ。"""
    def __init__(self, value):
        super().__init__(value)
        self.value = value


class _MacroFunc:
    """`!def` で定義されたマクロ 1 個。引数名、既定値、本文、定義位置。"""

    __slots__ = ('name', 'params', 'defaults', 'body', 'pos')

    def __init__(self, name, params, defaults, body, pos):
        self.name = name
        self.params = params
        self.defaults = defaults
        self.body = body
        self.pos = pos


def _sext_tick_at(s, i):
    """その位置の `'` が符号拡張演算子か（文字定数の引用符ではないか）。"""
    j = i + 1
    while j < len(s) and s[j] in ' \t':
        j += 1
    return j < len(s) and (s[j].isdigit() or s[j] == '(')


def _fmt_pos(pos):
    """診断に出す「ファイル:行」の形に整える。"""
    return f"{pos[0]}:{pos[1]}"


def _strip_comment(text, pat_mode=False):
    """マクロ行のコメントを落とす。

    ソース側は `;`、パターン側は `/* */` がコメントなので、pat_mode で
    切り替える。文字列リテラルの中は触らない。
    """
    quote = ''
    i = 0
    while i < len(text):
        c = text[i]
        if quote:
            if c == '\\':
                i += 2
                continue
            if c == quote:
                quote = ''
        elif c == '"':
            quote = c
        elif c == "'":
            if text.find("'", i + 1) >= 0:
                quote = c
        elif pat_mode:
            if c == '/' and text[i + 1:i + 2] == '*':
                return text[:i].rstrip()
        elif c == ';':
            return text[:i].rstrip()
        i += 1
    return text.rstrip()



class _ExprParser:
    """マクロ層の式を解析して値にする。優先順位ごとに 1 メソッドの再帰下降。

    値は整数と文字列の 2 種類で、演算子は C に倣う。本体の式評価器とは
    別物なので、`%` の符号（C と同じ被除数の符号）と `'` の結合位置が違う。
    `@` `'` `*(x,y)` は本体と同じ実装を呼ぶので意味は一致する。
    """

    __slots__ = ('s', 'i', 'n', 'pp', 'pos', 'suppress')

    def __init__(self, text, pp, pos):
        self.s = text
        self.i = 0
        self.n = len(text)
        self.pp = pp
        self.pos = pos
        self.suppress = 0


    def err(self, msg):
        """現在位置を添えて MacroError にする。"""
        raise MacroError(f"{_fmt_pos(self.pos)}: macro expression: {msg} in {self.s!r}")

    def skip(self):
        """空白を飛ばす。"""
        s = self.s
        i = self.i
        n = self.n
        while i < n and s[i] in ' \t':
            i += 1
        self.i = i

    def peek(self, n=1):
        """先の文字を消費せずに見る。"""
        self.skip()
        return self.s[self.i:self.i + n]

    def eat(self, tok):
        """次がそのトークンなら消費して真。"""
        self.skip()
        if self.s.startswith(tok, self.i):
            if tok[-1].isalpha():
                j = self.i + len(tok)
                if j < self.n and (self.s[j].isalnum() or self.s[j] == '_'):
                    return False
            self.i += len(tok)
            return True
        return False

    def expect(self, tok):
        """そのトークンを必ず消費する。無ければエラー。"""
        if not self.eat(tok):
            self.err(f"expected {tok!r}")

    def at_end(self):
        """読み切ったか。"""
        self.skip()
        return self.i >= self.n


    def parse(self):
        """式を 1 個解析して値を返す。"""
        v = self.ternary()
        if not self.at_end():
            self.err(f"unexpected trailing text {self.s[self.i:]!r}")
        return v

    def ternary(self):
        """`?:`。"""
        c = self.logic_or()
        if self.eat('?'):
            if _truth(c):
                a = self.ternary()
                self.expect(':')
                self.suppress += 1
                try:
                    self.ternary()
                finally:
                    self.suppress -= 1
                return a
            else:
                self.suppress += 1
                try:
                    self.ternary()
                finally:
                    self.suppress -= 1
                self.expect(':')
                b = self.ternary()
                return b
        return c

    def logic_or(self):
        """`||`。"""
        v = self.logic_and()
        while self.eat('||'):
            if _truth(v):
                self.suppress += 1
                try:
                    self.logic_and()
                finally:
                    self.suppress -= 1
                v = 1
            else:
                r = self.logic_and()
                v = 1 if _truth(r) else 0
        return v

    def logic_and(self):
        """`&&`。"""
        v = self.sext()
        while self.eat('&&'):
            if not _truth(v):
                self.suppress += 1
                try:
                    self.sext()
                finally:
                    self.suppress -= 1
                v = 0
            else:
                r = self.sext()
                v = 1 if _truth(r) else 0
        return v

    def sext(self):
        """`'` — 符号拡張。マクロ層ではビット演算より緩く `&&` よりきつい。

        本体の評価器での位置（`^` と比較の間）とは違う。マクロ層の優先順位が
        C に倣っていて、そこでは比較がビット演算よりきつく結合するため。
        """
        v = self.bit_or()
        while True:
            self.skip()
            if self.i >= len(self.s) or self.s[self.i] != "'":
                break
            if not _sext_tick_at(self.s, self.i):
                break
            self.i += 1
            t = self.bit_or()
            v, _warn, _go = op_sext(_as_int(self, v), _as_int(self, t))
            if _warn and not self.suppress:
                self.pp.warn(f"{_fmt_pos(self.pos)}: {_warn}")
            if not _go:
                break
        return v

    def bit_or(self):
        """`|`。"""
        v = self.bit_xor()
        while True:
            self.skip()
            if self.s.startswith('||', self.i):
                break
            if self.eat('|'):
                v = _as_int(self, v) | _as_int(self, self.bit_xor())
            else:
                break
        return v

    def bit_xor(self):
        """`^`。"""
        v = self.bit_and()
        while self.eat('^'):
            v = _as_int(self, v) ^ _as_int(self, self.bit_and())
        return v

    def bit_and(self):
        """`&`。"""
        v = self.equality()
        while True:
            self.skip()
            if self.s.startswith('&&', self.i):
                break
            if self.eat('&'):
                v = _as_int(self, v) & _as_int(self, self.equality())
            else:
                break
        return v

    def equality(self):
        """`==` `!=`。"""
        v = self.relational()
        while True:
            if self.eat('=='):
                v = 1 if _cmp_eq(v, self.relational()) else 0
            elif self.eat('!='):
                v = 0 if _cmp_eq(v, self.relational()) else 1
            else:
                return v

    def relational(self):
        """`<` `<=` `>` `>=`。"""
        v = self.shift()
        while True:
            self.skip()
            if self.eat('<='):
                v = 1 if _cmp_lt_eq(self, v, self.shift(), True) else 0
            elif self.eat('>='):
                v = 1 if _cmp_lt_eq(self, self.shift(), v, True) else 0
            elif self.eat('<'):
                v = 1 if _cmp_lt_eq(self, v, self.shift(), False) else 0
            elif self.eat('>'):
                v = 1 if _cmp_lt_eq(self, self.shift(), v, False) else 0
            else:
                return v

    def shift(self):
        """`<<` `>>`。"""
        v = self.additive()
        while True:
            if self.eat('<<'):
                r = _as_int(self, self.additive())
                if r < 0 or r > 4096:
                    if self.suppress:
                        r = 0
                    else:
                        self.err("shift count out of range")
                v = _as_int(self, v) << r
            elif self.eat('>>'):
                r = _as_int(self, self.additive())
                if r < 0 or r > 4096:
                    if self.suppress:
                        r = 0
                    else:
                        self.err("shift count out of range")
                v = _as_int(self, v) >> r
            else:
                return v

    def additive(self):
        """`+` `-`。どちらかが文字列なら `+` は連結。"""
        v = self.multiplicative()
        while True:
            self.skip()
            if self.s.startswith('+', self.i):
                self.i += 1
                r = self.multiplicative()
                if isinstance(v, str) or isinstance(r, str):
                    v = _as_str(v) + _as_str(r)
                else:
                    v = v + r
            elif self.s.startswith('-', self.i):
                self.i += 1
                v = _as_int(self, v) - _as_int(self, self.multiplicative())
            else:
                return v

    def multiplicative(self):
        """`*` `/` `%`。`/` と `%` は C と同じゼロ方向の切り捨て。

        文字列 `* 整数` は繰り返し。
        """
        v = self.unary()
        while True:
            self.skip()
            if self.s.startswith('*', self.i):
                self.i += 1
                r = self.unary()
                if isinstance(v, str) and isinstance(r, int):
                    v = v * max(0, r)
                elif isinstance(v, int) and isinstance(r, str):
                    v = r * max(0, v)
                else:
                    v = _as_int(self, v) * _as_int(self, r)
            elif self.s.startswith('/', self.i):
                self.i += 1
                r = _as_int(self, self.unary())
                if r == 0:
                    if self.suppress:
                        v = 0
                    else:
                        self.err("division by zero")
                else:
                    v = _c_div(_as_int(self, v), r)
            elif self.s.startswith('%', self.i):
                self.i += 1
                r = _as_int(self, self.unary())
                if r == 0:
                    if self.suppress:
                        v = 0
                    else:
                        self.err("modulo by zero")
                else:
                    v = _c_mod(_as_int(self, v), r)
            else:
                return v

    def unary(self):
        """単項 `-` `+` `~` `!`。"""
        self.skip()
        if self.eat('!'):
            return 0 if _truth(self.unary()) else 1
        if self.eat('~'):
            return ~_as_int(self, self.unary())
        if self.eat('-'):
            return -_as_int(self, self.unary())
        if self.eat('+'):
            return self.unary()
        if self.eat('@'):
            return op_msb(_as_int(self, self.unary()))
        if self.i < len(self.s) and self.s[self.i] == '*' \
                and self.s[self.i + 1:self.i + 2] == '(':
            self.i += 2
            x = self.ternary()
            self.expect(',')
            n = self.ternary()
            self.expect(')')
            v, _err = op_byte(_as_int(self, x), _as_int(self, n))
            if _err and not self.suppress:
                self.err(_err)
            return v
        return self.primary()

    def primary(self):
        """項そのもの。数値、文字列、名前、`(式)`、組み込み関数、`@` `*(x,y)`。"""
        self.skip()
        if self.i >= len(self.s):
            self.err("unexpected end of expression")
        c = self.s[self.i]

        if c == '(':
            self.i += 1
            v = self.ternary()
            self.expect(')')
            return v

        if c == '"':
            return self.read_string('"')

        if c == "'":
            t = self.read_string("'")
            if len(t) == 1:
                return ord(t)
            return t

        if c == '$':
            self.i += 1
            if self.s[self.i:self.i + 1] == '$':
                self.i += 1
            return self.pp.loc_counter(self.pos)

        if c.isdigit():
            return self.read_number()

        if c == '_' or c.isalpha():
            name = self.read_ident()
            if name == 'defined':
                self.expect('(')
                inner = self.read_ident()
                self.expect(')')
                return 1 if self.pp.is_defined(inner) else 0
            if self.peek() == '(':
                self.i += 1
                args = []
                if self.peek() == ')':
                    self.i += 1
                else:
                    while True:
                        args.append(self.ternary())
                        if self.eat(','):
                            continue
                        self.expect(')')
                        break
                if self.suppress:
                    return 0
                return self.pp.call_value(name, args, self.pos)
            if self.suppress:
                return 0
            return self.pp.lookup(name, self.pos)

        self.err(f"unexpected character {c!r}")

    def read_ident(self):
        """識別子を 1 個読む。"""
        self.skip()
        j = self.i
        while j < len(self.s) and (self.s[j].isalnum() or self.s[j] == '_'):
            j += 1
        if j == self.i:
            self.err("expected a name")
        name = self.s[self.i:j]
        self.i = j
        return name

    def read_number(self):
        """整数リテラルを読む。10 進・`0x`・`0b`・`0o`、アンダースコア可。"""
        s = self.s
        j = self.i
        if s.startswith('0x', j) or s.startswith('0X', j):
            k = j + 2
            while k < len(s) and (s[k] in '0123456789abcdefABCDEF_'):
                k += 1
            txt, base = s[j + 2:k], 16
        elif s.startswith('0b', j) or s.startswith('0B', j):
            k = j + 2
            while k < len(s) and s[k] in '01_':
                k += 1
            txt, base = s[j + 2:k], 2
        elif s.startswith('0o', j) or s.startswith('0O', j):
            k = j + 2
            while k < len(s) and s[k] in '01234567_':
                k += 1
            txt, base = s[j + 2:k], 8
        else:
            k = j
            while k < len(s) and (s[k].isdigit() or s[k] == '_'):
                k += 1
            txt, base = s[j:k], 10
        txt = txt.replace('_', '')
        if txt == '':
            self.err("malformed number")
        self.i = k
        try:
            return int(txt, base)
        except ValueError:
            self.err("malformed number")

    def read_string(self, q):
        """文字列リテラルを読む。`'A'` は 1 文字なら文字コードになる。"""
        s = self.s
        j = self.i + 1
        out = []
        while j < len(s):
            ch = s[j]
            if ch == '\\' and j + 1 < len(s):
                nxt = s[j + 1]
                out.append({'n': '\n', 't': '\t', 'r': '\r', '0': '\0',
                            '\\': '\\', '"': '"', "'": "'"}.get(nxt, nxt))
                j += 2
                continue
            if ch == q:
                self.i = j + 1
                return ''.join(out)
            out.append(ch)
            j += 1
        self.err("unterminated string literal")


def _truth(v):
    """マクロ層での真偽判定。"""
    if isinstance(v, str):
        return v != ''
    return v != 0


def _as_int(p, v):
    """値を整数として要求する。"""
    if isinstance(v, str):
        if getattr(p, 'suppress', 0):
            return 0
        p.err(f"expected an integer, got the string {v!r}")
    return v


def _as_str(v):
    """値を文字列として読む。"""
    return v if isinstance(v, str) else str(v)


def _echo_write(items):
    """`!echo` / `.echo` の出力を標準エラーへ書く。

    マクロ層とミニ言語で同じ体裁にするため、書き出しは 1 か所にしてある。
    """
    print(' '.join(_as_str(x) for x in items), file=sys.stderr)


_ECHO_CACHE = {}


def _echo_str_unescape(s):
    """`.echo` の文字列リテラルのエスケープを開く。"""
    out = []
    k = 0
    n = len(s)
    while k < n:
        c = s[k]
        if c == '\\':
            if k + 1 >= n:
                return None, "dangling '\\' in a string"
            e = _MINI_ESC.get(s[k + 1])
            if e is None:
                return None, f"unknown escape '\\{s[k + 1]}' in a string"
            out.append(e)
            k += 2
            continue
        out.append(c)
        k += 1
    return ''.join(out), None


def _echo_items_parse(text):
    """`.echo` の引数を、文字列と式の並びに割る。"""
    n = len(text)
    i = 0
    while i < n and text[i] in ' \t':
        i += 1
    if i >= n or text[i] != '(':
        return None, "needs '.echo(item, item, ...)'"
    i += 1
    start = i
    end = -1
    depth = 0
    instr = False
    while i < n:
        c = text[i]
        if instr:
            if c == '\\':
                i += 2
                continue
            if c == '"':
                instr = False
            i += 1
            continue
        if c == '"':
            instr = True
        elif c in '([{':
            depth += 1
        elif c in ')]}':
            if depth == 0 and c == ')':
                end = i
                break
            if depth > 0:
                depth -= 1
        i += 1
    if end < 0:
        return None, "missing ')'"
    for c in text[end + 1:]:
        if c not in ' \t':
            return None, "unexpected text after '.echo(...)'"
    inner = text[start:end]

    parts = []
    buf = []
    depth = 0
    instr = False
    k = 0
    m = len(inner)
    while k < m:
        c = inner[k]
        if instr:
            buf.append(c)
            if c == '\\' and k + 1 < m:
                buf.append(inner[k + 1])
                k += 2
                continue
            if c == '"':
                instr = False
            k += 1
            continue
        if c == '"':
            instr = True
        elif c in '([{':
            depth += 1
        elif c in ')]}':
            if depth > 0:
                depth -= 1
        elif c == ',' and depth == 0:
            parts.append(''.join(buf))
            buf = []
            k += 1
            continue
        buf.append(c)
        k += 1
    parts.append(''.join(buf))
    if len(parts) == 1 and parts[0].strip() == '':
        return [], None

    items = []
    for p in parts:
        p = p.strip()
        if p == '':
            return None, "empty item in the argument list"
        if p[0] == '"':
            j = 1
            pl = len(p)
            while j < pl:
                if p[j] == '\\':
                    j += 2
                    continue
                if p[j] == '"':
                    break
                j += 1
            if j >= pl:
                return None, f"unterminated string: '{p}'"
            if j != pl - 1:
                return None, f"unexpected text after a string: '{p}'"
            sv, err = _echo_str_unescape(p[1:j])
            if err is not None:
                return None, err
            items.append(('s', sv))
        else:
            items.append(('e', p))
    return items, None


def _echo_items_cached(text):
    """同じ `.echo` 行の解析結果を覚えて使い回す。"""
    ent = _ECHO_CACHE.get(text)
    if ent is None:
        ent = _echo_items_parse(text)
        if len(_ECHO_CACHE) >= 65536:
            _ECHO_CACHE.clear()
        _ECHO_CACHE[text] = ent
    return ent


def _cmp_eq(a, b):
    """`==` の比較。整数と文字列が混ざる場合の規則をここに閉じる。"""
    if isinstance(a, str) != isinstance(b, str):
        return False
    return a == b


def _cmp_lt_eq(p, a, b, or_equal):
    """`<` と `<=` の比較。"""
    if isinstance(a, str) != isinstance(b, str):
        if getattr(p, 'suppress', 0):
            return False
        p.err("cannot order a string against an integer")
    return (a <= b) if or_equal else (a < b)


def _c_div(a, b):
    """C と同じゼロ方向の切り捨て除算（`-7/2 == -3`）。"""
    q = abs(a) // abs(b)
    return q if (a >= 0) == (b >= 0) else -q


def _c_mod(a, b):
    """C と同じ剰余。結果は被除数の符号に従う（`-7%3 == -1`）。"""
    return a - _c_div(a, b) * b



class MacroPreprocessor:
    """行指向のマクロ層。アセンブラ本体の前に走るソース間変換。

    文はすべて行頭の `!` で始まる（`!def` `!if` `!while` `!set` ...）。補間は
    `!{式}` で、`!{式:04x}` の書式指定は Python のフォーマットミニ言語。

    ソース側のマクロはラベル値・`.equ`・`$` / `$$` を読めるが、見えるのは
    *前回の*リラクゼーション反復の値（最初の反復では未定義）。展開が反復ごとに
    変わりうるので、収束はリラクゼーションループ自体が強制する。
    パターンファイル側のマクロはソースのアセンブル前に走るため、ラベルも
    ロケーションカウンタも存在しない（pat_mode がそれを表す）。

    caxx.c と同じ仕様だが、数の表現だけ違う。こちらは多倍長整数、
    あちらは int64。食い違うのはマクロ時の計算が 64bit を超える場合だけで、
    マクロ層はテキストを出すので本体の 256bit 式評価には影響しない。
    """

    def __init__(self, state=None, pat_mode=False):
        self.state = state
        self.pat_mode = pat_mode
        self.reset()


    def reset(self):
        """状態をすべて初期化する。"""
        self.enabled = True
        self.had_error = False
        self._reported = set()
        self.reset_pass()

    def reset_pass(self):
        """1 パスぶんの状態を初期化する（定義・スコープ・出力）。"""
        self.funcs = {}
        self.declared = set()
        self.globals = {}
        self.scopes = [self.globals]
        self.out = []
        self.depth = 0
        self.uid = 0
        self.include_stack = []
        self._expand_key = None


    def scope(self):
        """現在のスコープ（変数の辞書）。"""
        return self.scopes[-1]

    def asm_label(self, name):
        """ラベルの値を引く。返り値は (種別, 値)。

        種別は 'val'（前回の反復の値がある）、'unk'（名前は知っているが値が
        まだ無い）、'no'（そんな名前は無い）。パターンファイル側のマクロでは
        常に 'no' で、読めるラベルがそもそも存在しない。
        """
        if self.pat_mode or self.state is None:
            return ('no', 0)
        values = self.state._macro_label_values
        if values is None:
            return ('unk', 0)
        if name in values:
            return ('val', values[name])
        if name in (self.state._macro_label_names or ()):
            return ('unk', 0)
        return ('no', 0)

    def loc_counter(self, pos):
        """`$` / `$$` の値。前回の反復で記録した行ごとの PC から引く。

        パターンファイル側のマクロではエラーにする。ソースをアセンブルする
        前にロケーションカウンタは存在しない。
        """
        if self.pat_mode or self.state is None:
            raise MacroError(f"{_fmt_pos(pos)}: '$'/'$$' is not available in "
                             f"pattern-file macros (there is no location counter "
                             f"before the source is assembled)")
        pcs = self.state._macro_line_pcs
        if not pcs:
            return 0
        lst = pcs.get(self._expand_key)
        if not lst:
            return 0
        i = len(self.out)
        return lst[i] if 0 <= i < len(lst) else 0

    def lookup(self, name, pos):
        """名前を解決する。内側のスコープから外側へたどる。"""
        for sc in reversed(self.scopes):
            if name in sc:
                return sc[name]
        if name in self.funcs:
            raise MacroError(f"{_fmt_pos(pos)}: macro '{name}' used as a variable "
                             f"(call it as '{name}(...)')")
        _st, _v = self.asm_label(name)
        if _st != 'no':
            return _v
        raise MacroError(f"{_fmt_pos(pos)}: undefined macro variable '{name}'")

    def is_defined(self, name):
        """その名前が定義済みか。"""
        if name in self.funcs:
            return True
        if any(name in sc for sc in self.scopes):
            return True
        return self.asm_label(name)[0] == 'val'

    def assign(self, name, value):
        """`!set` の代入。内側から外側へ探し、無ければ現在のスコープに作る。"""
        for sc in reversed(self.scopes):
            if name in sc:
                sc[name] = value
                return
        self.scope()[name] = value


    def eval(self, text, pos):
        """マクロ式を 1 個評価する。"""
        text = text.strip()
        if text == '':
            raise MacroError(f"{_fmt_pos(pos)}: empty macro expression")
        return _ExprParser(text, self, pos).parse()

    def call_value(self, name, args, pos):
        """マクロを式として呼び、`!return` の値を得る。"""
        if name in _BUILTINS:
            return _BUILTINS[name](self, args, pos)
        if name not in self.funcs:
            raise MacroError(f"{_fmt_pos(pos)}: call to undefined macro '{name}'")
        mark = len(self.out)
        value = self.invoke(self.funcs[name], args, pos)
        if len(self.out) != mark:
            emitted = self.out[mark]
            del self.out[mark:]
            raise MacroError(f"{_fmt_pos(pos)}: macro '{name}' emits source text "
                             f"({emitted[0].strip()!r}) but was called from inside an "
                             f"expression, where there is nowhere to put it")
        return value

    def invoke(self, fn, args, pos):
        """マクロを 1 回展開する。引数を束縛し、新しいスコープで本文を走らせる。"""
        nreq = len(fn.params) - sum(1 for d in fn.defaults if d is not None)
        if len(args) > len(fn.params) or len(args) < nreq:
            raise MacroError(f"{_fmt_pos(pos)}: macro '{fn.name}' takes "
                             f"{nreq}..{len(fn.params)} argument(s), got {len(args)}")
        if self.depth >= _MACRO_MAX_DEPTH:
            raise MacroError(f"{_fmt_pos(pos)}: macro recursion deeper than "
                             f"{_MACRO_MAX_DEPTH} while expanding '{fn.name}'")

        local = {}
        self.scopes.append(local)
        try:
            for k, pname in enumerate(fn.params):
                if k < len(args):
                    local[pname] = args[k]
                else:
                    local[pname] = self.eval(fn.defaults[k], pos)
            self.uid += 1
            local['__id__'] = self.uid
            local['__name__'] = fn.name

            self.depth += 1
            try:
                self.exec_block(fn.body)
            except _MacroReturn as r:
                return r.value
            except (_MacroBreak, _MacroContinue):
                raise MacroError(f"{_fmt_pos(pos)}: '!break'/'!continue' outside a "
                                  f"'!while' loop in macro '{fn.name}'")
            finally:
                self.depth -= 1
            return 0
        finally:
            self.scopes.pop()


    def interpolate(self, text, pos):
        """行の中の `!{式}` を展開する。`\\!{` はリテラルな `!{`。"""
        if '!{' not in text:
            return text
        out = []
        i = 0
        n = len(text)
        while i < n:
            if text[i] == '\\' and text.startswith('!{', i + 1):
                out.append('!{')
                i += 3
                continue
            if not text.startswith('!{', i):
                out.append(text[i])
                i += 1
                continue
            j = i + 2
            depth = 1
            quote = ''
            while j < n:
                c = text[j]
                if quote:
                    if c == '\\':
                        j += 2
                        continue
                    if c == quote:
                        quote = ''
                elif c == "'" and _sext_tick_at(text, j):
                    pass
                elif c in '"\'':
                    quote = c
                elif c == '{':
                    depth += 1
                elif c == '}':
                    depth -= 1
                    if depth == 0:
                        break
                j += 1
            if j >= n:
                raise MacroError(f"{_fmt_pos(pos)}: unterminated '!{{' in line")
            body = text[i + 2:j]
            out.append(self.format_value(body, pos))
            i = j + 1
        return ''.join(out)

    def format_value(self, body, pos):
        """`!{式:書式}` の書式指定を適用する。

        Python のフォーマットミニ言語をそのまま受け、同じ指定を拒否し、
        エラーの文面も caxx.c と合わせる。既知の相違が 2 つある。
        指定の前後の空白を解釈前に落とすので空白を符号とする形式
        （`!{5: d}`）は表現できず、`!{0:c}` はこちらでは NUL 文字を返すが
        C 文字列は内部に NUL を持てないので Caxx では空文字列になる。
        """
        spec = None
        quote = ''
        par = 0
        k = 0
        while k < len(body):
            c = body[k]
            if quote:
                if c == '\\':
                    k += 2
                    continue
                if c == quote:
                    quote = ''
                k += 1
                continue
            if c in '"\'':
                quote = c
            elif c in '([':
                par += 1
            elif c in ')]':
                par -= 1
            elif c == ':' and par == 0:
                if '?' in body[:k]:
                    k += 1
                    continue
                spec = body[k + 1:].strip()
                body = body[:k]
                break
            k += 1
        v = self.eval(body, pos)
        if spec:
            try:
                if isinstance(v, str) and spec[-1:] in ('d', 'x', 'X', 'o', 'b'):
                    raise ValueError
                return format(v, spec)
            except (ValueError, TypeError, OverflowError):
                raise MacroError(f"{_fmt_pos(pos)}: bad format spec ':{spec}' "
                                 f"for value {v!r}")
        return _as_str(v)


    @staticmethod
    def statement_word(text):
        """行頭の `!` 文のキーワードと残りを取り出す。"""
        t = text.lstrip()
        if not t.startswith('!') or t.startswith('!!'):
            return None, None
        j = 1
        while j < len(t) and (t[j].isalnum() or t[j] == '_'):
            j += 1
        if j == 1:
            return None, None
        return t[1:j], t[j:]

    def parse_block(self, lines, i, depth):
        """1 ブロックを構文木にする。入れ子の深さに上限がある。"""
        nodes = []
        n = len(lines)
        while i < n:
            text, fn, ln = lines[i]
            pos = (fn, ln)
            stripped = text.strip()

            if stripped.startswith('}') and depth > 0:
                return nodes, i

            word, rest = self.statement_word(_strip_comment(text, self.pat_mode))
            if word is None:
                nodes.append(('text', text, pos))
                i += 1
                continue

            lw = word.lower()
            if lw not in _MACRO_KEYWORDS and word not in self.funcs \
                    and word not in self.declared and not self.looks_like_call(rest):
                nodes.append(('text', text, pos))
                i += 1
                continue

            if lw == 'if':
                node, i = self.parse_if(lines, i, depth)
                nodes.append(node)
                continue
            if lw == 'while':
                node, i = self.parse_while(lines, i, depth)
                nodes.append(node)
                continue
            if lw == 'def':
                node, i = self.parse_def(lines, i, depth)
                nodes.append(node)
                continue
            if lw in ('else', 'elif', 'then'):
                raise MacroError(f"{_fmt_pos(pos)}: '!{word}' without a matching '!if'")
            nodes.append(self.parse_simple(lw, word, rest, pos))
            i += 1
        if depth > 0:
            fn, ln = (lines[-1][1], lines[-1][2]) if lines else ('?', 0)
            raise MacroError(f"{fn}:{ln}: unexpected end of file: a macro block "
                             f"opened with '{{' is never closed")
        return nodes, i

    @staticmethod
    def looks_like_call(rest):
        """行の残りがマクロ呼び出しの形か。"""
        r = rest.strip()
        return r.startswith('(')

    def parse_simple(self, lw, word, rest, pos):
        """単純文 1 個を解析する。"""
        if lw == 'set':
            if '=' not in rest:
                raise MacroError(f"{_fmt_pos(pos)}: '!set' needs 'name = expression'")
            name, expr = rest.split('=', 1)
            return ('set', name.strip(), expr, pos)
        if lw == 'local':
            if '=' in rest:
                name, expr = rest.split('=', 1)
                return ('local', name.strip(), expr, pos)
            return ('local', rest.strip(), None, pos)
        if lw == 'undef':
            return ('undef', rest.strip(), pos)
        if lw == 'return':
            return ('return', rest.strip() or None, pos)
        if lw == 'break':
            return ('break', pos)
        if lw == 'continue':
            return ('continue', pos)
        if lw in ('error', 'warning', 'echo'):
            return (lw, rest.strip(), pos)
        if lw == 'include':
            return ('include', rest.strip(), pos)
        return ('call', word, rest.strip(), pos)

    def parse_header(self, text, kw, pos):
        """ブロック文のヘッダを解析する。開き `{` はヘッダ行の最後に要る。"""
        t = text.strip()
        body = t[len(kw) + 1:]
        if not body.rstrip().endswith('{'):
            raise MacroError(f"{_fmt_pos(pos)}: '!{kw}' header must end with '{{'")
        body = body.rstrip()[:-1]
        if kw == 'if' or kw == 'elif':
            low = body.lower()
            k = low.rfind('!then')
            if k < 0:
                raise MacroError(f"{_fmt_pos(pos)}: '!{kw}' needs '!then' before '{{'")
            body = body[:k]
        return body.strip()

    def parse_if(self, lines, i, depth):
        """`!if` / `!elif` / `!else` の連なりを解析する。"""
        text, fn, ln = lines[i]
        pos = (fn, ln)
        cond = self.parse_header(_strip_comment(text, self.pat_mode), 'if', pos)
        arms = []
        else_body = None
        while True:
            body, i = self.parse_block(lines, i + 1, depth + 1)
            arms.append((cond, body))
            if i >= len(lines):
                raise MacroError(f"{_fmt_pos(pos)}: '!if' block is never closed with '}}'")
            close, cfn, cln = lines[i]
            cpos = (cfn, cln)
            tail = _strip_comment(close, self.pat_mode).strip()[1:].strip()
            if tail == '' or tail.startswith(';'):
                return ('if', arms, else_body, pos), i + 1
            w, rest = self.statement_word(tail)
            if w is None:
                raise MacroError(f"{_fmt_pos(cpos)}: unexpected text after '}}': {tail!r}")
            if w.lower() == 'elif':
                cond = self.parse_header(tail, 'elif', cpos)
                continue
            if w.lower() == 'else':
                r = rest.strip()
                if r.startswith('!if'):
                    cond = self.parse_header(r, 'if', cpos)
                    continue
                if not r.startswith('{'):
                    raise MacroError(f"{_fmt_pos(cpos)}: '!else' must be followed by '{{'")
                else_body, i = self.parse_block(lines, i + 1, depth + 1)
                if i >= len(lines):
                    raise MacroError(f"{_fmt_pos(cpos)}: '!else' block is never closed")
                trailer = _strip_comment(lines[i][0], self.pat_mode).strip()[1:].strip()
                if trailer and not trailer.startswith(';'):
                    raise MacroError(f"{lines[i][1]}:{lines[i][2]}: unexpected text "
                                     f"after '}}': {trailer!r}")
                return ('if', arms, else_body, pos), i + 1
            raise MacroError(f"{_fmt_pos(cpos)}: unexpected '!{w}' after '}}'")

    def parse_while(self, lines, i, depth):
        """`!while` を解析する。"""
        text, fn, ln = lines[i]
        pos = (fn, ln)
        cond = self.parse_header(_strip_comment(text, self.pat_mode), 'while', pos)
        body, i = self.parse_block(lines, i + 1, depth + 1)
        if i >= len(lines):
            raise MacroError(f"{_fmt_pos(pos)}: '!while' block is never closed with '}}'")
        trailer = _strip_comment(lines[i][0], self.pat_mode).strip()[1:].strip()
        if trailer and not trailer.startswith(';'):
            raise MacroError(f"{lines[i][1]}:{lines[i][2]}: unexpected text after "
                             f"'}}': {trailer!r}")
        return ('while', cond, body, pos), i + 1

    def parse_def(self, lines, i, depth):
        """`!def` を解析する。既定値付きの引数を受ける。"""
        text, fn, ln = lines[i]
        pos = (fn, ln)
        t = _strip_comment(text, self.pat_mode).strip()[4:].strip()
        if not t.rstrip().endswith('{'):
            raise MacroError(f"{_fmt_pos(pos)}: '!def' header must end with '{{'")
        t = t.rstrip()[:-1].strip()
        if '(' not in t or not t.endswith(')'):
            raise MacroError(f"{_fmt_pos(pos)}: '!def' needs 'name(p1, p2, ...)'")
        name, plist = t.split('(', 1)
        name = name.strip()
        plist = plist[:-1].strip()
        if not name or not (name[0].isalpha() or name[0] == '_') \
                or not all(c.isalnum() or c == '_' for c in name):
            raise MacroError(f"{_fmt_pos(pos)}: bad macro name {name!r}")
        if name.lower() in _MACRO_KEYWORDS or name in _BUILTINS:
            raise MacroError(f"{_fmt_pos(pos)}: '{name}' is a reserved macro name")
        params, defaults = [], []
        if plist:
            for p in plist.split(','):
                p = p.strip()
                if '=' in p:
                    pn, dv = p.split('=', 1)
                    params.append(pn.strip())
                    defaults.append(dv.strip())
                else:
                    params.append(p)
                    defaults.append(None)
                if not params[-1] or not (params[-1][0].isalpha() or params[-1][0] == '_'):
                    raise MacroError(f"{_fmt_pos(pos)}: bad parameter name "
                                     f"{params[-1]!r} in '!def {name}'")
        seen = None
        for k, p in enumerate(params):
            if defaults[k] is None and seen:
                raise MacroError(f"{_fmt_pos(pos)}: parameter '{p}' without a default "
                                 f"follows '{seen}' which has one")
            if defaults[k] is not None:
                seen = p

        self.declared.add(name)
        body, i = self.parse_block(lines, i + 1, depth + 1)
        if i >= len(lines):
            raise MacroError(f"{_fmt_pos(pos)}: '!def {name}' block is never closed")
        trailer = _strip_comment(lines[i][0], self.pat_mode).strip()[1:].strip()
        if trailer and not trailer.startswith(';'):
            raise MacroError(f"{lines[i][1]}:{lines[i][2]}: unexpected text after "
                             f"'}}': {trailer!r}")
        return ('def', _MacroFunc(name, params, defaults, body, pos), pos), i + 1


    def emit(self, text, pos):
        """展開結果の 1 行を出力に積む。"""
        if len(self.out) >= _MACRO_MAX_LINES:
            raise MacroError(f"{_fmt_pos(pos)}: macro expansion produced more than "
                             f"{_MACRO_MAX_LINES} lines; assuming a runaway macro")
        self.out.append((text, pos[0], pos[1]))

    def exec_block(self, nodes):
        """文の並びを順に実行する。"""
        for node in nodes:
            self.exec_node(node)

    def exec_node(self, node):
        """文 1 個を実行する。"""
        kind = node[0]

        if kind == 'text':
            _, text, pos = node
            self.emit(self.interpolate(text, pos), pos)
            return

        if kind == 'if':
            _, arms, else_body, _pos = node
            for cond, body in arms:
                if _truth(self.eval(cond, _pos)):
                    self.exec_block(body)
                    return
            if else_body is not None:
                self.exec_block(else_body)
            return

        if kind == 'while':
            _, cond, body, pos = node
            count = 0
            while _truth(self.eval(cond, pos)):
                count += 1
                if count > _MACRO_MAX_ITER:
                    raise MacroError(f"{_fmt_pos(pos)}: '!while' ran more than "
                                     f"{_MACRO_MAX_ITER} iterations; assuming it "
                                     f"never terminates")
                try:
                    self.exec_block(body)
                except _MacroContinue:
                    continue
                except _MacroBreak:
                    break
            return

        if kind == 'def':
            _, fn, pos = node
            prev = self.funcs.get(fn.name)
            if prev is not None and prev.body and prev.pos != fn.pos:
                self.warn(f"{_fmt_pos(pos)}: macro '{fn.name}' redefined "
                          f"(previous definition at {_fmt_pos(prev.pos)})")
            self.funcs[fn.name] = fn
            return

        if kind == 'set':
            _, name, expr, pos = node
            self.assign(name, self.eval(expr, pos))
            return

        if kind == 'local':
            _, name, expr, pos = node
            self.scope()[name] = self.eval(expr, pos) if expr is not None else 0
            return

        if kind == 'undef':
            _, name, pos = node
            self.funcs.pop(name, None)
            for sc in reversed(self.scopes):
                if name in sc:
                    del sc[name]
                    break
            return

        if kind == 'call':
            _, name, argtext, pos = node
            if name not in self.funcs:
                raise MacroError(f"{_fmt_pos(pos)}: call to undefined macro '{name}'")
            args = self.parse_args(argtext, pos)
            self.invoke(self.funcs[name], args, pos)
            return

        if kind == 'return':
            _, expr, pos = node
            raise _MacroReturn(self.eval(expr, pos) if expr else 0)

        if kind == 'break':
            raise _MacroBreak()

        if kind == 'continue':
            raise _MacroContinue()

        if kind == 'error':
            _, expr, pos = node
            raise MacroError(f"{_fmt_pos(pos)}: {_as_str(self.eval(expr, pos))}")

        if kind == 'warning':
            _, expr, pos = node
            self.warn(f"{_fmt_pos(pos)}: {_as_str(self.eval(expr, pos))}")
            return

        if kind == 'echo':
            _, expr, pos = node
            if self.state is None or getattr(self.state, 'pas', 2) != 1:
                _echo_write([self.eval(expr, pos)])
            else:
                self.eval(expr, pos)
            return

        if kind == 'include':
            _, expr, pos = node
            self.do_include(self.eval(expr, pos), pos)
            return

        raise MacroError(f"internal: unknown macro node {kind!r}")

    def parse_args(self, argtext, pos):
        """マクロ呼び出しの引数を解析する。"""
        t = argtext.strip()
        if t.startswith(';') or t == '':
            return []
        if not t.startswith('('):
            raise MacroError(f"{_fmt_pos(pos)}: macro call needs parentheses")
        p = _ExprParser(t, self, pos)
        p.expect('(')
        args = []
        if p.peek() == ')':
            p.i += 1
        else:
            while True:
                args.append(p.ternary())
                if p.eat(','):
                    continue
                p.expect(')')
                break
        rest = p.s[p.i:].strip()
        if rest and not rest.startswith(';'):
            raise MacroError(f"{_fmt_pos(pos)}: unexpected text after macro call: "
                             f"{rest!r}")
        return args

    def do_include(self, name, pos):
        """`!include` — 展開時にテキストを取り込む。"""
        if not isinstance(name, str):
            raise MacroError(f"{_fmt_pos(pos)}: '!include' needs a file name string")
        path = name
        if not os.path.isabs(path):
            base = os.path.dirname(pos[0]) if pos[0] else ''
            if base:
                path = os.path.join(base, path)
        try:
            real = os.path.abspath(path)
        except OSError:
            real = path
        if real in self.include_stack:
            raise MacroError(f"{_fmt_pos(pos)}: circular '!include' of {name!r}")
        if len(self.include_stack) >= _MACRO_MAX_INCLUDE_DEPTH:
            raise MacroError(f"{_fmt_pos(pos)}: '!include' nested deeper than "
                             f"{_MACRO_MAX_INCLUDE_DEPTH}")
        try:
            with open(path, 'rt', encoding='utf-8', errors='surrogateescape') as f:
                raw = f.readlines()
        except OSError as e:
            raise MacroError(f"{_fmt_pos(pos)}: cannot '!include' {name!r}: {e}")
        lines = [(t.rstrip('\r\n'), path, k + 1) for k, t in enumerate(raw)]
        self.include_stack.append(real)
        try:
            nodes, _ = self.parse_block(lines, 0, 0)
            self.exec_block(nodes)
        finally:
            self.include_stack.pop()


    def warn(self, msg):
        """`!warning` の出力。"""
        if msg in self._reported:
            return
        self._reported.add(msg)
        diag(f" warning - {msg}", set_error=False, force=True)

    def fail(self, msg):
        """マクロ展開を失敗として記録する。"""
        if msg not in self._reported:
            self._reported.add(msg)
            diag(f" error - {msg}", set_error=False, force=True)
        self.had_error = True
        if self.state is not None:
            self.state.had_error = True


    def contains_macros(self, raw):
        """ソース側に展開すべきものがあるか（軽い前判定）。"""
        for t in raw:
            if '!' in t or t.lstrip().startswith('}'):
                return True
        return False

    @staticmethod
    def has_interpolation(t):
        """その行に `!{...}` の補間があるか。"""
        i = t.find('!{')
        while i >= 0:
            if i == 0 or t[i - 1] != '\\':
                return True
            i = t.find('!{', i + 2)
        return False

    def has_macro_constructs(self, raw):
        """パターン側に展開すべきものがあるか（軽い前判定）。"""
        for t in raw:
            s = t.lstrip()
            if s.startswith('}'):
                return True
            if self.has_interpolation(t):
                return True
            word, rest = self.statement_word(s)
            if word is None:
                continue
            if word.lower() in _MACRO_KEYWORDS or word in self.funcs \
                    or word in self.declared or self.looks_like_call(rest):
                return True
        return False

    def expand(self, raw, filename):
        """行の並びをマクロ展開して返す。

        展開すべきものが 1 つも無ければ、解析せずにそのまま返す。これが
        マクロを使わないパターンファイルの速さを保っている。
        展開中は再帰上限を一時的に上げ、finally で必ず元に戻す。
        """
        lines = [(t.rstrip('\r\n'), filename, k + 1) for k, t in enumerate(raw)]
        if not self.enabled:
            return lines
        texts = [t for t, _, _ in lines]
        engaged = (self.has_macro_constructs(texts) if self.pat_mode
                   else self.contains_macros(texts))
        if not engaged:
            return lines
        if self.had_error:
            return []
        saved_out = self.out
        saved_expand_key = self._expand_key
        self._expand_key = filename
        self.out = []
        saved_reclimit = sys.getrecursionlimit()
        need = _MACRO_MAX_DEPTH * 40 + 1000
        if saved_reclimit < need:
            sys.setrecursionlimit(need)
        try:
            nodes, _ = self.parse_block(lines, 0, 0)
            self.exec_block(nodes)
            result = self.out
        except MacroError as e:
            self.fail(e.msg)
            result = []
        except _MacroReturn:
            self.fail(f"{filename}: '!return' outside a macro definition")
            result = []
        except (_MacroBreak, _MacroContinue):
            self.fail(f"{filename}: '!break'/'!continue' outside a '!while' loop")
            result = []
        except RecursionError:
            self.fail(f"{filename}: macro expansion recursed too deeply")
            result = []
        finally:
            sys.setrecursionlimit(saved_reclimit)
            self.out = saved_out
            self._expand_key = saved_expand_key
        return result



def _bi_check(pp, args, pos, name, lo, hi=None):
    """組み込み関数の引数の数を検査する。"""
    hi = lo if hi is None else hi
    if not (lo <= len(args) <= hi):
        raise MacroError(f"{_fmt_pos(pos)}: {name}() takes {lo}..{hi} argument(s), "
                         f"got {len(args)}")


def _bi_len(pp, a, pos):
    """`len(s)` — 文字列の長さ。"""
    _bi_check(pp, a, pos, 'len', 1)
    return len(a[0]) if isinstance(a[0], str) else len(str(a[0]))


def _bi_hex(pp, a, pos):
    """`hex(n)` — 16 進表記。"""
    _bi_check(pp, a, pos, 'hex', 1, 2)
    v = a[0]
    if isinstance(v, str):
        raise MacroError(f"{_fmt_pos(pos)}: hex() needs an integer")
    width = a[1] if len(a) > 1 else 0
    if not isinstance(width, int):
        raise MacroError(f"{_fmt_pos(pos)}: hex() width must be an integer")
    neg = v < 0
    s = format(abs(v), 'x')
    if width > len(s):
        s = '0' * (width - len(s)) + s
    return ('-' if neg else '') + s


def _bi_str(pp, a, pos):
    """`str(v)` — 文字列化。"""
    _bi_check(pp, a, pos, 'str', 1)
    return _as_str(a[0])


def _bi_int(pp, a, pos):
    """`int(v)` — 整数化。"""
    _bi_check(pp, a, pos, 'int', 1, 2)
    if isinstance(a[0], int):
        return a[0]
    base = a[1] if len(a) > 1 else 0
    try:
        return int(a[0].strip(), base)
    except ValueError:
        raise MacroError(f"{_fmt_pos(pos)}: int({a[0]!r}) is not a number")


def _bi_upper(pp, a, pos):
    """`upper(s)`。"""
    _bi_check(pp, a, pos, 'upper', 1)
    return _as_str(a[0]).upper()


def _bi_lower(pp, a, pos):
    """`lower(s)`。"""
    _bi_check(pp, a, pos, 'lower', 1)
    return _as_str(a[0]).lower()


def _bi_substr(pp, a, pos):
    """`substr(s, start[, len])`。"""
    _bi_check(pp, a, pos, 'substr', 2, 3)
    s = _as_str(a[0])
    start = a[1]
    if not isinstance(start, int):
        raise MacroError(f"{_fmt_pos(pos)}: substr() index must be an integer")
    ln = len(s)
    if start < 0:
        start = 0
    elif start > ln:
        start = ln
    if len(a) > 2:
        if not isinstance(a[2], int):
            raise MacroError(f"{_fmt_pos(pos)}: substr() length must be an integer")
        cnt = a[2]
    else:
        cnt = ln - start
    if cnt < 0:
        cnt = 0
    if start + cnt > ln:
        cnt = ln - start
    return s[start:start + cnt]


def _bi_abs(pp, a, pos):
    """`abs(n)`。"""
    _bi_check(pp, a, pos, 'abs', 1)
    if isinstance(a[0], str):
        raise MacroError(f"{_fmt_pos(pos)}: abs() needs an integer")
    return abs(a[0])


def _bi_minmax(pp, a, pos, want_min):
    """`min` / `max` の共通実装。"""
    p = _ExprParser('', pp, pos)
    best = a[0]
    for v in a[1:]:
        lt = _cmp_lt_eq(p, v, best, False)
        if lt if want_min else (not lt and not _cmp_eq(v, best)):
            best = v
    return best


def _bi_min(pp, a, pos):
    """`min(...)`。"""
    _bi_check(pp, a, pos, 'min', 1, 64)
    return _bi_minmax(pp, a, pos, True)


def _bi_max(pp, a, pos):
    """`max(...)`。"""
    _bi_check(pp, a, pos, 'max', 1, 64)
    return _bi_minmax(pp, a, pos, False)


def _bi_uid(pp, a, pos):
    """`uid()` — 展開ごとに違う番号。生成したラベル名の衝突を避けるため。"""
    _bi_check(pp, a, pos, 'uid', 0)
    pp.uid += 1
    return pp.uid


def _bi_label(pp, a, pos):
    """`label(name)` — ラベルの値。前回の反復の値が見える。"""
    _bi_check(pp, a, pos, 'label', 1)
    name = a[0]
    if not isinstance(name, str):
        raise MacroError(f"{_fmt_pos(pos)}: label() needs a string")
    st, v = pp.asm_label(name)
    if st == 'no':
        raise MacroError(f"{_fmt_pos(pos)}: no such label or .equ: '{name}'")
    return v


_BUILTINS = {
    'len': _bi_len,
    'hex': _bi_hex,
    'str': _bi_str,
    'int': _bi_int,
    'upper': _bi_upper,
    'lower': _bi_lower,
    'substr': _bi_substr,
    'abs': _bi_abs,
    'min': _bi_min,
    'max': _bi_max,
    'uid': _bi_uid,
    'label': _bi_label,
}


class Assembler:
    """アセンブラ全体の組み立てと駆動。入口は run()。

    各部品（式評価器・照合器・ディレクティブ処理・出力生成）を作って
    つなぎ、パターンファイルとソースを読み、パス1とパス2を回して
    出力を書く。
    """

    def __init__(self):
        self.state = AssemblerState()
        self.parser = Parser(self.state)
        self.var_manager = VariableManager(self.state)
        self.label_manager = LabelManager(self.state)
        self.symbol_manager = SymbolManager(self.state)
        self.expr_eval = ExpressionEvaluator(self.state, self.var_manager,
                                            self.label_manager, self.symbol_manager, self.parser)
        self.binary_writer = BinaryWriter(self.state)
        self.directive_proc = DirectiveProcessor(self.state, self.expr_eval, self.binary_writer,
                                                  self.symbol_manager, self.parser)
        self.pattern_matcher = PatternMatcher(self.state, self.expr_eval, self.var_manager,
                                             self.symbol_manager, self.parser)
        self.pat_macro_proc = MacroPreprocessor(self.state, pat_mode=True)
        self.pattern_reader = PatternFileReader(self.parser, self.pat_macro_proc)
        self.obj_gen = ObjectGenerator(self.state, self.expr_eval, self.binary_writer)
        self.vliw_proc = VLIWProcessor(self.state, self.expr_eval, self.binary_writer)
        self.asm_directive_proc = AssemblyDirectiveProcessor(self.state, self.expr_eval,
                                                             self.binary_writer, self.label_manager, self.parser)
        self.macro_proc = MacroPreprocessor(self.state)
        self._imp_sections: dict = {}

    def include_asm(self, l1, l2):
        """ソース側の `.include` を処理する。"""
        if StringUtils.upper(l1) != ".INCLUDE":
            return False
        s = StringUtils.get_string(l2)
        if not s:
            raw = l2.strip()
            if raw:
                fallback, _ = StringUtils.get_param_to_spc(raw, 0)
                if fallback:
                    self.state.diag(f" warning - .INCLUDE filename not quoted: {fallback!r}. "
                                     "Please use double quotes.", set_error=False)
                    s = fallback
                else:
                    self.state.diag(f" error - .INCLUDE directive has no filename: {l2!r}", set_error=True)
                    return True
            else:
                self.state.diag(f" error - .INCLUDE directive has no filename: {l2!r}", set_error=True)
                return True

        if s != "stdin" and not os.path.isabs(s):
            cur = self.state.current_file
            if cur and cur not in ("(stdin)", ""):
                base = os.path.dirname(os.path.abspath(cur))
                s = os.path.join(base, s)
        self.fileassemble(s)
        return True

    def _dir_line_done(self, l, l2, idx):
        """ディレクティブ行を処理し終えたときの後片付け。"""
        if self.state.textmode:
            return self._passthru_line(l, l2, idx)
        return 0, [], True, idx

    def lineassemble2(self, line, idx):
        """1 命令（VLIW なら 1 スロット）をアセンブルする。

        候補のパターンを順に照合し、当たったものに特異度スコアを付けて
        最良のものを選ぶ。選んだパターンの error_patterns を評価し、
        通れば binary_list からワード列を作る。
        """
        l, idx = StringUtils.get_param_to_spc(line, idx)
        l2, idx = StringUtils.get_param_to_eon(line, idx)
        l = l.rstrip()
        l2 = l2.rstrip()
        l = l.replace(' ', '')

        if self.state.textmode and StringUtils.upper(l) in _TEXTMODE_TEXT_ONLY_DIRS:
            return self._passthru_line(l, l2, idx)

        if self.asm_directive_proc.section_processing(l, l2):
            return self._dir_line_done(l, l2, idx)
        if self.asm_directive_proc.endsection_processing(l, l2):
            return self._dir_line_done(l, l2, idx)
        if self.asm_directive_proc.resb_processing(l, l2):
            return self._dir_line_done(l, l2, idx)
        if self.asm_directive_proc.zero_processing(l, l2):
            return self._dir_line_done(l, l2, idx)
        _l_upper = StringUtils.upper(l)
        if _l_upper == '.ASCII':
            _ok = self.asm_directive_proc.ascii_processing(l, l2)
            if not _ok and (self.state.should_report_errors()):
                self.state.diag(f" error - .ASCII: failed to process string argument: {l2!r}", set_error=True)
            return 0, [], True, idx
        if _l_upper == '.ASCIZ':
            _ok = self.asm_directive_proc.asciiz_processing(l, l2)
            if not _ok and (self.state.should_report_errors()):
                self.state.diag(f" error - .ASCIZ: failed to process string argument: {l2!r}", set_error=True)
            return 0, [], True, idx
        if self.include_asm(l, l2):
            self.state.comment_text = ''
            self.state.indent_text = ''
            return 0, [], True, idx
        if self.asm_directive_proc.align_processing(l, l2):
            return self._dir_line_done(l, l2, idx)
        if self.asm_directive_proc.org_processing(l, l2):
            return self._dir_line_done(l, l2, idx)
        if self.asm_directive_proc.labelc_processing(l, l2):
            return self._dir_line_done(l, l2, idx)
        if self.asm_directive_proc.extern_processing(l, l2):
            return self._dir_line_done(l, l2, idx)
        if self.asm_directive_proc.reloctype_processing(l, l2):
            return self._dir_line_done(l, l2, idx)
        if self.asm_directive_proc.export_processing(l, l2):
            return self._dir_line_done(l, l2, idx)
        if self.asm_directive_proc.type_processing(l, l2):
            return self._dir_line_done(l, l2, idx)
        if self.asm_directive_proc.size_processing(l, l2):
            return self._dir_line_done(l, l2, idx)
        if self.asm_directive_proc.weak_processing(l, l2):
            return self._dir_line_done(l, l2, idx)
        if self.asm_directive_proc.visibility_processing(l, l2):
            return self._dir_line_done(l, l2, idx)
        if self.asm_directive_proc.other_processing(l, l2):
            return self._dir_line_done(l, l2, idx)
        if self.asm_directive_proc.comm_processing(l, l2):
            return self._dir_line_done(l, l2, idx)

        if l == "":
            if self.state.textmode and (self.state.label_text
                                        or self.state.comment_text):
                return 0, [], True, idx
            return 0, [], False, idx

        se = False
        oerr = False
        pln = 0
        pl = ""
        idxs = 0
        objl = []
        loopflag = True

        best = None
        hit_sentinel = False
        first_match_exc = None

        exc_log = []

        _DIR_SCALAR_FIELDS = ('endian', 'bts', 'padding', 'swordchars',
                              'vliwbits', 'vliwinstbits', 'vliwtemplatebits',
                              'vliwflag')

        def _snap_dirstate():
            snap = {f: getattr(self.state, f) for f in _DIR_SCALAR_FIELDS}
            snap['symbols'] = dict(self.state.symbols)
            snap['check_constraints'] = dict(self.state.check_constraints)
            snap['reloc_constraints'] = dict(self.state.reloc_constraints)
            snap['enum_defs'] = dict(self.state.enum_defs)
            snap['vliwnop'] = list(self.state.vliwnop)
            snap['vliwset'] = list(self.state.vliwset)
            return snap

        def _restore_dirstate(snap):
            for f in _DIR_SCALAR_FIELDS:
                setattr(self.state, f, snap[f])
            self.state.symbols = dict(snap['symbols'])
            self.state.check_constraints = dict(snap['check_constraints'])
            self.state.reloc_constraints = dict(snap['reloc_constraints'])
            self.state.enum_defs = dict(snap['enum_defs'])
            self.state.vliwnop = list(snap['vliwnop'])
            self.state.vliwset = list(snap['vliwset'])


        lin = StringUtils.reduce_spaces((l + ' ' + l2) if l2 else l)

        _isdir = self.state.pat_isdir
        _pat = self.state.pat
        _dirfn = self.state.pat_dirfn

        _always = self.state.pat_always
        _cand = _pat_candidates(self.state.pat_index, self.state.pat_maxkey, lin)
        _na = len(_always)
        _nc = len(_cand)
        _hoist = self.state.hoist_rows
        _ai = self.state.hoist_first_ai if (_hoist and self.state.hdrsnap is not None) else 0
        _ci2 = 0
        _hoist_diag0 = self.state.diag_count

        while True:
            if _ai < _na:
                _row = _always[_ai]
                if _ci2 < _nc and _cand[_ci2] < _row:
                    _row = _cand[_ci2]
                    _ci2 += 1
                    _from_always = False
                else:
                    _ai += 1
                    _from_always = True
            elif _ci2 < _nc:
                _row = _cand[_ci2]
                _ci2 += 1
                _from_always = False
            else:
                break

            i = _pat[_row]
            pln = _row + 1
            pl = i

            if _hoist and self.state.hdrsnap is None and _row >= _hoist:
                if self.state.diag_count != _hoist_diag0:
                    _hoist = 0
                    self.state.hoist_rows = 0
                else:
                    self._hdrsnap_take()

            if i is None:
                continue

            if _isdir[_row]:
                if self.state.vars:
                    self.state.vars = {}
                if self.state.vars_undef:
                    self.state.vars_undef = {}
                if self.state.vars_text:
                    self.state.vars_text = {}
                _fn = _dirfn[_row]
                if _fn is not None and _fn(i):
                    continue

            if not any(i):
                continue

            if i[0] == '':
                hit_sentinel = True
                if best is None:
                    self.state.vars = {}
                    self.state.vars_undef = {}
                    self.state.vars_text = {}
                    idxs, _ = self.expr_eval.expression_pat(i[3], 0)
                break

            if _from_always:
                _pfx, _closed = _lead_caps(i[0])
                if _pfx:
                    _k = 0
                    _ok = True
                    _end = -1
                    for _ci, _ch in enumerate(lin):
                        if _ch == ' ':
                            continue
                        if _ch.upper() != _pfx[_k]:
                            _ok = False
                            break
                        _k += 1
                        if _k == len(_pfx):
                            _end = _ci + 1
                            break
                    if _k < len(_pfx):
                        _ok = False
                    if _ok and _closed and _end < len(lin) and lin[_end] in _PFX_WORD:
                        _ok = False
                    if not _ok:
                        continue

            self.state.vars = {}
            self.state.vars_undef = {}
            self.state.vars_text = {}

            self.state.error_undefined_label = False

            self.state.expmode = EXP_ASM
            self.state.expcaps = CAPS_ASM

            saved_vars = dict(self.state.vars)
            saved_vars_undef = dict(self.state.vars_undef)
            saved_vars_text = dict(self.state.vars_text)
            saved_refs_len = len(self.state._elf_label_refs_seen)
            saved_v2l = dict(self.state._elf_var_to_label)
            saved_hint = dict(self.state._elf_insn_reloc_hint)

            _cand_diags = []
            try:
                self.state._in_match_attempt = True
                self.state.diag_capture_begin()
                _match_result = self.pattern_matcher.match0(lin, i[0])
            except (ArithmeticError, KeyError, IndexError, ValueError,
                    TypeError, AttributeError, OverflowError,
                    struct.error) as _pat_exc:

                _match_result = False
                if first_match_exc is None:
                    first_match_exc = (pln, pl)
                exc_log.append((pln, pl, type(_pat_exc).__name__, str(_pat_exc)))
            finally:
                self.state._in_match_attempt = False
                _cand_diags = self.state.diag_capture_take()

            if _match_result is True:
                score = self.pattern_matcher.last_match_score
                if best is None or score < best['score']:
                    best = {
                        'score': score,
                        'pln':   pln,
                        'pat':   i,
                        'vars':  dict(self.state.vars),
                        'vars_undef': dict(self.state.vars_undef),
                        'vars_text': dict(self.state.vars_text),
                        'refs':  self.state._elf_label_refs_seen[saved_refs_len:],
                        'v2l':   dict(self.state._elf_var_to_label),
                        'hint':  dict(self.state._elf_insn_reloc_hint),
                        'dir':   _snap_dirstate(),
                        'error_undefined_label': self.state.error_undefined_label,
                        'diags': _cand_diags,
                    }

                self.state.vars = saved_vars
                self.state.vars_undef = saved_vars_undef
                self.state.vars_text = saved_vars_text
                del self.state._elf_label_refs_seen[saved_refs_len:]
                self.state._elf_var_to_label = saved_v2l
                self.state._elf_insn_reloc_hint = saved_hint


            self.state.error_undefined_label = False

        if best is not None and exc_log and (self.state.verbose or self.state.debug):

            _other_plns = sorted({e[0] for e in exc_log if e[0] != best['pln']})
            if _other_plns:
                self.state.diag(f" warning - {len(_other_plns)} other candidate pattern(s) at line(s) "
                     f"{_other_plns} raised an exception during matching and were skipped "
                     f"in favor of pattern line {best['pln']}.  "
                     f"[{self.state.current_file}:{self.state.ln}]", set_error=False)

        if best is not None:
            i = best['pat']
            pln = best['pln']
            pl = i
            loopflag = False

            _restore_dirstate(best['dir'])
            self.state.vars = dict(best['vars'])
            self.state.vars_undef = dict(best['vars_undef'])
            self.state.vars_text = dict(best['vars_text'])
            self.state._elf_label_refs_seen.extend(best['refs'])
            self.state._elf_var_to_label = dict(best['v2l'])
            self.state._elf_insn_reloc_hint = dict(best['hint'])
            self.state.error_undefined_label = best.get('error_undefined_label', False)
            self.state.diag_replay(best.get('diags', ()))
            self.state.expmode = EXP_ASM
            self.state.expcaps = CAPS_ASM

            try:
                self.state.pc_instr_start = self.state.pc
                self.state.pc_instr_end   = self.state.pc_instr_start
                _probe_sm_saved    = self.state._pass1_size_mode
                _probe_refs_len    = len(self.state._elf_label_refs_seen)
                _probe_widx_saved  = self.state._elf_current_word_idx
                _probe_hint_saved  = dict(self.state._elf_insn_reloc_hint)
                self.state._pass1_size_mode = True
                try:
                    _probe_objl = self.obj_gen.makeobj(i[2])
                    self.state.pc_instr_end = self.state.pc_instr_start + len(_probe_objl)
                except Exception:
                    pass
                finally:
                    self.state._pass1_size_mode = _probe_sm_saved
                    del self.state._elf_label_refs_seen[_probe_refs_len:]
                    self.state._elf_current_word_idx = _probe_widx_saved
                    self.state._elf_insn_reloc_hint = _probe_hint_saved
                    self.state.error_undefined_label = best.get('error_undefined_label', False)
                err_triggered, _err_code = self.directive_proc.error(i[1])
                if not err_triggered:
                    objl = self.obj_gen.makeobj(i[2])
                else:
                    objl = []
                idxs, _ = self.expr_eval.expression_pat(i[3], 0)
            except (ArithmeticError, KeyError, IndexError, ValueError,
                    TypeError, AttributeError, OverflowError,
                    struct.error) as _exc:
                if self.state.pas == 1:
                    if self.state.debug:
                        import traceback as _tb
                        print(f" [pass1 forward-ref fallback] {type(_exc).__name__}: {_exc}", file=sys.stderr)
                        _tb.print_exc()
                    try:
                        self.state._pass1_size_mode = True
                        objl = self.obj_gen.makeobj(i[2])
                        idxs, _ = self.expr_eval.expression_pat(i[3], 0)
                    except (ArithmeticError, KeyError, IndexError, ValueError,
                            TypeError, AttributeError, OverflowError,
                            struct.error):
                        objl = []
                    finally:
                        self.state._pass1_size_mode = False
                        self.state.error_undefined_label = False
                else:
                    oerr = True
        elif hit_sentinel:
            loopflag = False
        elif first_match_exc is not None:
            pln, pl = first_match_exc
            oerr = True
            loopflag = False

        if loopflag:
            se = True
            pln = 0
            pl = ""

        if se and self.state.passthru:
            return self._passthru_line(l, l2, idx)

        if self.state.should_report_errors():
            _loc = f"  [{self.state.current_file}:{self.state.ln}]"
            if self.state.error_undefined_label:
                self.state.had_error = True
                self.state.diag(f" error - Undefined label in expression.{_loc}", set_error=False)
                return 0, [], False, idx
            if se:
                self.state.had_error = True
                self.state.diag(f" error - Syntax error.{_loc}", set_error=False)
                return 0, [], False, idx
            if oerr:
                self.state.had_error = True
                self.state.diag(f" error - Illegal syntax in assemble line or pattern line.{_loc}", set_error=False)
                if self.state.debug:
                    self.state.diag(f"   (pattern {pln}: {pl})", set_error=False)
                return 0, [], False, idx

        return idxs, objl, True, idx

    def _text_words(self, txt):
        """テキストを出力ワードの並びにする（UTF-8 の 1 バイトが 1 ワード）。"""
        words = list(txt.encode('utf-8', errors='surrogateescape'))
        _word_mask = (1 << self.state.bts) - 1 if self.state.bts > 0 else 0xFF
        if (any(_v > _word_mask for _v in words)
                and not self.state._pass1_size_mode
                and self.state.should_report_errors()):
            self.state.diag(f" warning - .passthru: one or more bytes exceed the "
                            f"output word width ({self.state.bts} bit(s)) and were "
                            f"truncated (high bits discarded): {txt!r}", set_error=False)
        return words

    def _passthru_line(self, l, l2, idx):
        """`.passthru` が有効なとき、当たらなかった行をそのまま出す。"""
        txt = (l + ' ' + l2) if l2 else l
        self.state.error_undefined_label = False
        objl = self._text_words(txt)
        self.state.asmtext = txt
        self.state.asmtext_disp = '"%s"' % asmtext_escaped(txt)
        return 0, objl, True, idx

    def lineassemble(self, line):
        """ソース 1 行を処理する。

        ラベル定義、ソース側ディレクティブ、`!!` のバンドル分解、
        テキスト置換モードの扱いを済ませてから lineassemble2 を呼ぶ。
        """
        _ind = line[:len(line) - len(line.lstrip(' \t'))]
        if len(_ind) > 511:
            _ind = _ind[:511]
        self.state.indent_text = _ind if self.state.textmode else ''
        line = StringUtils.normalize_ws(line)
        line, _cmt = StringUtils.split_comment_asm(line)
        self.state.comment_text = _cmt if self.state.textmode else ''
        if line == '' and not self.state.comment_text:
            return False
        line = StringUtils.resolve_vliw_escapes(line)

        if self.state.hoist_rows and self.state.hdrsnap is not None:
            self._hdrsnap_restore()
            self.state.freed_subs.clear()
        else:
            self.state.check_constraints.clear()
            self.state.reloc_constraints.clear()
            self.state.enum_defs.clear()
            self.state.freed_subs.clear()

            self.state.symbols = dict(self.state.patsymbols)

        self.state.label_text = ''
        line = self.asm_directive_proc.label_processing(line)

        _vparts = line.replace(VLIW_STOP, VLIW_SEP).split(VLIW_SEP)
        self.state.vcnt = sum(1 for _p in _vparts if _p != '')

        if self.state.elf_objfile and self.state.pas == 2:
            self.state._elf_tracking = True
            self.state._elf_label_refs_seen = []
            self.state._elf_current_word_idx = -1
            self.state._elf_var_to_label = {}
            self.state._elf_capturing_var = None
            self.state._elf_insn_reloc_hint = {}

        try:
            idxs, objl, flag, idx = self.lineassemble2(line, 0)
        finally:
            self.state._elf_tracking = False

        if not flag:
            return False

        if (self.state.textmode and self.state.label_text
                and not self.state.vliwflag
                and (self.state.asmtext is not None or not objl)):
            _lpfx = self.state.label_text
            _ltxt = self.state.asmtext
            if _ltxt:
                _lpfx += ' '
            _lbytes = list(_lpfx.encode('utf-8', errors='surrogateescape'))
            objl[0:0] = _lbytes
            self.state.asmtext = _lpfx + (_ltxt or '')
            self.state.asmtext_disp = '"%s"' % asmtext_escaped(self.state.asmtext)
            if _lbytes:
                self.state._elf_label_refs_seen = [
                    (_n, _v, (_w + len(_lbytes)) if _w >= 0 else _w)
                    for (_n, _v, _w) in self.state._elf_label_refs_seen]

        if (self.state.textmode and self.state.comment_text
                and not self.state.vliwflag
                and (self.state.asmtext is not None or not objl)):
            _ctxt = self.state.comment_text
            _cur = self.state.asmtext or ''
            _csfx = (' ' + _ctxt) if _cur else _ctxt
            objl.extend(self._text_words(_csfx))
            self.state.asmtext = _cur + _csfx
            self.state.asmtext_disp = '"%s"' % asmtext_escaped(self.state.asmtext)

        if (self.state.textmode and self.state.indent_text
                and not self.state.vliwflag
                and self.state.asmtext):
            _itxt = self.state.indent_text
            _ibytes = list(_itxt.encode('utf-8', errors='surrogateescape'))
            objl[0:0] = _ibytes
            self.state.asmtext = _itxt + self.state.asmtext
            self.state.asmtext_disp = '"%s"' % asmtext_escaped(self.state.asmtext)
            if _ibytes:
                self.state._elf_label_refs_seen = [
                    (_n, _v, (_w + len(_ibytes)) if _w >= 0 else _w)
                    for (_n, _v, _w) in self.state._elf_label_refs_seen]

        if self.state.eol and objl and not self.state.vliwflag:
            objl.append(ord('\n'))

        if not self.state.vliwflag or (idx >= len(line) or line[idx] not in (VLIW_SEP, VLIW_STOP)):
            of = len(objl)
            if self.state.elf_objfile and self.state.pas == 2 and objl and self.state._elf_label_refs_seen:
                bpw_r = max(1, (self.state.bts + 7) // 8)
                sec_name_r = self.state.current_section

                _completed_words = 0
                _entry_pc_cur = 0
                if sec_name_r in self.state.sections:
                    _sentry = self.state.sections[sec_name_r]
                    _completed_words = _sentry[1]
                    _entry_pc_cur = _sentry[2] if len(_sentry) > 2 else _sentry[0]

                valid_refs = [(ln, aw, wi) for (ln, aw, wi) in self.state._elf_label_refs_seen if wi >= 0]
                valid_refs.sort(key=lambda r: r[2])

                _seen_ln_wi = set()
                _deduped_refs = []
                for _r in valid_refs:
                    _key = (_r[0], _r[2])
                    if _key in _seen_ln_wi:
                        continue
                    _seen_ln_wi.add(_key)
                    _deduped_refs.append(_r)
                valid_refs = _deduped_refs

                _widx_labels = {}
                for _ln, _, _wi in valid_refs:
                    _widx_labels.setdefault(_wi, set()).add(_ln)
                _ambiguous = {_wi for _wi, ns in _widx_labels.items() if len(ns) > 1}
                valid_refs = [r for r in valid_refs if r[2] not in _ambiguous]

                groups = []
                gi = 0
                while gi < len(valid_refs):
                    lname, abs_w, widx = valid_refs[gi]
                    gj = gi + 1
                    while gj < len(valid_refs) and valid_refs[gj][0] == lname and valid_refs[gj][2] == widx + (gj - gi):
                        gj += 1
                    groups.append((lname, abs_w, widx, gj - gi))
                    gi = gj

                _mach_tbl_la = elf_machine_table(self.state)
                _rmap = {**_mach_tbl_la['width_guess'], **self.state.reloctype_override}
                _pc_rel_types_all = _mach_tbl_la['pc_rel']

                for lname, abs_w, first_widx, num_words in groups:
                    num_bytes = num_words * bpw_r

                    _hint = self.state._elf_insn_reloc_hint.get(first_widx)
                    lentry = self.state.labels.get(lname)
                    _src_rtype = lentry[4] if (lentry and len(lentry) > 4
                                               and lentry[4] is not None) else None
                    _forced_rtype = None
                    if _hint is not None:
                        _hint_rtype, _hint_addend = _hint
                        if _src_rtype is not None and lname not in self.state.extern_untyped:
                            _hint_rtype = _src_rtype
                        _fmask = insn_reloc_field_mask(_hint_rtype, self.state.elf_machine, self.state)
                        _fdecl = insn_reloc_field_decl(self.state, _hint_rtype)
                        _foff = _fdecl[1] if _fdecl is not None else 0
                        if _fmask is None:
                            _forced_rtype = _hint_rtype
                        else:
                            _insn_bytes = _mach_tbl_la['reloc_bytes'].get(_hint_rtype, 4)
                            _insn_words = max(1, _insn_bytes // bpw_r)
                            _fw = first_widx + _foff // bpw_r
                            if _fw + _insn_words <= len(objl):
                                _wmask = (1 << self.state.bts) - 1
                                for _k in range(_insn_words):
                                    _sh = self.state.bts * _k if self.state.endian == 'little' \
                                        else self.state.bts * (_insn_words - 1 - _k)
                                    _clear = (_fmask >> _sh) & _wmask
                                    objl[_fw + _k] = int(objl[_fw + _k]) & ~_clear & _wmask
                            _sec_rel_h = (_completed_words
                                          + (self.state.pc + _fw - _entry_pc_cur)) * bpw_r
                            self.state.relocations.append(
                                (sec_name_r, _sec_rel_h, lname, _hint_rtype,
                                 _hint_addend, _insn_bytes))
                            continue

                    rtype = 0
                    _rtype_is_default_guess = False
                    if _forced_rtype is not None:
                        rtype = _forced_rtype
                    elif _src_rtype is not None:
                        rtype_override = _src_rtype
                        expected = _mach_tbl_la['reloc_bytes'].get(rtype_override)
                        if expected is None or expected == num_bytes:
                            rtype = rtype_override
                        else:
                            rtype = _rmap.get(num_bytes, 0)
                            _rtype_is_default_guess = True
                    else:
                        rtype = _rmap.get(num_bytes, 0)
                        _rtype_is_default_guess = True

                    if first_widx >= len(objl):
                        continue
                    if rtype == 0:
                        if self.state.debug:
                            self.state.diag(
                                f" warning - no relocation type available for a {num_bytes}-byte "
                                f"reference to '{lname}'; relocation omitted.", set_error=False)
                        continue

                    sec_rel = (_completed_words + (self.state.pc + first_widx - _entry_pc_cur)) * bpw_r

                    word_mask = (1 << self.state.bts) - 1
                    raw_val = 0
                    if self.state.endian == 'little':
                        for k in range(num_words):
                            widx_k = first_widx + k
                            if widx_k < len(objl):
                                raw_val |= (int(objl[widx_k]) & word_mask) << (self.state.bts * k)
                    else:
                        for k in range(num_words):
                            widx_k = first_widx + k
                            if widx_k < len(objl):
                                raw_val = (raw_val << self.state.bts) | (int(objl[widx_k]) & word_mask)

                    if (isinstance(abs_w, float) and not math.isfinite(abs_w)) or \
                       _is_undef_derived(abs_w):
                        continue

                    _field_bits = num_words * self.state.bts
                    if _field_bits > 0 and raw_val >= (1 << (_field_bits - 1)):
                        raw_val -= (1 << _field_bits)

                    abs_w_bytes = int(abs_w) * bpw_r

                    if (_rtype_is_default_guess and rtype in _pc_rel_types_all
                            and raw_val == abs_w_bytes):
                        _alt = _reloc_same_width(_mach_tbl_la, num_bytes, False)
                        if _alt is not None:
                            rtype = _alt

                    if (_rtype_is_default_guess and self.state.elf_machine == 4
                            and rtype not in _pc_rel_types_all
                            and raw_val != abs_w_bytes):
                        _alt = _reloc_same_width(_mach_tbl_la, num_bytes, True)
                        if _alt is not None:
                            rtype = _alt

                    if rtype in _pc_rel_types_all:
                        _P_raw = (self.state.pc + first_widx) * bpw_r
                        _P_adj = self.label_manager._section_relative_offset(
                            self.state.current_section, self.state.pc + first_widx)
                        P_asm_bytes = _P_adj * bpw_r if _P_adj is not None else _P_raw

                        addend = raw_val - abs_w_bytes + P_asm_bytes

                    else:
                        addend = raw_val - abs_w_bytes

                    self.state.relocations.append((sec_name_r, sec_rel, lname, rtype, addend, num_bytes))

            if self.state.gen_debug and self.state.pas == 2 and of > 0:
                self.state.line_map.append(
                    (self.state.current_section, self.state.pc,
                     self.state.current_file, self.state.ln))

            for cnt in range(of):
                self.binary_writer.outbin(self.state.pc + cnt, objl[cnt])
            self.state.pc += of
        else:
            vflag = False
            try:
                vflag = self.vliw_proc.vliwprocess(line, idxs, objl, flag, idx, self.lineassemble2)
            except Exception as _vliw_exc:
                if self.state.should_report_errors():
                    self.state.diag(" error - Some error(s) in vliw definition.", set_error=True)

                    if self.state.verbose or self.state.debug:
                        print(f"   ({type(_vliw_exc).__name__}: {_vliw_exc})", file=sys.stderr)
            return vflag

        return True

    def lineassemble0(self, line):
        """1 行を処理する外枠。行の前処理と診断の文脈を整える。"""
        cleaned = line.replace('\n', '').replace('\r', '')
        _show = (self.state.pas == 2 and self.state.verbose) or self.state.pas == 0
        if _show:
            self.state.cl = cleaned
            print("%016x " % self.state.pc, end='')
            print(f"{self.state.current_file} {self.state.ln} {self.state.cl} //", end='')
        self.state.asmtext = None
        self.state.asmtext_disp = None
        f = self.lineassemble(cleaned)
        if self.state.asmtext is not None and self.state.pas in (0, 2):
            if _show:
                print(' %s' % (self.state.asmtext_disp or ''), end='')
            elif self.state.text_output:
                print(self.state.asmtext)
        self.state.asmtext = None
        self.state.asmtext_disp = None
        if _show:
            print("")
        self.state.ln += 1
        return f

    _ELF_DECL_DIRECTIVES = ('.elftype', '.elfmachine', '.elfclass', '.elfrela',
                            '.elfwidth', '.elfextern', '.elfdwarf', '.elfheader',
                            '.elfsection', '.elffield')

    def register_elfdecls(self, pat):
        """パターンファイル中の ELF 記述ディレクティブを先に読んでおく。"""
        d = self.directive_proc
        table = {
            '.elftype':    d.elftype_processing,
            '.elfmachine': d.elfmachine_processing,
            '.elfclass':   d.elfclass_processing,
            '.elfrela':    d.elfrela_processing,
            '.elfwidth':   d.elfwidth_processing,
            '.elfextern':  d.elfextern_processing,
            '.elfdwarf':   d.elfdwarf_processing,
            '.elfheader':  d.elfheader_processing,
            '.elfsection': d.elfsection_processing,
            '.elffield':   d.elffield_processing,
        }
        for i in pat:
            if i and i[0] in table:
                table[i[0]](i)
        self.check_elfdecls()

    def check_elfdecls(self):
        """ELF 記述の宣言が揃っているか、矛盾がないかを検査する。"""
        if not self.state.elf_objfile:
            return
        e = self.state.elf
        tbl = elf_machine_table(self.state)
        named = tbl['named']
        for w in sorted(e.decl_width):
            t = e.decl_width[w]
            if _elf_decl_type(self.state, named, t) is None:
                self.state.diag(f" warning - .elfwidth: unknown relocation type '{t}' "
                                f"for {tbl['name']}; ignored.", set_error=False)
        for dname, t in (('.elfextern', e.decl_extern), ('.elfdwarf', e.decl_dwarf)):
            if t and _elf_decl_type(self.state, named, t) is None:
                self.state.diag(f" warning - {dname}: unknown relocation type '{t}' "
                                f"for {tbl['name']}; ignored.", set_error=False)
        for t in e.decl_field:
            if _elf_decl_type(self.state, named, t) is None:
                self.state.diag(f" warning - .elffield: unknown relocation type '{t}' "
                                f"for {tbl['name']}; ignored.", set_error=False)

    def setpatsymbols(self, pat):
        """パターンファイルが定義するシンボルを先に集める。

        ソースのラベルがこれらと衝突したらエラーにできるようにするため、
        アセンブルを始める前に名前を知っておく必要がある。
        """
        fresh = {}
        self.state.strsymbols = {}
        self.state.arrsymbols = {}
        self.state.arrgen += 1
        for i in pat:
            if i is None:
                continue
            if len(i) > 0 and i[0] == '.setsym':
                if len(i) >= 2 and i[1]:
                    key = StringUtils.upper(i[1])
                    self.state.symbols = dict(fresh)
                    value_field = i[2] if len(i) >= 3 else ''
                    _vf = value_field.lstrip(' \t')
                    if _vf.startswith('"'):
                        self.state.strsymbols[key] = \
                            ObjectGenerator._txt_template_inner(_vf)
                        continue
                    if _vf.startswith('['):
                        self.state.arrsymbols[key] = arr_items_from_text(self.expr_eval, _vf)
                        continue
                    if symbol_copy_from_name(self.state, key, _vf):
                        continue
                    if symbol_set_from_text(self.state, key, value_field):
                        continue
                    if value_field:
                        v, _ = self.expr_eval.expression_pat(value_field, 0)
                    else:
                        v = 0
                    fresh[key] = v
                elif len(i) >= 3 and i[2]:
                    key = StringUtils.upper(i[2])
                    fresh[key] = 0
                continue
            if len(i) > 0 and i[0] == '.clearsym':
                if len(i) >= 3 and i[2] != '':
                    key = StringUtils.upper(i[2])
                    fresh.pop(key, None)
                    self.state.strsymbols.pop(key, None)
                    self.state.arrsymbols.pop(key, None)
                    self.state.arrgen += 1
                else:
                    fresh = {}
                    self.state.strsymbols = {}
                    self.state.arrsymbols = {}
                    self.state.arrgen += 1
                continue
            if len(i) > 0 and i[0] == '.map':
                self.state.symbols = dict(fresh)
                self.directive_proc.map_apply(i, into=fresh, set_check=False)
                continue
            if len(i) > 0 and i[0] == '.free':
                _names = (i[2] if len(i) >= 3 and i[2] else (i[1] if len(i) >= 2 else ''))
                for _nm in _names.split(','):
                    _nm = _nm.strip()
                    if not _nm:
                        continue
                    _k = StringUtils.upper(_nm)
                    fresh.pop(_k, None)
                    self.state.strsymbols.pop(_k, None)
                    self.state.arrsymbols.pop(_k, None)
                    self.state.arrgen += 1
                continue
            if len(i) > 0 and i[0] == '.bits':
                self.directive_proc.bits(i)
                continue
        self.state.patsymbols = fresh
        self.state.symbols = dict(fresh)

    def fileassemble(self, fn):
        """ソースファイル 1 つを 1 行ずつアセンブルする。"""

        if not self.state.fnstack:
            self.macro_proc.reset_pass()

        _MAX_INCLUDE_DEPTH = 100
        if len(self.state.fnstack) >= _MAX_INCLUDE_DEPTH:
            self.state.diag(f" error - .INCLUDE nesting depth exceeds {_MAX_INCLUDE_DEPTH}: '{fn}'", set_error=True)
            return
        try:
            abs_fn = os.path.abspath(fn) if fn not in ("stdin", "") else fn
        except Exception:
            abs_fn = fn
        for already in self.state.fnstack:
            try:
                already_abs = os.path.abspath(already) if already not in ("stdin", "", "(stdin)") else already
            except Exception:
                already_abs = already
            if abs_fn == already_abs:
                self.state.diag(f" error - circular .INCLUDE detected: '{fn}' is already being assembled.", set_error=True)
                return

        _caller_file = self.state.current_file
        self.state.fnstack.append(fn)
        self.state.lnstack.append(self.state.ln)
        self.state.current_file = fn
        self.state.ln = 1

        try:
            if fn == "stdin":
                if self.state.stdin_tmp_path is None:
                    fd, tmp_path = tempfile.mkstemp(prefix="axx_", suffix=".tmp", text=True)
                    os.close(fd)
                    self.state.stdin_tmp_path = tmp_path
                    af = self.file_input_from_stdin()
                    with open(self.state.stdin_tmp_path, "wt", encoding="utf-8",
                              errors="surrogateescape") as stdintmp:
                        stdintmp.write(af)
                fn = self.state.stdin_tmp_path

            try:
                with open(fn, "rt", encoding="utf-8", errors="surrogateescape") as f:
                    af = f.readlines()
            except OSError as e:
                self.state.diag(f" error - cannot open source file '{fn}': {e}",
                                set_error=True)
                return
            except UnicodeDecodeError as e:
                self.state.diag(f" error - source file '{fn}' is not valid UTF-8: {e}",
                                set_error=True)
                return
            af = StringUtils.join_backslash_continuations(af)

            _expkey = self.state.current_file
            _line_pcs = []
            self.state._macro_line_pcs_cur[_expkey] = _line_pcs
            for _mtext, _mfile, _mln in self.macro_proc.expand(af, self.state.current_file):
                _line_pcs.append(self.state.pc)
                self.state.current_file = _mfile
                self.state.ln = _mln
                self.lineassemble0(_mtext)
        finally:
            self.state.fnstack.pop()
            self.state.current_file = _caller_file
            self.state.ln = self.state.lnstack.pop()

    def file_input_from_stdin(self):
        """プロンプトモード。`>>` で行を読み、`?` でラベル表を出す。

        このモードではマクロ層を通らない。
        """
        af = ""
        while True:
            line = sys.stdin.readline()
            if line == '':
                break
            af += line.replace('\r', '')
        return af

    def imp_label(self, l):
        """`-i` のインポートファイルの 1 行からラベルを取り込む。"""
        l = l.rstrip('\r\n')
        if not l:
            return False

        fields = l.split('\t')

        if len(fields) >= 3:
            sname = fields[0]
            try:
                start = int(fields[1], 16)
                size  = int(fields[2], 16)
            except ValueError:
                return False

            self._imp_sections.setdefault(sname, []).append((start, size))
            return True

        if len(fields) == 2:
            label = fields[0]
            if not label:
                return False

            reloc_type = None
            if '::' in label:
                label, rt_str = label.split('::', 1)
                _mach_tbl_imp = elf_machine_table(self.state)
                reloc_type = _reloc_named(self.state, _mach_tbl_imp, rt_str)
                if reloc_type is None:
                    self.state.diag(f" warning - unknown reloc type '{rt_str}' for imported label '{label}'", set_error=False)
            if not label:
                return False
            try:
                v = int(fields[1], 16)
            except ValueError:
                return False
            section = '.text'

            _found = False
            for sname, _ranges in self._imp_sections.items():
                for (start, size) in _ranges:
                    if size > 0 and start <= v < start + size:
                        section = sname
                        _found = True
                        break
                    if size == 0 and v == start:
                        section = sname
                        _found = True
                        break
                if _found:
                    break

            bpw = max(1, (self.state.bts + 7) // 8)
            v_words = v // bpw

            entry = [v_words, section, False, True]
            if reloc_type is not None:
                entry.append(reloc_type)
            self.state.labels[label] = entry
            return True

        return False

    def printaddr(self, pc):
        """リスティングの行頭のアドレスを出す。"""
        print("%016x: " % pc, end='')

    def _section_word_ranges(self, name):
        """そのセクションが占めるワード範囲の並びを返す。"""
        ranges = [(rs, rl) for (rn, rs, rl) in self.state.section_ranges if rn == name]
        if ranges:
            return ranges
        entry = self.state.sections.get(name)
        if entry and entry[1] > 0:
            return [(entry[0], entry[1])]
        return []

    def _addr_to_word_offset(self, name, word_pc):
        """絶対アドレスを、そのセクション内のワードオフセットに直す。"""
        if not self.state.sections:
            return word_pc
        cum = 0
        for rs, rl in self._section_word_ranges(name):
            if rs <= word_pc <= rs + rl:
                return cum + (word_pc - rs)
            cum += rl
        return None

    def _build_dwarf_sections(self, csecs, sec_name_to_idx, bpw, machine):
        """`-g` の DWARF セクションを作る。

        `.debug_info` / `.debug_abbrev` / `.debug_line` を組み、行表は
        パス2で集めた line_map（アドレスとソース行の対応）から作る。
        """
        line_map = self.state.line_map
        if not self.state.gen_debug or not line_map:
            return [], []

        _mach_tbl_dw = elf_machine_table(self.state)
        _native_dw   = _mach_tbl_dw['elfclass']
        _eff_class_dw = getattr(self.state, 'elf_class', None) or _native_dw
        if not _mach_tbl_dw['dwarf_abs']:
            self.state.diag(f" warning - DWARF debug info (-g) needs an absolute "
                 f"relocation type for machine {machine}; declare it with .elfdwarf. "
                 f"Skipping debug sections.", set_error=False)
            return [], []

        import struct as _struct
        _pk = '<' if self.state.endian != 'big' else '>'

        is_elf64_dw = (_eff_class_dw == 2)
        addr_sz = 8 if is_elf64_dw else 4
        is_rela_dw = _mach_tbl_dw.get('is_rela', True)

        def _pack_addr(v):
            v &= (1 << (addr_sz * 8)) - 1
            return _struct.pack(f'{_pk}I', v) if addr_sz == 4 else _struct.pack(f'{_pk}Q', v)

        abs64 = _mach_tbl_dw['dwarf_abs']
        if _mach_tbl_dw['reloc_bytes'].get(abs64) != addr_sz:
            _want = 'abs64' if addr_sz == 8 else 'abs32'
            _alt = _mach_tbl_dw['named'].get(_want)
            if _alt is not None and _mach_tbl_dw['reloc_bytes'].get(_alt) == addr_sz:
                abs64 = _alt
            else:
                self.state.diag(
                    f" warning - DWARF debug info (-g) needs a {addr_sz}-byte absolute "
                    f"relocation, which {_mach_tbl_dw['name']} does not have; "
                    f"skipping debug sections.", set_error=False)
                return [], []

        def _uleb(v):
            out = bytearray()
            v = int(v)
            while True:
                b = v & 0x7f
                v >>= 7
                if v:
                    out.append(b | 0x80)
                else:
                    out.append(b)
                    return bytes(out)

        def _sleb(v):
            out = bytearray()
            v = int(v)
            while True:
                b = v & 0x7f
                v >>= 7
                if (v == 0 and not (b & 0x40)) or (v == -1 and (b & 0x40)):
                    out.append(b)
                    return bytes(out)
                out.append(b | 0x80)

        _csec_idx_by_name = {s.name: i + 1 for i, s in enumerate(csecs)}

        def _addr_to_sec(byte_addr, sec_name=None):
            word_pc = byte_addr // bpw if bpw else 0
            if sec_name is not None:
                _idx = _csec_idx_by_name.get(sec_name)
                if _idx is not None:
                    _woff = self._addr_to_word_offset(sec_name, word_pc)
                    if _woff is not None:
                        return _idx, _woff * bpw
            for i, s in enumerate(csecs):
                _woff = self._addr_to_word_offset(s.name, word_pc)
                if _woff is not None:
                    return i + 1, _woff * bpw
            return None, 0

        DW_TAG_compile_unit = 0x11
        DW_TAG_label        = 0x0a
        DW_CHILDREN_yes, DW_CHILDREN_no = 1, 0
        DW_AT_name, DW_AT_low_pc, DW_AT_high_pc = 0x03, 0x11, 0x12
        DW_AT_language, DW_AT_comp_dir = 0x13, 0x1b
        DW_AT_producer, DW_AT_stmt_list = 0x25, 0x10
        DW_FORM_addr, DW_FORM_data2, DW_FORM_data8 = 0x01, 0x05, 0x07
        DW_FORM_string, DW_FORM_sec_offset = 0x08, 0x17

        _dbg_labels = []
        for _name, *_rest in sorted(self.state.labels.items()):
            _entry = _rest[0]
            if (len(_entry) > 2 and _entry[2]) or (len(_entry) > 3 and _entry[3]):
                continue
            try:
                _byte_addr = int(_entry[0]) * bpw
            except (TypeError, ValueError, OverflowError):
                continue
            _sidx, _off = _addr_to_sec(_byte_addr, _entry[1])
            if _sidx is None:
                continue
            _dbg_labels.append((_name, _sidx, _off))

        abbrev = bytearray()
        abbrev += _uleb(1) + _uleb(DW_TAG_compile_unit) \
            + bytes([DW_CHILDREN_yes if _dbg_labels else DW_CHILDREN_no])
        for at, fm in ((DW_AT_producer, DW_FORM_string),
                       (DW_AT_language, DW_FORM_data2),
                       (DW_AT_name, DW_FORM_string),
                       (DW_AT_comp_dir, DW_FORM_string),
                       (DW_AT_low_pc, DW_FORM_addr),
                       (DW_AT_high_pc, DW_FORM_data8),
                       (DW_AT_stmt_list, DW_FORM_sec_offset)):
            abbrev += _uleb(at) + _uleb(fm)
        abbrev += _uleb(0) + _uleb(0)
        abbrev += _uleb(2) + _uleb(DW_TAG_label) + bytes([DW_CHILDREN_no])
        for at, fm in ((DW_AT_name, DW_FORM_string),
                       (DW_AT_low_pc, DW_FORM_addr)):
            abbrev += _uleb(at) + _uleb(fm)
        abbrev += _uleb(0) + _uleb(0)
        abbrev += _uleb(0)
        abbrev = bytes(abbrev)

        primary_sec = line_map[0][0]
        primary_idx = sec_name_to_idx.get(primary_sec)
        if primary_idx is None:
            primary_idx = 1 if csecs else None
        primary_csec = csecs[primary_idx - 1] if primary_idx else None
        primary_size = primary_csec.byte_size if primary_csec else 0

        producer = "axx general assembler (DWARF4)"
        comp_dir = os.getcwd()
        cu_name = line_map[0][2] or "(source)"

        info_relas = []
        die = bytearray()
        die += _uleb(1)
        die += producer.encode() + b'\x00'
        die += _struct.pack(f'{_pk}H', 0x8001)
        die += cu_name.encode() + b'\x00'
        die += comp_dir.encode() + b'\x00'
        if primary_idx:
            info_relas.append((len(die), primary_idx, abs64, 0))
        die += _pack_addr(0)
        die += _struct.pack(f'{_pk}Q', primary_size & 0xFFFFFFFFFFFFFFFF)
        die += _struct.pack(f'{_pk}I', 0)
        for name, sidx, off in _dbg_labels:
            die += _uleb(2)
            die += name.encode() + b'\x00'
            info_relas.append((len(die), sidx, abs64, off))
            die += _pack_addr(0 if is_rela_dw else off)
        if _dbg_labels:
            die += _uleb(0)

        info_body = (_struct.pack(f'{_pk}H', 4)
                     + _struct.pack(f'{_pk}I', 0)
                     + bytes([addr_sz])
                     + bytes(die))
        debug_info = _struct.pack(f'{_pk}I', len(info_body)) + info_body
        _info_prefix = 4 + 2 + 4 + 1
        info_relas = [(_info_prefix + o, s, t, a) for (o, s, t, a) in info_relas]

        files = []
        file_idx = {}
        for (_sec, _wpc, fn, _ln) in line_map:
            fn = fn or "(source)"
            if fn not in file_idx:
                files.append(fn)
                file_idx[fn] = len(files)

        hbody = bytearray()
        hbody += bytes([1])
        hbody += bytes([1])
        hbody += bytes([1])
        hbody += _struct.pack('b', -5)
        hbody += bytes([14])
        hbody += bytes([13])
        hbody += bytes([0, 1, 1, 1, 1, 0, 0, 0, 1, 0, 0, 1])
        hbody += b'\x00'
        for fn in files:
            hbody += fn.encode() + b'\x00' + _uleb(0) + _uleb(0) + _uleb(0)
        hbody += b'\x00'

        from collections import defaultdict as _dd
        rows_by_sec = _dd(list)
        for (sec, wpc, fn, ln) in line_map:
            sidx = sec_name_to_idx.get(sec)
            if sidx is None:
                continue
            rows_by_sec[sidx].append((wpc, file_idx.get(fn or "(source)", 1), ln))

        line_relas = []
        prog = bytearray()
        prog_base = 4 + 2 + 4 + len(hbody)

        for sidx in sorted(rows_by_sec.keys()):
            rows = sorted(rows_by_sec[sidx], key=lambda r: r[0])
            csec = csecs[sidx - 1]

            def _woff(wpc, _name=csec.name):
                _o = self._addr_to_word_offset(_name, wpc)
                return _o if _o is not None else 0
            first_off = _woff(rows[0][0]) * bpw
            prog += b'\x00' + _uleb(1 + addr_sz) + b'\x02'
            line_relas.append((prog_base + len(prog), sidx, abs64, first_off))
            prog += _pack_addr(0 if is_rela_dw else first_off)
            cur_off = first_off
            cur_line = 1
            cur_file = 1
            for (wpc, fidx, ln) in rows:
                byte_off = _woff(wpc) * bpw
                if fidx != cur_file:
                    prog += bytes([4]) + _uleb(fidx)
                    cur_file = fidx
                if ln != cur_line:
                    prog += bytes([3]) + _sleb(ln - cur_line)
                    cur_line = ln
                if byte_off > cur_off:
                    prog += bytes([2]) + _uleb(byte_off - cur_off)
                    cur_off = byte_off
                prog += bytes([1])
            end_off = csec.byte_size
            if end_off > cur_off:
                prog += bytes([2]) + _uleb(end_off - cur_off)
            prog += b'\x00' + _uleb(1) + b'\x01'

        line_body = (_struct.pack(f'{_pk}H', 4)
                     + _struct.pack(f'{_pk}I', len(hbody))
                     + bytes(hbody)
                     + bytes(prog))
        debug_line = _struct.pack(f'{_pk}I', len(line_body)) + line_body

        def _pack_dbg_relocs(entries):
            out = bytearray()
            if is_rela_dw:
                if is_elf64_dw:
                    _MAX, _MIN = (1 << 63) - 1, -(1 << 63)
                    for (off, sym, rtype, addend) in entries:
                        r_info = (sym << 32) | (rtype & 0xffffffff)
                        a = min(_MAX, max(_MIN, addend))
                        out += _struct.pack(f'{_pk}QQq', off, r_info, a)
                else:
                    _MAX, _MIN = (1 << 31) - 1, -(1 << 31)
                    for (off, sym, rtype, addend) in entries:
                        r_info = ((sym & 0xffffff) << 8) | (rtype & 0xff)
                        a = min(_MAX, max(_MIN, addend))
                        out += _struct.pack(f'{_pk}IIi', off, r_info, a)
            else:
                for (off, sym, rtype, _addend) in entries:
                    if is_elf64_dw:
                        r_info = (sym << 32) | (rtype & 0xffffffff)
                        out += _struct.pack(f'{_pk}QQ', off, r_info)
                    else:
                        r_info = ((sym & 0xffffff) << 8) | (rtype & 0xff)
                        out += _struct.pack(f'{_pk}II', off, r_info)
            return bytes(out)

        prog_sections = [
            ('.debug_abbrev', abbrev),
            ('.debug_info',   debug_info),
            ('.debug_line',   debug_line),
        ]
        _dbg_prefix = '.rela' if is_rela_dw else '.rel'
        rela_list = []
        if info_relas:
            rela_list.append((f'{_dbg_prefix}.debug_info', '.debug_info', _pack_dbg_relocs(info_relas)))
        if line_relas:
            rela_list.append((f'{_dbg_prefix}.debug_line', '.debug_line', _pack_dbg_relocs(line_relas)))

        return prog_sections, rela_list

    def write_elf_obj(self, path: str, machine: int = 62) -> None:
        """ELF 再配置可能オブジェクトを書く。

        セクション・シンボル表・リロケーションを組み、必要なら DWARF も
        付ける。マシン記述は elf_machine_table() が返す実表から取るので、
        組み込みの表に無い CPU でもパターンファイルの宣言だけで出せる。
        型の決まらない参照はリロケーションを出さない（当てずっぽうの
        型番号を書いてリンカを騙さないため）。
        """
        import struct as _struct

        bpw = max(1, (self.state.bts + 7) // 8)
        buf = self.binary_writer._buffer

        _is_le    = (self.state.endian != 'big')
        _ei_data  = 1 if _is_le else 2
        _pk       = '<' if _is_le else '>'

        _mach_tbl_w = elf_machine_table(self.state)
        _native_elfclass = _mach_tbl_w['elfclass']
        _elfclass  = getattr(self.state, 'elf_class', None) or _native_elfclass
        if _elfclass != _native_elfclass:
            self.state.diag(
                f" warning - -f forced ELF{'64' if _elfclass == 2 else '32'} for "
                f"machine {machine}, whose conventional class is "
                f"ELF{'64' if _native_elfclass == 2 else '32'}; writing a "
                f"non-default (but well-formed) combination.",
                set_error=False)
        _is_elf64  = (_elfclass == 2)
        _ehdr_size = 64 if _is_elf64 else 52
        _word_mask = 0xFFFFFFFFFFFFFFFF if _is_elf64 else 0xFFFFFFFF

        _hdr        = self.state.elf.decl_hdr
        _e_flags    = _hdr.get('flags', 0) & 0xFFFFFFFF
        _e_version  = _hdr.get('version', 1) & 0xFFFFFFFF
        _e_entry    = _hdr.get('entry', 0) & _word_mask
        _ei_osabi   = _hdr.get('osabi', self.state.osabi) & 0xFF
        _ei_abiver  = _hdr.get('abiversion', 0) & 0xFF

        def _pack_ehdr(e_type, e_machine, e_shoff, e_shnum, e_shstrndx):
            e_type = _hdr.get('type', e_type) & 0xFFFF
            ident = (b'\x7fELF'
                     + bytes([2 if _is_elf64 else 1, _ei_data, 1, _ei_osabi, _ei_abiver])
                     + b'\x00' * 7)
            if _is_elf64:
                return ident + _struct.pack(f'{_pk}HHIQQQIHHHHHH',
                    e_type, e_machine,
                    _e_version,
                    _e_entry,
                    0,
                    e_shoff,
                    _e_flags,
                    _ehdr_size,
                    0, 0,
                    64,
                    e_shnum,
                    e_shstrndx)
            else:
                return ident + _struct.pack(f'{_pk}HHIIIIIHHHHHH',
                    e_type, e_machine,
                    _e_version,
                    _e_entry,
                    0,
                    e_shoff,
                    _e_flags,
                    _ehdr_size,
                    0, 0,
                    40,
                    e_shnum,
                    e_shstrndx)

        def _pack_shdr(sh_name, sh_type, sh_flags, sh_addr, sh_offset,
                       sh_size, sh_link, sh_info, sh_addralign, sh_entsize):
            if _is_elf64:
                return _struct.pack(f'{_pk}IIQQQQIIQQ',
                    sh_name, sh_type, sh_flags, sh_addr, sh_offset,
                    sh_size, sh_link, sh_info, sh_addralign, sh_entsize)
            return _struct.pack(f'{_pk}IIIIIIIIII',
                sh_name, sh_type, sh_flags, sh_addr, sh_offset,
                sh_size, sh_link, sh_info, sh_addralign, sh_entsize)

        def _pack_sym(st_name, st_info, st_other, st_shndx, st_value, st_size):
            st_value &= _word_mask
            st_size  &= _word_mask
            if _is_elf64:
                return _struct.pack(f'{_pk}IBBHQQ',
                    st_name, st_info, st_other, st_shndx, st_value, st_size)
            return _struct.pack(f'{_pk}IIIBBH',
                st_name, st_value, st_size, st_info, st_other, st_shndx)

        def _align_up(x, a):
            return (x + a - 1) & ~(a - 1)

        def _extract(w_start, w_count):
            n = w_count * bpw
            if n == 0:
                return b''
            pad = int(self.state.padding) & ((1 << self.state.bts) - 1)
            if pad:
                tmp = pad
                if self.state.endian == 'little':
                    pad_bytes = bytes([(tmp >> (8 * j)) & 0xff for j in range(bpw)])
                else:
                    pad_bytes = bytes([(tmp >> (8 * (bpw - 1 - j))) & 0xff for j in range(bpw)])
                data = bytearray(pad_bytes * w_count)
            else:
                data = bytearray(n)
            for pos, val in buf.items():
                if pos < w_start or pos >= w_start + w_count:
                    continue
                off = (pos - w_start) * bpw
                tmp = val
                if self.state.endian == 'little':
                    for j in range(bpw):
                        if off + j < n:
                            data[off + j] = tmp & 0xff
                        tmp >>= 8
                else:
                    for j in range(bpw - 1, -1, -1):
                        if off + j < n:
                            data[off + j] = tmp & 0xff
                        tmp >>= 8
            return bytes(data)

        class _CSec:
            """ELF へ書くセクション 1 つぶん。名前、位置、中身、属性。"""
            __slots__ = ('name', 'byte_start', 'data', 'byte_size', 'flags',
                         'sh_type', 'align', 'entsize')

            def __init__(self, name, byte_start, data, flags, sh_type, align,
                         entsize):
                self.name       = name
                self.byte_start = byte_start
                self.data       = data
                self.byte_size  = len(data)
                self.flags      = flags
                self.sh_type    = sh_type
                self.align      = align
                self.entsize    = entsize

        csecs = []
        max_w = max(buf.keys(), default=-1)

        if not self.state.sections:
            w_count = max_w + 1 if max_w >= 0 else 0
            _fl0, _sht0, _al0, _es0 = _elf_section_attrs(self.state, '.text')
            csecs.append(_CSec('.text', 0, _extract(0, w_count), _fl0, _sht0,
                               _al0, _es0))
        else:
            sec_names = list(self.state.sections.keys())
            for i, sname in enumerate(sec_names):

                ranges = self._section_word_ranges(sname)
                w0 = ranges[0][0] if ranges else self.state.sections[sname][0]
                byte_start = w0 * bpw
                data = b''.join(_extract(rs, rl) for rs, rl in ranges)
                flags, _sht, _al, _es = _elf_section_attrs(self.state, sname)
                csecs.append(_CSec(sname, byte_start, data, flags, _sht, _al, _es))

        ncs = len(csecs)

        sec_name_to_idx = {s.name: i + 1 for i, s in enumerate(csecs)}

        _is_rela = _mach_tbl_w['is_rela']

        from collections import defaultdict as _defaultdict
        rela_entries = _defaultdict(list)
        for (sname, off, sym_name, rtype, addend, nbytes) in self.state.relocations:
            sidx = sec_name_to_idx.get(sname, 0)
            if sidx:
                rela_entries[sidx].append((off, sym_name, rtype, addend, nbytes))
            else:
                if self.state.should_report_errors():
                    self.state.diag(
                        f" error - relocation references unknown section '{sname}'; dropped from output.",
                        set_error=True)

        if not _is_rela:
            for sidx, entries in rela_entries.items():
                csec = csecs[sidx - 1]
                patched = bytearray(csec.data)
                for (off, _sym_name, _rtype, addend, nbytes) in entries:
                    field = addend & ((1 << (nbytes * 8)) - 1)
                    if self.state.endian == 'little':
                        field_bytes = bytes((field >> (8 * j)) & 0xff for j in range(nbytes))
                    else:
                        field_bytes = bytes((field >> (8 * (nbytes - 1 - j))) & 0xff
                                             for j in range(nbytes))
                    if 0 <= off and off + nbytes <= len(patched):
                        patched[off:off + nbytes] = field_bytes
                csec.data = bytes(patched)

        rela_sec_order = [i + 1 for i, s in enumerate(csecs) if (i + 1) in rela_entries]
        nrela = len(rela_sec_order)

        dbg_prog, dbg_rela = self._build_dwarf_sections(
            csecs, sec_name_to_idx, bpw, machine)

        shstrtab = bytearray(b'\x00')
        sec_name_offs = []
        for s in csecs:
            sec_name_offs.append(len(shstrtab))
            shstrtab += s.name.encode() + b'\x00'
        _rela_prefix = '.rela' if _is_rela else '.rel'
        rela_name_offs = []
        for sidx in rela_sec_order:
            rela_name_offs.append(len(shstrtab))
            shstrtab += (_rela_prefix + csecs[sidx - 1].name).encode() + b'\x00'
        symtab_name_off   = len(shstrtab)
        shstrtab += b'.symtab\x00'
        strtab_name_off   = len(shstrtab)
        shstrtab += b'.strtab\x00'
        shstrtab_name_off = len(shstrtab)
        shstrtab += b'.shstrtab\x00'
        dbg_prog_name_offs = []
        for (dname, _ddata) in dbg_prog:
            dbg_prog_name_offs.append(len(shstrtab))
            shstrtab += dname.encode() + b'\x00'
        dbg_rela_name_offs = []
        for (rname, _tname, _rdata) in dbg_rela:
            dbg_rela_name_offs.append(len(shstrtab))
            shstrtab += rname.encode() + b'\x00'
        shstrtab = bytes(shstrtab)

        def _find_shndx(byte_addr, sec_name=None):
            word_pc = byte_addr // bpw if bpw else 0
            if sec_name is not None:
                _idx = sec_name_to_idx.get(sec_name)
                if _idx is not None:
                    _woff = self._addr_to_word_offset(sec_name, word_pc)
                    if _woff is not None:
                        return _idx, _woff * bpw
            for i, s in enumerate(csecs):
                _woff = self._addr_to_word_offset(s.name, word_pc)
                if _woff is not None:
                    return i + 1, _woff * bpw
            if csecs:
                best_i = 0
                best_start = csecs[0].byte_start
                for i, s in enumerate(csecs):
                    if s.byte_start <= byte_addr and s.byte_start >= best_start:
                        best_i = i
                        best_start = s.byte_start
                sym_val = byte_addr - csecs[best_i].byte_start
                if sym_val < 0:
                    sym_val = 0
                return best_i + 1, sym_val
            return 0xfff1, byte_addr

        strtab = bytearray(b'\x00')
        syms   = []

        syms.append(_pack_sym(0, 0, 0, 0, 0, 0))

        for i in range(ncs):
            syms.append(_pack_sym(0, 0x03, 0, i + 1, 0, 0))

        export_keys = set(self.state.export_labels.keys())

        for name, *_lentry in sorted(self.state.labels.items()):
            val         = _lentry[0][0]
            _lsec       = _lentry[0][1]
            is_equ      = len(_lentry[0]) > 2 and _lentry[0][2]
            is_imported = len(_lentry[0]) > 3 and _lentry[0][3]
            if name in export_keys or is_imported:
                continue
            _equ_has_reloc = is_equ and len(_lentry[0]) > 4 and _lentry[0][4] is not None
            if is_equ and not _equ_has_reloc:
                shndx, sym_val = 0xfff1, val
            else:
                byte_addr = val * bpw
                shndx, sym_val = _find_shndx(byte_addr, _lsec)
            sym_val = int(sym_val) & _word_mask
            _sa = _sym_attr(self.state, name)
            _sz = _sym_size_of(self.state, name, bpw)
            shndx, sym_val, _sz = _sym_common_override(
                self.state, name, bpw, shndx, sym_val, _sz)
            name_off = len(strtab)
            strtab += name.encode() + b'\x00'
            syms.append(_pack_sym(name_off, _sym_st_info(self.state, name, 0),
                                  _sa[_SA_OTHER], shndx,
                                  int(sym_val) & _word_mask, _sz))

        first_global = len(syms)

        for name, *_lentry in sorted(self.state.labels.items()):
            is_imported = len(_lentry[0]) > 3 and _lentry[0][3]
            if not is_imported or name in export_keys:
                continue
            _sa = _sym_attr(self.state, name)
            _shndx, _sval, _sz = _sym_common_override(
                self.state, name, bpw, 0, 0, _sym_size_of(self.state, name, bpw))
            name_off = len(strtab)
            strtab += name.encode() + b'\x00'
            syms.append(_pack_sym(name_off, _sym_st_info(self.state, name, 1),
                                  _sa[_SA_OTHER], _shndx,
                                  int(_sval) & _word_mask, _sz))

        for name, *_eentry in sorted(self.state.export_labels.items()):
            val, _sec = _eentry[0][0], _eentry[0][1]
            if _is_undef_derived(val):
                continue
            is_equ = len(_eentry[0]) > 2 and _eentry[0][2]
            _lbl = self.state.labels.get(name, [])
            _equ_has_reloc = is_equ and len(_lbl) > 4 and _lbl[4] is not None
            if is_equ and not _equ_has_reloc:
                shndx, sym_val = 0xfff1, val
            else:
                byte_addr = val * bpw
                shndx, sym_val = _find_shndx(byte_addr, _sec)
            sym_val = int(sym_val) & _word_mask
            _sa = _sym_attr(self.state, name)
            shndx, sym_val, _sz = _sym_common_override(
                self.state, name, bpw, shndx, sym_val,
                _sym_size_of(self.state, name, bpw))
            name_off = len(strtab)
            strtab += name.encode() + b'\x00'
            syms.append(_pack_sym(name_off, _sym_st_info(self.state, name, 1),
                                  _sa[_SA_OTHER], shndx,
                                  int(sym_val) & _word_mask, _sz))

        symtab = b''.join(syms)
        strtab = bytes(strtab)

        sym_name_to_idx = {}
        _si = 1 + ncs

        for name, *_lentry in sorted(self.state.labels.items()):
            is_imported = len(_lentry[0]) > 3 and _lentry[0][3]
            if name in export_keys or is_imported:
                continue
            sym_name_to_idx[name] = _si
            _si += 1

        for name, *_lentry in sorted(self.state.labels.items()):
            is_imported = len(_lentry[0]) > 3 and _lentry[0][3]
            if not is_imported or name in export_keys:
                continue
            sym_name_to_idx[name] = _si
            _si += 1

        for name, *_eentry in sorted(self.state.export_labels.items()):
            val = _eentry[0][0]
            if _is_undef_derived(val):
                continue
            sym_name_to_idx[name] = _si
            _si += 1

        _RELA_ENTSIZE = 24 if _is_elf64 else 12
        _REL_ENTSIZE  = 16 if _is_elf64 else 8
        _REL_ENTSIZE_ACTIVE = _RELA_ENTSIZE if _is_rela else _REL_ENTSIZE

        def _pack_rela(r_offset, r_sym, r_type, r_addend):
            if _is_elf64:
                r_info = (r_sym << 32) | (r_type & 0xffffffff)
                _MAX, _MIN = (1 << 63) - 1, -(1 << 63)
                if r_addend > _MAX:
                    r_addend = _MAX
                elif r_addend < _MIN:
                    r_addend = _MIN
                return _struct.pack(f'{_pk}QQq', r_offset, r_info, r_addend)
            r_info = ((r_sym & 0xffffff) << 8) | (r_type & 0xff)
            _MAX, _MIN = (1 << 31) - 1, -(1 << 31)
            if r_addend > _MAX:
                r_addend = _MAX
            elif r_addend < _MIN:
                r_addend = _MIN
            return _struct.pack(f'{_pk}IIi', r_offset, r_info, r_addend)

        def _pack_rel(r_offset, r_sym, r_type):
            if _is_elf64:
                r_info = (r_sym << 32) | (r_type & 0xffffffff)
                return _struct.pack(f'{_pk}QQ', r_offset, r_info)
            r_info = ((r_sym & 0xffffff) << 8) | (r_type & 0xff)
            return _struct.pack(f'{_pk}II', r_offset, r_info)

        if not _is_elf64:
            _warned_rt = set()
            _warned_sym = False
            for sidx in rela_sec_order:
                for (_off, _sn, _rt, _ad, _nb) in rela_entries[sidx]:
                    if _rt > 0xFF and _rt not in _warned_rt:
                        _warned_rt.add(_rt)
                        self.state.diag(
                            f" warning - relocation type {_rt} does not fit the "
                            f"8-bit type field of an ELF32 r_info; it is written "
                            f"as {_rt & 0xFF}.", set_error=False)
                    if not _warned_sym and sym_name_to_idx.get(_sn, 0) > 0xFFFFFF:
                        _warned_sym = True
                        self.state.diag(
                            " warning - more than 16777215 symbols: the symbol "
                            "index does not fit the 24-bit field of an ELF32 "
                            "r_info.", set_error=False)

        rela_datas = []
        for sidx in rela_sec_order:
            entries = rela_entries[sidx]
            if _is_rela:
                data = b''.join(
                    _pack_rela(off, sym_name_to_idx.get(sn, 0), rtype, addend)
                    for (off, sn, rtype, addend, _nbytes) in entries
                )
            else:
                data = b''.join(
                    _pack_rel(off, sym_name_to_idx.get(sn, 0), rtype)
                    for (off, sn, rtype, _addend, _nbytes) in entries
                )
            rela_datas.append(data)

        def _is_nobits(s):
            return s.sh_type == 8

        offset = _ehdr_size
        sec_offsets = []
        for s in csecs:
            offset = _align_up(offset, 16)
            sec_offsets.append(offset)
            if not _is_nobits(s):
                offset += s.byte_size

        rela_offsets = []
        for rd in rela_datas:
            offset = _align_up(offset, 8)
            rela_offsets.append(offset)
            offset += len(rd)

        symtab_off  = _align_up(offset, 8)
        offset = symtab_off + len(symtab)
        strtab_off  = offset
        offset += len(strtab)
        shstrtab_off = offset
        offset += len(shstrtab)

        base_idx = ncs + nrela + 3
        dbg_prog_offsets = []
        dbg_prog_shndx = {}
        for i, (dname, ddata) in enumerate(dbg_prog):
            offset = _align_up(offset, 1)
            dbg_prog_offsets.append(offset)
            dbg_prog_shndx[dname] = base_idx + 1 + i
            offset += len(ddata)
        dbg_rela_offsets = []
        for i, (rname, tname, rdata) in enumerate(dbg_rela):
            offset = _align_up(offset, 8)
            dbg_rela_offsets.append(offset)
            offset += len(rdata)

        shdr_off    = _align_up(offset, 8)

        ndbg = len(dbg_prog) + len(dbg_rela)
        total_shdrs = 1 + ncs + nrela + 3 + ndbg
        shstrndx    = ncs + nrela + 3
        symtab_shidx = ncs + nrela + 1
        strtab_shidx = ncs + nrela + 2
        symtab_link = strtab_shidx

        try:
            _elf_file = open(path, 'wb')
        except OSError as _e:
            self.state.diag(f" error - cannot create ELF output file '{path}': {_e}", set_error=True)
            return
        with _elf_file as f:
            f.write(_pack_ehdr(1, machine, shdr_off, total_shdrs, shstrndx))

            for i, s in enumerate(csecs):
                cur = f.tell()
                f.write(b'\x00' * (sec_offsets[i] - cur))
                if not _is_nobits(s):
                    f.write(s.data)

            for i, rd in enumerate(rela_datas):
                cur = f.tell()
                f.write(b'\x00' * (rela_offsets[i] - cur))
                f.write(rd)

            cur = f.tell()
            f.write(b'\x00' * (symtab_off - cur))
            f.write(symtab)

            f.write(strtab)

            f.write(shstrtab)

            for i, (dname, ddata) in enumerate(dbg_prog):
                cur = f.tell()
                f.write(b'\x00' * (dbg_prog_offsets[i] - cur))
                f.write(ddata)
            for i, (rname, tname, rdata) in enumerate(dbg_rela):
                cur = f.tell()
                f.write(b'\x00' * (dbg_rela_offsets[i] - cur))
                f.write(rdata)

            cur = f.tell()
            f.write(b'\x00' * (shdr_off - cur))

            f.write(_pack_shdr(0, 0, 0, 0, 0, 0, 0, 0, 0, 0))

            for i, s in enumerate(csecs):
                _sh_type_i = s.sh_type
                _al_i = (s.align if s.align is not None
                         else _elf_default_align(_sh_type_i, _is_elf64))
                f.write(_pack_shdr(
                    sec_name_offs[i], _sh_type_i, s.flags, 0,
                    sec_offsets[i], s.byte_size, 0, 0, _al_i, s.entsize))

            _word_align = 8 if _is_elf64 else 4
            _sym_entsize = 24 if _is_elf64 else 16
            _rela_sh_type = 4 if _is_rela else 9
            for ri, sidx in enumerate(rela_sec_order):
                f.write(_pack_shdr(
                    rela_name_offs[ri], _rela_sh_type, 0x40, 0,
                    rela_offsets[ri], len(rela_datas[ri]),
                    symtab_shidx, sidx, _word_align, _REL_ENTSIZE_ACTIVE))

            f.write(_pack_shdr(
                symtab_name_off, 2, 0, 0,
                symtab_off, len(symtab),
                symtab_link, first_global, _word_align, _sym_entsize))

            f.write(_pack_shdr(
                strtab_name_off, 3, 0, 0,
                strtab_off, len(strtab), 0, 0, 1, 0))

            f.write(_pack_shdr(
                shstrtab_name_off, 3, 0, 0,
                shstrtab_off, len(shstrtab), 0, 0, 1, 0))

            for i, (dname, ddata) in enumerate(dbg_prog):
                f.write(_pack_shdr(
                    dbg_prog_name_offs[i], 1, 0, 0,
                    dbg_prog_offsets[i], len(ddata), 0, 0, 1, 0))
            for i, (rname, tname, rdata) in enumerate(dbg_rela):
                f.write(_pack_shdr(
                    dbg_rela_name_offs[i], _rela_sh_type, 0x40, 0,
                    dbg_rela_offsets[i], len(rdata),
                    symtab_shidx, dbg_prog_shndx.get(tname, 0),
                    _word_align, _REL_ENTSIZE_ACTIVE))

        _dbg_msg = f", {len(dbg_prog)} debug section(s)" if dbg_prog else ""
        _reloc_kind = "rela" if _is_rela else "rel"
        print(f"elf: wrote {path} ({ncs} section(s), {nrela} {_reloc_kind} section(s), "
              f"{len(syms)} symbol(s){_dbg_msg})",
              file=sys.stderr)

    def _build_arg_parser(self):
        """コマンドライン引数の定義。"""
        import argparse
        ap = argparse.ArgumentParser(
            prog='axx',
            description='axx general assembler programmed and designed by Taisuke Maekawa',
            formatter_class=argparse.RawDescriptionHelpFormatter,
        )
        ap.add_argument('patternfile',
                        help='Pattern definition file (.axx)')
        ap.add_argument('sourcefile', nargs='?', default=None,
                        help='Assembly source file (.s). Omit for interactive mode.')

        ap.add_argument('--osabi', dest='elf_osabi', type=str, default='Linux',
                        help='ELF OSABI value (default: Linux; FreeBSD/Linux, case-insensitive)')
        ap.add_argument('-b', dest='outfile', default='',
                        metavar='OUTFILE',
                        help='Output binary file')
        ap.add_argument('-e', dest='expfile', default='',
                        metavar='EXPORT_TSV',
                        help='Export labels to TSV file (plain format)')
        ap.add_argument('-E', dest='expfile_elf', default='',
                        metavar='EXPORT_ELF_TSV',
                        help='Export labels to TSV file (ELF section flags format)')
        ap.add_argument('-i', dest='impfile', default='',
                        metavar='IMPORT_TSV',
                        help='Import labels from TSV file')
        ap.add_argument('-o', dest='elf_objfile', default='',
                        metavar='OBJ_FILE',
                        help='Write ELF relocatable object file (.o); class '
                             'selected by -f (default: ELF64)')
        ap.add_argument('-f', dest='elf_format', type=int, default=None,
                        choices=(32, 64), metavar='{32,64}',
                        help='ELF class for -o output: 64 for ELF64/ELFCLASS64, '
                             '32 for ELF32/ELFCLASS32. Default: the pattern '
                             'file\'s .elfclass, or the conventional class of '
                             'the -m machine (ELF64 if that is unknown too). '
                             'Independent of -m/--machine; a value that does not '
                             'match the machine\'s conventional class (e.g. '
                             '-m 62 -f 32, the real x32 ABI\'s EM_X86_64-in-'
                             'ELFCLASS32 layout) is honored, with a warning. '
                             '-g/--gen-debug DWARF output supports both 32 and 64.')
        ap.add_argument('-m', dest='elf_machine', type=int, default=None,
                        metavar='MACHINE',
                        help='ELF e_machine value (default: the pattern file\'s '
                             '.elfmachine, else 62=EM_X86_64). axx carries '
                             'built-in relocation numbering for 3=i386, 4=M68K, '
                             '20=PowerPC, 21=PowerPC64, 22=s390x, 40=ARM, '
                             '42=SuperH, 43=SPARCV9, 62=x86-64, 183=AArch64, '
                             '243=RISC-V. Any other number is accepted too, but '
                             'then the relocation types must come from the '
                             'pattern file (.elftype / .elfwidth / .elfextern, '
                             'manual 3.7.7); references whose type is unknown '
                             'get no relocation entry rather than a guessed one.')
        ap.add_argument('-v', '--verbose', dest='verbose', action='store_true',
                        default=False,
                        help='Verbose: print assembly listing to stdout (default: silent)')
        ap.add_argument('-V', '--text-output', dest='text_output', action='store_true',
                        default=False,
                        help='Print the text built from string-template patterns '
                             '(.textmode translation output) to stdout (default: silent). '
                             'With -v the same text is shown inside the listing instead.')
        ap.add_argument('-d', '--debug', dest='debug', action='store_true',
                        default=False,
                        help='Enable debug output (forward-ref fallback, relaxation log, etc.)')
        ap.add_argument('-g', '--gen-debug', dest='gen_debug', action='store_true',
                        default=False,
                        help='Generate DWARF debug information (.debug_info/.debug_abbrev/'
                             '.debug_line) in the ELF object so that gdb/lldb can do '
                             'source-level debugging. Effective only together with -o.')
        ap.add_argument('--no-macro', dest='no_macro', action='store_true',
                        default=False,
                        help='Disable the macro preprocessor layer (!if/!while/!def/'
                             '!return/!set and !{...} interpolation), so the source is '
                             'handed to the assembler exactly as written.')
        ap.add_argument('-P', '--macro-expand', dest='macro_expand', nargs='?',
                        const='-', default=None, metavar='FILE',
                        help='Macro-expand the source file and write the resulting '
                             'assembly to FILE (or stdout if FILE is omitted or "-") '
                             'without assembling it. Useful for debugging macros.')
        ap.add_argument('-p', '--macro-expand-pattern', dest='macro_expand_pattern',
                        nargs='?', const='-', default=None, metavar='FILE',
                        help='The pattern-file counterpart of -P: macro-expand the '
                             'pattern file and write the resulting pattern text to '
                             'FILE (or stdout if FILE is omitted or "-") without '
                             'assembling. Useful for debugging pattern-file macros.')
        return ap

    _HOIST_VLIW_FIELDS = ('vliwbits', 'vliwinstbits', 'vliwtemplatebits',
                          'vliwflag')

    def _hdrsnap_take(self):
        """持ち上げたディレクティブを処理し終えた状態を写し取る。

        リラクゼーションの反復ごとにここまで巻き戻せば、先頭の
        ディレクティブを読み直さずに済む。
        """
        st = self.state
        snap = {
            'symbols':           dict(st.symbols),
            'check_constraints': dict(st.check_constraints),
            'reloc_constraints': dict(st.reloc_constraints),
            'enum_defs':         dict(st.enum_defs),
        }
        f = st.hoist_fields
        if 'bits' in f:
            snap['endian'] = st.endian
            snap['bts'] = st.bts
        if 'padding' in f:
            snap['padding'] = st.padding
        if 'symbolc' in f:
            snap['swordchars'] = st.swordchars
        if 'vliw' in f:
            for k in self._HOIST_VLIW_FIELDS:
                snap[k] = getattr(st, k)
            snap['vliwnop'] = list(st.vliwnop)
        st.hdrsnap = snap

    def _hdrsnap_restore(self):
        """写し取った状態へ戻す。"""
        st = self.state
        snap = st.hdrsnap
        st.symbols = dict(snap['symbols'])
        st.check_constraints = dict(snap['check_constraints'])
        st.reloc_constraints = dict(snap['reloc_constraints'])
        st.enum_defs = dict(snap['enum_defs'])
        f = st.hoist_fields
        if 'bits' in f:
            st.endian = snap['endian']
            st.bts = snap['bts']
        if 'padding' in f:
            st.padding = snap['padding']
        if 'symbolc' in f:
            st.swordchars = snap['swordchars']
        if 'vliw' in f:
            for k in self._HOIST_VLIW_FIELDS:
                setattr(st, k, snap[k])
            st.vliwnop = list(snap['vliwnop'])

    def _build_dir_dispatch(self, pat, isdir):
        """ディレクティブ行ごとに、呼ぶべきハンドラを先に決めておく。

        毎行すべてのハンドラを試すのをやめるための前処理。
        """
        d = self.directive_proc
        table = {
            '.setsym':   d.set_symbol,
            '.clearsym': d.clear_symbol,
            '.padding':  d.paddingp,
            '.bits':     d.bits,
            '.symbolc':  d.symbolc,
            '.vliw':     d.vliwp,
            '.check':    d.check_processing,
            '.clrcheck': d.clrcheck_processing,
            '.reloc':    d.reloc_processing,
            '.clrreloc': d.clrreloc_processing,
            '.map':      d.map_processing,
            '.free':     d.free_processing,
            '.passthru': d.passthru_processing,
            '.eol':      d.eol_processing,
            '.textmode': d.textmode_processing,
            '.enum':     d.enum_processing,
            '.clrenum':  d.clrenum_processing,
            '.error':    d.errmsg_processing,
            '.echo':     d.echo_processing,
            '.elftype':  d.elftype_processing,
            '.elfmachine': d.elfmachine_processing,
            '.elfclass':   d.elfclass_processing,
            '.elfrela':    d.elfrela_processing,
            '.elfwidth':   d.elfwidth_processing,
            '.elfextern':  d.elfextern_processing,
            '.elfdwarf':   d.elfdwarf_processing,
            '.elfheader':  d.elfheader_processing,
            '.elfsection': d.elfsection_processing,
            '.elffield':   d.elffield_processing,
        }
        out = []
        for row, i in enumerate(pat):
            fn = None
            if isdir[row] and i and i[0]:
                fn = table.get(i[0])
                if fn is None:
                    fn = d.epic
            out.append(fn)
        return out

    def _macro_expand_only(self, sourcefile, dest):
        """`-P` — ソースをマクロ展開して書き出し、アセンブルせずに終わる。"""
        self.macro_proc.reset_pass()
        try:
            with open(sourcefile, "rt", encoding="utf-8", errors="surrogateescape") as f:
                raw = f.readlines()
        except OSError as e:
            self.state.diag(f" error - cannot open source file '{sourcefile}': {e}", set_error=False, force=True)
            return False
        except UnicodeDecodeError as e:
            self.state.diag(f" error - source file '{sourcefile}' is not valid UTF-8: {e}", set_error=False, force=True)
            return False

        expanded = self.macro_proc.expand(raw, sourcefile)
        if self.macro_proc.had_error or self.state.had_error:
            return False

        out = []
        for text, fname, ln in expanded:
            out.append(f"{text}\n")
        data = ''.join(out)
        if dest in ('-', ''):
            sys.stdout.write(data)
        else:
            try:
                with open(dest, "wt", encoding="utf-8", errors="surrogateescape") as f:
                    f.write(data)
            except OSError as e:
                self.state.diag(f" error - cannot write '{dest}': {e}", set_error=False, force=True)
                return False
        return True

    def _pat_macro_expand_only(self, patternfile, dest):
        """`-p` — パターンファイルをマクロ展開して書き出して終わる。"""
        self.pat_macro_proc.reset_pass()
        try:
            with open(patternfile, "rt", encoding="utf-8", errors="surrogateescape") as f:
                raw = f.readlines()
        except OSError as e:
            self.state.diag(f" error - cannot open pattern file '{patternfile}': {e}",
                            set_error=False, force=True)
            return False
        except UnicodeDecodeError as e:
            self.state.diag(f" error - pattern file '{patternfile}' is not valid UTF-8: {e}",
                            set_error=False, force=True)
            return False

        expanded = self.pat_macro_proc.expand(raw, patternfile)
        if self.pat_macro_proc.had_error or self.state.had_error:
            return False

        data = ''.join(text + "\n" for text, _fname, _ln in expanded)
        if dest in ('-', ''):
            sys.stdout.write(data)
        else:
            try:
                with open(dest, "wt", encoding="utf-8", errors="surrogateescape") as f:
                    f.write(data)
            except OSError as e:
                self.state.diag(f" error - cannot write '{dest}': {e}",
                                set_error=False, force=True)
                return False
        return True

    @staticmethod
    def _normalise_macro_expand_argv(argv):
        """`-P` / `-p` の省略可能なファイル名を引数解析器に合う形へ整える。"""
        _with_arg = {'--osabi', '-b', '-e', '-E', '-f', '-i', '-o', '-m'}
        out, positional, i = [], 0, 0
        while i < len(argv):
            a = argv[i]
            if a in _with_arg and i + 1 < len(argv):
                out += [a, argv[i + 1]]
                i += 2
                continue
            if a in ('-P', '--macro-expand', '-p', '--macro-expand-pattern'):
                need = 1 if a in ('-p', '--macro-expand-pattern') else 2
                nxt = argv[i + 1] if i + 1 < len(argv) else None
                if nxt == '-':
                    out += [a, '-']
                    i += 2
                elif (nxt is not None and not nxt.startswith('-')
                        and positional >= need):
                    out += [a, nxt]
                    i += 2
                elif nxt is not None and not nxt.startswith('-'):
                    _long = ('--macro-expand-pattern'
                             if a in ('-p', '--macro-expand-pattern')
                             else '--macro-expand')
                    _what = ('the pattern file'
                             if a in ('-p', '--macro-expand-pattern')
                             else 'the pattern/source files')
                    diag(f" error - '{a} {nxt}' is ambiguous here: {nxt!r} could be "
                         f"{a}'s output file or a positional argument. Write "
                         f"'{_long}={nxt}', or put {a} after {_what}.",
                         set_error=False, force=True)
                    sys.exit(2)
                else:
                    out += [a, '-']
                    i += 1
                continue
            if not a.startswith('-'):
                positional += 1
            out.append(a)
            i += 1
        return out

    def run(self):
        """入口。引数を読み、パターンとソースを読み、出力を書く。

        パス1はリラクゼーションで、最大 MAX_RELAX (16) 回まわす。各反復の
        終わりに「ラベル → (アドレス, セクション)」の写しを取り、過去の写しと
        同じものが出たら、周期 1 なら収束として抜け、周期 2 以上なら振動として
        報告し中断する。単純な繰り返しでは収束しないことが決まるからで、
        誤ったアドレスのコードを出すよりは何も出さない。16 回で終わらない
        場合も同様に中断し、まだ動いているラベル名を挙げる。

        パス2は確定アドレスで 1 回だけ回し、バイト列とリロケーションを作る。
        パス1と食い違っていればそこでもエラーにする。
        """
        ap = self._build_arg_parser()

        if len(sys.argv) == 1:
            ap.print_help()
            return True

        args = ap.parse_args(self._normalise_macro_expand_argv(sys.argv[1:]))

        osabitbl = {'linux': 0, 'freebsd': 9}

        self.state.outfile      = args.outfile
        self.state.expfile      = args.expfile
        self.state.expfile_elf  = args.expfile_elf
        self.state.impfile      = args.impfile
        self.state.elf_objfile  = args.elf_objfile

        if args.elf_machine is not None:
            if not 0 <= args.elf_machine <= 65535:
                self.state.diag(f" error - -m/--machine value {args.elf_machine} is out of "
                     f"range (an ELF e_machine number is 0..65535).",
                     set_error=False, force=True)
                return False
            self.state.elf_machine = args.elf_machine
            self.state.elf.machine_from_cli = True
            if args.elf_machine not in ELF_MACHINES and args.elf_objfile:
                _known = ', '.join(f"{m} ({ELF_MACHINES[m]['name']})" for m in sorted(ELF_MACHINES))
                self.state.diag(f" warning - -m/--machine value {args.elf_machine} is not one of "
                     f"the machines axx has built-in relocation numbering for ({_known}); "
                     f"relocation types must come from the pattern file (.elftype / "
                     f".elfwidth / .elfextern). References whose type is not declared get "
                     f"no relocation entry, rather than a guessed (and wrong) one.",
                     set_error=False, force=True)

        self.state.elf_class    = None if args.elf_format is None else \
                                  (2 if args.elf_format == 64 else 1)

        _osabi_key = args.elf_osabi.lower()
        if _osabi_key not in osabitbl:
            print(f"warning: unknown --osabi value '{args.elf_osabi}'; "
                  f"valid choices are {list(osabitbl.keys())} (case-insensitive). Using 'Linux'.",
                  file=sys.stderr)
        self.state.osabi        = osabitbl.get(_osabi_key, 0)
        self.state.verbose      = args.verbose
        self.state.text_output  = args.text_output
        self.state.debug        = args.debug
        self.state.gen_debug    = args.gen_debug
        self.macro_proc.enabled = not args.no_macro
        self.pat_macro_proc.enabled = not args.no_macro

        if args.macro_expand_pattern is not None:
            return self._pat_macro_expand_only(args.patternfile,
                                               args.macro_expand_pattern)

        if args.macro_expand is not None:
            if args.sourcefile is None:
                self.state.diag(" error - -P/--macro-expand needs a source file.", set_error=False, force=True)
                return False
            return self._macro_expand_only(args.sourcefile, args.macro_expand)

        try:
            self.state.pat = self.pattern_reader.readpat(args.patternfile)
            self.state.pat_isdir = [_pat_is_directive(_p) for _p in self.state.pat]
            (self.state.pat_index,
             self.state.pat_always,
             self.state.pat_maxkey) = _build_pat_index(self.state.pat,
                                                       self.state.pat_isdir)
            (self.state.hoist_rows,
             self.state.hoist_fields) = _pat_hoist_scan(self.state.pat,
                                                        self.state.pat_isdir)
            self.state.hoist_first_ai = sum(
                1 for _r in self.state.pat_always if _r < self.state.hoist_rows)
            self.state.pat_dirfn = self._build_dir_dispatch(self.state.pat,
                                                            self.state.pat_isdir)
            self.state.sub_defs = self.pattern_reader.subs
            self.state.func_defs = self.pattern_reader.funcs
            if self.state.had_error:
                self.state.diag(" error - one or more errors were reported during assembly; "
                                "output would be incomplete or wrong.",
                                set_error=False, force=True)
                self.state.diag("         Aborting: no output file written.",
                                set_error=False, force=True)
                return False
            self.setpatsymbols(self.state.pat)
            self.register_elfdecls(self.state.pat)
            if self.state.had_error:
                self.state.diag(" error - one or more errors were reported while reading "
                                "the pattern file; output would be incomplete or wrong.",
                                set_error=False, force=True)
                self.state.diag("         Aborting: no output file written.",
                                set_error=False, force=True)
                return False

            if self.state.impfile:

                try:
                    with open(self.state.impfile, 'rt', encoding="utf-8",
                              errors="surrogateescape") as label_file:
                        raw_lines = label_file.readlines()
                except OSError as e:
                    self.state.diag(f" error - cannot open import file "
                                    f"'{self.state.impfile}': {e}", set_error=True)
                    return False
                except UnicodeDecodeError as e:
                    self.state.diag(f" error - import file "
                                    f"'{self.state.impfile}' is not valid UTF-8: {e}", set_error=True)
                    return False
                for l in raw_lines:
                    fields = l.rstrip('\r\n').split('\t')
                    if len(fields) >= 3:
                        self.imp_label(l)
                for l in raw_lines:
                    fields = l.rstrip('\r\n').split('\t')
                    if len(fields) == 2:
                        self.imp_label(l)


            if args.sourcefile is None:
                self.state.pc = 0
                self.state.pas = 0
                self.state.ln = 1
                self.state.current_file = "(stdin)"
                while True:
                    self.printaddr(self.state.pc)
                    try:
                        line = input(">> ")
                    except EOFError:
                        break
                    line = line.strip()
                    if line == "":
                        continue
                    if line == "?":
                        self.label_manager.printlabels()
                        continue
                    self.lineassemble0(line)
            else:

                MAX_RELAX = 16
                self.state._pass1_prev_label_pcs = _RELAXATION_SENTINEL
                self.state._relax_prev_values = {}
                self.state._relax_optimistic = False

                _seen_pcs_history = {}

                _imported_labels = dict(self.state.labels)

                _initial_vars = dict(self.state.vars)
                _initial_vars_undef = dict(self.state.vars_undef)

                for relax_iter in range(MAX_RELAX):
                    self.state._relax_optimistic = (relax_iter == 0)
                    self.state._macro_line_pcs_cur = {}
                    self.state.pc = 0
                    self.state.pas = 1
                    self.state.ln = 1
                    self.state.labels = dict(_imported_labels)
                    self.state.sections = {}
                    self.state.export_labels = {}
                    self.state.current_section = '.text'
                    self.state.symbols = dict(self.state.patsymbols)
                    self.state.vars = dict(_initial_vars)
                    self.state.vars_undef = dict(_initial_vars_undef)
                    self.state.section_ranges = []
                    self.fileassemble(args.sourcefile)

                    _last_sec1 = self.state.current_section
                    if _last_sec1 in self.state.sections:
                        _e1 = self.state.sections[_last_sec1]
                        _ep1 = _e1[2] if len(_e1) > 2 else _e1[0]
                        _blk1 = self.state.pc - _ep1
                        if _blk1 > 0:
                            _e1[1] += _blk1
                            self.state.section_ranges.append((_last_sec1, _ep1, _blk1))

                    current_pcs = {k: (v[0], v[1]) for k, v in self.state.labels.items()}
                    has_undef = any(
                        _is_undef_derived(pc)
                        for k, (pc, _sec) in current_pcs.items()
                        if not (len(self.state.labels[k]) > 2 and self.state.labels[k][2])
                    )

                    self.state._relax_prev_values = {
                        k: v[0] for k, v in self.state.labels.items()
                        if not _is_undef_derived(v[0])
                    }

                    self.state._macro_label_values = dict(self.state._relax_prev_values)
                    self.state._macro_label_names = set(self.state.labels)
                    self.state._macro_line_pcs = dict(self.state._macro_line_pcs_cur)
                    if not has_undef:
                        _pcs_key = frozenset(current_pcs.items())
                        _first_seen = _seen_pcs_history.get(_pcs_key)
                        if _first_seen is not None:
                            _cycle_len = (relax_iter + 1) - _first_seen
                            if _cycle_len == 1:
                                if self.state.debug:
                                    print(f"Pass1 relaxation converged after {relax_iter + 1} iteration(s)", file=sys.stderr)
                                break
                            else:
                                self.state.diag(f" error - Pass1 relaxation is oscillating with period "
                                     f"{_cycle_len} (the instruction layout at iteration "
                                     f"{relax_iter + 1} is identical to iteration {_first_seen}); "
                                     f"it will never converge by simple repetition.", set_error=False, force=True)
                                print("         Aborting: no output file written.", file=sys.stderr)
                                return False
                        _seen_pcs_history[_pcs_key] = relax_iter + 1
                    self.state._pass1_prev_label_pcs = current_pcs
                else:

                    self.state.diag(" error - Pass1 relaxation did not converge after {0} iterations.".format(MAX_RELAX), set_error=False, force=True)
                    print("         Generated code would have incorrect addresses for", file=sys.stderr)
                    print("         variable-length instructions with forward references.", file=sys.stderr)
                    print("         Aborting: no output file written.", file=sys.stderr)
                    if isinstance(self.state._pass1_prev_label_pcs, dict):
                        changed = []
                        for k in current_pcs:
                            if k in self.state._pass1_prev_label_pcs:
                                if current_pcs[k] != self.state._pass1_prev_label_pcs[k]:
                                    changed.append(k)
                        if changed:
                            print(f"         Labels still changing: {', '.join(changed[:10])}", file=sys.stderr)
                    return False

                self.state._relax_optimistic = False

                _pass1_final_addrs = {
                    k: v[0] for k, v in self.state.labels.items()
                    if not (len(v) > 2 and v[2])
                }

                self.state.pc = 0
                self.state.pas = 2
                self.state.ln = 1
                self.state.relocations = []
                self.state.line_map = []
                self.state.sections = {}
                self.state.current_section = '.text'
                self.state.section_ranges = []
                self.fileassemble(args.sourcefile)

                _last_sec = self.state.current_section
                if _last_sec in self.state.sections:
                    _e = self.state.sections[_last_sec]
                    _entry_pc = _e[2] if len(_e) > 2 else _e[0]
                    _block = self.state.pc - _entry_pc
                    if _block > 0:
                        _e[1] += _block
                        self.state.section_ranges.append((_last_sec, _entry_pc, _block))

                _drift = []
                for k, p2 in ((kk, vv[0]) for kk, vv in self.state.labels.items()
                              if not (len(vv) > 2 and vv[2])):
                    p1 = _pass1_final_addrs.get(k)
                    if p1 is not None and p1 != p2 and not _is_undef_derived(p2):
                        _drift.append((k, p1, p2))
                if _drift:
                    self.state.diag(" error - address mismatch between pass1 and pass2 "
                                    f"({len(_drift)} label(s)); output addresses are "
                                    f"UNRELIABLE.", set_error=False, force=True)
                    if self.state.reported_label_errors:
                        print("         This is a consequence of the label definition "
                              "error(s) reported above; fix those first.", file=sys.stderr)
                    else:
                        print("         This usually means pass1 relaxation did not fully "
                              "converge for variable-length forward references.", file=sys.stderr)
                    for k, p1, p2 in _drift[:10]:
                        try:
                            print(f"           {k}: pass1=0x{int(p1):X} pass2=0x{int(p2):X}",
                                  file=sys.stderr)
                        except (TypeError, ValueError):
                            print(f"           {k}: pass1={p1!r} pass2={p2!r}", file=sys.stderr)
                    if len(_drift) > 10:
                        print(f"           ... and {len(_drift) - 10} more.", file=sys.stderr)
                    print("         Aborting: no output file written.", file=sys.stderr)
                    return False

                if self.state.had_error:
                    self.state.diag(" error - one or more errors were reported during assembly; "
                         "output would be incomplete or wrong.", set_error=False, force=True)
                    print("         Aborting: no output file written.", file=sys.stderr)
                    return False

            self.binary_writer.flush()

            if self.state.had_error:
                return False

            if self.state.elf_objfile:
                try:
                    self.write_elf_obj(self.state.elf_objfile, self.state.elf_machine)
                except OSError as _we:
                    self.state.diag(f" error - cannot write "
                                    f"'{self.state.elf_objfile}': {_we}", set_error=True)
                if self.state.had_error:
                    self.state.diag(" error - one or more errors were reported during assembly; "
                         "output would be incomplete or wrong.", set_error=False, force=True)
                    print("         Aborting: no output file written.", file=sys.stderr)
                    return False

            if self.state.expfile_elf and self.state.expfile:
                print(f"warning: both -e '{self.state.expfile}' and -E '{self.state.expfile_elf}' specified; "
                      f"exporting plain format to -e and ELF format to -E separately.",
                      file=sys.stderr)

            def _write_export(path, elf):
                h   = list(self.state.export_labels.items())
                key = list(self.state.sections.keys())
                _bpw_export = max(1, (self.state.bts + 7) // 8)
                with open(path, 'wt', encoding="utf-8") as label_file:
                    for i in key:
                        if i == '.text' and elf == 1:
                            flag = 'AX'
                        elif i == '.data' and elf == 1:
                            flag = 'WA'
                        else:
                            flag = ''

                        ranges = [(rs, rl) for (rn, rs, rl) in self.state.section_ranges if rn == i]
                        if not ranges:
                            ranges = [(self.state.sections[i][0], self.state.sections[i][1])]
                        for (w_start, w_count) in ranges:
                            try:
                                byte_start = int(w_start) * _bpw_export
                                byte_size  = int(w_count) * _bpw_export
                            except (OverflowError, ValueError, TypeError):
                                byte_start = 0
                                byte_size  = 0
                            label_file.write(
                                f"{i}\t{byte_start:#x}\t{byte_size:#x}\t{flag}\n"
                            )
                    for i in h:
                        lbl_is_equ = len(i[1]) > 2 and i[1][2]
                        lbl_addr_raw = i[1][0] if lbl_is_equ else i[1][0] * _bpw_export
                        if _is_undef_derived(i[1][0]):
                            continue
                        try:
                            lbl_addr = int(lbl_addr_raw)
                        except (OverflowError, ValueError, TypeError):
                            lbl_addr = 0

                        reloc_type_str = ''
                        if elf == 1:
                            lentry = self.state.labels.get(i[0], [])
                            if len(lentry) > 4 and lentry[4] is not None:
                                _mach_tbl_exp = elf_machine_table(self.state)
                                reloc_type_str = _reloc_reverse(self.state, _mach_tbl_exp, lentry[4])
                                if reloc_type_str:
                                    reloc_type_str = f'::{reloc_type_str}'

                        label_file.write(f"{i[0]}{reloc_type_str}\t{lbl_addr:#x}\n")

            for _exp_path, _exp_elf in ((self.state.expfile, 0),
                                        (self.state.expfile_elf, 1)):
                if not _exp_path:
                    continue
                try:
                    _write_export(_exp_path, elf=_exp_elf)
                except OSError as _we:
                    self.state.diag(f" error - cannot write '{_exp_path}': {_we}",
                                    set_error=True)
                    return False

        finally:
            if self.state.stdin_tmp_path and os.path.exists(self.state.stdin_tmp_path):
                try:
                    os.remove(self.state.stdin_tmp_path)
                except OSError:
                    pass
                self.state.stdin_tmp_path = None

        try:
            sys.stdout.flush()
        except OSError as _oe:
            print(f" error - cannot write to standard output: {_oe}", file=sys.stderr)
            try:
                _devnull = os.open(os.devnull, os.O_WRONLY)
                os.dup2(_devnull, 1)
                os.close(_devnull)
            except OSError:
                sys.stderr.flush()
                os._exit(1)
            return False

        return True


def main():
    """コマンドとしての入口。終了コードを決める。"""
    assembler = Assembler()
    return assembler.run()


if __name__ == '__main__':
    ok = main()
    exit(0 if ok else 1)
