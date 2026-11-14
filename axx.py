#!/usr/bin/env python3
"""axx — パターンファイル駆動の汎用アセンブラ（Python 実装、愛称 Paxx）。

命令セットはコードに持たず、`.axx` パターンファイルの
「命令の書式 :: エラー条件 :: 出力バイト列」の行がすべてを決める。

    axx.py <パターンファイル.axx> <ソース.s> -o <出力.o>

処理の流れ（入口は Assembler.run()）:
  1. パターンファイル読み込み  PatternFileReader.readpat()（.INCLUDE 展開、"::" で分割）
  2. マクロ展開                MacroPreprocessor.expand()（!def / !if / !while ...）
  3. パス1                     長さが収束するまで最大 MAX_RELAX 回（リラクゼーション）
  4. パス2                     確定した番地でバイト列とリロケーションを作る
  5. 出力                      ELF / 生バイナリ / ラベル TSV

計算の 3 層: マクロ層（制限なし）、パターン層（PatternMatcher、停止性を保証）、
ミニ言語（MiniInterp、`.call` のときだけ動く、上限付き）。
caxx.c（C 版）と同じ入力に同じバイト列を出す。食い違いはどちらかのバグ。
"""

from decimal import Decimal, Context, localcontext, ROUND_HALF_EVEN
from fractions import Fraction
try:
    import readline
except ImportError:
    pass
import functools
import itertools
import struct
import sys
import errno
import os
import math
import signal
import re
import tempfile


# パス1で「まだ値が無い」を 0 番地と区別する番兵。
_RELAXATION_SENTINEL = object()

# いま動いている AssemblerState。モジュール関数の diag() がここを見る。
_ACTIVE_STATE = None


def diag(text, set_error=True, force=False):
    """診断を 1 行出す。AssemblerState が無い時期は stderr へ直接書く。"""
    st = _ACTIVE_STATE
    if st is None:
        print(text, file=sys.stderr)
        return True
    return st.diag(text, set_error=set_error, force=force)


class ExprCaps:
    """式評価器で使える項の集合（パターン変数と VLIW 計数を許すか）。"""

    __slots__ = ('name', 'patvars', 'vliw')

    def __init__(self, name, patvars=False, vliw=False):
        self.name = name
        self.patvars = patvars
        self.vliw = vliw

    def __repr__(self):
        return f"<ExprCaps {self.name}>"


CAPS_PAT = ExprCaps('pattern', patvars=True, vliw=True)
CAPS_ASM = ExprCaps('assembly')
CAPS_MINI = ExprCaps('mini language')

# 内部表現の 1 文字: `[[` `]]`（省略可能グループ）、`!S{{表}}` の差し込みの前後
# （caxx.c の SUB_OPEN_CHAR / SUB_CLOSE_CHAR）、ソース行の VLIW 区切り `!!` と終端 `!!!!`。
OB = chr(0x90)
CB = chr(0x91)
SUB_OPEN = chr(0x1e)
SUB_CLOSE = chr(0x1f)
VLIW_SEP = chr(0x92)
VLIW_STOP = chr(0x93)
# caxx.c の VLIW_EMPTY_SLOT_MSG と同じ文面。
_VLIW_EMPTY_SLOT_MSG = (" error - VLIW: empty slot in the packet "
                        "(nothing before or after a '!!').")
_VLIW_NO_VLIW_MSG = (" error - '!!' separates VLIW slots, but the pattern file "
                     "has no .vliw.")

# 未定義ラベルの値。整数なので算術を通って「未定義性」が伝わる。
UNDEF = (1 << 1024) - 1
# 未束縛のパターン変数の値。
VAR_UNDEF = 0
# `.check` の許可リストの `""`（省略可）の印。シンボル名は空にならないので衝突しない。
CHECK_OMIT = ''
# これ以上の大きさなら未定義由来とみなす。2**256 からここまでの帯は一度だけ警告する。
_UNDEF_DERIVED_THRESHOLD = 1 << 768
_UNDEF_SANE_CEILING = 1 << 256
_undef_ceiling_warned = False
# `*(値, 位置)` のシフトの頭打ちと、`x'bits` の幅の上限。
_BYTE_EXTRACT_SHIFT_MAX = 1 << 20
_SEXT_MAX_BITS = 128


def _byte_char(c):
    """1 バイトで書かれた文字（ASCII か surrogateescape の 1 バイト）ならその値、違えば None。"""
    o = ord(c)
    if o < 0x80:
        return o
    if 0xDC80 <= o <= 0xDCFF:
        return o - 0xDC00
    return None


def op_msb(v):
    """`@v` — 最上位の立っているビットの位置（非数・無限は 0）。"""
    if isinstance(v, float) and not math.isfinite(v):
        return 0
    try:
        return int(abs(v)).bit_length()
    except (OverflowError, ValueError):
        return 0


def op_sext(x, bits):
    """`x'bits` の符号拡張。返り値は (値, 伝える文言か None, 成否)。"""
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
    v = x & ((1 << bits) - 1)
    return (v - (1 << bits) if v >> (bits - 1) else v), None, True


def op_byte(x, index):
    """`*(x, index)` — index バイト目より上を残した値。返り値は (値, 文言か None)。"""
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
    """`**` の浮動小数点版。C99 附属書 F の pow() と同じ答え（定義域外は -nan）。"""
    a = float(a)
    b = float(b)
    if b == 0.0 or a == 1.0:
        return 1.0
    if math.isnan(a) or math.isnan(b):
        return float('nan')
    b_is_int = math.isfinite(b) and b == math.floor(b)
    b_is_odd = b_is_int and math.fmod(b, 2.0) != 0.0
    if a == 0.0 and b < 0.0:
        return math.copysign(float('inf'), a) if b_is_odd else float('inf')
    if a < 0.0 and math.isfinite(a) and math.isfinite(b) and not b_is_int:
        return math.copysign(float('nan'), -1.0)
    try:
        return math.pow(a, b)
    except OverflowError:
        return float('-inf') if a < 0.0 and b_is_odd else float('inf')
    except ValueError:
        return math.copysign(float('nan'), -1.0)


def _undef(v):
    """値が番兵 UNDEF そのものか（caxx.c の u256_is_undef()）。演算はこれを毒として伝える。"""
    return type(v) is int and v == UNDEF


def _float_int(v):
    """整数を caxx.c と同じ 256 ビットの符号付きに読み直す。"""
    if type(v) is int:
        v &= (1 << 256) - 1
        return v - (1 << 256) if v >> 255 else v
    return v


def _float_of(v):
    """値を倍精度にする（整数は 256 ビットの符号付き、溢れたら inf）。"""
    try:
        return float(_float_int(v))
    except OverflowError:
        return float('inf')


def _g17(f):
    """C の printf("%.17g") と同じ書き方。"""
    if math.isnan(f):
        return '-nan' if math.copysign(1.0, f) < 0 else 'nan'
    if math.isinf(f):
        return 'inf' if f > 0 else '-inf'
    return '%.17g' % f


def _is_undef_derived(v):
    """値が未定義ラベル由来か（閾値で判定。紛らわしい帯は一度だけ警告）。"""
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
    """命令書式の先頭の大文字の連なり（空白は飛ばす）と、そこでニーモニックが閉じるか。"""
    n = len(pat_text)
    i = 0
    while i < n and (pat_text[i] in CAPITAL or pat_text[i] == ' '):
        i += 1
    return pat_text[:i].replace(' ', ''), (pat_text[i] if i < n else '') not in _PFX_OPEN


# 位置によらず効き方が変わらないディレクティブ（_pat_hoist_scan() が先に処理する）。
_HOIST_TEXT_ONLY = ('.check', '.clrcheck', '.reloc', '.clrreloc',
                    '.symbolc', '.passthru', '.eol', '.textmode',
                    '.elfmachine', '.elfclass', '.elfrela', '.elfwidth',
                    '.elfextern', '.elfdwarf', '.elfheader', '.elfsection',
                    '.elffield', '.elfpcguess', '.elfrelax', '.elfanchor', '.elfresolve',
                    '.elfbuiltin', '.elfextra',
                    '.elfdiff', '.elfencode', '.elfrinfo', '.elfunit', '.elflink',
                    '.elfgroup', '.elfcfi', '.elfcfiinit', '.elfcfireg', '.elfunaligned')
def _pat_text_dynamic(t):
    """欄の中身がソース行ごとに変わりうるか（`!$#@'` か小文字を含む）。"""
    return any(ch in "!$#@'" or 'a' <= ch <= 'z' for ch in t)


def _pat_is_name_list(t):
    """欄が「大文字の名前をカンマで並べたもの」だけで出来ているか。"""
    return (all(ch in ', \t_' or 'A' <= ch <= 'Z' or '0' <= ch <= '9' for ch in t)
            and ',' in t)


def _pat_dir_line_invariant(i):
    """このディレクティブ行をソースを読む前に 1 回だけ処理してよいか（迷えば偽）。"""
    name = i[0]
    const = _CONST_SETSYM_RE.match
    if name == '.setsym':
        nm = i[1] if i[1] else i[2]
        val = i[2] if i[1] else ''
        if _pat_text_dynamic(nm):
            return False
        if not val:
            return True
        v = val.lstrip(' \t')[:1]
        if v in ('"', '['):
            return v == '"'
        return bool(const(val)) or _pat_is_name_list(val)
    if name in _HOIST_TEXT_ONLY:
        return not any(ch in "!$#@" for f in i[1:] if f for ch in f)
    if name == '.bits':
        return all(not f or StringUtils.upper(f) in ('BIG', 'LITTLE') or const(f)
                   for f in i[1:])
    if name in ('.padding', '.vliw'):
        return all(not f or const(f) for f in i[1:])
    if name == '.error':
        return bool(const(i[1])) and i[2].lstrip(' \t')[:1] == '"'
    if name == '.elftype':
        if not i[1] or any(ch in "!$#@'" for ch in i[1]):
            return False
        return all(not f or const(f) for f in i[3:]) and bool(const(i[2]))
    return False


_HOIST_FIELD_OF = {'.bits': 'bits', '.padding': 'padding', '.symbolc': 'symbolc',
                   '.vliw': 'vliw'}


def _pat_hoist_scan(pat, isdir):
    """先頭から何行を事前処理に持ち上げられるか。返り値は (行数, 設定される欄の名前)。

    持ち上げた範囲が読む名前を後の `.setsym` / `.clearsym` / `.free` が
    書き換えるなら、順序が壊れるので持ち上げない。
    """
    h = 0
    fields = set()
    while h < len(pat):
        i = pat[h]
        if i is not None and any(i):
            if not isdir[h] or not _pat_dir_line_invariant(i):
                break
            if i[0] in _HOIST_FIELD_OF:
                fields.add(_HOIST_FIELD_OF[i[0]])
        h += 1
    if h <= 0 or h >= len(pat):
        return 0, fields
    reads = set()
    for i in pat[:h]:
        if i is not None:
            for f in i[1:]:
                reads.update(re.findall(r'[A-Z0-9_]+', f))
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


# `.unordered` で使えないディレクティブ（位置の意味しか持たない）と、先に処理する設定もの。
_UNORDERED_BANNED = ('.clearsym', '.clrcheck', '.clrenum', '.clrreloc', '.free')
_UNORDERED_FIRST = ('.unordered', '.symbolc', '.bits', '.padding', '.vliw',
                    '.passthru', '.eol', '.textmode')


def _unordered_key(i):
    """`.unordered` での重複検査の鍵と、エラーで名指す言い方（鍵が無ければ None）。"""
    name = i[0]
    if name == '.setsym':
        up = StringUtils.upper((i[1] if i[1] else i[2]).strip())
        return '.setsym ' + up, f"symbol '{up}'"
    if name in ('.check', '.map', '.enum', '.reloc'):
        var = (i[1] if i[1].strip() else i[2]).strip().translate(_ALOWER)
        grp = 'check' if name in ('.check', '.map') else name[1:]
        return grp + ' ' + var, f"variable '{var}' ({'.check/.map' if grp == 'check' else name})"
    if name == '.error':
        code = i[1].strip()
        return '.error ' + code, f"error code {code}"
    if name in _UNORDERED_FIRST and name != '.unordered':
        return name, f"'{name}'"
    if _pat_is_directive(i) and name not in _PAT_DIRECTIVES:
        return 'EPIC', "'EPIC'"
    return None, None


def _unordered_refs(text):
    """`.setsym` の値欄の名前（ASCII の英数字と `_` の連なり、大文字化）。`"..."` の中は読まない。"""
    out = []
    n = len(text)
    k = 0
    word = lambda c: c.isascii() and (c.isalnum() or c == '_')
    while k < n:
        ch = text[k]
        if ch == '"':
            k += 1
            while k < n and text[k] != '"':
                k += 2 if text[k] == '\\' else 1
            k += 1
        elif word(ch):
            b = k
            while k < n and word(text[k]):
                k += 1
            out.append(StringUtils.upper(text[b:k]))
        else:
            k += 1
    return out


def _pat_unordered_plan(pat, isdir):
    """`.unordered` のとき、ディレクティブ行を処理する順を返す（宣言が無ければ None）。

    順は 設定もの（_UNORDERED_FIRST と EPIC）→ `.setsym`（依存順）→ その他。
    中身の違う重複定義と _UNORDERED_BANNED はエラー。caxx.c の pat_unordered_plan() と同じ。
    """
    if not any(isdir[r] and pat[r] and pat[r][0] == '.unordered'
               for r in range(len(pat))):
        return None
    first, syms, rest = [], [], []
    seen = {}
    for r, i in enumerate(pat):
        if not isdir[r] or not i:
            continue
        name = i[0]
        if name in _UNORDERED_BANNED:
            diag(f" error - {name}: cannot be used in an .unordered pattern file "
                 f"(pattern line {r + 1}); there every definition holds for the "
                 f"whole file.", set_error=True)
        key, label = _unordered_key(i)
        if key is not None:
            text = '::'.join(f.strip() for f in i)
            prev = seen.setdefault(key, (r, text))
            if prev[1] != text:
                diag(f" error - .unordered: pattern lines {prev[0] + 1} and {r + 1} "
                     f"give {label} two different definitions.", set_error=True)
        if name in _UNORDERED_FIRST or key == 'EPIC':
            first.append(r)
        elif name == '.setsym':
            syms.append(r)
        else:
            rest.append(r)

    symname = lambda r: StringUtils.upper((pat[r][1] if pat[r][1] else pat[r][2]).strip())
    definer = {}
    for r in syms:
        definer.setdefault(symname(r), r)
    deps = {}
    for r in syms:
        val = pat[r][2] if pat[r][1] else ''
        deps[r] = {definer[t] for t in _unordered_refs(val)
                   if t in definer and definer[t] != r}
    done = set()
    order = []
    pending = list(syms)
    while pending:
        nxt = next((r for r in pending if deps[r] <= done), None)
        if nxt is None:
            names = ', '.join("'" + symname(r) + "'" for r in pending)
            diag(f" error - .unordered: the .setsym definitions of {names} refer to "
                 f"each other in a cycle.", set_error=True)
            order.extend(pending)
            break
        order.append(nxt)
        done.add(nxt)
        pending.remove(nxt)
    return first + order + rest


def _build_pat_index(pat, isdir):
    """先頭の大文字列を鍵にしたパターン索引 (index, always, maxkey) を作る。

    鍵ごとに ([続く書式], [そこで閉じる書式])。鍵の無い行とディレクティブは always。
    """
    index = {}
    always = []
    maxkey = 0
    for row, i in enumerate(pat):
        pfx, closed = _lead_caps(i[0]) if i and i[0] else ('', True)
        if not pfx or isdir[row]:
            always.append(row)
            continue
        index.setdefault(pfx, ([], []))[1 if closed else 0].append(row)
        maxkey = max(maxkey, len(pfx))
    return index, always, maxkey


def _pat_candidates(index, maxkey, lin):
    """ソース行に対して照合を試す価値のあるパターン行番号（昇順）。

    空白を飛ばして大文字化した先頭を 1 文字ずつ伸ばして索引を引く。閉じた書式は
    ソース側の次の文字が語を続けないときだけ候補にする（`ADD` が `ADDS` に当たらない）。
    """
    if not maxkey:
        return ()
    cand = []
    key = ''
    for ci, ch in enumerate(lin):
        if ch == ' ':
            continue
        key += _AUP1.get(ch, ch)
        ent = index.get(key)
        if ent is not None:
            cand.extend(ent[0])
            if lin[ci + 1:ci + 2] not in _PFX_WORD:
                cand.extend(ent[1])
        if len(key) >= maxkey:
            break
    if len(cand) > 1:
        cand.sort()
    return cand


# 文字クラス。パターンの命令欄では大文字が文字定数、小文字がパターン変数。
CAPITAL = "ABCDEFGHIJKLMNOPQRSTUVWXYZ"
LOWER = "abcdefghijklmnopqrstuvwxyz"
SET_OPS = "&|^+-"
DIGIT = '0123456789'
XDIGIT = "0123456789ABCDEF"
ALPHABET = LOWER + CAPITAL
# 大文字化・小文字化は ASCII だけ（caxx.c の toupper()/tolower() と同じ。str.upper() は
# 'ı' や 'ſ' まで畳む）。
_AUPPER = str.maketrans(LOWER, CAPITAL)
_ALOWER = str.maketrans(CAPITAL, LOWER)
_AUP1 = dict(zip(LOWER, CAPITAL))
_AALNUM = frozenset(ALPHABET + DIGIT)
# _PFX_OPEN: 先頭大文字列の直後にあればニーモニックはまだ続く。_PFX_WORD: 語を作る文字。
_PFX_OPEN = frozenset(LOWER + DIGIT + '!\\[_')
_PFX_WORD = frozenset(ALPHABET + DIGIT + '_')


def _is_sub_name(s):
    """`.sub::名前` / `!S{{名前}}` に書ける名前か。"""
    return bool(s) and all(c in _PFX_WORD for c in s)


def _dot_kw(s):
    """行頭のドット付きキーワードを大文字で（`.setsym::x::1` なら `.SETSYM`、無ければ ''）。"""
    t = s.strip()
    if not t.startswith('.'):
        return ''
    j = 1
    while j < len(t) and (_aan(t[j]) or t[j] == '_'):
        j += 1
    return StringUtils.upper(t[:j])


def _parse_func_header(l):
    """`.func` のヘッダを読み、(関数名, 引数名のリスト, エラー文言か None) を返す。

    `.func 名前(引数, ...)`（`()` は省ける）と古い `.func::名前::引数` の 2 通り。
    """
    t = l.strip()
    i = 1
    while i < len(t) and (_aan(t[i]) or t[i] == '_'):
        i += 1
    i = StringUtils.skipspc(t, i)
    if t[i:i + 2] == '::':
        hdr = t.split('::')
        nm = hdr[1].strip() if len(hdr) > 1 else ''
        ps = [p.strip() for p in (hdr[2] if len(hdr) > 2 else '').split(',') if p.strip()]
        return nm, ps, None
    j = i
    while j < len(t) and (_aan(t[j]) or t[j] == '_'):
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
    return nm, [p.strip() for p in t[k + 1:e].split(',') if p.strip()], None


# ミニ言語の入れ子の開き／閉じキーワード（`.endfunc` がどれを閉じるかを数える）。
_MINI_OPEN = frozenset(('.IF', '.FOR', '.WHILE'))
_MINI_CLOSE = frozenset(('.ENDIF', '.NEXT', '.ENDWHILE'))


class _MiniFunc:
    """ミニ言語の関数 1 個（`.func` 〜 `.endfunc`）。名前の解決は内側から外側へたどる。"""

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


# error_patterns の `;n` の文言（0 は使わない、空文字は文言なし）。`.error::n::"..."`
# で足せる。caxx.c の ERRORS と同じ並び。
ERRORS = [
    "",
    "Invalid syntax.",
    "Address out of range.",
    "Value out of range.",
    "",
    "Register out of range.",
    "Port number out of range."
]


# `-o` のリロケーションの、e_machine ごとの組み込み表。各欄:
#   name 診断に出す名前 / elfclass 1=ELF32 2=ELF64（-f の既定）/ is_rela .rela か .rel /
#   width_guess 欄の幅 → 推測の型 / pc_rel PC 相対の型 / extern_default 外部参照の既定の型 /
#   named 型名 → (型番号, 欄の幅) / dwarf_abs DWARF の絶対参照の型 /
#   pcrel_guess 値がラベルと違えば同じ幅の PC 相対型にする（m68k）/
#   field 命令欄の型 → (マスク, オフセット, シフト, 補正)（`.elffield` と同じ形）
# どれもパターンファイルの .elf* 宣言で書け、表は「あらかじめ書いた宣言」にすぎない
# （`.elfbuiltin::0` で使わない）。表に無い e_machine も -m に書ける。
# AArch64 の命令欄のマスク（ADR/ADRP は値が 2 つの欄に分かれる）。
_A64_ADR_MASK = (0x3 << 29) | (0x7ffff << 5)
_A64_LO12_MASK = 0xfff << 10
_A64_FIELD_MASKS = {rt: 0xffff << 5 for rt in (*range(263, 270), *range(287, 294))}
_A64_FIELD_MASKS.update({
    274: _A64_ADR_MASK, 275: _A64_ADR_MASK, 276: _A64_ADR_MASK,
    277: _A64_LO12_MASK, 278: _A64_LO12_MASK,
    273: 0x7ffff << 5, 279: 0x3fff << 5, 280: 0x7ffff << 5,
    282: 0x3ffffff, 283: 0x3ffffff,
    284: _A64_LO12_MASK, 285: _A64_LO12_MASK, 286: _A64_LO12_MASK, 299: _A64_LO12_MASK,
    309: 0x7ffff << 5, 311: _A64_ADR_MASK, 312: _A64_LO12_MASK, 313: _A64_LO12_MASK,
})


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
        pcrel_guess=True,
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
            'ld_prel_lo19': (273, 4),
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
        field={rt: (m, 0, 0, 0) for rt, m in _A64_FIELD_MASKS.items()},
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
    """生の表に named（名前 → 型）・reloc_bytes（型 → 幅）・reverse（型 → 最初の名前）を足す。"""
    out = {}
    for machine, entry in raw.items():
        named = {name: rt for name, (rt, _w) in entry['named'].items()}
        reverse = {}
        for name, rt in named.items():
            reverse.setdefault(rt, name)
        out[machine] = dict(entry, named=named,
                            reloc_bytes={rt: w for (rt, w) in entry['named'].values()},
                            reverse=reverse,
                            pcrel_guess=bool(entry.get('pcrel_guess', False)),
                            field=dict(entry.get('field', {})))
    return out


ELF_MACHINES = _build_elf_machine_tables(_ELF_MACHINE_RAW)

# 表に無いマシンの土台。型が無いので、宣言が無ければ型の決まらない参照はリロケーションを出さない。
_ELF_MACHINE_GENERIC = dict(
    name='', elfclass=2, is_rela=True, width_guess={}, pc_rel=frozenset(),
    extern_default=0, named={}, reloc_bytes={}, reverse={}, dwarf_abs=0,
    pcrel_guess=False, field={})


def _elf_decl_type(state, named, text):
    """型の綴りを型番号に（数値 → `.elftype` → 組み込みの順。無ければ None）。"""
    s = (text or '').replace(' ', '').replace('\t', '')
    if not s:
        return None
    try:
        return int(s, 0)
    except ValueError:
        pass
    key = s.translate(_ALOWER)
    rt = state.elftypes.get(key)
    return named.get(key) if rt is None else rt


def elf_machine_table(state):
    """組み込みの表にパターンファイルの .elf* 宣言をかぶせた実効の ELF マシン記述。

    同じ名前なら宣言が勝つ。`.elfbuiltin::0` なら土台は空の表。
    (machine, decl_gen) を鍵に覚える（宣言が増えると decl_gen が進む）。
    """
    e = state.elf
    key = (e.machine, e.decl_gen)
    if e.mach_cache_key == key:
        return e.mach_cache

    base = (_ELF_MACHINE_GENERIC if e.decl_builtin == 0
            else ELF_MACHINES.get(e.machine, _ELF_MACHINE_GENERIC))
    width_guess = dict(base['width_guess'])
    pc_rel = set(base['pc_rel'])

    named, reloc_bytes, reverse = {}, {}, {}
    merged = [(nm, rt, base['reloc_bytes'].get(rt, 0))
              for nm, rt in base['named'].items() if nm not in state.elftypes]
    merged += [(nm, rt, e.type_width.get(nm, 0)) for nm, rt in state.elftypes.items()]
    for nm, rt, w in merged:
        named.setdefault(nm, rt)
        reverse.setdefault(rt, nm)
        if w:
            reloc_bytes.setdefault(rt, w)
    pc_rel.update(rt for rt in map(state.elftypes.get, e.type_pcrel) if rt is not None)

    def ty(text):
        return _elf_decl_type(state, named, text)

    def pick(text, default):
        rt = ty(text)
        return default if rt is None else rt

    for nbytes, text in e.decl_width.items():
        rt = ty(text)
        if rt is not None:
            width_guess[nbytes] = rt
    name = (e.decl_name if e.decl_name and e.decl_machine in (None, e.machine)
            else base['name'] or ("machine %d" % e.machine))

    # 宣言した欄が先、組み込みの欄はその型の宣言が無いときだけ残る。
    field = {}
    for text, fo in e.decl_field.items():
        rt = ty(text)
        if rt is not None:
            field.setdefault(rt, fo)
    for rt, fo in base['field'].items():
        field.setdefault(rt, fo)

    # 添えるリロケーションは宣言の順。別名で同じ型に当たれば続けて足す。
    extra = {}
    for text, comps in e.decl_extra.items():
        rt = ty(text)
        if rt is not None:
            extra.setdefault(rt, []).extend(
                (crt, csym) for crt, csym in ((ty(c), s) for c, s in comps.items())
                if crt is not None)
    diff = {}
    for w, (ta, tb) in e.decl_diff.items():
        ra, rb = ty(ta), ty(tb)
        if ra is not None and rb is not None:
            diff[w] = (ra, rb)
    diff_t = {}
    for text, (ta, tb) in e.decl_diff_t.items():
        rt, ra, rb = ty(text), ty(ta), ty(tb)
        if rt is not None and ra is not None and rb is not None:
            diff_t.setdefault(rt, (ra, rb))
    encode = {}
    for text, fn in e.decl_encode.items():
        rt = ty(text)
        if rt is not None:
            encode.setdefault(rt, fn)
    unaligned = {}
    for text, utext in e.decl_unaligned.items():
        rt, urt = ty(text), ty(utext)
        if rt is not None and urt is not None:
            unaligned.setdefault(rt, urt)

    tbl = dict(base, name=name,
               elfclass=base['elfclass'] if e.decl_class is None else e.decl_class,
               is_rela=base['is_rela'] if e.decl_rela is None else bool(e.decl_rela),
               width_guess=width_guess, pc_rel=pc_rel,
               extern_default=pick(e.decl_extern, base['extern_default']),
               dwarf_abs=pick(e.decl_dwarf, base['dwarf_abs']),
               named=named, reloc_bytes=reloc_bytes, reverse=reverse,
               pcrel_guess=(base['pcrel_guess'] if e.decl_pcguess is None
                            else bool(e.decl_pcguess)),
               field=field, extra=extra, diff=diff, diff_t=diff_t, encode=encode,
               anchor={rt for rt in map(ty, e.decl_anchor) if rt is not None},
               resolve={rt for rt in map(ty, e.decl_resolve) if rt is not None},
               unaligned=unaligned, rinfo=e.decl_rinfo, unit=e.decl_unit or 'byte')
    e.mach_cache_key = key
    e.mach_cache = tbl
    return tbl


def _reloc_same_width(mach, nbytes, want_pcrel):
    """幅と PC 相対かどうかが一致する最初の型（表の順）。無ければ None。"""
    if not mach:
        return None
    return next((rt for rt in mach['named'].values()
                 if mach['reloc_bytes'].get(rt, 0) == nbytes
                 and (rt in mach['pc_rel']) == bool(want_pcrel)), None)


def _sectioned(state):
    """セクション相対の位置で考える出力か（-o か -E）。caxx.c の st_sectioned() と同じ。"""
    return bool(state.elf.objfile or state.expfile_elf)


def _elf_relaxing(state):
    """リンカがコードを縮める機種か（`.elfrelax`、無ければ `.elfdiff` の有無）。caxx.c の elf_relaxing()。"""
    e = state.elf
    if e.decl_relax is not None:
        return bool(e.decl_relax)
    return bool(e.decl_diff or e.decl_diff_t)


def _elf_anchor_at(state, sec, off):
    """sec の off に置くアンカー .Lanchor<n> の名前（同じ位置は同じ名前）。caxx.c の elf_anchor_at()。"""
    for nm, s_, o_ in state.elf.anchors:
        if o_ == off and s_ == sec:
            return nm
    nm = '.Lanchor%d' % len(state.elf.anchors)
    while nm in state.labels or nm in state.export_labels:
        nm += '_'
    state.elf.anchors.append((nm, sec, off))
    return nm


def _reloc_data_kind(mach, nbytes, pcrel):
    """幅 nbytes の、絶対か PC 相対のデータ型（命令欄の型を除く）で表の順に最初のもの。"""
    return next((rt for rt in mach['named'].values()
                 if mach['reloc_bytes'].get(rt, 0) == nbytes
                 and (rt in mach['pc_rel']) == pcrel and rt not in mach['field']), None)


def _reloc_data_abs(mach, nbytes):
    """CFI の絶対の番地の型。無ければ PC 相対でない幅の推測。caxx.c の elf_reloc_data_abs()。"""
    rt = _reloc_data_kind(mach, nbytes, False)
    if rt is not None:
        return rt
    rt = mach['width_guess'].get(nbytes)
    return rt if rt and rt not in mach['pc_rel'] else None


def _reloc_data_pcrel(mach, nbytes):
    """CFI の PC 相対の番地の型。caxx.c の elf_reloc_data_pcrel()。"""
    return _reloc_data_kind(mach, nbytes, True)


def _elf_section_attrs(state, name):
    """セクション名から (sh_flags, sh_type, 整列, 要素サイズ)。`.elfsection` の宣言が推測に勝つ。"""
    uname = name.translate(_AUPPER)
    flags = (0x6 if uname.startswith('.TEXT')
             else 0x3 if uname.startswith(('.DATA', '.BSS')) else 0x2)
    sh_type = 8 if uname.startswith('.BSS') else 1
    align = None
    entsize = 0
    decl = state.elf.decl_sec.get(name.translate(_ALOWER))
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
    """整列の既定値（SHT_NOTE だけ 4）。is_elf64 は caxx.c と呼び出し形をそろえるためだけ。"""
    return 4 if sh_type == 7 else 16


# ソースの `.cfi_*` → 引数の種類（r: レジスタ、n: 数、s: シンボル名、*: 1 つ以上のバイト）。
_CFI_OPS = {
    'startproc': '', 'endproc': '', 'sections': '',
    'def_cfa': 'rn', 'def_cfa_offset': 'n', 'def_cfa_register': 'r',
    'adjust_cfa_offset': 'n', 'offset': 'rn', 'val_offset': 'rn',
    'rel_offset': 'rn', 'restore': 'r', 'undefined': 'r', 'same_value': 'r',
    'register': 'rr', 'remember_state': '', 'restore_state': '',
    'return_column': 'r', 'signal_frame': '', 'window_save': '',
    'negate_ra_state': '', 'escape': '*', 'personality': 'ns', 'lsda': 'ns',
}

_struct_pack = struct.pack


def _cfi_uleb(v):
    """符号なし LEB128。"""
    out = bytearray()
    v = int(v)
    while True:
        b = v & 0x7f
        v >>= 7
        if not v:
            out.append(b)
            return bytes(out)
        out.append(b | 0x80)


def _cfi_sleb(v):
    """符号付き LEB128。"""
    out = bytearray()
    v = int(v)
    while True:
        b = v & 0x7f
        v >>= 7
        if (v == 0 and not (b & 0x40)) or (v == -1 and (b & 0x40)):
            out.append(b)
            return bytes(out)
        out.append(b | 0x80)


def _cfi_op_bytes(op, vals, stt, da):
    """CFI の命令 1 つを DW_CFA_* のバイト列に（誤りは文字列）。caxx.c の cfi_op_bytes() と同じ。

    stt は [CFA のレジスタ, CFA のオフセット, remember_state の積み]。
    """
    U, S = _cfi_uleb, _cfi_sleb

    def bad(o):
        return f"offset {o} is not a multiple of the data alignment factor {da}"

    if op == 'def_cfa':
        r, o = vals
        stt[0], stt[1] = r, o
        if o >= 0:
            return b'\x0c' + U(r) + U(o)
        return bad(o) if o % da else b'\x12' + U(r) + S(o // da)
    if op in ('def_cfa_offset', 'adjust_cfa_offset'):
        o = vals[0] if op == 'def_cfa_offset' else stt[1] + vals[0]
        stt[1] = o
        if o >= 0:
            return b'\x0e' + U(o)
        return bad(o) if o % da else b'\x13' + S(o // da)
    if op == 'def_cfa_register':
        stt[0] = vals[0]
        return b'\x0d' + U(vals[0])
    if op in ('offset', 'rel_offset', 'val_offset'):
        r, o = vals
        if op == 'rel_offset':
            o = o - stt[1]
        if o % da:
            return bad(o)
        f = o // da
        if op == 'val_offset':
            return b'\x14' + U(r) + U(f) if f >= 0 else b'\x15' + U(r) + S(f)
        if f < 0:
            return b'\x11' + U(r) + S(f)
        return bytes([0x80 | r]) + U(f) if r < 64 else b'\x05' + U(r) + U(f)
    if op == 'restore':
        r = vals[0]
        return bytes([0xc0 | r]) if r < 64 else b'\x06' + U(r)
    if op == 'undefined':
        return b'\x07' + U(vals[0])
    if op == 'same_value':
        return b'\x08' + U(vals[0])
    if op == 'register':
        return b'\x09' + U(vals[0]) + U(vals[1])
    if op == 'remember_state':
        stt[2].append((stt[0], stt[1]))
        return b'\x0a'
    if op == 'restore_state':
        if not stt[2]:
            return "restore_state without remember_state"
        stt[0], stt[1] = stt[2].pop()
        return b'\x0b'
    if op in ('window_save', 'negate_ra_state'):
        return b'\x2d'
    if op == 'escape':
        return bytes(vals)
    return f"'{op}' cannot be used here"


_CFI_PTR_SIZES = {0x02: 2, 0x0a: 2, 0x03: 4, 0x0b: 4, 0x04: 8, 0x0c: 8}


def _cfi_ptr_size(enc, psize):
    """ポインタの符号化 enc の大きさ（バイト）。対応しないものは 0。"""
    fmt = enc & 0x0f
    return psize if fmt == 0 else _CFI_PTR_SIZES.get(fmt, 0)


# ソースの `.type` に書ける名前 → ELF の STT_* 値。
ELF_SYM_TYPES = {
    'notype': 0, 'object': 1, 'func': 2, 'function': 2,
    'section': 3, 'file': 4, 'common': 5, 'tls': 6, 'tls_object': 6,
    'gnu_ifunc': 10, 'ifunc': 10,
}

# シンボル 1 個ぶんの属性（`.type` `.size` `.weak` `.hidden` `.other` `.comm` ...）の添字。
_SYM_ATTR_DEFAULT = (0, 0, 0, 0, 0, 0, 0)
_SA_TYPE, _SA_SIZE_SET, _SA_SIZE, _SA_OTHER, _SA_WEAK, _SA_COMMON, _SA_ALIGN = range(7)


def _sym_attr(state, name):
    """シンボルの属性を読む（無ければ既定。表は増やさない）。"""
    return state.sym_attrs.get(name, _SYM_ATTR_DEFAULT)


def _sym_attr_slot(state, name):
    """シンボルの属性を書く枠（無ければ作って登録する）。"""
    a = state.sym_attrs.get(name)
    if a is None:
        a = state.sym_attrs[name] = list(_SYM_ATTR_DEFAULT)
    return a


def _sym_st_info(state, name, bind):
    """st_info を組む（`.weak` なら STB_WEAK）。"""
    a = _sym_attr(state, name)
    return (((2 if a[_SA_WEAK] else bind) & 0xF) << 4) | (a[_SA_TYPE] & 0xF)


def _sym_common_override(state, name, bpw, shndx, value, size):
    """`.comm` のシンボルなら (SHN_COMMON, 整列, ワード数×幅)、違えば渡されたまま。"""
    a = _sym_attr(state, name)
    if not a[_SA_COMMON]:
        return shndx, value, size
    return 0xfff2, a[_SA_ALIGN], a[_SA_SIZE] * bpw


def _sym_size_of(state, name, bpw):
    """`.size` の値（ワード数）をバイト数で。"""
    a = _sym_attr(state, name)
    return a[_SA_SIZE] * bpw if a[_SA_SIZE_SET] else 0


def _reloc_named(state, mach, name):
    """リロケーション型の名前を番号に（`.elftype` が組み込みに勝つ）。"""
    if not name:
        return None
    key = name.translate(_ALOWER)
    rt = state.elftypes.get(key)
    if rt is not None:
        return rt
    return mach['named'].get(key) if mach else None


def _reloc_reverse(state, mach, rtype):
    """リロケーション型の番号を名前に（組み込み → `.elftype` の順、無ければ ''）。"""
    if rtype is None:
        return ''
    nm = mach['reverse'].get(rtype, '') if mach else ''
    return nm or next((k for k, v in state.elftypes.items() if v == rtype), '')


def insn_reloc_field_decl(state, rtype):
    """命令欄の記述 (マスク, オフセット, シフト, 補正)。無ければ None。caxx.c の insn_reloc_field_decl()。"""
    if state is None:
        return None
    return elf_machine_table(state)['field'].get(rtype)


def insn_reloc_field_mask(rtype, state=None):
    """その型が命令語で使うビットのマスク（命令欄でなければ None）。"""
    fd = insn_reloc_field_decl(state, rtype)
    return None if fd is None else fd[0]


def _elf_v2l_second(state, prev, k, v):
    """取り込み中の変数に 2 つ目以降のラベルが見えたときの記録。caxx.c の label_get_value() と同じ。

    `.elfdiff`（か pcrel_guess）があれば見えた順のリストに、無ければ曖昧の None。
    """
    if not (state.elf.decl_diff or state.elf.decl_diff_t
            or elf_machine_table(state)['pcrel_guess']):
        return None
    if isinstance(prev, tuple) and len(prev) == 2:
        return [prev, (k, v)]
    if isinstance(prev, list):
        return prev + [(k, v)]
    return None


_ISLABEL_ALNUM = set(ALPHABET + DIGIT)
_DIFF_WORD = set(ALPHABET + DIGIT + '_.$')


def _elf_v2l_finish(state, a, text, pcval=None):
    """変数 a の取り込みが終わったところでラベルの結び付きを決める。caxx.c の elf_v2l_finish() と同じ。

    2 つ以上ならラベル差。1 つでも符号が負なら、`.elfdiff` があれば引く型だけの
    ラベル差、無ければ曖昧。`.elfpcguess::1` で「ラベル − `$$` + 定数」なら `$$` を
    引く項にする（pcval は `$$` の値を返す関数）。
    """
    if not state.elf.tracking:
        return
    v2l = state.elf.var_to_label
    pend = v2l.get(a)
    if isinstance(pend, list):
        v2l[a] = _elf_diff_resolve(text, pend)
    elif isinstance(pend, tuple) and len(pend) == 2:
        if (pcval is not None and a not in state.reloc_constraints
                and elf_machine_table(state)['pcrel_guess']):
            r2 = _elf_diff_resolve(text, [pend, ('$$', pcval())])
            if r2 is not None and sorted(r2[1]) == sorted(((1, pend[0]), (-1, '$$'))):
                v2l[a] = r2
                return
        r = _elf_diff_resolve(text, [pend])
        if r is not None and r[1][0][0] < 0:
            v2l[a] = r if (state.elf.decl_diff or state.elf.decl_diff_t) else None


def _elf_diff_resolve(text, pend):
    """式の綴りからラベルの 1 次結合を読む。caxx.c の elf_diff_resolve() と同じ。

    `+ - ( )`・数・ラベルだけで、各ラベルの係数が ±1 なら
    ('D', ((符号, 名前), ...), Σ符号×値)（項は綴りに現れた順）、それ以外は None。
    """
    names = {}
    for n, v in pend:
        key = n.translate(_AUPPER)
        if key in names:
            return None
        names[key] = (n, int(v))
    coef = {}
    stack = [1]
    sign = 1
    expect = True
    t = text
    i = 0
    L = len(t)
    while i < L:
        c = t[i]
        i += 1
        if c in ' \t\0':
            continue
        if c in '+-':
            sg = -1 if c == '-' else 1
            if expect:
                sign *= sg
            else:
                sign = sg
                expect = True
        elif c == '(':
            if not expect:
                return None
            stack.append(stack[-1] * sign)
            sign = 1
        elif c == ')':
            if len(stack) == 1 or expect:
                return None
            stack.pop()
        elif c in _DIFF_WORD or c == "'":
            if not expect:
                return None
            if c == "'":
                j = t.find("'", i)
                if j < 0:
                    return None
                i = j + 1
            else:
                j = i - 1
                while i < L and t[i] in _DIFF_WORD:
                    i += 1
                key = t[j:i].translate(_AUPPER)
                if key in names:
                    coef[key] = coef.get(key, 0) + stack[-1] * sign
            expect = False
            sign = 1
        else:
            return None
    if len(stack) != 1 or expect:
        return None
    if len(coef) != len(names) or any(abs(c) != 1 for c in coef.values()):
        return None
    return ('D', tuple((c, names[k][0]) for k, c in coef.items()),
            sum(c * names[k][1] for k, c in coef.items()))


def _field_deposit(mask, value):
    """value の下位ビットから順に mask の立っているビットへ詰める。caxx.c の field_deposit()。"""
    out = 0
    bit = 0
    while mask:
        low = mask & -mask
        if (value >> bit) & 1:
            out |= low
        bit += 1
        mask ^= low
    return out


class VLIWState:
    """`.vliw` の宣言と組み立て中のバンドル。

    bits バンドルのビット数 / instbits 命令のビット数 / templatebits テンプレート欄
    （0 で非 EPIC、負なら左端）/ nop 埋める NOP / slotset `EPIC::` のスロットの組 /
    cnt `!!` で結んだ命令の数 / stop ストップビット。
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

    def save(self, slotset=True):
        """宣言の部分（stop と cnt を除く）を写し取る。"""
        return (self.bits, self.instbits, self.templatebits, self.flag,
                list(self.nop), list(self.slotset) if slotset else None)

    def load(self, snap):
        """save() で写した宣言の部分を戻す。"""
        self.bits, self.instbits, self.templatebits, self.flag = snap[:4]
        self.nop = list(snap[4])
        if snap[5] is not None:
            self.slotset = list(snap[5])


class ElfState:
    """`-o` の ELF 出力の状態。

    decl_* はパターンファイルの .elf* 宣言の綴りのまま（型番号への解決は
    elf_machine_table() まで遅らせる）。decl_gen はその表のキャッシュの世代。
    """

    def __init__(self):
        self.osabi: int = 0
        self.objfile: str = ""
        self.machine: int = 62
        self.elf_class: int | None = None

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
        self.decl_pcguess = None
        self.decl_relax = None
        self.decl_builtin = None
        # 添える型（型 → {添える型: シンボルを持つか}）、ラベル差の対（幅 → (足す型, 引く型)）、
        # REL の書き戻し関数、`.elfanchor` / `.elfresolve` の型（宣言順）、
        # `.elfunaligned`（型 → 整列していないときの型）、r_info を組む関数、単位、
        # sh_link / sh_info、セクショングループ。
        self.decl_extra = {}
        self.decl_diff = {}
        self.decl_diff_t = {}
        self.decl_encode = {}
        self.decl_anchor = []
        self.decl_resolve = []
        self.decl_unaligned = {}
        self.decl_rinfo = ''
        self.decl_unit = None
        self.decl_link = {}
        self.decl_group = {}
        # CFI: (戻り番地の列, コード整列, データ整列, 詰めの整列)、CIE の初期命令、レジスタ名 → 番号。
        self.decl_cfi = None
        self.decl_cfiinit = {}
        self.decl_cfireg = {}
        # ソースの .cfi_*（パス2で集める）: FDE ごとの記録と開いている FDE。
        self.cfi_fdes = []
        self.cfi_cur = None
        self.type_width = {}
        self.type_pcrel = set()
        self.decl_gen = 0
        self.machine_from_cli = False
        self.mach_cache = None
        self.mach_cache_key = None

        # パス2で集まるリロケーション。tracking 中に評価器が見たラベル参照を
        # label_refs_seen に積み、出力ワード（current_word_idx）と変数
        # （var_to_label / capturing_var）から型と位置を決める。
        self.relocations = []
        self.anchors = []                 # (名前, セクション, バイト位置)
        self.tracking = False
        self.label_refs_seen = []
        self.current_word_idx: int = -1
        self.var_to_label: dict = {}
        self.capturing_var: str | None = None
        self.insn_reloc_hint: dict = {}

        # `-g` の DWARF（line_map は番地 ↔ ソース行）。
        self.gen_debug: bool = False
        self.line_map: list = []

        self.reloctype_override: dict = {}


class RelaxationState:
    """パス1の反復（リラクゼーション）の状態。全ラベルの番地が前回と一致するまで繰り返す。"""

    def __init__(self):
        # 0 が対話モード、1 が長さの収束、2 がコード生成。診断は 0 と 2 だけ。
        self.pas = 0
        # パス1で長さだけを知りたい区間（診断を抑える）。
        self.pass1_size_mode = False
        # 前回の反復のラベル → 番地（番兵なら未実施）と、前方参照の推定値。
        self.pass1_prev_label_pcs = _RELAXATION_SENTINEL
        self.relax_prev_values = {}
        # 最初の反復だけ真。未定義ラベルを楽観的に扱い短い符号化から試す。
        self.relax_optimistic = False
        # 組み合わせ数・省略可能部分の上限の警告を一度だけ出すための印。
        self.combo_budget_warned = set()
        self.optgroups_warned = set()


class AssemblerState:
    """アセンブル中の状態すべて（VLIW / ELF / リラクゼーションは下位オブジェクト）。

    生成時に自分を _ACTIVE_STATE へ入れ、モジュール関数の diag() の宛先になる。
    """

    def __init__(self):
        global _ACTIVE_STATE
        _ACTIVE_STATE = self

        self.expr_depth = 0                 # 式の入れ子の深さ（_EXPR_MAX_DEPTH まで）
        self._diag_pending = None           # 照合の試行中に溜める診断
        self._diag_line_seen = set()        # いまの行で出した場所付きの診断（_diag_print）
        self._listing_open = False          # -v の一覧で改行していない行があるか
        self._expr_read_float_var = False   # 整数モードの式が浮動小数点の変数を読んだか

        self.outfile = ""
        self.expfile = ""
        self.expfile_elf = ""
        self.impfile = ""

        self.pc = 0
        self.padding = 0
        self.pc_instr_start = 0
        self.pc_instr_end = 0
        self._in_binary_list = False
        # 照合と `.db` などの式を読む間だけ立つ。-o / -E では binary_list の中と同じく
        # 同じセクションのラベルと `$$` / `$.` をセクション相対で読む。caxx.c の sec_frame。
        self._sec_frame = False

        # ラベルとシンボルに使える文字（`.labelc` / `.symbolc` で広がる）。シンボルの `-` は
        # `(IX-5)` を一度シンボルとして試してから後退するため。
        self.lwordchars = DIGIT + ALPHABET + "_."
        self.swordchars = DIGIT + ALPHABET + "_%$-~&|"

        self.current_section = ".text"
        self.current_file = ""

        # ラベル・シンボルの表、読み込んだパターン行と索引、持ち上げ（hoist_*）、
        # `.unordered` の処理順（pat_dirorder）。
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
        self.unordered = False
        self.pat_dirorder = []
        self.hdrsnap = None
        self.diag_count = 0

        self.vliw = VLIWState()
        self.expcaps = CAPS_PAT             # いま読んでいる式で使える項

        self.error_undefined_label = False
        self.reported_label_errors = set()
        self.had_error = False
        self._in_match_attempt = False
        # `.textmode` の `!L` を読む間は未定義ラベルを 0 として続ける。caxx.c の textmode_lcap。
        self._textmode_lcap = False
        # いまの行が `.db` などか（`.eol` の改行を足さない）。
        self._data_dir_line = False
        # -o の追跡で、`.db` などの 2 つ目以降の値が始まる出力ワードと、値が始まる出力ワード。
        self._elf_field_breaks = set()
        self._elf_data_fields = set()
        # 因子を 1 文字も読めなかった印（caxx.c の expr_missing）と、`!Q` の 0 除算の
        # 先送り（caxx.c の fdiv0_defer）。
        self.expr_missing = False
        self.fdiv0_defer = False
        self.fdiv0_seen = False

        # 出力ワードの形（`.bits` と `.align` の既定）。
        self.align = 16
        self.bts = 8
        self.endian = 'little'
        self.debug = False

        # いまの行と位置。fnstack / lnstack は `.include` の入れ子。
        self.cl = ""
        self.ln = 0
        self.fnstack = []
        self.lnstack = []

        # パターン変数の束縛（未束縛の印、浮動小数点の印、書かれたままの綴り）。
        self.vars = {}
        self.vars_undef = {}
        self.vars_float = {}
        self.vars_text = {}

        self._mini_suspects = set()         # ミニ言語の綴り間違いの疑い（MiniInterp._tick）

        self.exp_typ: str = 'i'             # 'i' 整数 / 'f' IEEE-754 倍精度

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

        self.varnames: set = set()
        self.check_constraints: dict = {}
        self.var_tables: dict = {}          # `.unordered` の `.map` の表
        self.reloc_constraints: dict = {}
        self.reloc_masks: dict = {}         # `.reloc` の第 4 欄
        self.reloc_pairs: dict = {}         # `.reloc` の第 5 欄
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
        """診断を 1 行出す。照合の試行中は溜め、報告しないパスでは捨てる（force は必ず出す）。"""
        self.diag_count += 1
        if not force:
            text = self._diag_locate(text)
            if self._in_match_attempt:
                if self._diag_pending is not None:
                    self._diag_pending.append((text, set_error))
                return False
            if not self.should_report_errors():
                return False
        self._diag_print(text)
        if set_error:
            self.had_error = True
        return True

    _DIAG_HAS_LOC = re.compile(r'\[[^\[\]]*:[0-9]+\][ \t]*$')

    def _diag_print(self, text):
        """診断を stderr へ。1 つの行で同じ場所付きの文面は 2 度出さない。caxx.c の diag_print()。"""
        if "\n" not in text and self._DIAG_HAS_LOC.search(text):
            if text in self._diag_line_seen:
                return
            self._diag_line_seen.add(text)
        print(text, file=sys.stderr)

    def _diag_locate(self, text):
        """ソースの行を組んでいる最中の 1 行の error / warning に `  [file:line]` を足す。

        caxx.c の diag_locate() と同じ規則である。
        """
        if not self.current_file:
            return text
        if not text.startswith((" error - ", " warning - ")):
            return text
        if "\n" in text or self._DIAG_HAS_LOC.search(text):
            return text
        return f"{text}  [{self.current_file}:{self.ln}]"

    def diag_capture_begin(self):
        """以降の診断を溜め始める（照合の試行に入るとき）。"""
        self._diag_pending = []

    def diag_capture_take(self):
        """溜めた診断を取り出して、溜めるのをやめる。"""
        out = self._diag_pending if self._diag_pending is not None else []
        self._diag_pending = None
        return out

    def diag_replay(self, items):
        """溜めた診断を出す（採択されたパターンのぶんだけ）。"""
        for text, set_error in items:
            if self.should_report_errors():
                self._diag_print(text)
                if set_error:
                    self.had_error = True

    def should_report_errors(self):
        """いま診断を出してよいパスか（パス2と対話モード）。"""
        return self.relax.pas in (0, 2)


class StringUtils:
    """行とトークンの文字列処理（状態なし）。

    `"..."` と文字定数 `'c'` の中は触らない、という規則を全員で共有する。`'` は
    符号拡張演算子でもあるので、文字定数の判定は skip_squote_literal に閉じてある。
    """

    _ASCII_UPPER = str.maketrans(LOWER, CAPITAL)
    _upper_cache = {}

    @staticmethod
    def upper(s):
        """ASCII だけを大文字にする（caxx.c の toupper() と同じ）。短い文字列は覚える。"""
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
        """行末の `\\` で続く行をつなぐ。つないだぶんは空行を残し、行番号を保つ。

        ファイルの最後で途切れたら、つないだ中身を最後の物理行に置く（caxx.c の m_read_lines()）。
        """
        out = []
        pending = ''
        open_cont = False
        for raw in raw_lines:
            body, ending = raw, ''
            if body.endswith('\r\n'):
                body, ending = body[:-2], '\r\n'
            elif body.endswith(('\n', '\r')):
                body, ending = body[:-1], body[-1]
            open_cont = body.endswith('\\')
            if open_cont:
                pending += body[:-1]
                out.append('')
            else:
                out.append(pending + body + ending)
                pending = ''
        if open_cont:
            out[-1] = pending
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
        """i の `'` が文字定数（`'c'` `'\\n'` `'\\xHH'`）ならその直後、違えば i+1。"""
        n = len(s)
        j = i + 1
        if j + 1 < n and s[j] == '\\':
            if s[j + 1] in 'xX':
                k = j + 2
                while k < n and k < j + 4 and s[k] in _HEXCHARS:
                    k += 1
                if k < n and s[k] == '\'':
                    return k + 1
            elif j + 2 < n and s[j + 2] == '\'':
                return j + 3
        elif j + 1 < n and s[j + 1] == '\'' and _byte_char(s[j]) is not None:
            return j + 2
        return i + 1

    @staticmethod
    def parse_hex_char_literal(s, idx):
        """`'\\xHH'` を読む。返り値は (読めたか, 値, 次の位置)。"""
        if s[idx:idx + 2] != "'\\" or s[idx + 2:idx + 3] not in ('x', 'X'):
            return False, 0, idx
        j = idx + 3
        while j < len(s) and j < idx + 5 and s[j] in _HEXCHARS:
            j += 1
        if j > idx + 3 and j < len(s) and s[j] == "'":
            return True, int(s[idx + 3:j], 16), j + 1
        return False, 0, idx

    # スペース・タブ・LF・CR の連なりだけを潰す（caxx.c の axx_reduce_spaces()。\s は使わない）。
    _SPACE_RUNS = re.compile(r'[ \t\n\r]+')

    @staticmethod
    def reduce_spaces(text):
        """空白の連なりを 1 個に潰す（リテラルの中も）。中身を守るなら normalize_ws()。"""
        return StringUtils._SPACE_RUNS.sub(' ', text)

    @staticmethod
    def normalize_ws(l):
        """空白の連なりを 1 個に潰す。`"..."` と `'c'` の中は触らない。"""
        out = []
        in_ws = False
        i = 0
        n = len(l)
        while i < n:
            ch = l[i]
            if ch == '"':
                j = i + 1
                while j < n and l[j] != '"':
                    j += 2 if l[j] == '\\' and j + 1 < n else 1
                j = min(j + 1, n)
            elif ch == '\'':
                j = StringUtils.skip_squote_literal(l, i)
            elif ch in ' \t\n\r':
                if not in_ws:
                    out.append(' ')
                    in_ws = True
                i += 1
                continue
            else:
                j = i + 1
            out.append(l[i:j])
            in_ws = False
            i = j
        return ''.join(out)

    @staticmethod
    def quoted_span(l, i):
        """l[i] から文字列として読み飛ばす長さ（無ければ 0）。caxx.c の axx_quoted_span() と同じ。

        `"..."` は同じ行に閉じるときだけ文字列（中の `\\` は次を逃がす）。`\\"` と `'"'` は開かない。
        """
        c = l[i]
        if c == '\\' and l[i + 1:i + 2] == '"':
            return 2
        if c == "'" and l[i + 1:i + 3] == '"\'':
            return 3
        if c != '"':
            return 0
        n = len(l)
        j = i + 1
        while j < n:
            if l[j] == '\\' and j + 1 < n:
                j += 2
            elif l[j] == '"':
                return j + 1 - i
            else:
                j += 1
        return 0

    @staticmethod
    def remove_comment(l, in_comment=False):
        """パターンファイルの `/* ... */` を落とす。返り値は (行, まだコメントの中か)。"""
        out = []
        i = 0
        n = len(l)
        while i < n:
            if in_comment:
                if l[i:i + 2] == '*/':
                    in_comment = False
                    i += 2
                else:
                    i += 1
                continue
            q = StringUtils.quoted_span(l, i)
            if q:
                out.append(l[i:i + q])
                i += q
            elif l[i:i + 2] == '/*':
                in_comment = True
                i += 2
            else:
                out.append(l[i])
                i += 1
        return ''.join(out), in_comment

    @staticmethod
    def _scan_escapes(l, esc, on_plain):
        """`"..."` と `'c'` を避けて読み、文字列の外の `\\esc` を esc に開く共通の走査。

        on_plain(out, i) は文字列の外の 1 文字を見て、進めた位置か、写すだけなら None、
        そこで止めるなら -1 を返す。返り値は (結果, 止めた位置か None, 文字列が開いたままか)。
        """
        in_dquote = False
        out = []
        i = 0
        n = len(l)
        while i < n:
            ch = l[i]
            if in_dquote and ch == '\\':
                out.append(l[i:i + 2])
                i += 2
                continue
            if not in_dquote:
                if ch == '\\' and l[i + 1:i + 2] == esc:
                    out.append(esc)
                    i += 2
                    continue
                if ch == '\'':
                    j = StringUtils.skip_squote_literal(l, i)
                    out.append(l[i:j])
                    i = j
                    continue
                r = on_plain(out, i)
                if r == -1:
                    return out, i, False
                if r is not None:
                    i = r
                    continue
            if ch == '"':
                in_dquote = not in_dquote
            out.append(ch)
            i += 1
        return out, None, in_dquote

    @staticmethod
    def split_comment_asm(l):
        """アセンブリ行を (コード, `;` コメント) に割る。`\\;` は文字としての `;`。

        落とす空白は caxx.c の axx_split_comment_asm() と同じ文字だけ。
        """
        out, stop, open_q = StringUtils._scan_escapes(
            l, ';', lambda out, i: -1 if l[i] == ';' else None)
        if stop is not None:
            return ''.join(out).rstrip(' \t'), l[stop:].rstrip(' \t\n\r')
        if open_q:
            diag(f" warning - unterminated string literal in line: {l!r}", set_error=False)
        return ''.join(out).rstrip(' \t\n\r'), ''

    @staticmethod
    def resolve_vliw_escapes(l):
        """ソース行の `!!!!` と `!!` を内部表現 1 文字に置き換える（`\\!` は文字の `!`）。"""
        def plain(out, i):
            for tok, rep in (('!!!!', VLIW_STOP), ('!!', VLIW_SEP)):
                if l.startswith(tok, i):
                    out.append(rep)
                    return i + len(tok)
            return None
        return ''.join(StringUtils._scan_escapes(l, '!', plain)[0])

    @staticmethod
    def get_param_to_spc(s, idx):
        """空白か VLIW スロット境界まで読む。返り値は (読んだ文字, 次の位置)。"""
        idx = j = StringUtils.skipspc(s, idx)
        while j < len(s) and s[j] not in (' ', VLIW_SEP, VLIW_STOP):
            j += 1
        return s[idx:j], j

    @staticmethod
    def get_param_to_eon(s, idx):
        """VLIW スロット境界まで読む（空白も含める）。"""
        idx = j = StringUtils.skipspc(s, idx)
        while j < len(s) and s[j] not in (VLIW_SEP, VLIW_STOP):
            j += 1
        return s[idx:j], j

    _STR_ESC = {'"': '"', '\\': '\\', 'n': '\n', 't': '\t', 'r': '\r'}

    @staticmethod
    def get_string(l2):
        """`"..."` を 1 個読んで中身を返す。

        エスケープは `\\n \\t \\r \\\\ \\"`・`\\xHH`・`\\uXXXX`・`\\UXXXXXXXX`。桁の過不足と
        閉じていない文字列は警告して、書かれた文字をそのまま採る。
        """
        idx = StringUtils.skipspc(l2, 0)
        n = len(l2)
        if idx >= n or l2[idx] != '"':
            return ""
        idx += 1
        s = ""
        while idx < n:
            c = l2[idx]
            if c == '"':
                return s
            if c != '\\' or idx + 1 >= n:
                s += c
                idx += 1
                continue
            e = l2[idx + 1]
            idx += 2
            if e in StringUtils._STR_ESC:
                s += StringUtils._STR_ESC[e]
            elif e in 'xX':
                j = idx
                while idx < n and idx < j + 2 and l2[idx] in _HEXCHARS:
                    idx += 1
                hex_str = l2[j:idx]
                if idx < n and l2[idx] in _HEXCHARS:
                    diag(f" warning - '\\x' escape takes at most 2 hex digits; "
                         f"extra digit(s) treated as literal characters in: {l2!r}", set_error=False)
                if hex_str:
                    s += chr(int(hex_str, 16))
                else:
                    diag(f" warning - '\\x' escape requires at least one hex digit; "
                         f"treated as literal 'x' in: {l2!r}", set_error=False)
                    s += 'x'
            elif e in 'uU':
                nd = 4 if e == 'u' else 8
                j = idx
                while idx < n and idx < j + nd and l2[idx] in _HEXCHARS:
                    idx += 1
                hex_str = l2[j:idx]
                if len(hex_str) == nd:
                    try:
                        s += chr(int(hex_str, 16))
                        continue
                    except (ValueError, OverflowError):
                        diag(f" warning - invalid \\{e} escape in: {l2!r}", set_error=False)
                else:
                    diag(f" warning - '\\{e}' escape requires {nd} hex digits; "
                         f"treated as literal characters in: {l2!r}", set_error=False)
                s += e + hex_str
            else:
                s += e
        diag(f" warning - unterminated string literal: {l2!r}", set_error=False)
        return s


_HEXCHARS = '0123456789abcdefABCDEF'


class Parser:
    """行から 1 個ずつトークンを切り出す低位の読み取り器。

    どれも (読んだもの, 次の位置) を返し、読めなければ位置を動かさない（照合は後退
    しながら何度も試すので、失敗が副作用を残さない）。文字の集合は state の
    lwordchars / swordchars（`.labelc` / `.symbolc`）。
    """

    def __init__(self, state):
        self.state = state

    def get_intstr(self, s, idx):
        """続く 10 進数字を綴りのまま取る。"""
        j = idx
        while j < len(s) and s[j] in DIGIT:
            j += 1
        return s[idx:j], j

    def get_floatstr(self, s, idx):
        """浮動小数点の綴りを取る（`inf` `-inf` `nan` も）。数字の無い `e` は指数にしない。"""
        for w in ('-inf', 'inf', 'nan'):
            if s.startswith(w, idx):
                return w, idx + len(w)
        n = len(s)
        j = idx
        while j < n and s[j] in "0123456789.":
            j += 1
        if j < n and s[j] in "eE":
            k = j + 1
            if k < n and s[k] in "+-":
                k += 1
            d = k
            while k < n and s[k] in DIGIT:
                k += 1
            if k > d:
                j = k
        return s[idx:j], j

    def isfloatstr(self, s, idx):
        """その位置から浮動小数点の数が始まるか。caxx.c の axx_isfloatstr() と同じ判定。"""
        if idx >= len(s):
            return False
        if s[idx:idx + 4] == '-inf' or s[idx:idx + 3] in ('inf', 'nan'):
            return True
        return s[idx] in '0123456789.'

    def get_curlb(self, s, idx):
        """`{ ... }` の中身を取る。返り値は (あったか, 中身, 次の位置)。閉じなければ診断。"""
        idx = StringUtils.skipspc(s, idx)
        if idx >= len(s) or s[idx] != '{':
            return False, '', idx
        idx = StringUtils.skipspc(s, idx + 1)
        e = s.find('}', idx)
        t = s[idx:e if e >= 0 else len(s)].rstrip(' \t\r\n\x00')
        if e < 0:
            if self.state.should_report_errors():
                self.state.diag(f" error - missing closing '}}' in expression: '{{{t}'",
                                set_error=True, force=True)
            return False, '', len(s)
        return True, t, e + 1

    def get_symbol_word(self, s, idx):
        """シンボル名を 1 個取り、大文字化して返す（数字では始まらない）。"""
        sw = self.state.swordchars
        j = idx
        if j < len(s) and s[j] not in DIGIT and s[j] in sw:
            j += 1
            while j < len(s) and s[j] in sw:
                j += 1
        return StringUtils.upper(s[idx:j]), j

    def get_label_word(self, s, idx, eat_colon=True):
        """ラベル名を 1 個取る（大文字化しない）。eat_colon なら `label:` の `:` まで（`:=` は残す）。"""
        lw = self.state.lwordchars
        j = idx
        if j < len(s) and (s[j] == '.' or (s[j] not in DIGIT and s[j] in lw)):
            j += 1
            while j < len(s) and s[j] in lw:
                j += 1
            t = s[idx:j]
            if eat_colon and j < len(s) and s[j] == ':' and s[j + 1:j + 2] != '=':
                j += 1
            return t, j
        return "", j

    def get_params1(self, l, idx):
        """`::` までを 1 欄として取る（`"..."` の中の `::` では割らない）。"""
        idx = StringUtils.skipspc(l, idx)
        n = len(l)
        j = idx
        while j < n:
            q = StringUtils.quoted_span(l, j)
            if q:
                j += q
            elif l[j:j + 2] == '::':
                return l[idx:j].rstrip(' \t'), j + 2
            else:
                j += 1
        return l[idx:j].rstrip(' \t'), j


def enfloat(a):
    """32bit の整数ビットパターンを float として読み直す（壊れた入力は 0.0）。"""
    try:
        return struct.unpack('f', struct.pack('I', int(a) & 0xFFFFFFFF))[0]
    except (struct.error, OverflowError, ValueError):
        return 0.0


def endouble(a):
    """64bit の整数ビットパターンを double として読み直す（壊れた入力は 0.0）。"""
    try:
        return struct.unpack('d', struct.pack('Q', int(a) & 0xFFFFFFFFFFFFFFFF))[0]
    except (struct.error, OverflowError, ValueError):
        return 0.0


enflt = enfloat
endbl = endouble


def _float_brace_result(state, f, name):
    """enflt{} / endbl{} の値を今のモードに合わせる。caxx.c の float_brace_result() と同じ。

    浮動小数点モードはそのまま。整数モードは 0 の方向へ切り捨て、有限でない値と
    |f| >= 2**255 はエラーで 0。
    """
    if state.exp_typ == 'f':
        return f
    if not math.isfinite(f) or abs(f) >= 2.0 ** 255:
        state.diag(f" error - {name}{{}}: the value {_g17(f)} cannot be an integer; using 0.",
                   set_error=True)
        return 0
    return math.trunc(f)


# ---- flt{} / dbl{} / qad{} の中身の式（caxx.c の xeval_*() と同じ規則）----
# Python の数の規則に倣った小さな再帰下降。値は int（256 ビット符号付き）か有限の float。
# 誤りは ValueError（診断は呼び出し側）。
#   - 数は Python のリテラルの綴り（0x 0o 0b、`_`、浮動小数点）。10 進の整数は 0 で始められない。
#   - 優先順位の低い順に `|` `^` `&` `<< >>` `+ -` `* / // %`、単項 `+ - ~`、`**`（右結合）。
#   - 整数の演算は整数のまま。256 ビットに収まらなければ倍精度でやり直す（`<<` はエラー）。
#     `/` と倍精度の混じった演算は倍精度。`<< >> & | ^ ~` は整数だけ。
#   - 0 除算・負のシフト・0 の負の数乗・負の数の非整数乗・有限でない値はエラー。
#   - `:名前` はラベルの値。関数は enfloat / enflt / endouble / endbl（引数 1 個）。
_XV_MIN = -(1 << 255)
_XV_MAX = (1 << 255) - 1
_XV_FUNCS = {"enfloat": 32, "enflt": 32, "endouble": 64, "endbl": 64}


class _XevalParser:
    def __init__(self, s, label_value, lwordchars):
        self.s = s
        self.i = 0
        self.n = len(s)
        self.label_value = label_value
        self.lwordchars = lwordchars

    @staticmethod
    def _fail(msg="bad expression"):
        raise ValueError("xeval: " + msg)

    def _int(self, v, fallback=None):
        """整数の結果。256 ビットに収まらなければ fallback()（倍精度でやり直した値）、無ければエラー。"""
        if _XV_MIN <= v <= _XV_MAX:
            return v
        if fallback is None:
            self._fail("integer out of 256-bit range")
        return self._flt(fallback())

    @classmethod
    def _flt(cls, v):
        if not math.isfinite(v):
            cls._fail("non-finite value")
        return v

    def _skip(self):
        while self.i < self.n and self.s[self.i] in ' \t':
            self.i += 1

    def _peek(self, tok):
        return self.s.startswith(tok, self.i)

    # -- 数 --
    def _digitpart(self, digits):
        """digit (_? digit)* を読み、`_` を除いた数字列を返す。無ければ None。"""
        s, i = self.s, self.i
        if i >= self.n or s[i] not in digits:
            return None
        out = [s[i]]
        i += 1
        while True:
            if i < self.n and s[i] in digits:
                out.append(s[i])
                i += 1
            elif i + 1 < self.n and s[i] == '_' and s[i + 1] in digits:
                out.append(s[i + 1])
                i += 2
            else:
                break
        self.i = i
        return ''.join(out)

    def _number(self):
        s = self.s
        if (s[self.i] == '0' and self.i + 1 < self.n
                and s[self.i + 1] in 'xXoObB'):
            base, digits = {'x': (16, '0123456789abcdefABCDEF'),
                            'o': (8, '01234567'),
                            'b': (2, '01')}[s[self.i + 1].translate(_ALOWER)]
            self.i += 2
            if self.i < self.n and s[self.i] == '_':
                self.i += 1
            d = self._digitpart(digits)
            if d is None:
                self._fail("bad number")
            v = int(d, base)
            is_float = False
        else:
            ip = self._digitpart('0123456789')
            text = ip or ''
            is_float = False
            if self.i < self.n and s[self.i] == '.':
                self.i += 1
                fp = self._digitpart('0123456789')
                if ip is None and fp is None:
                    self._fail("bad number")
                text += '.' + (fp or '')
                is_float = True
            if self.i < self.n and s[self.i] in 'eE':
                self.i += 1
                sign = ''
                if self.i < self.n and s[self.i] in '+-':
                    sign = s[self.i]
                    self.i += 1
                ep = self._digitpart('0123456789')
                if ep is None:
                    self._fail("bad number")
                text += 'e' + sign + ep
                is_float = True
            if is_float:
                v = float(text)
            else:
                if text[0] == '0' and text.strip('0'):
                    self._fail("leading zeros in a decimal integer")
                v = int(text)
        if self.i < self.n and (s[self.i].isascii() and s[self.i].isalnum() or s[self.i] == '_'):
            self._fail("bad number")
        return self._flt(v) if is_float else self._int(v, lambda: self._f(v))

    # -- 項 --
    def _primary(self):
        self._skip()
        if self.i >= self.n:
            self._fail("missing operand")
        c = self.s[self.i]
        if c == '(':
            self.i += 1
            v = self._expr()
            self._skip()
            if not self._peek(')'):
                self._fail("missing ')'")
            self.i += 1
            return v
        if c == ':':
            self.i += 1
            j = self.i
            while j < self.n and self.s[j] in self.lwordchars:
                j += 1
            if j == self.i:
                self._fail("missing label name")
            name = self.s[self.i:j]
            self.i = j
            return self.label_value(name)
        if ('a' <= c <= 'z') or ('A' <= c <= 'Z') or c == '_':
            j = self.i
            while j < self.n and (self.s[j].isascii() and self.s[j].isalnum()
                                  or self.s[j] == '_'):
                j += 1
            name = self.s[self.i:j]
            self.i = j
            self._skip()
            if name not in _XV_FUNCS or not self._peek('('):
                self._fail(f"unknown name '{name}'")
            self.i += 1
            a = self._expr()
            self._skip()
            if not self._peek(')'):
                self._fail("missing ')'")
            self.i += 1
            if isinstance(a, float):
                a = int(a)
            if _XV_FUNCS[name] == 32:
                r = struct.unpack('<f', struct.pack('<I', a & 0xFFFFFFFF))[0]
            else:
                r = struct.unpack('<d', struct.pack('<Q', a & 0xFFFFFFFFFFFFFFFF))[0]
            return self._flt(r)
        if c.isdigit() and c.isascii() or c == '.':
            return self._number()
        self._fail("bad operand")

    # -- 演算 --
    @staticmethod
    def _f(v):
        try:
            return float(v)
        except OverflowError:
            return math.inf

    def _pow(self, a, b):
        if isinstance(a, int) and isinstance(b, int) and b >= 0:
            if abs(a) >= 2 and b > 256:
                return self._fpow(a, b)
            return self._int(a ** b, lambda: self._fpow(a, b))
        return self._fpow(a, b)

    def _fpow(self, a, b):
        x, y = self._f(a), self._f(b)
        if x == 0.0 and y < 0.0:
            self._fail("zero to a negative power")
        if x < 0.0 and y != math.floor(y):
            self._fail("negative number to a non-integer power")
        try:
            r = x ** y
        except OverflowError:
            self._fail("non-finite value")
        return self._flt(r)

    def _power(self):
        a = self._primary()
        self._skip()
        if self._peek('**'):
            self.i += 2
            return self._pow(a, self._unary())
        return a

    def _unary(self):
        self._skip()
        if self.i < self.n and self.s[self.i] in '+-~':
            c = self.s[self.i]
            self.i += 1
            v = self._unary()
            if c == '+':
                return v
            if c == '-':
                return self._int(-v, lambda: -self._f(v)) if isinstance(v, int) else -v
            if not isinstance(v, int):
                self._fail("'~' needs an integer")
            return ~v
        return self._power()

    def _binop(self, op, a, b):
        both_int = isinstance(a, int) and isinstance(b, int)
        if op in ('<<', '>>', '&', '|', '^'):
            if not both_int:
                self._fail(f"'{op}' needs integers")
            if op == '&':
                return a & b
            if op == '|':
                return a | b
            if op == '^':
                return a ^ b
            if b < 0:
                self._fail("negative shift count")
            if op == '>>':
                return a >> min(b, 256)
            if a == 0:
                return 0
            if b > 256:
                self._fail("integer out of 256-bit range")
            return self._int(a << b)
        if op == '/':
            if b == 0:
                self._fail("division by zero")
            if both_int:
                return self._flt(a / b)
            return self._flt(self._f(a) / self._f(b))
        if op in ('//', '%'):
            if b == 0:
                self._fail("division by zero")
            x, y = self._f(a), self._f(b)
            if both_int:
                return self._int(a // b if op == '//' else a % b, lambda: x // y)
            return self._flt(x // y if op == '//' else x % y)
        x, y = self._f(a), self._f(b)
        if both_int:
            return self._int(a + b if op == '+' else a - b if op == '-' else a * b,
                             lambda: x + y if op == '+' else x - y if op == '-' else x * y)
        return self._flt(x + y if op == '+' else x - y if op == '-' else x * y)

    def _level(self, sub, ops):
        v = sub()
        while True:
            self._skip()
            for op in ops:
                if self._peek(op) and not (op == '*' and self._peek('**')) \
                        and not (op == '/' and self._peek('//')):
                    self.i += len(op)
                    v = self._binop(op, v, sub())
                    break
            else:
                return v

    def _term(self):
        return self._level(self._unary, ('//', '/', '%', '*'))

    def _arith(self):
        return self._level(self._term, ('+', '-'))

    def _shift(self):
        return self._level(self._arith, ('<<', '>>'))

    def _band(self):
        return self._level(self._shift, ('&',))

    def _bxor(self):
        return self._level(self._band, ('^',))

    def _expr(self):
        return self._level(self._bxor, ('|',))

    def parse(self):
        v = self._expr()
        self._skip()
        if self.i != self.n:
            self._fail("unexpected text")
        return v


class IEEE754Converter:
    """10 進表記 → IEEE-754 binary128 のビットパターン（`!Q` と `.float`）。

    Python に型が無いので Decimal で組む。inf / nan / -0.0 まで caxx.c（strtoflt128）と同じ。
    """

    @staticmethod
    def decimal_to_ieee754_128bit_hex(a):
        """binary128 のビットパターンを 16 進 32 桁で返す（Decimal の精度は 60 桁）。"""
        with localcontext() as _ctx:
            _ctx.prec = 60
            return IEEE754Converter._decimal_to_ieee754_128bit_hex_impl(a)

    @staticmethod
    def _decimal_to_ieee754_128bit_hex_impl(a):
        """符号・指数・仮数を組む。正規化は 1000 回まで、溢れは無限、下溢れは非正規化数、偶数丸め。"""
        BIAS = 16383
        SIG = 112
        EMAX = (1 << 15) - 1
        d = Decimal({'inf': 'Infinity', '-inf': '-Infinity', 'nan': 'NaN'}.get(a, a))
        if d.is_nan():
            sign, exponent, fraction = 0, EMAX, 1 << (SIG - 1)
        elif d.is_infinite():
            sign, exponent, fraction = int(d.is_signed()), EMAX, 0
        elif d == 0:
            sign, exponent, fraction = int(d.is_signed()), 0, 0
        else:
            sign = 0 if d >= 0 else 1
            d = abs(d)
            two = Decimal(2)
            exp_unbiased = int(d.adjusted() * math.log2(10))
            normalized = d / two ** exp_unbiased
            iters = 0

            def step():
                nonlocal iters
                iters += 1
                if iters > 1000:
                    raise ValueError(
                        "decimal_to_ieee754_128bit_hex: failed to normalize "
                        f"{d!r} (exponent estimate did not converge)")
            while normalized >= 2:
                exp_unbiased += 1
                normalized /= 2
                step()
            while normalized < 1:
                exp_unbiased -= 1
                normalized *= 2
                step()
            biased_exp = exp_unbiased + BIAS
            if biased_exp >= EMAX:
                return f"0x{(sign << 127) | (EMAX << SIG):032X}"
            if biased_exp <= 0:
                exponent = 0
                fraction = int((d / two ** (1 - BIAS - SIG)).to_integral_value(rounding=ROUND_HALF_EVEN))
                if fraction >= (1 << SIG):
                    exponent, fraction = 1, 0
            else:
                exponent = biased_exp
                fraction = int(((normalized - 1) * two ** SIG).to_integral_value(rounding=ROUND_HALF_EVEN))
                if fraction >= (1 << SIG):
                    exponent, fraction = exponent + 1, 0
            fraction &= (1 << SIG) - 1
        return f"0x{(sign << 127) | (exponent << SIG) | fraction:032X}"

    @staticmethod
    def decimal_eval_expr(text):
        """`!Q` と `qad{...}` の式を binary128 で評価してビットパターンを返す（不可は ValueError）。

        caxx.c の f128_eval_text() と同じ。数は 4 倍精度へ正しく丸め、`+ - * /` ごとに丸める。
        括弧・単項の `+ -`・数だけを読み、閉じ括弧は省ける。0 除算・有限でない結果・
        読めない後続は評価できない。
        """
        r = _F128Eval(text).run()
        if r is None:
            raise ValueError("cannot evaluate as a 128-bit expression")
        return r


class _F128Eval:
    """decimal_eval_expr() の本体（caxx.c の f128_*_fn() を写す）。

    値は (Fraction, 負のゼロか)（4 倍精度に丸めた値）か、inf / nan の float。
    """

    _P = 113
    _EMIN = -16382
    _EMAX = 16383
    _NUM_RE = re.compile(r'[0-9]*\.?[0-9]*')

    def __init__(self, text):
        self.s = text + chr(0)

    @classmethod
    def _round(cls, q):
        """正の有理数 q を 4 倍精度へ偶数丸めする。溢れたら inf。"""
        e = q.numerator.bit_length() - q.denominator.bit_length()
        if Fraction(2) ** e > q:
            e -= 1
        quantum = Fraction(2) ** (max(e, cls._EMIN) - (cls._P - 1))
        m, rem = divmod(q, quantum)
        m = int(m)
        if rem * 2 > quantum or (rem * 2 == quantum and m & 1):
            m += 1
        r = m * quantum
        return float('inf') if r >= Fraction(2) ** (cls._EMAX + 1) else r

    @classmethod
    def _make(cls, q, neg_zero=False):
        """有理数を 4 倍精度の値に（0 に丸まった値も符号は元のまま。-1e-5000 は -0）。"""
        if q == 0:
            return (Fraction(0), neg_zero)
        if q > 0:
            r = cls._round(q)
            return r if isinstance(r, float) else (r, False)
        r = cls._round(-q)
        return -r if isinstance(r, float) else (-r, r == 0)

    @staticmethod
    def _rep(v):
        """特別な値との演算用に、有限の値を符号つきの 0 か ±1 の float にする。"""
        if isinstance(v, float):
            return v
        q, nz = v
        if q == 0:
            return -0.0 if nz else 0.0
        return 1.0 if q > 0 else -1.0

    def _op(self, op, a, b):
        """IEEE の規則で 1 回の演算をし、4 倍精度へ丸める。"""
        if isinstance(a, float) or isinstance(b, float):
            x, y = self._rep(a), self._rep(b)
            r = x + y if op == '+' else x - y if op == '-' else x * y if op == '*' else x / y
            if math.isinf(r) or math.isnan(r):
                return r
            return (Fraction(0), math.copysign(1.0, r) < 0)
        (p, pz), (q, qz) = a, b
        if op in '+-':
            if op == '-':
                q, qz = -q, not qz
            r = p + q
            if r == 0:
                # 最近接丸めでゼロの和が負になるのは両方が -0 のときだけ。
                return (Fraction(0), p == 0 and q == 0 and pz and qz)
            return self._make(r)
        sign = ((p < 0) or (p == 0 and pz)) != ((q < 0) or (q == 0 and qz))
        r = p * q if op == '*' else p / q
        return (Fraction(0), sign) if r == 0 else self._make(r)

    def _skip(self, i):
        while self.s[i] in ' \t':
            i += 1
        return i

    def _number(self, i):
        """数字と `.` の並び（と指数）の先頭の正しい数を値にする（caxx.c の f128_factor_fn()）。

        綴りの長さに上限は無い。範囲をはるかに外れる値は 10 の累乗を作らずに inf / 0 と決める。
        """
        s = self.s
        buf = []
        while s[i].isdigit() and s[i].isascii() or s[i] == '.':
            buf.append(s[i])
            i += 1
        if s[i] in 'eE':
            buf.append(s[i])
            i += 1
            if s[i] in '+-':
                buf.append(s[i])
                i += 1
            while s[i].isdigit() and s[i].isascii():
                buf.append(s[i])
                i += 1
        b = ''.join(buf)
        m = self._NUM_RE.match(b).group(0)
        if not any(c.isdigit() for c in m):
            return (Fraction(0), False), i
        ip, _, fp = m.partition('.')
        if not (ip + fp).strip('0'):
            return (Fraction(0), False), i
        rest = b[len(m):]
        exp = 0
        em = re.match(r'[eE]([+-]?)([0-9]+)', rest)
        if em:
            ed = em.group(2).lstrip('0') or '0'
            exp = int(ed) if len(ed) <= 9 else 10 ** 10
            if em.group(1) == '-':
                exp = -exp
        # 値は [10**(e10-1), 10**e10)。4 倍精度の範囲（約 1.19e4932 〜 3.2e-4966）の十分外なら決め打つ。
        ips = ip.lstrip('0')
        e10 = len(ips) if ips else -(len(fp) - len(fp.lstrip('0')))
        if e10 + exp > 4940:
            return float('inf'), i
        if e10 + exp < -4970:
            return (Fraction(0), False), i
        # 桁の多い綴りを int にするので、4300 桁の制限をこの間だけ外す。
        _lim = getattr(sys, 'get_int_max_str_digits', None)
        _old = _lim() if _lim else None
        if _lim:
            sys.set_int_max_str_digits(0)
        try:
            q = Fraction(int(ip + fp), 10 ** int(len(fp)))
        finally:
            if _lim:
                sys.set_int_max_str_digits(_old)
        if exp > 0:
            q *= 10 ** exp
        elif exp < 0:
            q /= 10 ** (-exp)
        return self._make(q), i

    def _factor(self, i):
        i = self._skip(i)
        s = self.s
        if s[i] == '(':
            r, i = self._expr(i + 1)
            if r is None:
                return None, i
            i = self._skip(i)
            if s[i] == ')':
                i += 1
            return r, i
        if s[i] == '-':
            r, i = self._factor(i + 1)
            if r is None:
                return None, i
            if isinstance(r, float):
                return -r, i
            return (-r[0], not r[1]) if r[0] == 0 else (-r[0], False), i
        if s[i] == '+':
            return self._factor(i + 1)
        if (s[i].isdigit() and s[i].isascii()) or s[i] == '.':
            return self._number(i)
        return None, i

    def _term(self, i):
        r, i = self._factor(i)
        if r is None:
            return None, i
        while True:
            p = self._skip(i)
            c = self.s[p]
            if c != '*' and c != '/':
                break
            r2, j = self._factor(p + 1)
            if r2 is None:
                break
            if c == '/':
                if not isinstance(r2, float) and r2[0] == 0:
                    return None, i
                if isinstance(r2, float) and r2 == 0:
                    return None, i
            r = self._op(c, r, r2)
            i = j
        return r, i

    def _expr(self, i):
        i = self._skip(i)
        r, i = self._term(i)
        if r is None:
            return None, i
        while True:
            p = self._skip(i)
            c = self.s[p]
            if c != '+' and c != '-':
                break
            r2, j = self._term(p + 1)
            if r2 is None:
                break
            r = self._op(c, r, r2)
            i = j
        return r, i

    def run(self):
        """式全体を評価し、16 進 32 桁を返す。評価できなければ None。"""
        try:
            r, i = self._expr(0)
        except RecursionError:
            return None
        if r is None:
            return None
        if self.s[self._skip(i)] != chr(0):
            return None
        if isinstance(r, float):
            return None
        q, nz = r
        return _f128_bits_hex(q, nz)


def _f128_bits_hex(q, neg_zero):
    """4 倍精度で表せる有理数をビットパターンの 16 進 32 桁に。"""
    if q == 0:
        return ('8' if neg_zero else '0') + '0' * 31
    sign = 1 if q < 0 else 0
    q = abs(q)
    e = q.numerator.bit_length() - q.denominator.bit_length()
    if Fraction(2) ** e > q:
        e -= 1
    if e < _F128Eval._EMIN:
        exp_field = 0
        frac = int(q / Fraction(2) ** (_F128Eval._EMIN - 112))
    else:
        exp_field = e + 16383
        frac = int(q / Fraction(2) ** (e - 112)) - (1 << 112)
    bits = (sign << 127) | (exp_field << 112) | frac
    return '%032x' % bits


_VARNAME_RE = re.compile(r'[a-z][a-z0-9_]*')


class VariableManager:
    """パターン変数の束縛を読み書きする。

    変数は小文字で始まり小文字・数字・`_` が続く綴り。そうでないものは読めば
    VAR_UNDEF、書けば捨てる。束縛はパターン行ごとに消える。
    """

    def __init__(self, state):
        self.state = state

    @staticmethod
    def _index(s):
        """変数名を正規の鍵（小文字）に。変数名でなければ None（ASCII だけを見る）。"""
        if not s or not s.isascii():
            return None
        u = s.lower()
        return u if _VARNAME_RE.fullmatch(u) else None

    def get(self, s):
        """変数の値（未束縛・名前でないなら VAR_UNDEF）。"""
        i = self._index(s)
        return VAR_UNDEF if i is None else self.state.vars.get(i, VAR_UNDEF)

    def is_undef(self, s):
        """その変数が未定義ラベル由来の値を持っているか。"""
        i = self._index(s)
        return False if i is None else self.state.vars_undef.get(i, False)

    def put(self, s, v):
        """変数に値を束縛する（未定義由来の印は付けない）。"""
        self.put_tagged(s, v, False)

    def put_tagged(self, s, v, is_undef):
        """変数に値と「未定義由来か」の印を束縛する。整数で表せる値は int で持つ（caxx.c とそろえる）。"""
        c = self._index(s)
        if c is None:
            return
        st = self.state
        st.varnames.add(c)
        if isinstance(v, Decimal):
            st.vars[c] = int(v) if v.is_finite() and v == v.to_integral_value() else float(v)
        elif isinstance(v, float) and not v.is_integer():
            st.vars[c] = v
        else:
            try:
                st.vars[c] = int(v)
            except (OverflowError, ValueError):
                st.vars[c] = v
        st.vars_undef[c] = bool(is_undef)
        if st.exp_typ == 'f':
            st.vars_float[c] = True
        else:
            st.vars_float.pop(c, None)

    def is_float(self, s):
        """浮動小数点モードで書かれた変数か（caxx.c の PatVar.is_float）。"""
        i = self._index(s)
        return i is not None and self.state.vars_float.get(i, False)


class LabelManager:
    """ラベルの定義と参照（パスと照合の状況で答えを変える。-o では参照を ElfState に積む）。"""

    def __init__(self, state):
        self.state = state

    def _section_relative_offset(self, name, word_pc):
        """絶対のワード番地を、そのセクション先頭からの位置に直す（範囲外なら None）。

        開き直した範囲を順に累積する。範囲の終わりちょうども入れる（caxx.c の addr_to_word_offset()）。
        """
        cum = 0
        for rn, rs, rl in self.state.section_ranges:
            if rn != name:
                continue
            if rs <= word_pc <= rs + rl:
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
            return self.state.labels[k][1]
        except (KeyError, IndexError):
            self.state.error_undefined_label = True
            return UNDEF

    def get_value(self, k):
        """ラベルの値を読む。caxx.c の label_get_value() と同じ。

        未定義のときは、パス1で前回の値があればそれ、最初の反復なら現在の PC、
        長さだけ見る区間なら 0、それ以外は UNDEF（報告してよいパスなら診断。
        `.textmode` の `!L` の中は出さない）。-o の追跡中は参照を ElfState に積む
        （`.equ` は型付きのときだけ）。未定義を含む `.equ` はセクション相対に直さない。
        """
        st = self.state
        rx = st.relax
        try:
            ent = st.labels[k]
            v = ent[0]
        except (KeyError, IndexError):
            if rx.pas == 1 and k in rx.relax_prev_values:
                return rx.relax_prev_values[k]
            if rx.pas == 1 and rx.relax_optimistic:
                st.error_undefined_label = True
                return st.pc
            if rx.pass1_size_mode:
                return 0
            st.error_undefined_label = True
            if st.should_report_errors() and not st._textmode_lcap:
                st.diag(f" error - Label undefined: '{k}'"
                        f"  [{st.current_file or ''}:{st.ln}]", set_error=True)
            return UNDEF
        sec = ent[1]
        if st._equ_sections_touched is not None:
            st._equ_sections_touched.add(sec)
            adj = None if (_undef(v) or not _sectioned(st)) else self._section_relative_offset(sec, v)
            if adj is not None:
                v = adj
        elif ((st._in_binary_list or st._sec_frame) and sec == st.current_section
                and _sectioned(st)):
            adj = None if _undef(v) else self._section_relative_offset(sec, v)
            if adj is not None:
                v = adj
        is_equ = len(ent) > 2 and ent[2]
        equ_has_reloc = is_equ and len(ent) > 4 and ent[4] is not None
        e = st.elf
        if e.tracking and not st.error_undefined_label and (not is_equ or equ_has_reloc):
            cv = e.capturing_var
            if cv is not None:
                if cv not in e.var_to_label:
                    e.var_to_label[cv] = (k, v)
                else:
                    e.var_to_label[cv] = _elf_v2l_second(st, e.var_to_label[cv], k, v)
            elif e.current_word_idx >= 0:
                e.label_refs_seen.append((k, v, e.current_word_idx))
        return v

    def _report_definition_error(self, key, msg):
        """ラベル定義のエラーを、同じ原因について 1 回だけ出す（パス1と2で同じ行を通る）。"""
        self.state.had_error = True
        if key in self.state.reported_label_errors:
            return
        self.state.reported_label_errors.add(key)
        self.state.diag(f" error - {msg}  [{self.state.current_file or ''}:{self.state.ln}]",
                        set_error=True, force=True)

    def put_value(self, k, v, s, is_equ=False, reloc_type=None):
        """ラベルを定義する（できたかを返す）。

        弾くのは二重定義（インポートの上書きは可）・パス1に無くパス2で現れた名前・
        パターンファイルのシンボルとの衝突。型が無ければ前の定義の型を引き継ぐ。
        """
        st = self.state
        old = st.labels.get(k)
        if st.relax.pas in (0, 1):
            if old is not None and not (len(old) > 3 and old[3]):
                self._report_definition_error(('dup', k), f"label '{k}' is already defined.")
                return False
        elif st.relax.pas == 2 and k not in st.labels:
            self._report_definition_error(('pass1', k), f"label '{k}' not defined in pass 1.")
            return False
        if StringUtils.upper(k) in st.patsymbols:
            self._report_definition_error(('patsym', k), f"'{k}' is a pattern file symbol.")
            return False
        entry = [v, s, is_equ, False]
        if reloc_type is None and old is not None and len(old) > 4:
            reloc_type = old[4]
        if reloc_type is not None:
            entry.append(reloc_type)
        st.labels[k] = entry
        return True

    def printlabels(self):
        """ラベル表を標準エラーへ並べる（プロンプトモードの `?`）。"""
        result = {}
        for key, (num, section, *_rest) in self.state.labels.items():
            if num == UNDEF:
                num_str = "UNDEF"
            elif isinstance(num, float):
                num_str = repr(num)
            else:
                try:
                    num_str = hex(int(num))
                except (TypeError, ValueError, OverflowError):
                    num_str = repr(num)
            result[key] = (num_str, section)
        for k, v in sorted(result.items()):
            print(f"  {k:40s}  {v[0]}  ({v[1]})", file=sys.stderr)


class SymbolManager:
    """パターンファイルが定義したシンボルを引く（名前は大文字で正規化）。"""

    def __init__(self, state):
        self.state = state

    def get(self, w):
        """シンボルの値。無ければ空文字。"""
        return self.state.symbols.get(StringUtils.upper(w), "")


_ENUM_WORD_CHARS = set(DIGIT + ALPHABET + '_')


def _enum_name_at(s, idx, names, fold=False):
    """その位置の名前を最長一致で読む（語の途中では一致しない）。返り値は (番号, 次の位置) か (-1, idx)。

    fold なら names を大文字にして比べ、文字列でない項目は飛ばす（`!Y` の集合）。
    """
    best = -1
    best_end = idx
    for k, nm in enumerate(names):
        if fold:
            if not isinstance(nm, str):
                continue
            nm = StringUtils.upper(nm)
        n = len(nm)
        if n <= best_end - idx or StringUtils.upper(s[idx:idx + n]) != nm:
            continue
        e = idx + n
        if e < len(s) and s[e] in _ENUM_WORD_CHARS:
            continue
        best = k
        best_end = e
    return best, best_end


def _symset_item_at(s, idx, items):
    """`!Y` の集合の項目名を最長一致で読む（`A,AX,AL` で `al` は `AL`）。"""
    return _enum_name_at(s, idx, items, True)


# 文字定数のエスケープ（4 文字の綴り → 値）。
_CHAR_ESC = {"'\\t'": 0x09, "'\\''": 0x27, "'\\\\'": 0x5c, "'\\n'": 0x0a, "'\\0'": 0x00,
             "'\\r'": 0x0d, "'\\a'": 0x07, "'\\b'": 0x08, "'\\f'": 0x0c, "'\\v'": 0x0b}
# `flt{}` / `dbl{}` の nan / inf / -inf と struct の書式。
_FLT_BRACE = {'dbl': ({'nan': 0x7ff8000000000000, 'inf': 0x7ff0000000000000,
                       '-inf': 0xfff0000000000000}, '>d', 64),
              'flt': ({'nan': 0x7fc00000, 'inf': 0x7f800000, '-inf': 0xff800000}, '>f', 32)}
_BRACE_KWS = ('qad', 'dbl', 'flt', 'enflt', 'endbl')


class ExpressionEvaluator:
    """式評価器。優先順位ごとに 1 メソッドの再帰下降で、どの層も同じ式を同じ値にする。

    どれも (値, 次の位置) を返す。使える項の違いは state.expcaps だけで表す。
    state.exp_typ が 'f' なら浮動小数点で計算する。優先順位（緩いものが外側）:
      term11 ?:   term10 ||   term9 &&   term8 （素通し）  term7 <= < >= > == !=
      term6 '（符号拡張）  term5 ^   term4 |   term3 &   term2 << >>   term1 + -
      term0 * / // %   term0_0 **   factor 単項 - ~ @・`*(x,y)`・`!!!` `!!!!`   factor1 項
    """

    def __init__(self, state, var_manager, label_manager, symbol_manager, parser):
        self.state = state
        self.var_manager = var_manager
        self.label_manager = label_manager
        self.symbol_manager = symbol_manager
        self.parser = parser

    def factor(self, s, idx):
        """factor の入り口。入れ子を数え _EXPR_MAX_DEPTH で打ち切る（caxx.c の expr_factor と同じ）。"""
        st = self.state
        if st.expr_depth >= _EXPR_MAX_DEPTH:
            if st.should_report_errors():
                st.diag(" error - expression nesting too deep.", set_error=True)
            return 0, idx
        st.expr_depth += 1
        try:
            return self._factor_impl(s, idx)
        finally:
            st.expr_depth -= 1

    def _factor_impl(self, s, idx):
        """単項演算子・`*(x,y)`・VLIW の `!!!`（命令の数）と `!!!!`（ストップビット）。残りは factor1。

        factor1 が進めなければ expr_missing を立て、区切り文字でもなければ警告する。
        """
        st = self.state
        idx = StringUtils.skipspc(s, idx)
        c = s[idx] if idx < len(s) else ''
        x = 0
        if s.startswith('!!!!', idx) and st.expcaps.vliw:
            x = st.vliw.stop
            idx += 4
        elif s.startswith('!!!', idx) and st.expcaps.vliw:
            x = st.vliw.cnt
            idx += 3
        elif c == '-':
            x, idx = self.factor(s, idx + 1)
            if _undef(x):
                pass
            elif st.exp_typ == 'f' and type(x) is int and x == 0:
                x = -0.0        # 浮動小数点の文脈の 0 は 0.0（caxx.c と同じビット）
            else:
                x = -x
        elif c == '~':
            x, idx = self.factor(s, idx + 1)
            try:
                x = x if _undef(x) else ~int(x)
            except (OverflowError, ValueError):
                st.diag(" error - cannot apply bitwise NOT (~) to non-finite float value.", set_error=True)
                x = 0
        elif c == '@':
            x, idx = self.factor(s, idx + 1)
            x = x if _undef(x) else op_msb(x)
        elif c == '*':
            if s[idx + 1:idx + 2] != '(':
                st.diag(" error - expected '(' after '*' in *(expr,expr) expression.", set_error=True)
                idx += 1
            else:
                x, idx = self.expression(s, idx + 2)
                if s[idx:idx + 1] != ',':
                    st.diag(" error - missing ',' in *(expr, expr) expression.", set_error=True)
                    x = 0
                else:
                    x2, idx = self.expression(s, idx + 1)
                    if s[idx:idx + 1] != ')':
                        st.diag(" error - missing ')' in *(expr, expr) expression.", set_error=True)
                        x = 0
                    else:
                        idx += 1
                        if _undef(x) or _undef(x2):
                            x = UNDEF
                        else:
                            x, err = op_byte(x, x2)
                            if err:
                                st.diag(f" error - {err}.", set_error=True)
        else:
            prev_idx = idx
            x, idx = self.factor1(s, idx)
            if idx == prev_idx:
                st.expr_missing = True
                if (idx < len(s) and s[idx] not in (chr(0), ',', ')', ']', CB, ' ', '\t')
                        and not st._in_match_attempt and st.should_report_errors()):
                    st.diag(f" warning - unrecognized token at position {idx} in expression: "
                            f"{s[idx:idx + 8]!r} (treated as 0)", set_error=False)
        return x, StringUtils.skipspc(s, idx)

    def xeval(self, x, _=None):
        """flt{} / dbl{} / qad{} の中身を _XevalParser で読む（int か float、不可は ValueError）。

        `:ラベル` は 256 ビットの符号付き（caxx.c の xeval_primary()）。未定義は印を立てて 0。
        """
        st = self.state

        def label(name):
            try:
                val = st.labels[name][0]
                if _is_undef_derived(val):
                    raise ValueError
                v = int(val) & ((1 << 256) - 1)
            except (KeyError, IndexError, TypeError, ValueError, OverflowError):
                st.error_undefined_label = True
                return 0
            return v - (1 << 256) if v >> 255 else v

        return _XevalParser(x, label, st.lwordchars).parse()

    def _sec_rel_pc(self, raw):
        """binary_list・照合・`.equ` の中ではセクション相対に直した位置。"""
        st = self.state
        if ((st._in_binary_list or st._sec_frame or st._equ_sections_touched is not None)
                and _sectioned(st)):
            adj = self.label_manager._section_relative_offset(st.current_section, raw)
            return raw if adj is None else adj
        return raw

    def loc_counter_value(self):
        """`$$` の値（binary_list の中では命令の先頭）。caxx.c の loc_counter_value() と同じ。"""
        st = self.state
        return self._sec_rel_pc(st.pc_instr_start if st._in_binary_list else st.pc)

    def _brace_inner_int(self, t):
        """enflt{} / endbl{} の中身を整数モードで読む。返り値は (値, 未定義を含んだか)。"""
        st = self.state
        outer = st.error_undefined_label
        st.error_undefined_label = False
        prev_typ = st.exp_typ
        st.exp_typ = 'i'
        try:
            v, _ = self.expression(t + chr(0), 0)
        finally:
            st.exp_typ = prev_typ
        inner = st.error_undefined_label
        st.error_undefined_label = outer or inner
        return v, inner

    def _qad_value(self, t):
        """qad{} の中身を binary128 のビットにする（だめなら倍精度の評価を %.17g で）。"""
        st = self.state
        if t in ('nan', 'inf', '-inf'):
            return int(IEEE754Converter.decimal_to_ieee754_128bit_hex(t), 16)
        try:
            h = IEEE754Converter.decimal_eval_expr(t)
        except (ValueError, ZeroDivisionError):
            try:
                v = self.xeval(t, None)
            except (ValueError, TypeError, OverflowError, ZeroDivisionError):
                st.diag(f" error - qad{{}}: cannot evaluate expression '{t}'; using 0.", set_error=True)
                h = '0' * 32
            else:
                fv = _float_of(v)
                h = (IEEE754Converter.decimal_to_ieee754_128bit_hex(_g17(fv))
                     if math.isfinite(fv) else '7fff' + '0' * 28)
        if (int(h, 16) >> 112) & 0x7fff == 0x7fff:
            st.diag(f" error - qad{{}}: cannot evaluate expression '{t}'; using 0.", set_error=True)
            h = '0' * 32
        return int(h, 16)

    def factor1(self, s, idx):
        """項を 1 個読む（数・文字定数・ラベル・`#シンボル`・変数・`$$` `$.`・括弧・`:=`・
        配列の添字・`.enum` など）。どれでもなければ位置を動かさず 0。
        """
        st = self.state
        x = 0
        idx = StringUtils.skipspc(s, idx)
        n = len(s)
        if idx >= n:
            return x, idx

        enum_hit = None
        if st.enum_bindings is not None:
            enames, evals = st.enum_bindings
            ek, eend = _enum_name_at(s, idx, enames)
            if ek >= 0:
                enum_hit = (evals[ek], eend)
        kw = next((k for k in _BRACE_KWS if s.startswith(k, idx)
                   and (j := StringUtils.skipspc(s, idx + len(k))) < n and s[j] == '{'), None)

        if s[idx] == '(':
            x, idx = self.expression(s, idx + 1)
            if idx < n and s[idx] == ')':
                idx += 1
            else:
                st.diag(" error - missing closing ')' in expression.", set_error=True)
        elif s[idx:idx + 4] in _CHAR_ESC:
            x = _CHAR_ESC[s[idx:idx + 4]]
            idx += 4
        elif (hexlit := StringUtils.parse_hex_char_literal(s, idx))[0]:
            x, idx = hexlit[1], hexlit[2]
        elif (idx + 3 <= n and s[idx] == '\'' and s[idx + 1] != '\\' and s[idx + 2] == '\''
              and _byte_char(s[idx + 1]) is not None):
            x = _byte_char(s[idx + 1])
            idx += 3
        elif s.startswith('$$', idx):
            idx += 2
            x = self.loc_counter_value()
        elif s.startswith('$.', idx):
            idx += 2
            x = self._sec_rel_pc(st.pc_instr_end)
        elif s[idx] == '#':
            t, idx = self.parser.get_symbol_word(s, idx + 1)
            arr = st.arrsymbols.get(t)
            if arr is not None and idx < n and s[idx] == '[':
                iv, idx = self.expression_pat(s, idx + 1)
                if idx < len(s) and s[idx] == ']':
                    idx += 1
                else:
                    st.diag(f" error - '#{t}[': missing ']'.", set_error=True)
                k = int(iv)
                if k < 0 or k >= len(arr):
                    st.diag(f" error - index {k} is out of range for array "
                            f"symbol '{t}' (0..{len(arr) - 1}).", set_error=True)
                elif isinstance(arr[k], str):
                    st.diag(f" error - '#{t}[{k}]' is a string item and "
                            f"has no numeric value.", set_error=True)
                else:
                    x = arr[k]
            else:
                x = self.symbol_manager.get(t)
                if x == "":
                    st.diag(f" error - undefined symbol: '#{t}'", set_error=True)
                    x = 0
        elif StringUtils.q(s, '0b', idx):
            idx += 2
            while idx < len(s) and s[idx] in "01":
                x = 2 * x + int(s[idx], 2)
                idx += 1
        elif StringUtils.q(s, '0x', idx):
            idx += 2
            while idx < len(s) and StringUtils.upper(s[idx]) in XDIGIT:
                x = 16 * x + int(s[idx].translate(_ALOWER), 16)
                idx += 1
        elif kw is not None:
            f, t, idx = self.parser.get_curlb(s, idx + len(kw))
            if not f:
                pass
            elif kw == 'qad':
                x = self._qad_value(t)
            elif kw in _FLT_BRACE:
                special, fmt, bits = _FLT_BRACE[kw]
                if t in special:
                    x = special[t]
                else:
                    try:
                        v = float(self.xeval(t, None))
                        if not math.isfinite(v):
                            raise OverflowError('non-finite')
                        x = int.from_bytes(struct.pack(fmt, v), "big")
                    except (OverflowError, ValueError, TypeError, struct.error, ZeroDivisionError):
                        st.diag(f" error - {kw}{{}}: cannot convert expression to float{bits}; "
                                f"using 0.", set_error=True)
                        x = 0
            else:
                v, inner = self._brace_inner_int(t)
                if inner:
                    st.diag(f" error - {kw}{{}}: expression contains undefined label.", set_error=True)
                    v = 0
                x = (enflt(int(v) & 0xFFFFFFFF) if kw == 'enflt'
                     else endbl(int(v) & 0xFFFFFFFFFFFFFFFF))
                x = _float_brace_result(st, x, kw)
        elif s.startswith('not(', idx):
            x, idx = self.expression(s, idx + 4)
            idx = StringUtils.skipspc(s, idx)
            if idx < len(s) and s[idx] == ')':
                idx += 1
            else:
                st.diag(" error - missing closing ')' in not(...) expression.", set_error=True)
            x = 0 if x else 1
        elif st.exp_typ == 'i' and s[idx] in DIGIT:
            fs, idx = self.parser.get_intstr(s, idx)
            x = int(fs)
        elif st.exp_typ == 'f' and self.parser.isfloatstr(s, idx):
            fs, idx = self.parser.get_floatstr(s, idx)
            try:
                x = float(fs) if fs else 0.0
            except ValueError:
                x = 0.0
        elif enum_hit is not None:
            x, idx = enum_hit
        elif st.expcaps.patvars and (vnl := self._patvar_len_at(s, idx)) > 0:
            ch = s[idx:idx + vnl]
            if s[idx + vnl:idx + vnl + 2] == ':=':
                prior = st.error_undefined_label
                st.error_undefined_label = False
                x, idx = self.expression(s, idx + vnl + 2)
                undef = st.error_undefined_label
                st.error_undefined_label = prior or undef
                self.var_manager.put_tagged(ch, x, undef)
            else:
                x = self.var_manager.get(ch)
                if st.exp_typ != 'f' and self.var_manager.is_float(ch):
                    st._expr_read_float_var = True
                idx += vnl
                if (not st._in_match_attempt and not st.relax.pass1_size_mode
                        and st.should_report_errors()
                        and (self.var_manager.is_undef(ch) or _is_undef_derived(x))):
                    st.error_undefined_label = True
                    st.diag(f" error - Label undefined: variable '{ch}' contains undefined value"
                            f"  [{st.current_file}:{st.ln}]", set_error=False)
                self.elf_note_var_ref(ch, x)
        elif s[idx] in st.lwordchars:
            w, idx_new = self.parser.get_label_word(s, idx, eat_colon=False)
            if idx != idx_new:
                idx = idx_new
                x = self.label_manager.get_value(w)

        return x, StringUtils.skipspc(s, idx)

    def term0_0(self, s, idx):
        """`**`。caxx.c の expr_term0_0() と同じ。

        浮動小数点モードは _ieee_pow。整数モードは負の指数・1024 を超える指数・
        2**256 を超える結果をエラーで 0 にし、残りの `**` も読み進める。
        """
        x, idx = self.factor(s, idx)
        max_bits = _UNDEF_SANE_CEILING.bit_length() - 1
        while s.startswith('**', idx):
            t, idx = self.factor(s, idx + 2)
            if _undef(x) or _undef(t):
                x = UNDEF
                continue
            if self.state.exp_typ == 'f':
                x = _ieee_pow(x, t)
                continue
            try:
                t_int = int(t)
            except (ValueError, OverflowError):
                t_int = 0
            if t_int < 0:
                self.state.diag(" error - Negative exponent in ** expression; result set to 0.", set_error=True)
                x = 0
                continue
            if t_int > 1024:
                self.state.diag(f" error - Exponent {t_int} exceeds maximum 1024 in ** expression; result set to 0.", set_error=True)
                x = 0
                continue
            if t_int == 0:
                x = 1
                continue
            if t_int == 1:
                continue
            # |x| >= 2 なら結果は少なくとも (ビット数-1)×指数+1 ビット。超えるなら計算しない。
            try:
                base_bits = abs(x).bit_length() if isinstance(x, int) else 1024
            except (TypeError, ValueError, OverflowError):
                base_bits = 1024
            too_big = base_bits >= 2 and (base_bits - 1) * t_int + 1 > max_bits
            if not too_big:
                try:
                    r = x ** t_int
                except OverflowError:
                    self.state.diag(" error - ** result is too large to represent as a float; result set to 0.", set_error=True)
                    x = 0
                    continue
                too_big = isinstance(r, int) and abs(r).bit_length() > max_bits
            if too_big:
                self.state.diag(f" error - ** result would exceed {max_bits} bits "
                                f"(chained exponentiation); result set to 0.", set_error=True)
                x = 0
                continue
            x = int(r) if isinstance(r, float) and r.is_integer() else r
        return x, idx

    def _div0(self):
        """0 で割ったときの値 0（`!Q` の倍精度評価中は報告を先送りする）。"""
        st = self.state
        if st.fdiv0_defer and st.exp_typ == 'f':
            st.fdiv0_seen = True
        else:
            st.diag(" error - Division by 0 error.", set_error=True)
        return 0

    def term0(self, s, idx):
        """`*` `/` `//` `%`。整数の `/` は 0 方向へ切り捨て、`%` は Python と同じ除数の符号。"""
        x, idx = self.term0_0(s, idx)
        while idx < len(s):
            c = s[idx]
            if c == '*' and s[idx + 1:idx + 2] != '*':
                op = '*'
            elif s.startswith('//', idx):
                op = '//'
            elif c in '/%':
                op = c
            else:
                break
            t, idx = self.term0_0(s, idx + len(op))
            if _undef(x) or _undef(t):
                x = UNDEF
            elif op == '*':
                x = x * t
            elif t == 0:
                x = self._div0()
            elif op == '//':
                x //= t
            elif op == '%':
                x = x % t
            elif self.state.exp_typ == 'i' and isinstance(x, int) and isinstance(t, int):
                q = abs(x) // abs(t)
                x = -q if (x < 0) != (t < 0) else q
            else:
                x = x / t
        return x, idx

    def term1(self, s, idx):
        """`+` `-`。"""
        x, idx = self.term0(s, idx)
        while idx < len(s) and s[idx] in '+-':
            op = s[idx]
            t, idx = self.term0(s, idx + 1)
            x = UNDEF if _undef(x) or _undef(t) else (x + t if op == '+' else x - t)
        return x, idx

    def term2(self, s, idx):
        """`<<` `>>`。負と 65536 を超えるシフト量はエラーで 0 にし、残りも読む（caxx.c の expr_term2()）。"""
        x, idx = self.term1(s, idx)
        while s[idx:idx + 2] in ('<<', '>>'):
            op = s[idx:idx + 2]
            t, idx = self.term1(s, idx + 2)
            if _undef(x) or _undef(t):
                x = UNDEF
                continue
            try:
                x = int(x)
                t = int(t)
            except (ValueError, OverflowError):
                x = 0
                break
            if t < 0:
                self.state.diag(f" error - negative shift count ({t}) in {op} expression.", set_error=True)
                x = 0
            elif t > 65536:
                self.state.diag(f" error - shift count {t} exceeds maximum 65536 in {op} expression.", set_error=True)
                x = 0
            else:
                x = x << t if op == '<<' else x >> t
        return x, idx

    def _safe_int(self, v, op_name):
        """ビット演算の前に整数へ落とす。非有限値は報告して 0。"""
        try:
            return int(v)
        except (OverflowError, ValueError):
            if self.state.should_report_errors():
                self.state.diag(f" error - non-finite value {v!r} in bitwise '{op_name}' operation; treated as 0.", set_error=False)
                self.state.had_error = True
            return 0

    def _bit_level(self, s, idx, sub, op, fn, not_doubled):
        """ビット演算 1 段（not_doubled なら `&&` `||` は食べない）。"""
        x, idx = sub(s, idx)
        while idx < len(s) and s[idx] == op and not (not_doubled and s[idx + 1:idx + 2] == op):
            t, idx = sub(s, idx + 1)
            x = UNDEF if _undef(x) or _undef(t) else \
                fn(self._safe_int(x, op), self._safe_int(t, op))
        return x, idx

    def term3(self, s, idx):
        """`&`。"""
        return self._bit_level(s, idx, self.term2, '&', int.__and__, True)

    def term4(self, s, idx):
        """`|`。"""
        return self._bit_level(s, idx, self.term3, '|', int.__or__, True)

    def term5(self, s, idx):
        """`^`。"""
        return self._bit_level(s, idx, self.term4, '^', int.__xor__, False)

    def term6(self, s, idx):
        """`'` — 符号拡張（直後が数字か `(` のときだけ演算子。文字定数の `'` と区別する）。"""
        x, idx = self.term5(s, idx)
        while idx < len(s) and s[idx] == '\'':
            j = StringUtils.skipspc(s, idx + 1)
            if j >= len(s) or (s[j] not in DIGIT and s[j] != '('):
                break
            t, idx = self.term5(s, idx + 1)
            if _undef(x) or _undef(t):
                x = UNDEF
                continue
            x, warn, go = op_sext(x, t)
            if warn:
                self.state.diag(f" warning - {warn}.", set_error=False)
            if not go:
                break
        return x, idx

    _CMP_OPS = (('<=', lambda a, b: a <= b), ('<', lambda a, b: a < b),
                ('>=', lambda a, b: a >= b), ('>', lambda a, b: a > b),
                ('==', lambda a, b: a == b), ('!=', lambda a, b: a != b))

    def term7(self, s, idx):
        """比較 `<=` `<` `>=` `>` `==` `!=`（結果は 1 か 0）。"""
        x, idx = self.term6(s, idx)
        while idx < len(s):
            for op, fn in self._CMP_OPS:
                if s.startswith(op, idx):
                    break
            else:
                break
            t, idx = self.term6(s, idx + len(op))
            x = UNDEF if _undef(x) or _undef(t) else (1 if fn(x, t) else 0)
        return x, idx

    def term8(self, s, idx):
        """空けてある段（caxx.c と段の番号をそろえるため）。"""
        return self.term7(s, idx)

    def term9(self, s, idx):
        """`&&`（1 か 0）。左が偽なら右は評価せずに読み飛ばす（caxx.c の expr_term9()）。"""
        x, idx = self.term8(s, idx)
        while s.startswith('&&', idx):
            if not _undef(x) and not x:
                idx = self._skip_subexpr(s, idx + 2, True)
                x = 0
                continue
            t, idx = self.term8(s, idx + 2)
            x = UNDEF if _undef(x) or _undef(t) else (1 if x and t else 0)
        return x, idx

    def term10(self, s, idx):
        """`||`（1 か 0）。左が真なら右は評価せずに読み飛ばす（caxx.c の expr_term10()）。"""
        x, idx = self.term9(s, idx)
        while s.startswith('||', idx):
            if not _undef(x) and x:
                idx = self._skip_subexpr(s, idx + 2)
                x = 1
                continue
            t, idx = self.term9(s, idx + 2)
            x = UNDEF if _undef(x) or _undef(t) else (1 if x or t else 0)
        return x, idx

    @staticmethod
    def _skip_subexpr(s, idx, stop_at_or=False):
        """括弧の対応を数えて部分式 1 個を読み飛ばした位置。caxx.c の skip_subexpr() と同じ。

        深さ 0 の `?` `,` `;` `:`（`:=` は除く）と対応しない閉じ括弧で止まる。stop_at_or なら
        深さ 0 の `||` でも止まる（`&&` の右の項）。文字定数は一まとまりに飛ばす。
        """
        paren = brack = ob = 0
        n = len(s)
        while idx < n and s[idx] != chr(0):
            c = s[idx]
            if c == "'":
                idx = StringUtils.skip_squote_literal(s, idx)
                continue
            top = paren == 0 and brack == 0 and ob == 0
            if top and stop_at_or and s.startswith('||', idx):
                break
            if c == '(':
                paren += 1
            elif c == ')':
                if paren <= 0:
                    break
                paren -= 1
            elif c == '[':
                brack += 1
            elif c == ']':
                if brack <= 0:
                    break
                brack -= 1
            elif c == OB:
                ob += 1
            elif c == CB:
                if ob <= 0:
                    break
                ob -= 1
            elif top and (c in '?,;' or (c == ':' and s[idx + 1:idx + 2] != '=')):
                break
            idx += 1
        return idx

    @staticmethod
    def _at_colon(s, i):
        """s[i] が三項の `:` か（`:=` は代入）。"""
        return s[i:i + 1] == ':' and s[i + 1:i + 2] != '='

    @classmethod
    def _skip_ternary_expr(cls, s, idx, depth=0):
        """三項演算子の選ばれなかった側を読み飛ばす（深さは _EXPR_MAX_DEPTH まで）。"""
        if depth > _EXPR_MAX_DEPTH:
            return idx
        idx = cls._skip_subexpr(s, idx)
        if s[idx:idx + 1] == '?' and s[idx + 1:idx + 2] != '=':
            idx = StringUtils.skipspc(s, idx + 1)
            idx = StringUtils.skipspc(s, cls._skip_ternary_expr(s, idx, depth + 1))
            if cls._at_colon(s, idx):
                idx = StringUtils.skipspc(s, idx + 1)
                idx = cls._skip_ternary_expr(s, idx, depth + 1)
        return idx

    def term11(self, s, idx):
        """`?:`。選ばれなかった側は評価せずに読み飛ばす（`:=` の副作用を走らせない）。"""
        x, idx = self.term10(s, idx)
        if s[idx:idx + 1] != '?':
            return x, idx
        st = self.state
        if st.expr_depth >= _EXPR_MAX_DEPTH:
            # 深すぎる。両側とも読み飛ばして 0 にする（caxx.c と同じ）。
            if st.should_report_errors():
                st.diag(" error - expression nesting too deep.", set_error=True)
            idx = StringUtils.skipspc(s, self._skip_ternary_expr(s, StringUtils.skipspc(s, idx + 1)))
            if self._at_colon(s, idx):
                idx = self._skip_ternary_expr(s, StringUtils.skipspc(s, idx + 1))
            return 0, idx
        st.expr_depth += 1
        try:
            idx = StringUtils.skipspc(s, idx + 1)
            if x == 0:
                skip_end = self._skip_ternary_expr(s, idx)
                if self._at_colon(s, skip_end):
                    x, idx = self.term11(s, StringUtils.skipspc(s, skip_end + 1))
                else:
                    idx = skip_end
                    x = 0
            else:
                x, idx = self.term11(s, idx)
                idx = StringUtils.skipspc(s, idx)
                if self._at_colon(s, idx):
                    idx = self._skip_ternary_expr(s, StringUtils.skipspc(s, idx + 1))
        finally:
            st.expr_depth -= 1
        return x, idx

    def expression(self, s, idx):
        """式を 1 個評価する。"""
        try:
            return self.term11(s, StringUtils.skipspc(s, idx))
        except RecursionError:
            self.state.diag(" error - expression nesting too deep.", set_error=True)
            return 0, idx

    def _terminate(self, s):
        """末尾に NUL を足して式の終わりを確定させる。"""
        return s if s and s[-1] == chr(0) else s + chr(0)

    def _patvar_len_at(self, s, idx):
        """その位置のパターン変数名の長さ（直後がラベル文字なら変数ではない）。"""
        n = PatternMatcher._var_name_at(s, idx)
        if n == 0 or (idx + n < len(s) and s[idx + n] in self.state.lwordchars):
            return 0
        return n

    def expression_pat(self, s, idx):
        """パターン行の式として評価する（すべての項が使える）。"""
        return self._expression_in(s, idx, CAPS_PAT)

    def expression_caps(self, s, idx, caps):
        """使える項を明示して評価する。"""
        return self._expression_in(s, idx, caps)

    def expression_asm(self, s, idx):
        """アセンブリ行の式として評価する（パターン変数と VLIW 計数は使えない）。"""
        return self._expression_in(s, idx, CAPS_ASM)

    def _expression_in(self, s, idx, caps):
        """使える項を差し替えて評価し、必ず元に戻す。"""
        prev_caps = self.state.expcaps
        self.state.expcaps = caps
        try:
            return self.expression(self._terminate(s), idx)
        finally:
            self.state.expcaps = prev_caps

    def elf_note_var_ref(self, ch, x):
        """-o の追跡中、いまの出力ワードが変数 ch の値を使ったことを記録する（caxx.c の elf_note_var_ref()）。

        binary_list とソースの `.db` などの両方から呼ぶ。ラベル差は最初の足す項の名前で積み、
        項・`.reloc` の型・定数部を ('d', ワード位置) のヒントに添える。
        """
        st = self.state
        e = st.elf
        w = e.current_word_idx
        if not (e.tracking and w >= 0):
            return
        entry = e.var_to_label.get(ch)
        if isinstance(entry, tuple) and len(entry) == 3 and entry[0] == 'D':
            terms, tot = entry[1], entry[2]
            key = next((n for sg, n in terms if sg > 0), terms[0][1])
            e.label_refs_seen.append((key, tot, w))
            cst = 0 if _is_undef_derived(x) else int(x) - int(tot)
            e.insn_reloc_hint.setdefault(
                ('d', w), (terms, st.reloc_constraints.get(ch), cst, st.reloc_masks.get(ch, 0)))
            return
        if isinstance(entry, tuple):
            lname, lval = entry
            e.label_refs_seen.append((lname, lval, w))
            if not _is_undef_derived(x):
                # オペランドの値 − ラベルの値（`.elfpcguess` が見る）。
                e.insn_reloc_hint.setdefault(('v', w), int(x) - int(lval))
                rt = st.reloc_constraints.get(ch)
                if rt is not None:
                    e.insn_reloc_hint.setdefault(
                        w, (rt, int(x) - int(lval), st.reloc_masks.get(ch, 0),
                            st.reloc_pairs.get(ch, ())))

    def expression_esc(self, s, idx, stopchar):
        """入れ子の外側にある stopchar までを 1 つの式として評価する（`(` `[` `[[` を数える）。"""
        depth = 0
        for k in range(idx, len(s)):
            ch = s[k]
            if not depth and ch == stopchar:
                s = s[:k] + chr(0)
                break
            if ch in '([' or ch == OB:
                depth += 1
            elif (ch in ')]' or ch == CB) and depth:
                depth -= 1
        return self.expression(self._terminate(s), idx)

    def expression_esc_float(self, s, idx, stopchar):
        """expression_esc の浮動小数点版（評価後に必ずモードを戻す）。"""
        prev_typ = self.state.exp_typ
        prev_caps = self.state.expcaps
        self.state.exp_typ = 'f'
        try:
            return self.expression_esc(s, idx, stopchar)
        finally:
            self.state.exp_typ = prev_typ
            self.state.expcaps = prev_caps


class BinaryWriter:
    """出力ワードを「位置 → ワード」の辞書に溜め（`.org` で飛べるため）、`-b` の生バイナリを書く。"""

    def __init__(self, state):
        self.state = state
        self._buffer = {}

    def _store(self, position, word_val):
        """1 ワードを溜める（ワード幅で切り、負の位置は捨てる）。"""
        if self.state.bts > 0 and position >= 0:
            self._buffer[position] = word_val & ((1 << self.state.bts) - 1)

    def flush(self):
        """溜めたワードを `-b` のファイルへ書く。

        隙間は `.padding` で埋め、各ワードは `.bits` のバイト数とバイト順で並べる。1GB を
        超えたら書かない。-o と併用でリンカのために 0 のまま残した欄があれば警告する。
        """
        st = self.state
        if not st.outfile:
            return
        if st.bts <= 0:
            st.diag(f" error - flush: bts={st.bts} is invalid (<=0); "
                    f"no output written to '{st.outfile}'.", set_error=True)
            return
        if not self._buffer:
            return
        word_bits = st.bts
        bpw = (word_bits + 7) // 8
        nwords = max(self._buffer) + 1
        total_size = nwords * bpw
        if total_size > 1 << 30:
            st.diag(f" error - output size {total_size} bytes exceeds maximum "
                    f"{1 << 30}. Check for incorrect .ORG or address "
                    f"values.", set_error=True, force=True)
            return
        order = 'little' if st.endian == 'little' else 'big'
        pad_val = int(st.padding) & ((1 << word_bits) - 1)
        data = bytearray(pad_val.to_bytes(bpw, order) * nwords if pad_val else total_size)
        for pos, val in self._buffer.items():
            data[pos * bpw:(pos + 1) * bpw] = val.to_bytes(bpw, order)
        try:
            with open(st.outfile, 'wb') as f:
                f.write(data)
        except OSError as e:
            st.diag(f" error - cannot write '{st.outfile}': {e}", set_error=True)
            return
        print(f"raw: wrote {st.outfile} ({len(data)} bytes)", file=sys.stderr)

        if st.elf.objfile:
            rela = elf_machine_table(st)['is_rela']
            zeroed = [r for r in st.elf.relocations
                      if rela or insn_reloc_field_mask(r[3], st) is not None]
            if zeroed:
                where = ', '.join(f"{r[0]}+0x{r[1]:x}" for r in zeroed[:4])
                if len(zeroed) > 4:
                    where += ', ...'
                st.diag(f" warning - {len(zeroed)} field(s) were left 0 for the"
                        f" linker ({where}); this raw binary is only correct after linking"
                        f" {st.elf.objfile}. Drop -o to have axx fill them in.",
                        set_error=False, force=True)

    def fwrite(self, position, x, prt):
        """1 ワードを溜める。prt が真ならリスティング用に 16 進でも出す。"""
        b = self.state.bts
        if b <= 0:
            return 0
        val = x & ((1 << b) - 1)
        if prt:
            print(f" 0x{val:0{(b + 3) // 4}x}", end='')
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
        st = self.state
        if st.should_report_errors():
            prt = 1 if ((st.relax.pas == 2 and st.verbose) or st.relax.pas == 0) else 0
            try:
                self.fwrite(a, int(x), prt)
            except (OverflowError, ValueError):
                st.diag(f" error - non-finite value {x!r} cannot be written as binary word.", set_error=True)

    def align_(self, addr):
        """番地を現在の `.align` の倍数まで繰り上げる。"""
        al = self.state.align
        if al <= 0 or addr % al == 0:
            return addr
        return addr + al - addr % al


def _word_occurs(var, src):
    """var が src に語として（前後が英数字でも `_` でもなく）現れるか。"""
    for m in re.finditer(re.escape(var), src):
        b, e = m.start(), m.end()
        if b > 0 and (_aan(src[b - 1]) or src[b - 1] == '_'):
            continue
        if e < len(src) and (_aan(src[e]) or src[e] == '_'):
            continue
        return True
    return False


def _captext_words(txt, lw):
    """捕捉した綴りから、ラベルになりうる語を順に出す。

    数・文字定数・文字列・`$$` `$.`・`#記号` は飛ばす（式は評価しない）。
    """
    n = len(txt)
    i = 0
    while i < n:
        c = txt[i]
        if c in '"\'':
            j = i + 1
            while j < n and txt[j] != c:
                j += 2 if txt[j] == '\\' and j + 1 < n else 1
            i = j + 1
        elif c == '$':
            i += 2 if txt[i + 1:i + 2] in ('$', '.') else 1
        elif c == '#' or c in DIGIT:
            i += 1
            while i < n and (txt[i] in _ISLABEL_ALNUM or txt[i] in '_.'):
                i += 1
        elif c in lw:
            j = i
            while j < n and txt[j] in lw:
                j += 1
            yield txt[i:j][:511]
            i = j
        else:
            i += 1


def _check_syms(elems):
    """`.check` の候補の並び（空文字は CHECK_OMIT として 1 度だけ）。"""
    syms = []
    for nm in elems:
        if nm != '':
            syms.append(nm)
        elif CHECK_OMIT not in syms:
            syms.append(CHECK_OMIT)
    return syms


class DirectiveProcessor:
    """パターンファイル側のディレクティブを処理する。

    各ハンドラは担当でなければ False、処理したら True を返す。ディレクティブは
    書かれた位置から効く（後のものが前を上書きする）ので順序に依存する。
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
        """`.clearsym` — 名前を 1 つ、引数なしなら全部のシンボルを消す。"""
        if len(i) == 0 or i[0] != '.clearsym':
            return False
        st = self.state
        if len(i) >= 3 and i[2] != '':
            key = StringUtils.upper(i[2])
            for d in (st.symbols, st.strsymbols, st.arrsymbols):
                d.pop(key, None)
        else:
            st.symbols, st.strsymbols, st.arrsymbols = {}, {}, {}
        st.arrgen += 1
        return True

    # 定数の値欄の評価結果などを覚える（2 度目からは評価も診断も走らない）。
    _const_setsym_cache = {}
    _check_cache = {}
    _elftype_cache = {}
    _elfdecl_cache = {}

    def set_symbol(self, i):
        """`.setsym` — シンボルを定義する。種類は値欄の見た目で決まる。

        `"..."` 文字列、`[...]` 配列、名前のカンマ並び 集合、集合式 計算された集合、
        裸の名前 コピー（か名前を持つ文字列）、それ以外は数値式。
        """
        if len(i) == 0 or i[0] != '.setsym':
            return False
        st = self.state
        cache = DirectiveProcessor._const_setsym_cache
        if i[1]:
            value_field = i[2]
            key = StringUtils.upper(i[1])
            if _PLAIN_NUM_RE.match(value_field):
                v = cache.get(value_field, _SETSYM_MISS)
                if v is _SETSYM_MISS:
                    v, _idx = self.expr_eval.expression_pat(value_field, 0)
                    if len(cache) >= 65536:
                        cache.clear()
                    cache[value_field] = v
                st.symbols[key] = v
                return True
        elif i[2]:
            key = StringUtils.upper(i[2])
            value_field = ''
        else:
            st.diag(" error - .setsym directive requires at least a symbol name", set_error=True)
            return False

        vf = value_field.lstrip(' \t')
        if vf.startswith('"'):
            st.strsymbols[key] = ObjectGenerator._txt_template_inner(vf)
            return True
        if vf.startswith('['):
            st.arrsymbols[key] = arr_items_from_text(self.expr_eval, vf)
            st.arrgen += 1
            return True
        if symbol_copy_from_name(st, key, vf) or symbol_set_from_text(st, key, value_field):
            return True
        v = 0
        if value_field:
            v = cache.get(value_field, _SETSYM_MISS)
            if v is _SETSYM_MISS:
                v, _idx = self.expr_eval.expression_pat(value_field, 0)
                if _CONST_SETSYM_RE.match(value_field):
                    if len(cache) >= 65536:
                        cache.clear()
                    cache[value_field] = v
        st.symbols[key] = v
        return True

    def bits(self, i):
        """`.bits` — 出力ワードのビット数（1..64）とバイト順を決める。"""
        if len(i) == 0 or i[0] != '.bits':
            return False
        st = self.state
        wf = ''
        for f in i[1:3]:
            if f == '':
                continue
            fl = f.translate(_ALOWER)
            if fl in ('big', 'little'):
                st.endian = fl
            elif wf == '':
                wf = f
            else:
                st.diag(f" error - .bits: multiple word-width fields given "
                        f"({wf!r} and {f!r}).", set_error=True)
        if wf:
            st.error_undefined_label = False
            st.expr_missing = False
            v, idx = self.expr_eval.expression_pat(wf, 0)
            if (_pat_missing(st, '.bits', wf)
                    or _pat_trailing(st, '.bits', 'the word width', wf, idx)):
                st.error_undefined_label = False
                return True
            ok = not st.error_undefined_label and not _is_undef_derived(v)
            if ok:
                try:
                    nb = int(v)
                except (OverflowError, ValueError, TypeError):
                    ok = False
                else:
                    ok = (nb == v) and 1 <= nb <= 64
            if ok:
                st.bts = nb
            else:
                st.diag(f" error - .bits: word width must be an integer in "
                        f"1..64, got {wf!r}.", set_error=True)
            st.error_undefined_label = False
        return True

    def paddingp(self, i):
        """`.padding` — 隙間を埋める値。"""
        if len(i) == 0 or i[0] != '.padding':
            return False
        f = i[2] if len(i) >= 3 and i[2] != '' else i[1] if len(i) >= 2 and i[1] != '' else ''
        v = self.expr_eval.expression_pat(f, 0)[0] if f else 0
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
        """`.vliw` — バンドル幅・命令幅・テンプレート幅・NOP。caxx.c の dir_vliwp() と同じ順と範囲で検査する。"""
        if len(i) == 0 or i[0] != ".vliw":
            return False
        st = self.state
        if len(i) < 5:
            st.diag(f" error - .vliw directive requires 4 parameters (vliwbits, vliwinstbits, vliwtemplatebits, nop_value), got {len(i) - 1}", set_error=True)
            return False
        v1, v2, v3, v4 = (self.expr_eval.expression_pat(i[k], 0)[0] for k in range(1, 5))
        try:
            b, n, t = int(v1), int(v2), int(v3)
        except (OverflowError, ValueError):
            st.diag(" error - .vliw: non-finite parameter value.", set_error=True)
            return True
        try:
            v4 = int(v4) & 0xFFFFFFFFFFFFFFFF
        except (OverflowError, ValueError):
            st.diag(" error - .vliw: non-finite nop value.", set_error=True)
            return True
        if not (-8192 <= b <= 8192):
            st.diag(" error - .vliw: vliwbits is out of range (must be -8192..8192).", set_error=True)
            return True
        if not (0 <= n <= 8192):
            # 表示は下位 64 ビットを符号付きで読んだもの。
            n64 = ((n & 0xFFFFFFFFFFFFFFFF) ^ (1 << 63)) - (1 << 63)
            st.diag(f" error - .vliw: vliwinstbits {n64} is out of range "
                    f"(must be 0-8192).", set_error=True)
            return True
        if not (-8192 <= t <= 8192):
            st.diag(" error - .vliw: vliwtemplatebits is out of range (must be -8192..8192).", set_error=True)
            return True
        vl = st.vliw
        vl.bits, vl.instbits, vl.templatebits, vl.flag = b, n, t, True
        vl.nop = [(v4 >> (8 * k)) & 0xff for k in range((n + 7) // 8)]
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
            idxs.append(v)
            if idx < len(s) and s[idx] == ',':
                idx += 1
            else:
                break
        self.add_avoiding_dup(self.state.vliw.slotset, [idxs, i[2]])
        return True

    def _cond_tests_relocated_var(self, cond_src):
        """そのエラー条件が、リンカが埋める命令欄の変数を見ているか（-o では報告しない）。"""
        st = self.state
        if not st.elf.objfile or not st.reloc_constraints:
            return False
        return any(insn_reloc_field_mask(rtype, st) is not None and _word_occurs(var, cond_src)
                   for var, rtype in st.reloc_constraints.items())

    def _captext_has_linked_label(self, txt):
        """綴りが、値をリンカが決めるラベル（外部か別セクション）を含むか。

        caxx.c の captext_has_linked_label() と同じ規則である。
        """
        for w in _captext_words(txt, self.state.lwordchars):
            le = self.state.labels.get(w)
            if le is None or (len(le) > 2 and le[2] and not (len(le) > 4 and le[4] is not None)):
                continue
            if (len(le) > 3 and le[3]) or (le[1] and le[1] != self.state.current_section):
                return True
        return False

    def _cond_tests_linked_label(self, cond_src):
        """そのエラー条件が、リンカが決めるラベルを拾った変数を見ているか（-o だけ）。

        範囲の検査はリンカに任せる（GNU as と同じ）。caxx.c の cond_tests_linked_label() と同じ。
        """
        if not self.state.elf.objfile:
            return False
        return any(txt and self._captext_has_linked_label(txt) and _word_occurs(var, cond_src)
                   for var, txt in self.state.vars_text.items())

    def error(self, s):
        """error_patterns 欄を評価する。返り値は (発生したか, エラーコード)。caxx.c の dir_error() と同じ。

        `条件;コード` の組をカンマで並べたものを順に見る。組はまず整数モードで読み、
        浮動小数点の変数を読んだ・読み切れない・`/` か `**` を含むときだけ浮動小数点
        モードで読み直す。未定義に触れた条件と、リンカが埋める変数・ラベルを見る条件は
        判定しない。
        """
        if s.replace(' ', '') == "":
            return False, 0
        st = self.state
        ev = self.expr_eval
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
            prev_typ = st.exp_typ
            undef_prior = st.error_undefined_label
            try:
                st.exp_typ = 'i'
                st._expr_read_float_var = False
                st.error_undefined_label = False
                st.expr_missing = False
                u, idxn = ev.expression_pat(s, idx_before)
                cond_undef = st.error_undefined_label or _undef(u)
                int_ok = False
                if idxn < len(s) and s[idxn] == ';':
                    t, idx = ev.expression_pat(s, idxn + 1)
                    int_ok = ((idx >= len(s) or s[idx] in (',', chr(0)))
                              and not st._expr_read_float_var
                              and '/' not in s[idx_before:idx] and '**' not in s[idx_before:idx])
                if not int_ok:
                    st.exp_typ = 'f'
                    st.error_undefined_label = False
                    st.expr_missing = False
                    u, idxn = ev.expression_pat(s, idx_before)
                    cond_undef = st.error_undefined_label or _undef(u)
                    idx = idxn + 1 if idxn < len(s) and s[idxn] == ';' else idxn
                    t, idx = ev.expression_pat(s, idx)
            finally:
                st.exp_typ = prev_typ
                st.error_undefined_label = undef_prior or st.error_undefined_label

            if idx <= idx_before:
                break
            # 因子の欠けた組（`a>;3`）と、`;` / `,` の前に余計な文字が残る組は読まずにエラー。
            if _pat_missing(st, 'error_patterns', s[idx_before:idx]):
                break
            if (_pat_trailing(st, 'error_patterns', 'the condition', s, idxn, ';')
                    or _pat_trailing(st, 'error_patterns', 'the error code', s, idx, ',')):
                break
            if (st.should_report_errors() and u and not cond_undef
                    and not self._cond_tests_relocated_var(s[idx_before:idx])
                    and not self._cond_tests_linked_label(s[idx_before:idx])):
                # caxx.c と同じく倍精度を経て 64 ビットの範囲で読む（範囲外・非有限・未定義は 0）。
                tf = 0.0 if _undef(t) else _float_of(t)
                t_int = int(tf) if (math.isfinite(tf) and -2.0 ** 63 < tf < 2.0 ** 63) else 0
                print(f"Line {st.ln} Error code {t_int} ", end="", file=sys.stderr)
                if 0 <= t_int < len(st.errors):
                    print(f"{st.errors[t_int]}", end='', file=sys.stderr)
                print(": ", file=sys.stderr)
                error_code = t_int
                triggered = True
                st.had_error = True
        return triggered, error_code

    def _dir_var(self, field):
        """ディレクティブの変数名欄を正規化する（変数名でなければ None）。"""
        v = (field or '').strip()
        if not v or not v.isascii():
            return None
        v = v.lower()
        if not _VARNAME_RE.fullmatch(v):
            return None
        self.state.varnames.add(v)
        return v

    def elem_list_expand(self, text):
        """要素リストを展開する（配列シンボルの名前は中身に開き、`""` は CHECK_OMIT の空文字）。"""
        out = []
        for tok in (text or '').split(','):
            tok = StringUtils.upper(tok.strip())
            if tok in ('', '""', "''"):
                out.append('')
                continue
            arr = self.state.arrsymbols.get(tok)
            if arr is None:
                out.append(tok)
            else:
                out.extend(StringUtils.upper(v) if isinstance(v, str)
                           else ObjectGenerator._txt_radix(v, 10) for v in arr)
        return out

    def check_processing(self, i):
        """`.check` — その変数が捕らえてよいシンボルを制限する。"""
        if len(i) == 0 or i[0] != '.check':
            return False
        st = self.state
        if i[1].strip():
            var_field, syms_field = i[1], i[2]
        elif i[2].strip():
            var_field, syms_field = i[2], ''
        else:
            st.diag(" error - .check: variable name is not specified.", set_error=True)
            return True
        var = self._dir_var(var_field)
        if var is None:
            st.diag(f" error - .check: variable should be a lower case name ('{var_field}').", set_error=True)
            return True
        cache = DirectiveProcessor._check_cache
        ck = (var, syms_field)
        ce = cache.get(ck)
        if ce is not None and ce[0] == st.arrgen:
            st.check_constraints[var] = ce[1]
            return True
        syms = _check_syms(self.elem_list_expand(syms_field))
        if len(cache) >= 65536:
            cache.clear()
        cache[ck] = (st.arrgen, syms)
        st.check_constraints[var] = syms
        return True

    def elftype_processing(self, i):
        """`.elftype` — リロケーション型の名前と番号（と幅・PC 相対か）を決める。"""
        if len(i) == 0 or i[0] != '.elftype':
            return False
        st = self.state
        name_field = i[1] if i[1] else i[2]
        value_field = i[2] if i[1] else ''
        nm = name_field.replace(' ', '').replace('\t', '').translate(_ALOWER)
        if not nm:
            st.diag(" error - .elftype: type name is not specified.", set_error=True)
            return True
        if not value_field:
            st.diag(f" error - .elftype: type number is not specified ('{nm}').", set_error=True)
            return True
        cache = DirectiveProcessor._elftype_cache
        v = cache.get(value_field, _SETSYM_MISS)
        if v is _SETSYM_MISS:
            st.error_undefined_label = False
            v, _idx = self.expr_eval.expression_pat(value_field, 0)
            try:
                v = int(v)
            except (OverflowError, ValueError):
                v = None
            if st.error_undefined_label or v is None or v < 1 or v > 2147483647:
                st.diag(" error - .elftype: type number must be an integer in "
                        f"1..2147483647, got '{value_field}'.", set_error=True)
                v = None
            st.error_undefined_label = False
            if len(cache) >= 65536:
                cache.clear()
            cache[value_field] = v
        if v is None:
            return True
        e = st.elf
        w = pc = None
        if len(i) > 3 and i[3] and i[3].strip():
            w = self._elf_decl_num('.elftype', i[3], 1, 8)
            if w is None:
                return True
        if len(i) > 4 and i[4] and i[4].strip():
            pc = self._elf_decl_num('.elftype', i[4], 0, 1)
            if pc is None:
                return True
        if (st.elftypes.get(nm) != v or e.type_width.get(nm) != w
                or (nm in e.type_pcrel) != bool(pc)):
            st.elftypes[nm] = v
            if w is None:
                e.type_width.pop(nm, None)
            else:
                e.type_width[nm] = w
            if pc:
                e.type_pcrel.add(nm)
            else:
                e.type_pcrel.discard(nm)
            e.decl_gen += 1
        return True

    @staticmethod
    def _elf_decl_fields(i):
        """ELF 宣言の欄を (値, 名前) に整える（欄の詰め方の違いを吸収する）。"""
        f1 = i[1] if len(i) > 1 and i[1] and i[1].strip() else ''
        f2 = i[2] if len(i) > 2 and i[2] else ''
        return (f1, f2) if f1 else (f2, '')

    def _elf_decl_num(self, dname, field, lo, hi):
        """ELF 宣言の数値欄を lo..hi の整数として読む（範囲外は None）。結果は綴りごとに覚える。"""
        st = self.state
        text = field.strip() if field else ''
        if not text:
            st.diag(f" error - {dname}: a number is required.", set_error=True)
            return None
        cache = DirectiveProcessor._elfdecl_cache
        key = (text, lo, hi)
        v = cache.get(key, _SETSYM_MISS)
        if v is _SETSYM_MISS:
            st.error_undefined_label = False
            v, _idx = self.expr_eval.expression_pat(text, 0)
            try:
                v = int(v)
            except (OverflowError, ValueError):
                v = None
            if st.error_undefined_label or v is None or v < lo or v > hi:
                v = None
            st.error_undefined_label = False
            if len(cache) >= 65536:
                cache.clear()
            cache[key] = v
        if v is None:
            st.diag(f" error - {dname}: value must be an integer in "
                    f"{lo}..{hi}, got '{text}'.", set_error=True)
        return v

    def _elf_decl_set(self, attr, value):
        """ELF 宣言を書き込み、変わったときだけ世代番号（表のキャッシュ）を進める。"""
        e = self.state.elf
        if getattr(e, attr) != value:
            setattr(e, attr, value)
            e.decl_gen += 1

    def _elf_decl_type_text(self, i, dname, attr):
        """型の綴りを 1 つ取る宣言（`.elfextern` / `.elfdwarf`）。"""
        if len(i) == 0 or i[0] != dname:
            return False
        t = self._elf_decl_fields(i)[0].strip()
        if not t:
            self.state.diag(f" error - {dname}: relocation type is not specified.", set_error=True)
        else:
            self._elf_decl_set(attr, t)
        return True

    def elfmachine_processing(self, i):
        """`.elfmachine` — e_machine の既定値（`-m` より弱い）。"""
        if len(i) == 0 or i[0] != '.elfmachine':
            return False
        num, nm = self._elf_decl_fields(i)
        v = self._elf_decl_num('.elfmachine', num, 0, 65535)
        if v is None:
            return True
        self._elf_decl_set('decl_machine', v)
        self._elf_decl_set('decl_name', nm.strip())
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
        if text in ('32', '64'):
            self._elf_decl_set('decl_class', 1 if text == '32' else 2)
        else:
            self.state.diag(f" error - .elfclass: value must be 32 or 64, got '{text}'.",
                            set_error=True)
        return True

    def elfrela_processing(self, i):
        """`.elfrela` — .rela（加数を欄に持つ）か .rel か。"""
        if len(i) == 0 or i[0] != '.elfrela':
            return False
        text = self._elf_decl_fields(i)[0].strip().translate(_ALOWER)
        if text in ('1', 'rela', '0', 'rel'):
            self._elf_decl_set('decl_rela', 1 if text in ('1', 'rela') else 0)
        else:
            self.state.diag(f" error - .elfrela: value must be 1/rela or 0/rel, "
                            f"got '{text}'.", set_error=True)
        return True

    def elfwidth_processing(self, i):
        """`.elfwidth` — 欄の幅（2 のべき乗でなくてよい）から型を推測する対応。"""
        if len(i) == 0 or i[0] != '.elfwidth':
            return False
        wf, tf = self._elf_decl_fields(i)
        w = self._elf_decl_num('.elfwidth', wf, 1, 8)
        if w is None:
            return True
        t = tf.strip()
        if not t:
            self.state.diag(" error - .elfwidth: relocation type is not specified.", set_error=True)
            return True
        e = self.state.elf
        if e.decl_width.get(w) != t:
            e.decl_width[w] = t
            e.decl_gen += 1
        return True

    def elfextern_processing(self, i):
        """`.elfextern` — 外部シンボル参照に使う既定の型。"""
        return self._elf_decl_type_text(i, '.elfextern', 'decl_extern')

    def elfdwarf_processing(self, i):
        """`.elfdwarf` — DWARF セクション内の絶対参照に使う型。"""
        return self._elf_decl_type_text(i, '.elfdwarf', 'decl_dwarf')

    _ELF_HDR_FIELDS = {
        'type':       (0, 0xFFFF),
        'flags':      (0, 0xFFFFFFFF),
        'version':    (0, 0xFFFFFFFF),
        'entry':      (0, 0x7FFFFFFFFFFFFFFF),
        'osabi':      (0, 0xFF),
        'abiversion': (0, 0xFF),
    }

    def _elf_decl_put(self, d, key, val):
        """宣言の表 d に書き、変わったときだけ世代番号を進める。"""
        if d.get(key) != val:
            d[key] = val
            self.state.elf.decl_gen += 1

    @staticmethod
    def _fld(i, k):
        """欄 k を前後の空白を落として（無ければ ''）。"""
        return (i[k] if len(i) > k else '').strip()

    def _opt_num(self, dname, i, k, lo, hi, default=0):
        """省略できる数値欄 k。返り値は (読めたか, 値)。"""
        if len(i) > k and i[k] and i[k].strip():
            v = self._elf_decl_num(dname, i[k], lo, hi)
            return v is not None, v
        return True, default

    def _elf_decl_flag(self, i, dname, attr):
        """0 か 1 の宣言（`.elfpcguess` / `.elfrelax` / `.elfbuiltin`）。"""
        if len(i) == 0 or i[0] != dname:
            return False
        text = self._elf_decl_fields(i)[0].strip()
        if text in ('0', '1'):
            self._elf_decl_set(attr, int(text))
        else:
            self.state.diag(f" error - {dname}: value must be 0 or 1, got '{text}'.", set_error=True)
        return True

    def _elf_decl_typelist(self, i, dname, lst):
        """型の綴りを宣言順に並べる宣言（`.elfanchor` / `.elfresolve`）。"""
        if len(i) == 0 or i[0] != dname:
            return False
        t = self._elf_decl_fields(i)[0].lstrip(' \t').rstrip(' \t\r\n')
        if not t:
            self.state.diag(f" error - {dname}: relocation type is not specified.", set_error=True)
        elif t not in lst:
            lst.append(t)
            self.state.elf.decl_gen += 1
        return True

    def elfheader_processing(self, i):
        """`.elfheader` — ELF ヘッダの欄（e_flags など）を直接書く。"""
        if len(i) == 0 or i[0] != '.elfheader':
            return False
        ff, vf = self._elf_decl_fields(i)
        fld = ff.replace(' ', '').replace('\t', '').translate(_ALOWER)
        rng = DirectiveProcessor._ELF_HDR_FIELDS.get(fld)
        if rng is None:
            self.state.diag(f" error - .elfheader: unknown field '{fld}' (type, flags, "
                            f"version, entry, osabi, abiversion).", set_error=True)
            return True
        v = self._elf_decl_num('.elfheader', vf, rng[0], rng[1])
        if v is not None:
            self._elf_decl_put(self.state.elf.decl_hdr, fld, v)
        return True

    def elffield_processing(self, i):
        """`.elffield::<型>::<マスク>[::<オフセット>[::<シフト>[::<補正>]]]` — 命令語の中の欄。

        シフトは REL で加数を書き戻す前に右へずらすビット数、補正は加数に足す定数。
        caxx.c の dir_elffield() と同じ規則である。
        """
        if len(i) == 0 or i[0] != '.elffield':
            return False
        tf, mf = self._elf_decl_fields(i)
        t = tf.strip()
        if not t:
            self.state.diag(" error - .elffield: relocation type is not specified.", set_error=True)
            return True
        m = self._elf_decl_num('.elffield', mf, 1, 0xFFFFFFFFFFFFFFFF)
        if m is None:
            return True
        ok, off = self._opt_num('.elffield', i, 3, 0, 255)
        if not ok:
            return True
        ok, sh = self._opt_num('.elffield', i, 4, 0, 63)
        if not ok:
            return True
        ok, bias = self._opt_num('.elffield', i, 5, -0x7FFFFFFF, 0x7FFFFFFF)
        if ok:
            self._elf_decl_put(self.state.elf.decl_field, t, (m, off, sh, bias))
        return True

    def elfpcguess_processing(self, i):
        """`.elfpcguess` — 幅から推定した絶対型を、値がラベルと違えば PC 相対型にするか。caxx.c の dir_elfpcguess()。"""
        return self._elf_decl_flag(i, '.elfpcguess', 'decl_pcguess')

    def elfanchor_processing(self, i):
        """`.elfanchor` — `.reloc` の追加の再配置のうち行のアンカーを指す型。caxx.c の dir_elfanchor()。"""
        return self._elf_decl_typelist(i, '.elfanchor', self.state.elf.decl_anchor)

    def elfresolve_processing(self, i):
        """`.elfresolve` — 同じセクションの局所ラベルへのこの型の PC 相対の欄は axx が解く。caxx.c の dir_elfresolve()。"""
        return self._elf_decl_typelist(i, '.elfresolve', self.state.elf.decl_resolve)

    def elfrelax_processing(self, i):
        """`.elfrelax` — リンカがコードを縮める機種か（無ければ `.elfdiff` の有無）。caxx.c の dir_elfrelax()。"""
        return self._elf_decl_flag(i, '.elfrelax', 'decl_relax')

    def elfbuiltin_processing(self, i):
        """`.elfbuiltin` — 組み込みのマシン表を土台にするか（0 なら宣言だけ）。caxx.c の dir_elfbuiltin()。"""
        return self._elf_decl_flag(i, '.elfbuiltin', 'decl_builtin')

    def elfextra_processing(self, i):
        """`.elfextra::<型>::<添える型>[::<シンボル>]` — 同じ位置へもう 1 つ添える。caxx.c の dir_elfextra()。

        シンボルが 0（既定）ならシンボル 0・加数 0（R_RISCV_RELAX など）、1 なら元と同じシンボル。
        """
        if len(i) == 0 or i[0] != '.elfextra':
            return False
        t, c = self._fld(i, 1), self._fld(i, 2)
        if not t or not c:
            self.state.diag(" error - .elfextra: two relocation types are required.", set_error=True)
            return True
        ok, sym = self._opt_num('.elfextra', i, 3, 0, 1)
        if not ok:
            return True
        e = self.state.elf
        comps = e.decl_extra.get(t)
        if comps is None or comps.get(c) != sym:
            e.decl_extra[t] = {**(comps or {}), c: sym}
            e.decl_gen += 1
        return True

    def elfdiff_processing(self, i):
        """`.elfdiff::<幅か型>::<足す型>::<引く型>` — ラベル差を足す型と引く型の組で出す。caxx.c の dir_elfdiff()。

        第 1 欄が幅ならその幅のデータの欄、型名なら `.reloc` でその型を付けた欄。
        """
        if len(i) == 0 or i[0] != '.elfdiff':
            return False
        f1, a, b = self._fld(i, 1), self._fld(i, 2), self._fld(i, 3)
        e = self.state.elf
        typed = bool(f1) and not _PLAIN_NUM_RE.match(f1)
        if not typed:
            f1 = self._elf_decl_num('.elfdiff', f1, 1, 8)
            if f1 is None:
                return True
        if not a or not b:
            self.state.diag(" error - .elfdiff: an add type and a subtract type are required.",
                            set_error=True)
            return True
        self._elf_decl_put(e.decl_diff_t if typed else e.decl_diff, f1, (a, b))
        return True

    def elfunaligned_processing(self, i):
        """`.elfunaligned::<型>::<代わりの型>` — 幅の倍数でない位置のデータの欄の型。caxx.c の dir_elfunaligned()。"""
        if len(i) == 0 or i[0] != '.elfunaligned':
            return False
        t, u = self._fld(i, 1), self._fld(i, 2)
        if not t or not u:
            self.state.diag(" error - .elfunaligned: a relocation type and its unaligned type "
                            "are required.", set_error=True)
        else:
            self._elf_decl_put(self.state.elf.decl_unaligned, t, u)
        return True

    def elfencode_processing(self, i):
        """`.elfencode::<型>::<関数>` — REL で加数を欄へ書き戻す関数（欄の値, 加数）→ 欄。caxx.c の dir_elfencode()。"""
        if len(i) == 0 or i[0] != '.elfencode':
            return False
        t, f = self._fld(i, 1), self._fld(i, 2)
        if not t or not f:
            self.state.diag(" error - .elfencode: a relocation type and a function name are required.",
                            set_error=True)
        else:
            self._elf_decl_put(self.state.elf.decl_encode, t, f)
        return True

    def elfrinfo_processing(self, i):
        """`.elfrinfo` — r_info を組む関数（シンボル番号, 型番号）→ r_info。caxx.c の dir_elfrinfo()。"""
        if len(i) == 0 or i[0] != '.elfrinfo':
            return False
        f = self._elf_decl_fields(i)[0].strip()
        if not f:
            self.state.diag(" error - .elfrinfo: a function name is required.", set_error=True)
        else:
            self._elf_decl_set('decl_rinfo', f)
        return True

    def elfunit_processing(self, i):
        """`.elfunit` — 加数とシンボル値の単位（byte / word）。caxx.c の dir_elfunit()。"""
        if len(i) == 0 or i[0] != '.elfunit':
            return False
        text = self._elf_decl_fields(i)[0].strip().translate(_ALOWER)
        if text in ('byte', 'word'):
            self._elf_decl_set('decl_unit', text)
        else:
            self.state.diag(f" error - .elfunit: value must be byte or word, got '{text}'.",
                            set_error=True)
        return True

    def elflink_processing(self, i):
        """`.elflink::<セクション>::<sh_link>[::<sh_info>]`（値は名前か数）。caxx.c の dir_elflink()。"""
        if len(i) == 0 or i[0] != '.elflink':
            return False
        nm = self._fld(i, 1)
        if not nm:
            self.state.diag(" error - .elflink: section name is not specified.", set_error=True)
        else:
            self._elf_decl_put(self.state.elf.decl_link, nm.translate(_ALOWER),
                               (self._fld(i, 2), self._fld(i, 3)))
        return True

    def elfcfi_processing(self, i):
        """`.elfcfi::<戻り番地の列>::<コード整列>::<データ整列>[::<詰めの整列>]` — CIE の欄。caxx.c の dir_elfcfi()。"""
        if len(i) == 0 or i[0] != '.elfcfi':
            return False
        fld = lambda k: i[k] if len(i) > k else ''
        ra = self._elf_decl_num('.elfcfi', fld(1), 0, 0xFFFF)
        if ra is None:
            return True
        ca = self._elf_decl_num('.elfcfi', fld(2), 1, 0xFFFF)
        if ca is None:
            return True
        da = self._elf_decl_num('.elfcfi', fld(3), -0xFFFF, 0xFFFF)
        if da is None:
            return True
        if da == 0:
            self.state.diag(" error - .elfcfi: the data alignment factor must not be 0.", set_error=True)
            return True
        ok, pad = self._opt_num('.elfcfi', i, 4, 1, 64)
        if not ok:
            return True
        if pad & (pad - 1):
            self.state.diag(f" error - .elfcfi: the padding alignment must be a power "
                            f"of two, got '{pad}'.", set_error=True)
            return True
        self._elf_decl_set('decl_cfi', (ra, ca, da, pad))
        return True

    def elfcfiinit_processing(self, i):
        """`.elfcfiinit` — CIE の初期命令を 1 つ足す（`def_cfa 7, 8` など）。caxx.c の dir_elfcfiinit()。"""
        if len(i) == 0 or i[0] != '.elfcfiinit':
            return False
        t = ' '.join(self._elf_decl_fields(i)[0].split())
        if not t:
            self.state.diag(" error - .elfcfiinit: an instruction is required.", set_error=True)
        else:
            self._elf_decl_put(self.state.elf.decl_cfiinit, t, True)
        return True

    def elfcfireg_processing(self, i):
        """`.elfcfireg` — CFI の指令に書くレジスタ名と DWARF の番号。caxx.c の dir_elfcfireg()。"""
        if len(i) == 0 or i[0] != '.elfcfireg':
            return False
        nm = self._fld(i, 1).translate(_ALOWER)
        if not nm:
            self.state.diag(" error - .elfcfireg: a register name is required.", set_error=True)
            return True
        v = self._elf_decl_num('.elfcfireg', i[2] if len(i) > 2 else '', 0, 0xFFFF)
        if v is not None:
            self._elf_decl_put(self.state.elf.decl_cfireg, nm, v)
        return True

    def elfgroup_processing(self, i):
        """`.elfgroup::<グループ名>::<署名>::<フラグ>::<メンバー>[,...]` — SHT_GROUP。caxx.c の dir_elfgroup()。"""
        if len(i) == 0 or i[0] != '.elfgroup':
            return False
        gn, sig = self._fld(i, 1), self._fld(i, 2)
        if not gn or not sig:
            self.state.diag(" error - .elfgroup: a group name and a signature symbol are required.",
                            set_error=True)
            return True
        fl = self._elf_decl_num('.elfgroup', i[3] if len(i) > 3 else '', 0, 0xFFFFFFFF)
        if fl is None:
            return True
        mem = tuple(m.strip() for m in (i[4] if len(i) > 4 else '').split(',') if m.strip())
        if not mem:
            self.state.diag(" error - .elfgroup: no member section is given.", set_error=True)
            return True
        self._elf_decl_put(self.state.elf.decl_group, (gn.translate(_ALOWER), sig), (gn, sig, fl, mem))
        return True

    def elfsection_processing(self, i):
        """`.elfsection` — 名前から推測できないセクションの sh_flags / sh_type / 整列 / 要素サイズ。"""
        if len(i) == 0 or i[0] != '.elfsection':
            return False
        nf, ff = self._elf_decl_fields(i)
        nm = nf.strip()
        if not nm:
            self.state.diag(" error - .elfsection: section name is not specified.", set_error=True)
            return True
        fl = self._elf_decl_num('.elfsection', ff, 0, 0xFFFFFFFF)
        if fl is None:
            return True
        ok, ty = self._opt_num('.elfsection', i, 3, 0, 0xFFFFFFFF, None)
        if not ok:
            return True
        ok, al = self._opt_num('.elfsection', i, 4, 0, 0x40000000, None)
        if not ok:
            return True
        if al is not None and al & (al - 1):
            self.state.diag(" error - .elfsection: alignment must be 0 or a "
                            f"power of two, got '{al}'.", set_error=True)
            return True
        ok, es = self._opt_num('.elfsection', i, 5, 0, 0xFFFFFFFF, None)
        if ok:
            self._elf_decl_put(self.state.elf.decl_sec, nm.translate(_ALOWER), (fl, ty, al, es))
        return True

    def reloc_processing(self, i):
        """`.reloc::変数::型[::マスク[::型@オフセット,...]]` — その変数が捕らえたラベル参照の型。

        第 4 欄は `.elffield` の型の欄を言い直すマスク（PowerPC64 の DS / DQ 形式）。
        第 5 欄は追加の再配置（8 つまで。オフセットは参照の先頭からのバイト数、同じ
        シンボルと加数。`.elfanchor` の型は行のアンカーを指す）。caxx.c の dir_reloc() と同じ。
        """
        if len(i) == 0 or i[0] != '.reloc':
            return False
        st = self.state
        if not i[1].strip():
            st.diag(" error - .reloc: variable name is not specified.", set_error=True)
            return True
        var_field, type_field = i[1], (i[2] if len(i) > 2 else '')
        var = self._dir_var(var_field)
        if var is None:
            st.diag(f" error - .reloc: variable should be a lower case name ('{var_field}').", set_error=True)
            return True
        tname = type_field.strip()
        if not tname:
            st.diag(" error - .reloc: relocation type is not specified.", set_error=True)
            return True
        if not st.elf.objfile:
            return True
        mach = elf_machine_table(st)
        rtype = _reloc_named(st, mach, tname)
        if rtype is None:
            key = (tname.translate(_ALOWER), st.elf.machine)
            if key not in st._reloc_badname_seen:
                st._reloc_badname_seen.add(key)
                st.diag(f" error - .reloc: unknown relocation type '{tname}' for {mach['name']}.",
                        set_error=True)
            return True
        fmask = 0
        if len(i) > 3 and i[3].strip():
            if insn_reloc_field_decl(st, rtype) is None:
                st.diag(f" error - .reloc: a field mask needs a type declared with "
                        f".elffield ('{type_field}').", set_error=True)
                return True
            fmask = self._elf_decl_num('.reloc', i[3], 1, 0xFFFFFFFFFFFFFFFF)
            if fmask is None:
                return True
        xs = []
        pf = i[4] if len(i) > 4 else ''
        if pf.strip():
            for it in pf.split(','):
                if not it:
                    continue
                if '@' not in it:
                    st.diag(" error - .reloc: an extra relocation is written "
                            f"<type>@<offset> ('{it.lstrip(' \t').rstrip(' \t\r\n')}').",
                            set_error=True)
                    return True
                tn, po = it.rsplit('@', 1)
                pn = tn.lstrip(' \t').rstrip(' \t\r\n').translate(_ALOWER)
                prt = _reloc_named(st, mach, pn)
                if prt is None or prt <= 0:
                    st.diag(f" error - .reloc: unknown relocation type '{pn}' for "
                            f"{mach['name']}.", set_error=True)
                    return True
                if insn_reloc_field_decl(st, prt) is None:
                    st.diag(f" error - .reloc: an extra relocation needs a type declared "
                            f"with .elffield ('{pn}').", set_error=True)
                    return True
                poff = self._elf_decl_num('.reloc', po, 0, 255)
                if poff is None:
                    return True
                if len(xs) >= 8:
                    st.diag(" error - .reloc: at most 8 extra relocations.", set_error=True)
                    return True
                xs.append((prt, poff))
        st.reloc_constraints[var] = rtype
        for d, v in ((st.reloc_masks, fmask), (st.reloc_pairs, tuple(xs))):
            if v:
                d[var] = v
            else:
                d.pop(var, None)
        return True

    def _clear_var_dir(self, i, dname, tables, alt_field):
        """`.clrreloc` / `.clrcheck` — 変数 1 つ（引数なしで全部）の宣言を外す。"""
        if len(i) == 0 or i[0] != dname:
            return False
        var_field = i[2].strip() if len(i) >= 3 and i[2] else ''
        if alt_field and not var_field and len(i) >= 2 and i[1]:
            var_field = i[1].strip()
        if not var_field:
            for d in tables:
                d.clear()
            return True
        var = self._dir_var(var_field)
        if var is None:
            self.state.diag(f" error - {dname}: variable should be a lower case name ('{var_field}').", set_error=True)
        else:
            for d in tables:
                d.pop(var, None)
        return True

    def clrreloc_processing(self, i):
        """`.clrreloc` — `.reloc` の宣言を外す（引数なしで全部）。"""
        st = self.state
        return self._clear_var_dir(i, '.clrreloc',
                                   (st.reloc_constraints, st.reloc_masks, st.reloc_pairs), True)

    def clrcheck_processing(self, i):
        """`.clrcheck` — `.check` の制限を外す（引数なしで全部）。"""
        return self._clear_var_dir(i, '.clrcheck', (self.state.check_constraints,), False)

    def map_apply(self, i, into=None, set_check=True):
        """`.map` の本体。名前の並びに値を与え、同時に `.check` も設定する。

        値欄が 1 つの式なら、その中の変数はリスト中の位置（0 起点）。カンマ区切りなら
        名前と 1 対 1（長さが違えばエラー）。`""` の位置は番号だけ進め、`.check` では省略可。
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
            if nm:
                src = vals[n] if len(vals) > 1 else expr_str
                target[nm] = self.expr_eval.expression_pat(
                    PatternFileReader._map_subst_index(src, var, n), 0)[0]
        if set_check:
            self.state.check_constraints[var] = _check_syms(elems)

    def map_processing(self, i):
        """`.map` — シンボル表とそのチェックを 1 行で書く。

        `.unordered` では名前と値をその変数だけの表に入れる（Z80 の C レジスタと C キャリー）。
        """
        if len(i) == 0 or i[0] != '.map':
            return False
        if self.state.unordered:
            var = self._dir_var(i[1].strip() if len(i) >= 2 else '')
            if var is not None:
                tbl = {}
                self.map_apply(i, into=tbl)
                self.state.var_tables[var] = tbl
            return True
        self.map_apply(i)
        return True

    def unordered_processing(self, i):
        """`.unordered` — 宣言だけ（中身は _pat_unordered_plan() が扱う）。"""
        return len(i) > 0 and i[0] == '.unordered'

    def free_processing(self, i):
        """`.free` — 名前をすべての表（シンボル・`.sub`・`.check` の候補、変数なら
        その `.check` / `.enum` / `.reloc`）から外す。位置依存。
        """
        if len(i) == 0 or i[0] != '.free':
            return False
        st = self.state
        names = (i[2] if len(i) >= 3 and i[2] else (i[1] if len(i) >= 2 else ''))
        if not names.strip():
            st.diag(" error - .free: needs '.free::<name,name,...>'.", set_error=True)
            return True
        for nm in names.split(','):
            nm = nm.strip()
            if not nm:
                continue
            key = StringUtils.upper(nm)
            for d in (st.symbols, st.strsymbols, st.arrsymbols):
                d.pop(key, None)
            st.arrgen += 1
            st.freed_subs.add(key)
            for var, syms in st.check_constraints.items():
                st.check_constraints[var] = [x for x in syms if x != key]
            v = nm.translate(_ALOWER)
            if v and PatternMatcher._var_name_at(v, 0) == len(v):
                for d in (st.check_constraints, st.reloc_constraints, st.reloc_masks,
                          st.reloc_pairs, st.enum_defs):
                    d.pop(v, None)
        return True

    def echo_processing(self, i):
        """`.echo` — 本文行から標準エラーへ印字する（ワードは出さない）。"""
        if len(i) == 0 or i[0] != '.echo':
            return False
        st = self.state
        if not st.should_report_errors() or st.relax.pass1_size_mode:
            return True
        items, err = _echo_items_cached(i[1])
        if err is not None:
            return True
        parts = []
        for k, v in items:
            if k == 's':
                parts.append(v)
                continue
            # 裸の名前は 文字列シンボル → 配列シンボル（集合も）→ 式 の順。
            nm = bare_name_of(v)
            if nm is not None:
                key = StringUtils.upper(nm)
                if key in st.strsymbols:
                    parts.append(st.strsymbols[key])
                    continue
                if key in st.arrsymbols:
                    parts.append('[' + ', '.join(
                        '"' + e.replace('\0', '\\0') + '"' if isinstance(e, str)
                        else str(_mini_signed(e)) for e in st.arrsymbols[key]) + ']')
                    continue
            val = self.expr_eval.expression_pat(v, 0)[0]
            parts.append('UNDEF' if _undef(val) else _mini_signed(val))
        _echo_write(parts)
        return True

    def _onoff(self, i, dname):
        """`on` / `off` の引数（省略は on）。1 / 0、誤りは None（診断済み）。"""
        arg = next((StringUtils.upper(f.strip()) for f in i[1:] if f and f.strip()), '')
        if arg in ('', 'ON'):
            return 1
        if arg == 'OFF':
            return 0
        self.state.diag(f" error - {dname}: expected 'on' or 'off' ('{arg}').", set_error=True)
        return None

    def passthru_processing(self, i):
        """`.passthru` — どのパターンにも当たらない行をエラーにせず素通しする。"""
        if len(i) == 0 or i[0] != '.passthru':
            return False
        v = self._onoff(i, '.passthru')
        if v is not None:
            self.state.passthru = v
        return True

    def eol_processing(self, i):
        """`.eol` — 1 ソース行につき 1 行の改行を自動で入れる。"""
        if len(i) == 0 or i[0] != '.eol':
            return False
        v = self._onoff(i, '.eol')
        if v is not None:
            self.state.eol = v
        return True

    def textmode_processing(self, i):
        """`.textmode` — テキスト置換モード（ラベル・式・コメント・字下げを綴りのまま残す）。"""
        if len(i) == 0 or i[0] != '.textmode':
            return False
        v = self._onoff(i, '.textmode')
        if v is not None:
            self.state.textmode = self.state.passthru = self.state.eol = v
        return True

    def enum_processing(self, i):
        """`.enum` — 要素のリストを取る位置を宣言する（68000 の MOVEM など）。"""
        if len(i) == 0 or i[0] != '.enum':
            return False
        st = self.state
        var_field = i[1].strip() if len(i) >= 2 else ''
        names_field = i[2] if len(i) >= 3 else ''
        expr_field = i[3] if len(i) >= 4 else ''
        var = self._dir_var(var_field)
        if var is None:
            st.diag(f" error - .enum: variable should be a lower case name ('{var_field}').", set_error=True)
            return True
        names = []
        for nm in self.elem_list_expand(names_field):
            if nm and nm not in names:
                names.append(nm)
        if not names:
            st.diag(" error - .enum: no enumeration element is given.", set_error=True)
        elif not expr_field.strip():
            st.diag(" error - .enum: the value expression is missing.", set_error=True)
        else:
            st.enum_defs[var] = (tuple(names), expr_field)
        return True

    def clrenum_processing(self, i):
        """`.clrenum` — `.enum` の宣言を外す（引数なしで全部）。"""
        return self._clear_var_dir(i, '.clrenum', (self.state.enum_defs,), False)

    def errmsg_processing(self, i):
        """`.error::n::"文言"` — エラーコードの文言を足す・上書きする。"""
        if len(i) == 0 or i[0] != '.error':
            return False
        st = self.state
        n_field = i[1].strip() if len(i) >= 2 else ''
        msg_field = i[2] if len(i) >= 3 else ''
        if not n_field:
            st.diag(" error - .error directive requires an error code (number).", set_error=True)
            return True
        st.error_undefined_label = False
        n, _idx = self.expr_eval.expression_pat(n_field, 0)
        bad = st.error_undefined_label or _is_undef_derived(n)
        st.error_undefined_label = False
        n_int = None
        if not bad:
            try:
                n_int = int(n)
            except (OverflowError, ValueError, TypeError):
                pass
        if n_int is None or n_int != n or not 0 <= n_int <= 1000000:
            st.diag(f" error - .error: error code must be a non-negative integer "
                    f"(0-1000000), got {n_field!r}.", set_error=True)
            return True
        if not msg_field.strip().startswith('"'):
            st.diag(f" error - .error: message must be a double-quoted string, got {msg_field!r}.", set_error=True)
            return True
        if n_int >= len(st.errors):
            st.errors.extend([''] * (n_int + 1 - len(st.errors)))
        st.errors[n_int] = StringUtils.get_string(msg_field.strip())
        return True


_SYM_CORE = set(DIGIT + ALPHABET + '_')

_PAT_DIRECTIVES = frozenset((
    '.setsym', '.clearsym', '.padding', '.bits', '.symbolc', '.vliw',
    '.check', '.clrcheck', '.reloc', '.clrreloc', '.map', '.free',
    '.passthru', '.eol', '.textmode', '.enum', '.clrenum', '.error',
    '.echo', '.unordered',
    '.elftype', '.elfmachine', '.elfclass', '.elfrela', '.elfwidth',
    '.elfextern', '.elfdwarf', '.elfheader', '.elfsection', '.elffield',
    '.elfpcguess', '.elfrelax', '.elfanchor', '.elfresolve', '.elfbuiltin', '.elfextra',
    '.elfdiff', '.elfencode',
    '.elfrinfo', '.elfunit', '.elflink', '.elfgroup', '.elfcfi', '.elfcfiinit',
    '.elfcfireg', '.elfunaligned'))

_CONST_SETSYM_RE = re.compile(r"^[\s0-9+\-*/%()<>|&^~]+$|^\s*0[xX][0-9a-fA-F]+\s*$")
_PLAIN_NUM_RE = re.compile(r"^\s*(?:0[xX][0-9a-fA-F]+|[0-9]+)\s*$")
_SETSYM_MISS = object()


def _pat_is_directive(i):
    """そのパターン行がディレクティブか（`EPIC::` も含める）。"""
    if not i or not i[0]:
        return False
    i0 = i[0]
    return i0 in _PAT_DIRECTIVES or (len(i0) == 4 and StringUtils.upper(i0) == 'EPIC')


# テキスト置換モードでバイトを出さずに綴りだけ通す組み込みディレクティブ。
_TEXTMODE_TEXT_ONLY_DIRS = frozenset((
    '.ORG', '.ALIGN', '.ZERO', '.ASCII', '.ASCIZ',
    '.RESB', '.RESW', '.RESD', '.RESQ',
    '.DB', '.DW', '.DD', '.DQ', '.DO', '.DY', '.DZ'))


def _expects_expr(t, idx):
    """その位置でパターンが式捕捉 `!` を待っているか。"""
    while idx < len(t) and t[idx] in ' \t' + SUB_OPEN + SUB_CLOSE:
        idx += 1 if t[idx] in ' \t' else 2
    return idx < len(t) and t[idx] == '!'


class PatternMatcher:
    """アセンブリ行とパターンの命令欄を照合する。

      match0          `!S{{表}}` のサブ表参照を展開して試す
      match0_brackets `[[ ]]` の省略可能部分を組み合わせを変えて試す
      match           1 文字ずつ突き合わせる本体

    当たったものすべてに特異度スコア (n_expr, -n_lit, n_sym) を付け、最小のものを採る
    （行の順序は結果に影響しない）。失敗した試行の束縛と -o の参照は巻き戻す。
    """

    def __init__(self, state, expr_eval, var_manager, symbol_manager, parser):
        self.state = state
        self.expr_eval = expr_eval
        self.var_manager = var_manager
        self.symbol_manager = symbol_manager
        self.parser = parser
        self.last_score = None
        self.last_match_score = None
        self._sub_spans = {}

    def remove_brackets(self, s, l):
        """番号（開き括弧の出現順、1 起点）で指した `[[ ]]` 群を中身ごと取り除く。"""
        serial = 0
        stack = []
        pairs = {}
        for i, ch in enumerate(s):
            if ch == OB:
                serial += 1
                stack.append((serial, i))
            elif ch == CB and stack:
                ser, open_pos = stack.pop()
                pairs[ser] = (open_pos, i)
        drop = set()
        for index in l:
            if index in pairs:
                drop.update(range(pairs[index][0], pairs[index][1] + 1))
        return ''.join(c for k, c in enumerate(s) if k not in drop)

    @staticmethod
    def _var_name_at(t, i):
        """その位置のパターン変数名の長さ（変数名でなければ 0）。"""
        if i >= len(t) or not ('a' <= t[i] <= 'z'):
            return 0
        n = 1
        while i + n < len(t) and ('a' <= t[i + n] <= 'z'
                                  or _ad(t[i + n]) or t[i + n] == '_'):
            n += 1
        return n

    def _var_declare(self, name):
        """変数名を「この行で使われた名前」として登録する。"""
        if name:
            self.state.varnames.add(name)
        return name

    def _enum_capture(self, s, idx, edef):
        """`!E` の位置で要素のリストを読む。返り値は (値, 次の位置) か None。

        `,` と `/` が区切り、`first-last` は列挙順の範囲（逆順は範囲にせず `-` を
        パターンに委ねる）。区切りは次の要素が続くときだけ食べる。
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
        return None if v is None else (v, pos)

    def _enum_eval(self, edef, present):
        """`.enum` の式を、現れた要素だけ値を持つ（ほかは 0）状態で評価する。

        `.setsym` の無い要素があれば None（パターンを不一致にする）。
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
            return self.expr_eval.expression_pat(expr, 0)[0]
        finally:
            self.state.enum_bindings = prev

    def _cap_text(self, a, s, b, e, stopchar=chr(0)):
        """捕捉した s[b:e] の綴りを変数 a に覚える（止め文字と前後の空白は落とす）。caxx.c の cap_text_set()。"""
        raw = s[b:e]
        if stopchar != chr(0) and raw.endswith(stopchar):
            raw = raw[:-1]
        self.state.vars_text[a] = raw.strip(' \t' + chr(0))

    @staticmethod
    def _var_stopchar(t, idx_t):
        """変数名の後ろの `\\c` 止め文字を読む。返り値は (止め文字, 次の位置, 閉じ印の段)。

        `!S{{表}}` の閉じ印が変数名と `\\c` の間にあれば、式を読み終えた位置で閉じる。
        caxx.c の pat_var_stopchar() と同じ規則である。
        """
        j = StringUtils.skipspc(t, idx_t)
        closes = []
        while j + 1 < len(t) and t[j] == SUB_CLOSE:
            closes.append(t[j + 1])
            j = StringUtils.skipspc(t, j + 2)
        if j < len(t) and t[j] == '\\':
            j += 1
            return (t[j] if j < len(t) else chr(0)), j + 1, closes
        return chr(0), StringUtils.skipspc(t, idx_t), []

    def _sub_mark(self, m, k, idx_s):
        """`!S{{表}}` の開き印・閉じ印に当たったソース上の位置を覚える。"""
        if m == SUB_OPEN:
            self._sub_spans[k] = [idx_s, idx_s]
        else:
            self._sub_spans.setdefault(k, [idx_s, idx_s])[1] = idx_s

    def match(self, s, t):
        """ソース行 s とパターン t を 1 文字ずつ突き合わせる。

        大文字・数字・記号は文字定数、小文字の名前はシンボル、`!x` は式、`!!x` は因子、
        `!F/!D/!Q` は浮動小数点、`!L` は式とその綴り、`!E` は列挙リスト、
        `!Y集合[変数]` は集合の項目番号。当たれば last_score に特異度を残す。
        式の捕捉で因子が欠けていればそのパターンは当たらない。
        """
        st = self.state
        ev = self.expr_eval
        n_expr = n_sym = n_lit = 0
        # `[[xxx]]yyy` は `xxx yyy` として読む（rep と p が repp につながらない。caxx.c の pat_match()）。
        t = t.replace(OB, '').replace(CB, ' ')
        idx_s = StringUtils.skipspc(s, 0)
        idx_t = StringUtils.skipspc(t, 0)
        s += chr(0)
        t += chr(0)
        prev_alnum = False
        self._sub_spans = {}

        def skip_stop(idx_s, stopchar):
            if stopchar != chr(0) and idx_s < len(s) and s[idx_s] == stopchar:
                return idx_s + 1
            return idx_s

        while True:
            s_sp = idx_s < len(s) and s[idx_s] in ' \t'
            t_sp = idx_t < len(t) and t[idx_t] in ' \t'
            idx_s = StringUtils.skipspc(s, idx_s)
            idx_t = StringUtils.skipspc(t, idx_t)
            while t[idx_t] == SUB_OPEN or t[idx_t] == SUB_CLOSE:
                self._sub_mark(t[idx_t], t[idx_t + 1], idx_s)
                idx_t += 2
                if t[idx_t] in ' \t':
                    t_sp = True
                idx_t = StringUtils.skipspc(t, idx_t)

            word_break = s_sp and not t_sp
            b = s[idx_s]
            a = t[idx_t]

            if a == chr(0) and b == chr(0):
                self.last_score = (n_expr, -n_lit, n_sym)
                return True

            if a == '\\':
                idx_t += 1
                if not (idx_t < len(t) - 1 and t[idx_t] == b):
                    return False
                lit_alnum = t[idx_t] in _AALNUM
                if lit_alnum and prev_alnum and word_break:
                    return False
                idx_t += 1
                idx_s += 1
                n_lit += 1
                prev_alnum = lit_alnum
                continue
            if a in CAPITAL:
                if a != _AUP1.get(b, b) or (prev_alnum and word_break):
                    return False
                idx_s += 1
                idx_t += 1
                n_lit += 1
                prev_alnum = True
                continue
            if a == '!':
                prev_alnum = False
                n_expr += 1
                kind = t[idx_t + 1]
                idx_t += 2
                if kind == chr(0):
                    return False
                if kind not in 'FDQLEY!':
                    # `!x` — 式（変数名は ! の直後から）
                    idx_t -= 1
                    kind = ''
                if kind == 'Y':
                    # `!Y集合[変数]`
                    sl = self._var_name_at(t, idx_t)
                    if sl == 0:
                        return False
                    setkey = StringUtils.upper(t[idx_t:idx_t + sl])
                    idx_t += sl
                    if t[idx_t] != '[':
                        return False
                    idx_t += 1
                nl = self._var_name_at(t, idx_t)
                if nl == 0:
                    return False
                a = self._var_declare(t[idx_t:idx_t + nl])
                idx_t += nl

                if kind in ('F', 'D'):
                    stopchar, idx_t, closes = self._var_stopchar(t, idx_t)
                    cap_start = idx_s
                    st.expr_missing = False
                    try:
                        v, idx_s = ev.expression_esc_float(s, idx_s, stopchar)
                    finally:
                        st.elf.capturing_var = None
                    for k in closes:
                        self._sub_mark(SUB_CLOSE, k, idx_s)
                    self._cap_text(a, s, cap_start, idx_s, stopchar)
                    fmt, bits = ('>f', 32) if kind == 'F' else ('>d', 64)
                    try:
                        # 未定義は 0（報告済み）。整数は 256 ビットの符号付きとして（caxx.c と同じ）。
                        v = 0.0 if _undef(v) else float(_float_int(v))
                        v = int.from_bytes(struct.pack(fmt, v), "big")
                    except (OverflowError, ValueError, struct.error):
                        st.diag(f" error - !{kind}: cannot convert value to float{bits}; using 0.", set_error=True)
                        v = 0
                    self.var_manager.put(a, v)
                    if st.expr_missing:
                        return False
                    idx_s = skip_stop(idx_s, stopchar)
                elif kind == 'Q':
                    stopchar, idx_t, closes = self._var_stopchar(t, idx_t)
                    q_start = idx_s
                    st.expr_missing = False
                    d0_prev = (st.fdiv0_defer, st.fdiv0_seen)
                    st.fdiv0_defer, st.fdiv0_seen = True, False
                    try:
                        v, q_end = ev.expression_esc_float(s, idx_s, stopchar)
                    finally:
                        st.elf.capturing_var = None
                        d0 = st.fdiv0_seen
                        st.fdiv0_defer, st.fdiv0_seen = d0_prev
                    for k in closes:
                        self._sub_mark(SUB_CLOSE, k, q_end)
                    self._cap_text(a, s, q_start, q_end, stopchar)
                    raw = s[q_start:q_end]
                    if stopchar != chr(0) and raw.endswith(stopchar):
                        raw = raw[:-1]
                    # 前後の空白は落とさず、終端の NUL だけ落とす（caxx.c と同じ）。
                    raw = raw.split(chr(0), 1)[0]
                    if len(raw) > 4 and raw.startswith('qad{') and raw.endswith('}'):
                        raw = raw[4:-1]
                    # 4 倍精度の式として評価し、だめなら倍精度の値を %.17g で（caxx.c と同じ順）。
                    if _undef(v):
                        h = '0' * 32
                    else:
                        try:
                            if not raw:
                                raise ValueError
                            h = IEEE754Converter.decimal_eval_expr(raw)
                            d0 = False
                        except (ValueError, ZeroDivisionError):
                            h = IEEE754Converter.decimal_to_ieee754_128bit_hex(
                                raw if raw in ('inf', '-inf', 'nan') else _g17(_float_of(v)))
                    if d0:
                        st.diag(" error - Division by 0 error.", set_error=True)
                    self.var_manager.put(a, int(h, 16))
                    if st.expr_missing:
                        return False
                    idx_s = skip_stop(q_end, stopchar)
                elif kind == 'L':
                    stopchar, idx_t, closes = self._var_stopchar(t, idx_t)
                    text_start = idx_s
                    st.elf.capturing_var = a
                    cap_prior = st.error_undefined_label
                    st.error_undefined_label = False
                    st.expr_missing = False
                    lcap_prior = st._textmode_lcap
                    if st.textmode:
                        st._textmode_lcap = True
                    try:
                        v, idx_s = ev.expression_esc(s, idx_s, stopchar)
                    finally:
                        st.elf.capturing_var = None
                        st._textmode_lcap = lcap_prior
                    cap_undef = st.error_undefined_label
                    for k in closes:
                        self._sub_mark(SUB_CLOSE, k, idx_s)
                    raw = s[text_start:idx_s]
                    if stopchar != chr(0) and raw.endswith(stopchar):
                        raw = raw[:-1]
                    self._cap_text(a, s, text_start, idx_s, stopchar)
                    _elf_v2l_finish(st, a, raw, ev.loc_counter_value)
                    if st.textmode:
                        st.error_undefined_label = cap_prior
                        if cap_undef or _is_undef_derived(v):
                            v = 0
                        self.var_manager.put_tagged(a, v, False)
                    else:
                        st.error_undefined_label = cap_prior or cap_undef
                        self.var_manager.put_tagged(a, v, cap_undef)
                    if st.expr_missing:
                        return False
                    idx_s = skip_stop(idx_s, stopchar)
                elif kind == 'E':
                    edef = st.enum_defs.get(a)
                    if edef is None:
                        return False
                    hit = self._enum_capture(s, idx_s, edef)
                    if hit is None:
                        return False
                    cap_start = idx_s
                    v, idx_s = hit
                    self.var_manager.put(a, v)
                    self._cap_text(a, s, cap_start, idx_s)
                elif kind == 'Y':
                    if t[idx_t] != ']':
                        return False
                    idx_t += 1
                    arr = st.arrsymbols.get(setkey)
                    if not arr:
                        return False
                    yk, yend = _symset_item_at(s, idx_s, arr)
                    if yk < 0:
                        return False
                    self._cap_text(a, s, idx_s, yend)
                    idx_s = yend
                    self.var_manager.put(a, yk)
                    n_expr -= 1
                    n_sym += 1
                else:
                    # `!!x`（因子）と `!x`（止め文字までの式）。
                    if kind == '!':
                        stopchar, closes = chr(0), ()
                    else:
                        stopchar, idx_t, closes = self._var_stopchar(t, idx_t)
                    st.elf.capturing_var = a
                    cap_prior = st.error_undefined_label
                    st.error_undefined_label = False
                    cap_start = idx_s
                    st.expr_missing = False
                    try:
                        if kind == '!':
                            v, idx_s = ev.factor(s, idx_s)
                        else:
                            v, idx_s = ev.expression_esc(s, idx_s, stopchar)
                    finally:
                        st.elf.capturing_var = None
                    for k in closes:
                        self._sub_mark(SUB_CLOSE, k, idx_s)
                    _elf_v2l_finish(st, a, s[cap_start:idx_s], ev.loc_counter_value)
                    self._cap_text(a, s, cap_start, idx_s, stopchar)
                    cap_undef = st.error_undefined_label
                    st.error_undefined_label = cap_prior or cap_undef
                    self.var_manager.put_tagged(a, v, cap_undef)
                    if st.expr_missing:
                        return False
                    idx_s = skip_stop(idx_s, stopchar)
                continue
            if a in LOWER:
                prev_alnum = False
                nl = self._var_name_at(t, idx_t)
                a = self._var_declare(t[idx_t:idx_t + nl])
                idx_t += nl
                prev_idx_s = idx_s
                allowed = st.check_constraints.get(a)
                allow_omit = allowed is not None and CHECK_OMIT in allowed
                # `.unordered` の `.map` の変数ごとの表があれば値はそこから（caxx.c の cap_sym_get()）。
                tbl = st.var_tables.get(a)
                sget = self.symbol_manager.get if tbl is None \
                    else (lambda w_, t_=tbl: t_.get(StringUtils.upper(w_), ""))
                w, idx_s = self.parser.get_symbol_word(s, idx_s)
                v = sget(w)
                if v == "":
                    # 語の途中の記号で切って短い名前を試す（`(IX-5)` の `IX`）。
                    for cut in range(len(w) - 1, 0, -1):
                        if w[cut] in _SYM_CORE:
                            continue
                        v2 = sget(w[:cut])
                        if v2 != "":
                            w, v, idx_s = w[:cut], v2, prev_idx_s + cut
                            break
                ok = v != "" and idx_s != prev_idx_s and (allowed is None or w in allowed)
                if not ok and allowed:
                    best = ''
                    for nm in allowed:
                        if nm and len(nm) > len(best) and \
                                StringUtils.upper(s[prev_idx_s:prev_idx_s + len(nm)]) == nm:
                            best = nm
                    if best:
                        v2 = sget(best)
                        if v2 != "":
                            w, v, idx_s, ok = best, v2, prev_idx_s + len(best), True
                if not ok:
                    if not allow_omit:
                        return False
                    idx_s = prev_idx_s
                    self.var_manager.put(a, VAR_UNDEF)
                    st.vars_text[a] = ''
                    n_sym += 1
                    continue
                self.var_manager.put(a, v)
                self._cap_text(a, s, prev_idx_s, idx_s)
                n_sym += 1
                continue
            if a == '+' and b == '-' and _expects_expr(t, idx_t + 1):
                idx_t += 1
                n_lit += 1
                prev_alnum = False
                continue
            if a != b:
                return False
            lit_alnum = a in _AALNUM
            if lit_alnum and prev_alnum and word_break:
                return False
            idx_t += 1
            idx_s += 1
            n_lit += 1
            prev_alnum = lit_alnum

    _MAX_COMBINATIONS = 1 << 16
    _SUB_MAX_DEPTH = 8

    @staticmethod
    def _find_sub_ref(t, start=0):
        """パターン中の最初の `!S{{表}}変数`。返り値は (開始, 終了, 表の名前, 変数名) か None。

        `\\` で逃がしたもの、表の名前として読めないもの、変数名が続かないものは飛ばす。
        """
        i = start
        while True:
            i = t.find('!S{{', i)
            if i < 0:
                return None
            j = t.find('}}', i + 4)
            if j < 0:
                return None
            if not (i > 0 and t[i - 1] == '\\'):
                name = t[i + 4:j]
                vl = PatternMatcher._var_name_at(t, j + 2)
                if _is_sub_name(name) and vl > 0:
                    return i, j + 2 + vl, name, t[j + 2:j + 2 + vl]
            i = j + 2

    def _sub_variants(self, t, depth=0):
        """サブ表参照を選択肢に展開し、(パターン, 束縛) を順に生む。

        エントリがさらに表を参照していれば再帰する（8 段まで）。内側の変数が先に束縛される。
        差し込んだ範囲は印ではさみ、印の後ろの 1 文字が段（束縛の並びの位置）になる。
        """
        ref = self._find_sub_ref(t)
        if ref is None:
            yield t, ()
            return
        start, end, name, var = ref
        self._var_declare(var)
        ref_text = '!S{{' + name + '}}'
        if depth >= self._SUB_MAX_DEPTH:
            self.state.diag(f" error - {ref_text}: sub table expansion exceeds "
                            f"maximum depth {self._SUB_MAX_DEPTH}.", set_error=True)
            return
        entries = self.state.sub_defs.get(name)
        if entries is None or StringUtils.upper(name) in self.state.freed_subs:
            self.state.diag(f" error - {ref_text}: no sub table named {name!r} "
                            f"(define it with '.sub::{name} ... .return').",
                            set_error=True)
            return
        k = chr(ord('0') + depth)
        for ent_pat, ent_val in entries:
            nt = t[:start] + SUB_OPEN + k + ent_pat + SUB_CLOSE + k + t[end:]
            for vt, binds in self._sub_variants(nt, depth + 1):
                yield vt, ((var, ent_val),) + binds

    def _sub_value(self, expr_text):
        """サブ表エントリの値リストを 1 つの値に（2 つ以上なら先頭を上位に `.bits` 幅ずつ詰める）。"""
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
        if len(vals) <= 1:
            return vals[0] if vals else 0
        bts = self.state.bts if self.state.bts > 0 else 8
        acc = 0
        for v in vals:
            acc = (acc << bts) | (int(v) & ((1 << bts) - 1))
        return acc

    def _try_save(self):
        """照合の試行の前の、変数の束縛と -o のラベル参照を写し取る。"""
        st = self.state
        e = st.elf
        return (dict(st.vars), dict(st.vars_undef), dict(st.vars_float), dict(st.vars_text),
                len(e.label_refs_seen), dict(e.var_to_label), dict(e.insn_reloc_hint))

    def _try_restore(self, saved):
        """失敗した試行のぶんを巻き戻す（当たらなかった選択肢が出力に化けないように）。"""
        st = self.state
        e = st.elf
        st.vars, st.vars_undef, st.vars_float, st.vars_text, n, e.var_to_label, \
            e.insn_reloc_hint = saved
        del e.label_refs_seen[n:]

    def match0(self, s, t):
        """サブ表の選択肢を順に試す。当たったら変数へ値と綴りを束縛して True。"""
        for vt, binds in self._sub_variants(t):
            saved = self._try_save()
            if self.match0_brackets(s, vt):
                spans = self._sub_spans
                for var, ent_val in reversed(binds):
                    self.var_manager.put(var, self._sub_value(ent_val))
                for k, (var, _ent_val) in enumerate(binds):
                    sp = spans.get(chr(ord('0') + k))
                    if sp is None:
                        self.state.vars_text[var] = ''
                    else:
                        self._cap_text(var, s, sp[0], sp[1])
                return True
            self._try_restore(saved)
        return False

    def match0_brackets(self, s, t):
        """`[[ ]]` の省略可能部分を、取り除く群を 0 個から増やして試す。

        群は 20 までが省略可能（超えたぶんは常に含める）。組み合わせが 65536 を超えた
        パターンは不一致とし、パターンごとに一度だけ警告する。どちらの警告も照合の溜め置きを
        通さずに出す（caxx.c と同じ）。
        """
        if '[[' not in t and ']]' not in t:
            if self.match(s, t):
                self.last_match_score = self.last_score
                return True
            return False
        st = self.state
        t = t.replace('[[', OB).replace(']]', CB)
        cnt = t.count(OB)
        sl = list(range(1, cnt + 1))
        if cnt > 20:
            if st.should_report_errors() and t not in st.relax.optgroups_warned:
                st.relax.optgroups_warned.add(t)
                st.diag(st._diag_locate(
                    f" warning - pattern has {cnt} optional groups (max 20); "
                    f"first 20 are treated as optional, "
                    f"remainder are always included."), set_error=False, force=True)
            sl = sl[:20]
            cnt = 20
        tried = 0
        for i in range(len(sl) + 1):
            for j in itertools.combinations(sl, i):
                tried += 1
                if tried > self._MAX_COMBINATIONS:
                    if st.should_report_errors() and t not in st.relax.combo_budget_warned:
                        st.relax.combo_budget_warned.add(t)
                        st.diag(st._diag_locate(
                            f" warning - a pattern with {cnt} optional group(s) exceeded the "
                            f"{self._MAX_COMBINATIONS}-combination match budget and was treated "
                            f"as non-matching; consider splitting it into multiple explicit "
                            f"pattern entries."), set_error=False, force=True)
                    return False
                lt = self.remove_brackets(t, list(j))
                saved = self._try_save()
                if self.match(s, lt):
                    self.last_match_score = self.last_score
                    return True
                self._try_restore(saved)
        return False


class PatternFileReader:
    """パターンファイルを読み、行を欄に割った表にする。

    `.INCLUDE` を再帰で展開し、各行をマクロ層に通してから `::` で最大 6 欄に割る。
    `.sub` と `.func` のブロックはここで本文を集めて別に持つ。
    """

    def __init__(self, parser, macro_proc=None):
        self.parser = parser
        self.macro_proc = macro_proc if macro_proc is not None \
            else MacroPreprocessor(None, pat_mode=True)
        self.subs = {}
        self.funcs = {}

    def readpat(self, fn, base_dir=None, _depth=0, _chain=None):
        """パターンファイル 1 つを読み、パターン行の表を返す。

        `.INCLUDE` は 50 段まで、循環は報告して飛ばす、相対パスはそのファイルの場所から。
        コメントの後方互換: 古い「全行の先頭に `/*`」の書き方のため、すぐ次の行も `/*` で
        始まるか、以降どこにも `*/` が無ければ、`/*` は自分の行を超えて延長しない。
        """
        if fn == '':
            return []
        if _depth > 50:
            diag(f" error - pattern .INCLUDE nesting exceeds 50: '{fn}'", set_error=True)
            return []
        if base_dir and not os.path.isabs(fn):
            fn = os.path.join(base_dir, fn)
        real = os.path.realpath(fn)
        _chain = _chain or frozenset()
        if real in _chain:
            diag(f" error - circular pattern .INCLUDE detected: '{fn}' "
                 f"(already in include chain). Skipped.", set_error=True)
            return []
        _chain = _chain | {real}
        this_dir = os.path.dirname(os.path.abspath(fn))
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

        def opens_comment(s):
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
                bare_open = opens_comment(expanded[_li][0])
                legacy = (legacy_chain and bare_open) or (
                    _li + 1 < len(expanded) and opens_comment(expanded[_li + 1][0])) \
                    or not rest_has_close[_li + 1]
                if legacy:
                    in_block_comment = False
                legacy_chain = legacy and bare_open
            l = StringUtils.reduce_spaces(l.replace('\t', ' ').replace('\r', '').replace('\n', ''))

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
                        diag(f" error - '.func::{cur.name}': {_dk.translate(_ALOWER)} without a "
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
            r = []
            idx = 0
            while True:
                fld, idx = self.parser.get_params1(l, idx)
                r.append(fld)
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
                    diag(f" error - '{_kw.translate(_ALOWER)}' without a matching '.sub'.",
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

            # 引数なしで意味を持つもの（切り替えと「全部消す」）は警告しない（caxx.c の readpat() と同じ一覧）。
            if (len(l) == 1 and l[0].strip() != ''
                    and _kw not in ('.PASSTHRU', '.EOL', '.TEXTMODE', '.UNORDERED',
                                    '.CLEARSYM', '.CLRCHECK', '.CLRRELOC', '.CLRENUM')):
                diag(f" warning - pattern line has no '::' field separator "
                     f"and can never match (likely a stray line left over "
                     f"from a multi-line comment, or a binary_list/"
                     f"error_patterns continued onto the next physical "
                     f"line without a '\\' at the end of the line before): "
                     f"{l[0]!r}", set_error=False)
            elif len(l) > 6:
                diag(f" warning - pattern line has more than 6 fields "
                     f"(extra fields ignored): {l[6:]!r}", set_error=False)
            # 2 欄なら 2 つ目は binary_list（第 3 欄）。
            w.append([l[0], '', l[1], '', '', ''] if len(l) == 2 else (l + [''] * 6)[:6])

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
        v = (field or '').strip()
        if not v or not v.isascii():
            return None
        v = v.lower()
        return v if _VARNAME_RE.fullmatch(v) else None

    @staticmethod
    def _map_subst_index(expr, var, i):
        """`.map` の式の中の変数（語として現れた所だけ）を `(i)` に置き換える。"""
        num = '(%d)' % i
        vl = len(var)
        out = []
        k = 0
        while k < len(expr):
            if expr[k:k + vl].translate(_ALOWER) == var:
                prev = expr[k - 1] if k > 0 else ''
                nxt = expr[k + vl] if k + vl < len(expr) else ''
                if not (_aan(prev) or prev == '_') and not (_aan(nxt) or nxt == '_'):
                    out.append(num)
                    k += vl
                    continue
            out.append(expr[k])
            k += 1
        return ''.join(out)

    def compile_funcs(self):
        """集めた `.func` の本文を構文木にする。"""
        saved_reclimit = sys.getrecursionlimit()
        if saved_reclimit < _MINI_RECLIMIT:
            sys.setrecursionlimit(_MINI_RECLIMIT)

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
        try:
            walk(self.funcs)
        finally:
            sys.setrecursionlimit(saved_reclimit)

    def check_sub_refs(self, pat):
        """`!S{{表}}` の参照（未知の表名と循環）を、ファイル全体を読んでから一度だけ検査する。"""
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
        """`.INCLUDE` の行なら読み込んだ表を返す（違えば None）。引用符の無い名前は警告して採る。"""
        idx = StringUtils.skipspc(l, 0)
        if l[idx:idx + 8].translate(_AUPPER) != ".INCLUDE":
            return None
        s = StringUtils.get_string(l[idx + 8:])
        if s == "":
            raw = l[idx + 8:].strip()
            fallback = StringUtils.get_param_to_spc(raw, 0)[0] if raw else ''
            if not fallback:
                diag(f" error - .INCLUDE directive has no filename: {l!r}", set_error=True)
                return []
            diag(f" warning - .INCLUDE filename not quoted: {fallback!r}. "
                 "Please use double quotes.", set_error=False)
            s = fallback
        return self.readpat(s, base_dir, _depth=_depth, _chain=_chain)


class MiniLangError(Exception):
    """ミニ言語の実行時エラー（行と桁を文言に持つ）。"""


class _MiniBreak(Exception):
    """`.break` を外側のループへ伝える。"""

    __slots__ = ()


class _MiniContinue(Exception):
    """`.continue` を外側のループへ伝える。"""

    __slots__ = ()


class _MiniReturn(Exception):
    """`.return` を呼び出し元へ伝える（値を持つことがある）。"""

    __slots__ = ('value',)

    def __init__(self, value=None):
        super().__init__()
        self.value = value


_MINI_RECLIMIT = 20000
# 入れ子の上限: ミニ言語の式と文（caxx.c の MINI_EXPR_MAX_DEPTH / MINI_BLOCK_MAX_DEPTH）、
# 本体の式（EXPR_MAX_DEPTH。括弧 1 段で十数フレーム使うので再帰の上限も上げる）。
_MINI_EXPR_MAX_DEPTH = 1000
_MINI_BLOCK_MAX_DEPTH = 1000
_EXPR_MAX_DEPTH = 500
_EXPR_RECLIMIT = 20000
# ミニ言語の整数は 256bit で回り込む（caxx.c と同じ結果にするため演算ごとにマスクする）。
_MINI_BITS = 256
_MINI_MASK = (1 << _MINI_BITS) - 1


def _mini_wrap(v):
    """値を 256bit に丸める（符号なしの表現）。"""
    return int(v) & _MINI_MASK


def _mini_signed(v):
    """値を 256bit の符号付きとして読み直す。"""
    v = int(v) & _MINI_MASK
    return v - (1 << _MINI_BITS) if v >> (_MINI_BITS - 1) else v


# ミニ言語の字句（2 文字の演算子を先に試す）。
_MINI_OPS2 = ('**', '<<', '>>', '<=', '>=', '==', '!=', '&&', '||')
_MINI_OPS1 = frozenset('+-*/%&|^~<>!()[]:,=')
_MINI_ESC = {'\\': '\\', '"': '"', 'n': '\n', 't': '\t'}


def _mini_bytes(text):
    """ソースの文字列をミニ言語の文字列（UTF-8 のバイト列。長さも添字もバイト単位）にする。"""
    return text.encode('utf-8', 'surrogateescape')


def _mini_dec(v):
    """整数を符号付き 10 進の文字列（バイト列）にする。"""
    return str(_mini_signed(v)).encode('ascii')


def _ascii_alpha(c):
    """ASCII の英字か（ミニ言語の名前は ASCII の英数字と `_`。caxx.c と同じ）。"""
    return ('a' <= c <= 'z') or ('A' <= c <= 'Z')


def _ascii_alnum(c):
    """ASCII の英数字か。"""
    return _ascii_alpha(c) or ('0' <= c <= '9')


def _mini_lex(text, pos):
    """ミニ言語の 1 行を (種類, 値) のトークンに割る。pos は診断に出す位置。"""
    toks = []
    t = text
    i = 0
    n = len(t)
    where = f"{pos[0]}:{pos[1]}"

    def word_end(j, extra='_'):
        while j < n and (_ascii_alnum(t[j]) or t[j] in extra):
            j += 1
        return j

    while i < n:
        c = t[i]
        if c in ' \t':
            i += 1
        elif c in DIGIT:
            pfx = t[i + 1:i + 2] if c == '0' else ''
            if pfx in ('x', 'X', 'b', 'B'):
                hexa = pfx in ('x', 'X')
                digits = '0123456789abcdefABCDEF_' if hexa else '01_'
                j = i + 2
                while j < n and t[j] in digits:
                    j += 1
                if j == i + 2:
                    raise MiniLangError(f"{where}: malformed {'hex' if hexa else 'binary'} number")
                toks.append(('num', int(t[i + 2:j].replace('_', ''), 16 if hexa else 2)))
            else:
                j = i
                while j < n and (t[j] in DIGIT or t[j] == '_'):
                    j += 1
                toks.append(('num', int(t[i:j].replace('_', ''))))
            i = j
        elif _ascii_alpha(c) or c == '_':
            j = word_end(i)
            toks.append(('name', t[i:j]))
            i = j
        elif c == '.':
            j = word_end(i + 1)
            if j == i + 1:
                raise MiniLangError(f"{where}: stray '.'")
            toks.append(('dot', StringUtils.upper(t[i:j])))
            i = j
        elif c == '$':
            if t[i:i + 2] not in ('$$', '$.'):
                raise MiniLangError(f"{where}: '$' must be written "
                                    f"'$$' (location counter) or '$.' "
                                    f"(start of the next instruction)")
            toks.append(('core', t[i:i + 2]))
            i += 2
        elif c == '#':
            j = word_end(i + 1, '_.$')
            if j == i + 1:
                raise MiniLangError(f"{where}: '#' needs a symbol name")
            toks.append(('core', t[i:j]))
            i = j
        elif c == '"':
            j = i + 1
            buf = []
            while True:
                if j >= n:
                    raise MiniLangError(f"{where}: unterminated string")
                ch = t[j]
                if ch == '"':
                    j += 1
                    break
                if ch == '\\':
                    if j + 1 >= n:
                        raise MiniLangError(f"{where}: unterminated string")
                    e = t[j + 1]
                    if e not in _MINI_ESC:
                        raise MiniLangError(f"{where}: unknown escape "
                                            f"'\\{e}' in a string")
                    buf.append(_MINI_ESC[e])
                    j += 2
                else:
                    buf.append(ch)
                    j += 1
            toks.append(('str', _mini_bytes(''.join(buf))))
            i = j
        elif t[i:i + 2] in _MINI_OPS2:
            toks.append(('op', t[i:i + 2]))
            i += 2
        elif c in _MINI_OPS1:
            toks.append(('op', c))
            i += 1
        else:
            raise MiniLangError(f"{where}: unexpected character {c!r}")
    return toks


def _mini_tok_repr(k, v):
    """診断に出すトークンの書き方（数は 10 進、文字列はソースの綴り）。caxx.c の mxp_tokdesc()。"""
    if k == 'end':
        return repr('end of line')
    if k == 'num':
        return str(v)
    if k == 'str':
        return repr(v.decode('utf-8', 'surrogateescape'))
    return repr(v)


class _MiniExprParser:
    """ミニ言語の式を構文木にする。優先順位ごとに 1 メソッドの再帰下降。

    演算子は C に倣う（本体の式評価器とは `%` の符号などが違う）。
    構文木を作るだけで、評価は MiniInterp が行う。
    """

    def __init__(self, toks, pos):
        self.toks = toks
        self.i = 0
        self.pos = pos
        self.depth = 0

    def fail(self, msg):
        """現在位置を添えて構文エラーにする。"""
        raise MiniLangError(f"{self.pos[0]}:{self.pos[1]}: {msg}")

    def enter(self):
        """式の入れ子を 1 段深くする。_MINI_EXPR_MAX_DEPTH を超えたら構文エラー。

        caxx.c の mxp_enter と同じ数え方（`||` の段・単項 `-` `+` `~`・`!`）。
        """
        self.depth += 1
        if self.depth > _MINI_EXPR_MAX_DEPTH:
            self.fail(f"expression nests too deeply (more than {_MINI_EXPR_MAX_DEPTH} levels)")

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
        """その演算子を必ず 1 つ消費する（無ければ構文エラー）。"""
        if not self.eat_op(op):
            k, v = self.peek()
            self.fail(f"expected {op!r}, found {_mini_tok_repr(k, v)}")

    def at_end(self):
        """トークンを読み切ったか。"""
        return self.i >= len(self.toks)

    def arglist(self, close):
        """カンマで区切った式の並びを close まで読む（close も消費する）。"""
        items = []
        if not self.at_op(close):
            items.append(self.or_())
            while self.eat_op(','):
                items.append(self.or_())
        self.expect_op(close)
        return items

    def parse(self):
        """式を 1 個解析する（後ろに何か残ればエラー）。"""
        e = self.or_()
        if not self.at_end():
            k, v = self.peek()
            self.fail(f"unexpected {_mini_tok_repr(k, v)} in expression")
        return e

    def _binlevel(self, sub, ops):
        """左結合の二項演算の 1 段。"""
        e = sub()
        while self.at_op(*ops):
            op = self.peek()[1]
            self.i += 1
            e = ('bin', op, e, sub())
        return e

    def or_(self):
        self.enter()
        e = self._binlevel(self.and_, ('||',))
        self.depth -= 1
        return e

    def and_(self):
        return self._binlevel(self.not_, ('&&',))

    def not_(self):
        """単項 `!`。"""
        if self.at_op('!'):
            self.i += 1
            self.enter()
            e = ('un', '!', self.not_())
            self.depth -= 1
            return e
        return self.cmp_()

    def cmp_(self):
        return self._binlevel(self.bitor_, ('==', '!=', '<=', '>=', '<', '>'))

    def bitor_(self):
        return self._binlevel(self.bitxor_, ('|',))

    def bitxor_(self):
        return self._binlevel(self.bitand_, ('^',))

    def bitand_(self):
        return self._binlevel(self.shift_, ('&',))

    def shift_(self):
        return self._binlevel(self.add_, ('<<', '>>'))

    def add_(self):
        return self._binlevel(self.mul_, ('+', '-'))

    def mul_(self):
        return self._binlevel(self.unary_, ('*', '/', '%'))

    def unary_(self):
        """単項 `-` `+` `~`。"""
        if self.at_op('-', '+', '~'):
            op = self.peek()[1]
            self.i += 1
            self.enter()
            e = ('un', op, self.unary_())
            self.depth -= 1
            return e
        return self.power_()

    def power_(self):
        """`**`（右結合で、右は単項から）。"""
        e = self.postfix_()
        if self.at_op('**'):
            self.i += 1
            return ('bin', '**', e, self.unary_())
        return e

    def postfix_(self):
        """後置の添字 `名前[式]` と範囲 `名前[lo:hi]`。"""
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

    _BUILTINS = {'.LEN': 'len', '.STR': 'tostr', '.CHR': 'chr', '.INT': 'toint'}

    def primary_(self):
        """項（数・名前・文字列・`$$` `#シンボル`・`(式)`・配列リテラル・`.call`・組み込み）。"""
        k, v = self.peek()
        if k in ('str', 'core', 'num', 'name'):
            self.i += 1
            return ('num', _mini_wrap(v)) if k == 'num' else ('var' if k == 'name' else k, v)
        if k == 'dot':
            if v in self._BUILTINS:
                self.i += 1
                self.expect_op('(')
                e = self.or_()
                self.expect_op(')')
                return (self._BUILTINS[v], e)
            if v == '.CALL':
                self.i += 1
                k2, v2 = self.peek()
                if k2 != 'name':
                    self.fail("'.call' needs a function name")
                self.i += 1
                self.expect_op('(')
                return ('callexpr', v2, self.arglist(')'))
            self.fail(f"{v.translate(_ALOWER)!r} cannot be used in an expression")
        if k == 'op' and v == '(':
            self.i += 1
            e = self.or_()
            self.expect_op(')')
            return e
        if k == 'op' and v == '[':
            self.i += 1
            return ('arr', self.arglist(']'))
        self.fail(f"expected a value, found {_mini_tok_repr(k, v)}")


class MiniParser:
    """`.func` の本文を文の構文木にする（ブロックの対応は行の並びで取る。字下げは見ない）。"""

    _ENDERS = frozenset(('.ELIF', '.ELSE', '.ENDIF', '.NEXT', '.ENDWHILE'))

    def __init__(self, func):
        self.func = func
        self.lines = func.lines
        self.loopdepth = 0
        self.nest = 0

    def _nest(self, pos):
        """文の入れ子を 1 段深くする（_MINI_BLOCK_MAX_DEPTH まで。caxx.c の msp_nest と同じ数え方）。"""
        self.nest += 1
        if self.nest > _MINI_BLOCK_MAX_DEPTH:
            raise MiniLangError(f"{pos[0]}:{pos[1]}: '.if'/'.while'/'.for' blocks nest "
                                f"too deeply (more than {_MINI_BLOCK_MAX_DEPTH} levels)")

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
                raise MiniLangError(f"{f}:{ln}: '{kw.translate(_ALOWER)}' without a matching opener")
            if kw == '.IF':
                node, i = self._if_chain(i)
                out.append(node)
                i += 1
                continue
            if kw == '.WHILE':
                self._nest(pos)
                toks = _mini_lex(text, pos)
                cond = _MiniExprParser(toks[1:], pos).parse()
                self.loopdepth += 1
                body, i = self._block(i + 1, ('.ENDWHILE',))
                self.loopdepth -= 1
                if i >= len(self.lines):
                    raise MiniLangError(f"{f}:{ln}: '.while' is never closed with '.endwhile'")
                self.nest -= 1
                out.append(('while', cond, body, pos))
                i += 1
                continue
            if kw == '.FOR':
                self._nest(pos)
                var, kind, args = self._for_header(text, pos)
                self.loopdepth += 1
                body, i = self._block(i + 1, ('.NEXT',))
                self.loopdepth -= 1
                if i >= len(self.lines):
                    raise MiniLangError(f"{f}:{ln}: '.for' is never closed with '.next'")
                self.nest -= 1
                out.append((kind, var, args, body, pos))
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
        self._nest(pos)
        toks = _mini_lex(text, pos)
        if not toks or toks[-1] != ('dot', '.THEN'):
            raise MiniLangError(f"{f}:{ln}: '{kw.translate(_ALOWER)}' must end with '.then'")
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
        self.nest -= 1
        return ('if', cond, then_b, else_b, pos), i

    def _for_header(self, text, pos):
        """`.for 変数 in range(...)` は ('for', 変数, 引数)、`.for 変数 in 式` は ('forin', 変数, 式)。

        caxx.c の msp_block() の `.FOR` と同じ規則である。
        """
        toks = _mini_lex(text, pos)
        f, ln = pos
        if len(toks) < 4 or toks[1][0] != 'name':
            raise MiniLangError(f"{f}:{ln}: '.for' needs 'variable in range(...)' "
                                f"or 'variable in array'")
        var = toks[1][1]
        if toks[2] != ('name', 'in'):
            raise MiniLangError(f"{f}:{ln}: '.for {var}' must be followed by "
                                f"'in range(...)' or 'in array'")
        if toks[3] != ('name', 'range') or len(toks) < 5 or toks[4] != ('op', '('):
            return var, 'forin', _MiniExprParser(toks[3:], pos).parse()
        p = _MiniExprParser(toks[4:], pos)
        p.expect_op('(')
        args = p.arglist(')')
        if not p.at_end():
            raise MiniLangError(f"{f}:{ln}: unexpected text after 'range(...)'")
        if not 1 <= len(args) <= 3:
            raise MiniLangError(f"{f}:{ln}: range() takes 1 to 3 arguments, got {len(args)}")
        return var, 'for', args

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
                args = p.arglist(')')
                if not p.at_end():
                    raise MiniLangError(f"{f}:{ln}: unexpected text after '.emit(...)'")
                if not args:
                    raise MiniLangError(f"{f}:{ln}: '.emit' needs at least one value")
                return ('emit', args, pos)
            if v == '.ECHO':
                p = _MiniExprParser(toks[1:], pos)
                p.expect_op('(')
                items = p.arglist(')')
                if not p.at_end():
                    raise MiniLangError(f"{f}:{ln}: unexpected text after '.echo(...)'")
                return ('echo', items, pos)
            if v in ('.BREAK', '.CONTINUE'):
                low = v.translate(_ALOWER)
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
                    if j + 1 < len(toks) and toks[j + 1] != ('op', ','):
                        raise MiniLangError(f"{f}:{ln}: '.nonlocal' names must be "
                                            f"separated by ','")
                    j += 2
                if not names:
                    raise MiniLangError(f"{f}:{ln}: '.nonlocal' needs variable names")
                return ('nonlocal', names, pos)
            raise MiniLangError(f"{f}:{ln}: unknown statement {v.translate(_ALOWER)!r}")
        if k != 'name':
            raise MiniLangError(f"{f}:{ln}: statement must be a directive or an assignment")
        name = v
        p = _MiniExprParser(toks[1:], pos)
        idx = None
        if p.at_op('['):
            p.i += 1
            lo = None if p.at_op(':') else p.or_()
            if p.eat_op(':'):
                # `名前[lo:hi] = 値` は範囲の置き換え。
                hi = None if p.at_op(']') else p.or_()
                idx = ('slicetarget', lo, hi)
            else:
                idx = lo
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
        args = p.arglist(')')
        if not p.at_end():
            raise MiniLangError(f"{f}:{ln}: unexpected text after '.call'")
        return name, args


def _mini_err(pos, msg):
    """位置を添えたミニ言語のエラー（raise して使う）。"""
    return MiniLangError(f"{pos[0]}:{pos[1]}: {msg}")


_MINI_CMP = {'<': lambda a, b: a < b, '>': lambda a, b: a > b,
             '<=': lambda a, b: a <= b, '>=': lambda a, b: a >= b,
             '==': lambda a, b: a == b, '!=': lambda a, b: a != b}


class MiniInterp:
    """ミニ言語の評価器。`.call` から呼ばれて出力ワードを作る。

    チューリング完全なので、文の数・呼び出しの入れ子・出力ワード数・配列長の上限で
    止める（超えたらその行をエラーにする）。未定義ラベル由来の引数は 0 として渡る。
    パターン変数は使えない（必要なら `.call` の引数で渡す）。
    """

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
        self.fallback_names = set()

    @staticmethod
    def _is_arr(v):
        return isinstance(v, list)

    @staticmethod
    def _is_str(v):
        return isinstance(v, bytes)

    @classmethod
    def _copy(cls, v):
        """値を複製する（配列はコピー、文字列は共有）。"""
        if cls._is_arr(v):
            return list(v)
        return v if cls._is_str(v) else _mini_wrap(v)

    @classmethod
    def _echo_value(cls, v):
        """`.echo` に出す形（配列は `[1, "ab", 3]`、NUL は `\\0`）。caxx.c の mini_echo_text() と同じ。"""
        if cls._is_arr(v):
            return b'[' + b', '.join(
                b'"' + e.replace(b'\0', b'\\0') + b'"' if cls._is_str(e)
                else str(_mini_signed(e)).encode('ascii') for e in v) + b']'
        if cls._is_str(v):
            return v.replace(b'\0', b'\\0')
        return _mini_signed(v)

    @staticmethod
    def _echo_out(parts):
        """`.echo` の 1 行をバイト列のまま標準エラーへ（体裁はマクロ層の `!echo` と同じ）。"""
        line = b' '.join(x if isinstance(x, bytes) else _as_str(x).encode('utf-8')
                         for x in parts) + b'\n'
        sys.stderr.flush()
        buf = getattr(sys.stderr, 'buffer', None)
        if buf is None:
            sys.stderr.write(line.decode('utf-8', 'surrogateescape'))
        else:
            buf.write(line)
            buf.flush()

    def _need_int(self, v, pos, what):
        """整数を要求する（配列か文字列ならエラー）。"""
        if self._is_arr(v):
            raise _mini_err(pos, f"{what} must be a number, not an array")
        if self._is_str(v):
            raise _mini_err(pos, f"{what} must be a number, not a string")
        return _mini_wrap(v)

    def _need_elem(self, v, pos):
        """配列の要素にできる値（整数か文字列）を要求する。"""
        if self._is_arr(v):
            raise _mini_err(pos, "an array element must be a number or a string, not an array")
        return v if self._is_str(v) else _mini_wrap(v)

    def _need_strlen(self, n, pos):
        """作った文字列の長さを検査する（配列と同じ上限）。"""
        if n > self.MAX_ARRAY:
            raise _mini_err(pos, f"string longer than the maximum length {self.MAX_ARRAY}")

    def _text_of(self, v, pos):
        """`+` で文字列とつなぐ側を文字列に（整数は符号付き 10 進）。"""
        return v if self._is_str(v) else _mini_dec(self._need_int(v, pos, 'an operand'))

    _INT_DIGITS = {10: b'0123456789', 16: b'0123456789abcdefABCDEF', 2: b'01'}

    def _to_int(self, v, pos):
        """`.int(文字列)`（空白・符号・`0x` / `0b`・`_` を受ける）。caxx.c の mini_str_to_int() と同じ。"""
        if self._is_arr(v):
            raise _mini_err(pos, "'.int' needs a number or a string")
        if not self._is_str(v):
            return _mini_wrap(v)
        t = v.strip(b' \t')
        neg = t[:1] == b'-'
        if t[:1] in (b'+', b'-'):
            t = t[1:]
        base = {b'0x': 16, b'0X': 16, b'0b': 2, b'0B': 2}.get(t[:2], 10)
        if base != 10:
            t = t[2:]
        digits = self._INT_DIGITS[base]
        if not t or any(c not in digits and c != 0x5f for c in t) or all(c == 0x5f for c in t):
            raise _mini_err(pos, "'.int' cannot read the string as a number")
        x = int(t.replace(b'_', b'').decode('ascii'), base)
        return _mini_wrap(-x if neg else x)

    def _frame_for(self, name):
        """その名前を持つスコープ（`.nonlocal` なら外側へたどる。無ければ None）。"""
        top = self.frames[-1]
        if name not in top['nonlocal']:
            return top
        return next((fr for fr in reversed(self.frames[:-1]) if name in fr['vars']), None)

    def _core_eval(self, text, pos):
        """本体の式評価器に委ねる（ラベル・`$$`・`#記号`）。未定義由来の値は 0。"""
        if self.expr_eval is None:
            raise _mini_err(pos, f"{text!r} is not available here")
        v, _ = self.expr_eval.expression_caps(text, 0, CAPS_MINI)
        return 0 if _is_undef_derived(v) else _mini_wrap(v)

    def _core_name(self, name):
        """その名前が本体側（ラベル・シンボル・前回の反復の値）にあるか。"""
        st = self.state
        return st is not None and (name in st.labels or StringUtils.upper(name) in st.symbols
                                   or name in st.relax.relax_prev_values)

    def _get(self, name, pos):
        """変数を読む。無ければ本体側の名前として解決する。caxx.c の mini_get() と同じ。

        本体側にも無い名前を前方参照のラベルとして許すのは、パス1の最初の反復
        （と対話モード）だけ。それ以外は「設定前に使われた」エラー。
        """
        fr = self._frame_for(name)
        if fr is None:
            raise _mini_err(pos, f"'.nonlocal {name}' found no enclosing definition of {name!r}")
        if name in fr['vars']:
            return fr['vars'][name]
        st = self.state
        permissive = (st is not None and st.relax.pas != 2
                      and not (st.relax.pas == 1 and not st.relax.relax_optimistic)
                      and name not in st._mini_suspects)
        if self.expr_eval is not None and st is not None and (self._core_name(name) or permissive):
            if permissive and not self._core_name(name):
                self.fallback_names.add(name)
            return self._core_eval(name, pos)
        raise _mini_err(pos, f"{name!r} is used before it is set")

    def _set(self, name, value, pos):
        """変数へ代入する。"""
        fr = self._frame_for(name)
        if fr is None:
            raise _mini_err(pos, f"'.nonlocal {name}' found no enclosing definition of {name!r}")
        fr['vars'][name] = value

    def _seq(self, e, pos, what):
        """添字や範囲を取れる値（配列か文字列）を評価する。"""
        base = self.eval(e, pos)
        if not self._is_arr(base) and not self._is_str(base):
            raise _mini_err(pos, f"only an array or a string can be {what}")
        return base

    def _sint(self, e, pos, what):
        """式を評価して符号付きの整数にする。"""
        return _mini_signed(self._need_int(self.eval(e, pos), pos, what))

    def eval(self, e, pos):
        """式の構文木を評価する。"""
        k = e[0]
        if k in ('num', 'str'):
            return e[1]
        if k == 'core':
            return self._core_eval(e[1], pos)
        if k == 'var':
            return self._get(e[1], pos)
        if k == 'arr':
            return [self._need_elem(self.eval(x, pos), pos) for x in e[1]]
        if k == 'callexpr':
            fn = self._lookup(e[1], pos)
            ret = self.call(fn, [self.eval(a, pos) for a in e[2]], pos)
            if ret is None:
                raise _mini_err(pos, f"{e[1]!r} returned no value; give it a '.return <expression>'")
            return ret
        if k == 'len':
            v = self.eval(e[1], pos)
            if not self._is_arr(v) and not self._is_str(v):
                raise _mini_err(pos, "'.len' needs an array or a string")
            return _mini_wrap(len(v))
        if k == 'tostr':
            v = self.eval(e[1], pos)
            if self._is_arr(v):
                raise _mini_err(pos, "'.str' needs a number or a string")
            return v if self._is_str(v) else _mini_dec(v)
        if k == 'chr':
            c = self._sint(e[1], pos, "'.chr' argument")
            if c < 0 or c > 255:
                raise _mini_err(pos, "'.chr' needs a value from 0 to 255")
            return bytes((c,))
        if k == 'toint':
            return self._to_int(self.eval(e[1], pos), pos)
        if k == 'index':
            base = self._seq(e[1], pos, 'indexed')
            idx = self._sint(e[2], pos, 'an index')
            return base[idx] if 0 <= idx < len(base) else 0
        if k == 'slice':
            base = self._seq(e[1], pos, 'sliced')
            n = len(base)
            lo = 0 if e[2] is None else self._sint(e[2], pos, 'a slice bound')
            hi = n if e[3] is None else self._sint(e[3], pos, 'a slice bound')
            lo = max(0, min(lo, n))
            return base[lo:max(lo, min(hi, n))]
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
        raise _mini_err(pos, "bad expression")

    def _binop(self, e, pos):
        """二項演算（`/` と `%` は C と同じゼロ方向の切り捨て）。"""
        op = e[1]
        if op in ('&&', '||'):
            left = self._sint(e[2], pos, 'an operand') != 0
            if left == (op == '||'):
                return int(left)
            return 1 if self._sint(e[3], pos, 'an operand') != 0 else 0
        a = self.eval(e[2], pos)
        b = self.eval(e[3], pos)
        if self._is_str(a) or self._is_str(b):
            return self._str_binop(op, a, b, pos)
        a = self._need_int(a, pos, 'an operand')
        b = self._need_int(b, pos, 'an operand')
        sa, sb = _mini_signed(a), _mini_signed(b)
        if op == '+':
            return _mini_wrap(sa + sb)
        if op == '-':
            return _mini_wrap(sa - sb)
        if op == '*':
            return _mini_wrap(sa * sb)
        if op in ('/', '%'):
            if sb == 0:
                raise _mini_err(pos, "division by zero")
            if op == '/':
                q = abs(sa) // abs(sb)
                return _mini_wrap(-q if (sa < 0) != (sb < 0) else q)
            r = abs(sa) % abs(sb)
            return _mini_wrap(-r if sa < 0 else r)
        if op == '**':
            if sb < 0:
                raise _mini_err(pos, "negative exponent")
            return _mini_wrap(pow(sa, sb, 1 << _MINI_BITS))
        if op == '<<':
            return 0 if sb < 0 or sb >= _MINI_BITS else _mini_wrap(a << sb)
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
        return 1 if _MINI_CMP[op](sa, sb) else 0

    def _str_binop(self, op, a, b, pos):
        """片方でも文字列のときの二項演算。caxx.c の mini_str_binop() と同じ。

        `+` は連結（整数は 10 進にして）、`*` は繰り返し、`==` `!=` は種類も含めた一致、
        `<` などはバイト順の辞書式比較。
        """
        if op == '+':
            r = self._text_of(a, pos) + self._text_of(b, pos)
            self._need_strlen(len(r), pos)
            return r
        if op == '*':
            if self._is_str(a) and self._is_str(b):
                raise _mini_err(pos, "a string can only be repeated by a number")
            t, n = (a, b) if self._is_str(a) else (b, a)
            n = _mini_signed(self._need_int(n, pos, 'a repeat count'))
            if n <= 0:
                return b''
            self._need_strlen(len(t) * n, pos)
            return t * n
        if op in ('==', '!='):
            if self._is_arr(a) or self._is_arr(b):
                raise _mini_err(pos, "an operand must be a number, not an array")
            eq = self._is_str(a) and self._is_str(b) and a == b
            return 1 if eq == (op == '==') else 0
        if op in ('<', '<=', '>', '>='):
            if not (self._is_str(a) and self._is_str(b)):
                raise _mini_err(pos, "cannot order a string against a number")
            return 1 if _MINI_CMP[op](a, b) else 0
        raise _mini_err(pos, f"an operand of '{op}' must be a number, not a string")

    def _bound(self, e, default, pos):
        """切り出しの境界を 1 つ読む（省略なら default）。"""
        return default if e is None else self._sint(e, pos, 'a slice bound')

    def _store_slice(self, name, lo_e, hi_e, v, pos):
        """`名前[lo:hi] = 値` — lo から hi の手前を置き換える（境界は切り詰め、`lo == hi` は挿入）。

        文字列には文字列を、配列には配列を書く。caxx.c の mini_store_slice() と同じ規則である。
        """
        lo = self._bound(lo_e, None, pos)
        hi = self._bound(hi_e, None, pos)
        cur = self._get(name, pos)
        if not self._is_arr(cur) and not self._is_str(cur):
            raise _mini_err(pos, f"{name!r} is not an array or a string")
        n = len(cur)
        lo = 0 if lo is None else max(0, min(lo, n))
        hi = n if hi is None else max(lo, min(hi, n))
        if self._is_str(cur):
            if not self._is_str(v):
                raise _mini_err(pos, "a string slice can only be given a string")
            r = cur[:lo] + v + cur[hi:]
            self._need_strlen(len(r), pos)
        else:
            if not self._is_arr(v):
                raise _mini_err(pos, "an array slice can only be given an array")
            r = cur[:lo] + list(v) + cur[hi:]
            if len(r) > self.MAX_ARRAY:
                raise _mini_err(pos, f"array longer than the maximum length {self.MAX_ARRAY}")
        self._set(name, r, pos)

    def _store(self, name, idx, v, pos):
        """変数か配列要素へ代入する（配列は上限まで伸ばす）。caxx.c の mini_store() と同じ。

        文字列の 1 バイトには 0〜255 の整数か 1 バイトの文字列を書き、末尾より先なら NUL で伸ばす。
        """
        if idx is None:
            self._set(name, self._copy(v), pos)
            return
        if idx[0] == 'slicetarget':
            self._store_slice(name, idx[1], idx[2], v, pos)
            return
        i = self._sint(idx, pos, 'an index')
        if i < 0:
            raise _mini_err(pos, f"negative index {i} in assignment")
        if i >= self.MAX_ARRAY:
            raise _mini_err(pos, f"array index {i} exceeds the maximum length {self.MAX_ARRAY}")
        elem = self._need_elem(v, pos)
        arr = self._get(name, pos)
        if self._is_str(arr):
            if self._is_str(elem):
                b = elem[0] if len(elem) == 1 else -1
            else:
                b = _mini_signed(elem)
            if not 0 <= b <= 255:
                raise _mini_err(pos, "a byte of a string must be a value from 0 to 255 or a one-byte string")
            if i >= len(arr):
                arr = arr + b'\0' * (i + 1 - len(arr))
            self._set(name, arr[:i] + bytes((b,)) + arr[i + 1:], pos)
            return
        if not self._is_arr(arr):
            raise _mini_err(pos, f"{name!r} is not an array or a string")
        if i >= len(arr):
            arr.extend([0] * (i + 1 - len(arr)))
        arr[i] = elem

    def _tick(self, pos):
        """実行した文を 1 つ数え、上限を超えたらエラー。caxx.c の mini_tick() と同じ。

        パス1の最初の反復で超えたら、前方参照として許した名前を綴り間違いの疑いとして覚える。
        """
        self.steps += 1
        if self.steps > self.MAX_STEPS:
            st = self.state
            if st is not None and st.relax.pas == 1 and st.relax.relax_optimistic:
                st._mini_suspects.update(self.fallback_names)
            raise _mini_err(pos, f"mini language ran more than {self.MAX_STEPS} statements; "
                                 f"assuming a runaway loop")

    def exec_block(self, body):
        """文の並びを順に実行する。"""
        for st in body:
            self._exec(st)

    def _loop_body(self, body):
        """ループの本体を 1 回実行する（`.break` なら偽）。"""
        try:
            self.exec_block(body)
        except _MiniContinue:
            pass
        except _MiniBreak:
            return False
        return True

    def _reporting(self):
        """`.raise` / `.echo` を出してよいか。"""
        st = self.state
        return st is not None and st.should_report_errors() and not st.relax.pass1_size_mode

    def _invoke(self, fname, args, pos, need_value):
        """関数を名前で探して呼ぶ。need_value なら値の無い戻りをエラーにする。"""
        fn = self._lookup(fname, pos)
        ret = self.call(fn, [self.eval(a, pos) for a in args], pos)
        if need_value and ret is None:
            raise _mini_err(pos, f"{fname!r} returned no value; give it a '.return <expression>'")
        return ret

    def _exec(self, st):
        """文 1 個を実行する。"""
        kind = st[0]
        pos = st[-1]
        self._tick(pos)
        if kind == 'assign':
            _, name, idx, val, _ = st
            self._store(name, idx, self.eval(val, pos), pos)
        elif kind == 'callassign':
            _, name, idx, fname, args, _ = st
            self._store(name, idx, self._invoke(fname, args, pos, True), pos)
        elif kind == 'emit':
            for x in st[1]:
                v = self.eval(x, pos)
                # 文字列は 1 バイト 1 ワード、配列は要素ごと（caxx.c の MS_EMIT と同じ）。
                if self._is_arr(v):
                    ws = [w for e in v for w in (e if self._is_str(e) else (e,))]
                elif self._is_str(v):
                    ws = v
                else:
                    ws = (v,)
                for w in ws:
                    if len(self.out) >= self.MAX_EMIT:
                        raise _mini_err(pos, f"'.emit' produced more than {self.MAX_EMIT} words")
                    self.out.append(w)
        elif kind == 'raise':
            v = self.eval(st[1], pos)
            if self._is_arr(v) or self._is_str(v):
                raise _mini_err(pos, "'.raise' needs a number, not "
                                     + ("an array" if self._is_arr(v) else "a string"))
            if self._reporting():
                lo = int(v) & 0xFFFFFFFFFFFFFFFF
                code = lo - (1 << 64) if lo >> 63 else lo
                print(f"Line {self.state.ln} Error code {code} ", end="", file=sys.stderr)
                if 0 <= code < len(self.state.errors):
                    print(f"{self.state.errors[code]}", end='', file=sys.stderr)
                print(": ", file=sys.stderr)
                self.state.had_error = True
        elif kind == 'echo':
            parts = [self._echo_value(self.eval(x, pos)) for x in st[1]]
            if self._reporting():
                self._echo_out(parts)
        elif kind == 'call':
            self._invoke(st[1], st[2], pos, False)
        elif kind == 'break':
            raise _MiniBreak()
        elif kind == 'continue':
            raise _MiniContinue()
        elif kind == 'return':
            raise _MiniReturn(None if st[1] is None else self.eval(st[1], pos))
        elif kind == 'nonlocal':
            top = self.frames[-1]
            for nm in st[1]:
                if nm in top['vars']:
                    raise _mini_err(pos, f"{nm!r} is already local; '.nonlocal' must come before it is set")
                top['nonlocal'].add(nm)
        elif kind == 'if':
            _, cond, then_b, else_b, _ = st
            self.exec_block(then_b if self._sint(cond, pos, 'a condition') != 0 else else_b)
        elif kind == 'while':
            _, cond, body, _ = st
            while self._sint(cond, pos, 'a condition') != 0:
                self._tick(pos)
                if not self._loop_body(body):
                    break
        elif kind == 'for':
            _, var, args, body, _ = st
            vs = [self._sint(a, pos, 'a range bound') for a in args]
            start, stop, step = (0, vs[0], 1) if len(vs) == 1 else \
                (vs[0], vs[1], 1) if len(vs) == 2 else vs
            if step == 0:
                raise _mini_err(pos, "range() step must not be zero")
            i = start
            while (i < stop) if step > 0 else (i > stop):
                self._tick(pos)
                self._set(var, _mini_wrap(i), pos)
                if not self._loop_body(body):
                    break
                i += step
        elif kind == 'forin':
            _, var, expr, body, _ = st
            arr = self.eval(expr, pos)
            if not self._is_arr(arr):
                raise _mini_err(pos, f"'.for {var} in' needs an array")
            # 写しを回るので、本体で配列を書き換えても順番は変わらない。
            for elem in list(arr):
                self._tick(pos)
                self._set(var, self._copy(elem), pos)
                if not self._loop_body(body):
                    break
        else:
            raise _mini_err(pos, "bad statement")

    def _lookup(self, name, pos):
        """呼び出す関数を名前で探す（内側の定義から外側へ）。"""
        fn = self.frames[-1]['func'] if self.frames else None
        while fn is not None:
            if name in fn.children:
                return fn.children[name]
            fn = fn.parent
        fn = self.state.func_defs.get(name)
        if fn is None:
            raise _mini_err(pos, f"no function named {name!r}")
        return fn

    def call(self, func, args, pos):
        """関数を 1 回呼ぶ（新しいスコープを積み、入れ子の深さを検査する）。"""
        if len(self.frames) >= self.MAX_DEPTH:
            raise _mini_err(pos, f"call nesting deeper than {self.MAX_DEPTH}; assuming runaway recursion")
        if len(args) != len(func.params):
            raise _mini_err(pos, f"{func.name!r} takes {len(func.params)} argument(s), got {len(args)}")
        self.frames.append({'vars': {nm: self._copy(v) for nm, v in zip(func.params, args)},
                            'nonlocal': set(), 'func': func})
        try:
            self.exec_block(func.body or [])
        except _MiniReturn as r:
            return r.value
        finally:
            self.frames.pop()
        return None

    def run(self, func, args, pos):
        """`.call` の入口。関数を走らせ、(出力ワードの並び, 戻り値) を返す。"""
        self.out = []
        self.steps = 0
        self.frames = []
        self.fallback_names = set()
        ret = self.call(func, args, pos)
        return self.out, ret


_TXT_ESCAPES = {'n': '\n', 't': '\t', 'r': '\r', '\\': '\\', '"': '"'}
_ASMTEXT_SHOW = {'\n': '\\n', '\t': '\\t', '\r': '\\r', '\\': '\\\\', '"': '\\"'}


def asmtext_escaped(s):
    """テキストを 1 行の診断に収まる形にエスケープする（改行を `\\n` に）。"""
    return ''.join(_ASMTEXT_SHOW.get(c, c) for c in s)


def _dq_end(s, i):
    """s[i] の `"` から始まる文字列の閉じ `"` の直後（閉じなければ末尾）。中の `\\` は次を逃がす。"""
    n = len(s)
    j = i + 1
    while j < n:
        if s[j] == '\\' and j + 1 < n:
            j += 2
        elif s[j] == '"':
            return j + 1
        else:
            j += 1
    return n


class ObjectGenerator:
    """binary_list（出力欄）からその行のワード列を作る。

    要素はカンマ区切りで、数値式・文字列テンプレート `"..."`・繰り返し `@@[n,...]`・
    ミニ言語の `.call f(...)`。頭の `;` は値が 0 なら出さず、`;;` は評価だけ、空要素は整列。
    """

    def __init__(self, state, expr_eval, binary_writer):
        self.state = state
        self.expr_eval = expr_eval
        self.binary_writer = binary_writer

    def replace_percent_with_index(self, s):
        """`%%` を繰り返しの番号に、`%0` でその番号を 0 に戻す（文字列の中は触らない）。"""
        count = 0
        result = []
        i = 0
        while i < len(s):
            if s[i] == '"':
                j = _dq_end(s, i)
                result.append(s[i:j])
                i = j
            elif s.startswith('%%', i):
                result.append(str(count))
                count += 1
                i += 2
            elif s.startswith('%0', i):
                count = 0
                i += 2
            else:
                result.append(s[i])
                i += 1
        return ''.join(result)

    def e_p(self, pattern):
        """`@@[n, 中身]` の繰り返しを展開する。返り値は (展開後, 中身が空か)。"""
        result = []
        has_content = False
        i = 0
        n_pat = len(pattern)
        while i < n_pat:
            if pattern.startswith('@@[', i):
                i += 3
                depth = 1
                expr_start = i
                comma_pos = -1
                while i < n_pat and depth > 0:
                    c = pattern[i]
                    if c == '"':
                        i = _dq_end(pattern, i)
                        continue
                    if c == '[':
                        depth += 1
                    elif c == ']':
                        depth -= 1
                        if depth == 0:
                            break
                    elif c == ',' and depth == 1 and comma_pos == -1:
                        comma_pos = i
                    i += 1
                if comma_pos < 0:
                    self.state.diag(" error - @@[...]: missing ',' separating count and pattern.", set_error=True)
                    result.append('@@[')
                    has_content = True
                    continue
                st = self.state
                prior = st.error_undefined_label
                st.error_undefined_label = False
                n, _idx = self.expr_eval.expression_pat(pattern[expr_start:comma_pos], 0)
                rep_undef = st.error_undefined_label
                st.error_undefined_label = prior or rep_undef
                if rep_undef or _is_undef_derived(n):
                    n = 0
                try:
                    n_int = int(n)
                except (ValueError, OverflowError):
                    n_int = 0
                if n_int > 1 << 24:
                    st.diag(f" error - @@[n,...]: repeat count {n_int} exceeds maximum {1 << 24}.", set_error=True)
                    n_int = 0
                if n_int > 0:
                    has_content = True
                    expanded_rep, _ = self.e_p(pattern[comma_pos + 1:i])
                    result.append(','.join([expanded_rep] * n_int))
                i += 1
            elif pattern[i] == '"':
                j = _dq_end(pattern, i)
                result.append(pattern[i:j])
                has_content = True
                i = j
            else:
                result.append(pattern[i])
                has_content = True
                i += 1
        return ''.join(result), not has_content

    def _mini_diag(self, msg):
        """ミニ言語からのエラーを診断として出す。"""
        if not self.state.relax.pass1_size_mode:
            self.state.diag(msg, set_error=True)

    @staticmethod
    def _mini_close(s, k):
        """s[k] の開き括弧に対応する閉じ括弧の位置（`"..."` は飛ばす）。返り値は (位置, 深さ)。"""
        depth = 0
        while k < len(s) and s[k] != chr(0):
            if s[k] == '"':
                k = ObjectGenerator._mini_skip_str(s, k)
                continue
            if s[k] in '([':
                depth += 1
            elif s[k] in ')]':
                depth -= 1
                if depth == 0:
                    break
            k += 1
        return k, depth

    def _mini_args(self, tz, name, in_array):
        """NUL で終わる tz をカンマ区切りの引数の並びとして読む（失敗は None）。"""
        out = []
        a = 0
        while True:
            a = StringUtils.skipspc(tz, a)
            if a >= len(tz) or tz[a] == chr(0):
                break
            if tz[a] == ',':
                a += 1
                continue
            v, a = self._mini_arg_one(tz, a, name, in_array)
            if v is None:
                return None
            out.append(v)
            a = StringUtils.skipspc(tz, a)
            if a < len(tz) and tz[a] == ',':
                a += 1
                continue
            break
        return out

    def mini_call(self, s, idx):
        """`.call 名前(引数, ...)` を実行し、生まれたワード列を返す（引数はパターン層の式）。"""
        idx = StringUtils.skipspc(s, idx + 5)
        j = idx
        while j < len(s) and s[j] in _SYM_CORE:
            j += 1
        name = s[idx:j]
        idx = StringUtils.skipspc(s, j)
        if not name or idx >= len(s) or s[idx] != '(':
            self._mini_diag(" error - '.call' needs 'name(argument, ...)'.")
            return [], len(s)
        k, depth = self._mini_close(s, idx)
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
        args = self._mini_args(arg_text + chr(0), name, False)
        if args is None:
            return [], idx
        saved_reclimit = sys.getrecursionlimit()
        if saved_reclimit < _MINI_RECLIMIT:
            sys.setrecursionlimit(_MINI_RECLIMIT)
        try:
            words, ret = MiniInterp(self.state, self.expr_eval).run(fn, args, (fn.file, fn.line))
        except MiniLangError as e:
            self._mini_diag(f" error - {e}")
            return [], idx
        except RecursionError:
            self._mini_diag(f" error - '.call {name}': expression nesting too deep.")
            return [], idx
        finally:
            sys.setrecursionlimit(saved_reclimit)
        if ret is not None:
            # 配列は要素ごとに、文字列（の要素）は 1 バイト 1 ワードで出す。
            if isinstance(ret, list):
                ret = [w for e in ret for w in (e if isinstance(e, bytes) else (e,))]
            words = words + (list(ret) if isinstance(ret, (list, bytes)) else [ret])
        return words, idx

    @staticmethod
    def _mini_skip_str(s, k):
        """s[k] の `"` から始まる文字列の次の位置（閉じなければ行末）。caxx.c の mini_skip_str()。"""
        k += 1
        while k < len(s) and s[k] != chr(0):
            if s[k] == '\\' and k + 1 < len(s):
                k += 2
            elif s[k] == '"':
                return k + 1
            else:
                k += 1
        return k

    @staticmethod
    def _mini_is_call(t, a, kw, word_chars):
        """t[a] から `kw(`（大文字小文字は問わない。kw の直後が語の続きなら別の名前）が始まるか。"""
        k = a + len(kw)
        if StringUtils.upper(t[a:k]) != kw or (k < len(t) and t[k] in word_chars):
            return False
        k = StringUtils.skipspc(t, k)
        return k < len(t) and t[k] == '('

    @staticmethod
    def _mini_is_islabel(t, a):
        return ObjectGenerator._mini_is_call(t, a, '.ISLABEL', _ISLABEL_ALNUM | {'_'})

    @staticmethod
    def _mini_is_exp(t, a):
        return ObjectGenerator._mini_is_call(t, a, '.EXP', _SYM_CORE)

    def _captext_has_label(self, txt):
        """綴りがラベル（再配置を持たない `.equ` は除く）か未定義の名前を含むか。caxx.c の captext_has_label()。"""
        st = self.state
        for w in _captext_words(txt, st.lwordchars):
            le = st.labels.get(w)
            if le is not None:
                if not (len(le) > 2 and le[2]) or (len(le) > 4 and le[4] is not None):
                    return True
            elif StringUtils.upper(w) not in st.symbols:
                return True
        return False

    def _mini_var_arg(self, t, a, kwlen, what, name):
        """`.islabel(変数)` / `.exp(変数)` の変数名を読む。返り値は (変数名, 次の位置) か (None, 末尾)。"""
        k = StringUtils.skipspc(t, a + kwlen) + 1
        e = t.find(')', k)
        nm = t[k:e].strip(' \t') if e >= 0 else ''
        if e < 0 or not nm or PatternMatcher._var_name_at(nm, 0) != len(nm):
            self._mini_diag(f" error - '.call {name}': '{what}' needs '{what}(variable)'.")
            return None, len(t)
        if nm not in self.state.varnames:
            self._mini_diag(f" error - '{nm}' is not a pattern variable; "
                            f"'{what}({nm})' needs '{nm}' captured in the "
                            f"instruction field.")
            return None, len(t)
        return nm, e + 1

    def _mini_arg_islabel(self, t, a, name):
        """`.islabel(変数)` — 捕捉した綴りがラベルを含めば 1。caxx.c の mini_arg_islabel() と同じ。"""
        nm, e = self._mini_var_arg(t, a, 8, '.islabel', name)
        if nm is None:
            return None, e
        return (1 if self._captext_has_label(self.state.vars_text.get(nm, '')) else 0), e

    def _mini_arg_exp(self, t, a, name):
        """`.exp(変数)` — 捕捉した綴りの文字列（`{{.exp(変数)}}` と同じ）。caxx.c の mini_arg_exp() と同じ。"""
        nm, e = self._mini_var_arg(t, a, 4, '.exp', name)
        if nm is None:
            return None, e
        return _mini_bytes(self.state.vars_text.get(nm, '')), e

    def _mini_symname_at(self, t, a, table):
        """t[a] からの引数が table のシンボル名 1 つだけ（後ろが `,` か終わり）なら (名前, 次の位置)。

        caxx.c の mini_symname_at() と同じ規則である。
        """
        k = a
        while k < len(t) and t[k] in _SYM_CORE:
            k += 1
        if k == a:
            return None
        e = StringUtils.skipspc(t, k)
        if e < len(t) and t[e] not in (',', chr(0)):
            return None
        key = StringUtils.upper(t[a:k])
        return (key, e) if key in table else None

    def _mini_strsym_at(self, t, a):
        """文字列シンボルの名前 1 つだけの引数か。"""
        return self._mini_symname_at(t, a, self.state.strsymbols)

    def _mini_arrsym_value(self, key, name):
        """配列シンボルを引数の配列に（数は整数、文字列は `"..."` と同じに逃げ記号を開く）。

        caxx.c の mini_arrsym_value() と同じ規則である。
        """
        out = []
        for it in self.state.arrsymbols[key]:
            if isinstance(it, str):
                v, _ = self._mini_arg_str('"' + it + '"' + chr(0), 0, name)
                if v is None:
                    return None
                out.append(v)
            else:
                out.append(_mini_wrap(0 if _is_undef_derived(it) else it))
        return out

    def _mini_arg_str(self, t, a, name):
        """`"..."` の引数を文字列に（逃げ記号は `\\\\` `\\"` `\\n` `\\t`）。caxx.c の mini_arg_str() と同じ。"""
        out = []
        k = a + 1
        while True:
            if k >= len(t) or t[k] == chr(0):
                self._mini_diag(f" error - '.call {name}': unterminated string "
                                f"in the argument list.")
                return None, len(t)
            c = t[k]
            if c == '"':
                return _mini_bytes(''.join(out)), k + 1
            if c == '\\':
                e = t[k + 1] if k + 1 < len(t) else chr(0)
                if e not in _MINI_ESC:
                    self._mini_diag(f" error - '.call {name}': unknown escape in a "
                                    f"string in the argument list.")
                    return None, len(t)
                out.append(_MINI_ESC[e])
                k += 2
            else:
                out.append(c)
                k += 1

    def _mini_arg_one(self, t, a, name, in_array):
        """`.call` の引数を 1 つ読む。返り値は (値, 次の位置)、失敗は (None, _)。caxx.c の mini_arg_one()。

        `[...]` 配列（配列の中には書けない）、`"..."` 文字列、`.exp(変数)`、`.islabel(変数)`、
        文字列シンボル・配列シンボルの名前 1 つ、それ以外はパターン層の式。
        """
        nested = f" error - '.call {name}': an array element cannot be an array."
        if t[a] == '[':
            if in_array:
                self._mini_diag(nested)
                return None, len(t)
            return self._mini_arg_array(t, a, name)
        if t[a] == '"':
            return self._mini_arg_str(t, a, name)
        if self._mini_is_exp(t, a):
            return self._mini_arg_exp(t, a, name)
        if self._mini_is_islabel(t, a):
            return self._mini_arg_islabel(t, a, name)
        hit = self._mini_strsym_at(t, a)
        if hit is not None:
            key, a = hit
            v, _ = self._mini_arg_str('"' + self.state.strsymbols[key] + '"' + chr(0), 0, name)
            return v, a
        hit = self._mini_symname_at(t, a, self.state.arrsymbols)
        if hit is not None:
            key, a = hit
            if in_array:
                self._mini_diag(nested)
                return None, len(t)
            return self._mini_arrsym_value(key, name), a
        v, a = self.expr_eval.expression_pat(t, a)
        return _mini_wrap(0 if _is_undef_derived(v) else v), a

    def _mini_arg_array(self, t, a, name):
        """`[e1, e2, ...]` の引数を配列に（要素の書き方は _mini_arg_one と同じ）。"""
        k, depth = self._mini_close(t, a)
        if depth != 0 or k >= len(t) or t[k] != ']':
            self._mini_diag(f" error - '.call {name}': unbalanced '[' in the "
                            f"argument list.")
            return None, len(t)
        out = self._mini_args(t[a + 1:k] + chr(0), name, True)
        return (None, len(t)) if out is None else (out, k + 1)

    _TXT_CONVS = (('float', 3), ('hex', 0), ('dec', 1), ('bin', 2))

    @staticmethod
    def _arr_split(q):
        """配列リテラルをトップレベルのカンマで項目に割る（文字列・入れ子の中では割らない）。"""
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
        """文字列テンプレートの外側のダブルクォートを外す（中の逃げ記号はそのまま）。"""
        i = 1
        while i < len(q):
            if q[i] == '\\' and i + 1 < len(q):
                i += 2
            elif q[i] == '"':
                break
            else:
                i += 1
        return q[1:i]

    _RADIX_FMT = {16: 'x', 10: 'd', 2: 'b'}

    @staticmethod
    def _txt_radix(v, radix):
        """値をその基数の数字だけで書く（未定義は `UNDEF`）。caxx.c の txt_radix() と同じ。"""
        if _undef(v):
            return 'UNDEF'
        n = int(v)
        return ('-' if n < 0 else '') + format(abs(n), ObjectGenerator._RADIX_FMT[radix])

    _TXT_FLOAT_PREC = 34

    @classmethod
    def _txt_float_parts(cls, neg, digits, exp10):
        """`.float` の出力を符号・数字列・指数から組み立てる。"""
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
            body = '%s.%se%s%02d' % (digits[0], frac, '-' if exp10 < 0 else '+', abs(exp10))
        return ('-' + body) if neg else body

    @classmethod
    def _txt_float(cls, v):
        """`{{.float(x)}}` — 有効数字 34 桁・偶数丸めの 10 進で書く（`16` は `16.0`、範囲外は指数形式）。"""
        if isinstance(v, float):
            if not math.isfinite(v):
                return 'nan' if v != v else ('inf' if v > 0 else '-inf')
            d = Context(prec=cls._TXT_FLOAT_PREC).create_decimal(Decimal(v))
        else:
            d = Context(prec=cls._TXT_FLOAT_PREC).create_decimal(Decimal(int(v)))
        sign, digits, dexp = d.as_tuple()
        digits = ''.join(str(x) for x in digits) or '0'
        return cls._txt_float_parts(sign == 1, digits, len(digits) - 1 + dexp)

    @staticmethod
    def _txt_close(s, i, o='(', c=')'):
        """i から数えて対応する閉じ括弧の位置（無ければ -1）。"""
        depth = 0
        while i < len(s):
            if s[i] == o:
                depth += 1
            elif s[i] == c:
                depth -= 1
                if depth == 0:
                    return i
            i += 1
        return -1

    @classmethod
    def _txt_conv_name(cls, s):
        """`{{ }}` の中の変換名（`.hex` `.dec` `.bin` `.float`）。返り値は (長さ, 種類) か (0, -1)。"""
        u = StringUtils.upper(s)
        for name, kind in cls._TXT_CONVS:
            if u.startswith(StringUtils.upper(name)) and s[len(name):len(name) + 1] == '(':
                return len(name), kind
        return 0, -1

    def _txt_emit_expr(self, parts, expr, kind, inner=None):
        """`{{ }}` の 1 個を評価してテキストとして積む（inner は診断に出す中身）。"""
        st = self.state
        saved_undef = st.error_undefined_label
        st.error_undefined_label = False
        st.expr_missing = False
        v, end = self.expr_eval.expression_pat(expr, 0)
        _pat_missing(st, 'text template', expr[:end])
        _pat_trailing(st, 'text template',
                      "the expression in '{{%s}}'" % (expr if inner is None else inner), expr, end)
        st.error_undefined_label = saved_undef or st.error_undefined_label
        if _undef(v):
            parts.append('UNDEF')
        elif kind == 3:
            parts.append(self._txt_float(v))
        else:
            parts.append(self._txt_radix(v, {0: 16, 2: 2}.get(kind, 10)))

    def _txt_render(self, s):
        """文字列テンプレートを展開する（置き換えるのは `{{ }}` の中だけ）。

        単独の名前は 文字列シンボル → 配列シンボル → 式 の順で解く（数値の `.setsym` は
        式としてしか引かないので、ただの単語が数値に化けない。欲しいときは `{{#NAME}}`）。
        """
        parts = []
        i = 0
        st = self.state
        while i < len(s):
            c = s[i]
            if c == '\\' and i + 1 < len(s):
                parts.append(_TXT_ESCAPES.get(s[i + 1], s[i + 1]))
                i += 2
                continue
            e = s.find('}}', i + 2) if s.startswith('{{', i) else -1
            if e < 0:
                parts.append(c)
                i += 1
                continue
            inner = s[i + 2:e]
            i = e + 2
            j = len(inner) - len(inner.lstrip(' '))
            if inner[j:j + 1] == '.':
                rest = inner[j + 1:]
                en = self._txt_exp_call(rest)
                if en is not None:
                    parts.append(self._txt_exp_text(en))
                    continue
                nm, ix = self._txt_index_call(rest)
                if nm is not None:
                    parts.append(self._txt_index_text(nm, ix))
                    continue
                nl, kind = self._txt_conv_name(rest)
                if nl:
                    cp = self._txt_close(inner, j + 1 + nl)
                    if cp > 0:
                        self._txt_emit_expr(parts, inner[j + 2 + nl:cp], kind, inner)
                        _pat_trailing(st, 'text template',
                                      "'%s' in '{{%s}}'" % (inner[j:cp + 1], inner), inner, cp + 1)
                        continue
            nm, ix = self._txt_bare_indexed(inner)
            if nm is not None:
                parts.append(self._txt_indexed_text(nm, ix))
                continue
            bare = self._txt_bare_name(inner)
            if bare is not None and (bare in st.strsymbols or bare in st.arrsymbols):
                parts.append(self._txt_name_text(bare))
                continue
            self._txt_emit_expr(parts, inner, -1)
        return ''.join(parts)

    _IDENT_RE = re.compile(r'[A-Za-z_][A-Za-z0-9_]*')

    @classmethod
    def _txt_bare_indexed(cls, inner):
        """`{{名前[式]}}` の形なら (名前, 添字の綴り)、違えば (None, None)。"""
        t = inner.strip()
        m = cls._IDENT_RE.match(t) if t.isascii() else None
        if m is None:
            return None, None
        i = m.end()
        while i < len(t) and t[i] in ' \t':
            i += 1
        if i >= len(t) or t[i] != '[':
            return None, None
        cb = cls._txt_close(t, i, '[', ']')
        if cb < 0 or t[cb + 1:].strip() != '':
            return None, None
        return m.group(), t[i + 1:cb]

    @staticmethod
    def _txt_bare_name(inner):
        """`{{名前}}` の形ならその名前（大文字）。"""
        t = inner.strip()
        if not t.isascii() or not ObjectGenerator._IDENT_RE.fullmatch(t):
            return None
        return StringUtils.upper(t)

    def _txt_name_text(self, name):
        """`{{名前}}` を解決してテキストにする。"""
        st = self.state
        key = StringUtils.upper(name)
        if key in st.strsymbols:
            return st.strsymbols[key]
        if key in st.arrsymbols:
            return ','.join(v if isinstance(v, str) else self._txt_radix(v, 10)
                            for v in st.arrsymbols[key])
        v = name.translate(_ALOWER)
        if v == name and v in st.varnames:
            return self._txt_radix(st.vars.get(v, VAR_UNDEF), 10)
        return name

    def _txt_array_key(self, name, form):
        """配列シンボルの名前を大文字に（配列でなければ診断して None）。"""
        key = StringUtils.upper(name)
        if key not in self.state.arrsymbols:
            self.state.diag(f" error - '{key}' is not an array symbol; "
                            f"'{form % key}' needs '.setsym::{key}::[...]'.",
                            set_error=True)
            return None
        return key

    def _txt_indexed_text(self, name, idxtext):
        """`{{配列[添字]}}` を解決してテキストにする。"""
        key = self._txt_array_key(name, '%s[...]')
        n = None if key is None else self._arr_index_of(key, idxtext)
        if n is None:
            return ''
        it = self.state.arrsymbols[key][n]
        return it if isinstance(it, str) else self._txt_radix(it, 10)

    @classmethod
    def _txt_paren_arg(cls, s, kw, need_paren):
        """`{{.kw 引数}}` / `{{.kw(引数)}}` の引数の綴り（形が違えば None）。"""
        if StringUtils.upper(s[:len(kw)]) != kw:
            return None
        rest = s[len(kw):]
        if rest[:1] not in (' ', '\t', '('):
            return None
        rest = rest.strip()
        if rest[:1] != '(':
            return None if need_paren else rest
        cp = cls._txt_close(rest, 0)
        if cp < 0 or rest[cp + 1:].strip() != '':
            return None
        return rest[1:cp]

    @classmethod
    def _txt_index_call(cls, s):
        """`{{.index 名前[添字]}}` と `{{.index(名前[添字])}}` を読む。"""
        rest = cls._txt_paren_arg(s, 'INDEX', False)
        return (None, None) if rest is None else cls._txt_bare_indexed(rest)

    def _txt_index_text(self, name, idxtext):
        """`{{.index 配列[添字]}}` — 添字そのものを 10 進で書く（名前から番号を引く）。"""
        key = self._txt_array_key(name, '.index %s[...]')
        n = None if key is None else self._arr_index_of(key, idxtext)
        return '' if n is None else self._txt_radix(n, 10)

    @classmethod
    def _txt_exp_call(cls, s):
        """`{{.exp(変数)}}` の変数名（形が違えば None）。"""
        nm = cls._txt_paren_arg(s, 'EXP', True)
        if nm is None:
            return None
        nm = nm.strip()
        return nm if nm and PatternMatcher._var_name_at(nm, 0) == len(nm) else None

    def _txt_exp_text(self, name):
        """`{{.exp(変数)}}` — 変数が捕捉した綴りをソースに書かれていたまま出す。"""
        if name not in self.state.varnames:
            self.state.diag(f" error - '{name}' is not a pattern variable; "
                            f"'.exp({name})' needs '{name}' captured in the "
                            f"instruction field.", set_error=True)
            return ''
        return self.state.vars_text.get(name, '')

    @staticmethod
    def _txt_quoted_text(t):
        """添字に書かれた文字列リテラルを中身に開く（`arrb["CX"]` は `arrb[CX]` と同じ）。"""
        delim = '\\"' if t.startswith('\\"') else '"' if t.startswith('"') else None
        if delim is None:
            return None
        out = []
        i = len(delim)
        while i < len(t):
            if t.startswith(delim, i):
                return ''.join(out) if t[i + len(delim):].strip() == '' else None
            if t[i] == '\\' and i + 1 < len(t):
                out.append(_TXT_ESCAPES.get(t[i + 1], t[i + 1]))
                i += 2
            else:
                out.append(t[i])
                i += 1
        return None

    def _arr_index_of(self, key, idxtext):
        """配列の添字を整数にする。

        文字列シンボルの名前（中身を読み直す）→ パターン変数 → その配列の項目名 →
        同名の数値シンボル → 式 の順。
        """
        st = self.state
        arr = st.arrsymbols[key]
        t = (idxtext or '').strip()
        q = self._txt_quoted_text(t)
        if q is not None:
            t = q.strip()
        nm = self._txt_bare_name(t)
        if nm is not None and nm in st.strsymbols:
            t = st.strsymbols[nm].strip()
            nm = self._txt_bare_name(t)
        v = t.translate(_ALOWER)
        if nm is not None and not (v == t and v in st.varnames):
            for k, it in enumerate(arr):
                if isinstance(it, str) and StringUtils.upper(it) == nm:
                    return k
            if nm in st.symbols:
                return self._arr_index_check(key, arr, st.symbols[nm])
        saved_undef = st.error_undefined_label
        st.error_undefined_label = False
        v, _ = self.expr_eval.expression_pat(t, 0)
        st.error_undefined_label = saved_undef or st.error_undefined_label
        return self._arr_index_check(key, arr, v)

    def _arr_index_check(self, key, arr, v):
        """添字が範囲内か（範囲外は報告、未定義は報告済みなので黙って None）。caxx.c の txt_arr_index_check()。"""
        if _undef(v):
            return None
        try:
            n = int(v)
        except (OverflowError, ValueError, TypeError):
            n = -1
        if n < 0 or n >= len(arr):
            self.state.diag(f" error - index {n} is out of range for array symbol "
                            f"'{key}' (0..{len(arr) - 1}).", set_error=True)
            return None
        return n

    def _drop_refs_at(self, wi):
        """出力ワード wi について積んだラベル参照を捨てる（出さない要素の分）。"""
        e = self.state.elf
        e.label_refs_seen = [r for r in e.label_refs_seen if r[2] != wi]

    def makeobj(self, s):
        """binary_list を評価してその行のワード列を返す。

        先に `@@[]` と `%%` を展開し、カンマで 1 要素ずつ見る。`"..."` はテキスト
        テンプレート（UTF-8 の 1 バイトが 1 ワード、幅を超えるバイトは警告して切る）、
        `.call` はミニ言語、ほかは式。`;` 付きは値が 0（文字列なら空）のとき飛ばし、
        `;;` 付きは評価して捨てる。
        """
        st = self.state
        e = st.elf
        txtacc = []
        dispacc = []
        s, z = self.e_p(s)
        s = self.replace_percent_with_index(s) + chr(0)
        idx = 0
        objl = []
        if z:
            return objl
        st._in_binary_list = True
        prior_undef = st.error_undefined_label
        st.error_undefined_label = False
        try:
            while idx < len(s) and s[idx] != chr(0):
                if s[idx] == ',':
                    idx += 1
                    continue
                semicolon = drop = False
                if s[idx] == ';':
                    semicolon = True
                    idx += 1
                    if idx < len(s) and s[idx] == ';':
                        drop = True
                        idx += 1
                qs = StringUtils.skipspc(s, idx)
                if qs < len(s) and s[qs] == '"':
                    src = s[qs:].split(chr(0), 1)[0]
                    txt = self._txt_render(self._txt_template_inner(src))
                    if not (drop or (semicolon and txt == '')):
                        mask = (1 << st.bts) - 1 if st.bts > 0 else 0xFF
                        vals = list(txt.encode('utf-8', errors='surrogateescape'))
                        if (any(v > mask for v in vals) and not st.relax.pass1_size_mode
                                and st.should_report_errors()):
                            st.diag(f" warning - text template: one or more bytes exceed "
                                    f"the output word width ({st.bts} bit(s)) and were "
                                    f"truncated (high bits discarded): {txt!r}", set_error=False)
                        objl += vals
                        txtacc.append(txt)
                        dispacc.append('"%s"' % asmtext_escaped(txt))
                    closed = False
                    idx = qs + 1
                    while idx < len(s) and s[idx] != chr(0):
                        if s[idx] == '\\' and idx + 1 < len(s):
                            idx += 2
                        elif s[idx] == '"':
                            idx += 1
                            closed = True
                            break
                        else:
                            idx += 1
                    if not closed and not st.relax.pass1_size_mode and st.should_report_errors():
                        st.diag(f" warning - unterminated string literal in pattern "
                                f"encoding field: {src!r}", set_error=False)
                    idx = StringUtils.skipspc(s, idx)
                elif StringUtils.upper(s[idx:idx + 5]) == '.CALL' and (
                        idx + 5 >= len(s) or s[idx + 5] not in _SYM_CORE):
                    e.current_word_idx = len(objl)
                    words, idx = self.mini_call(s, idx)
                    if drop or (semicolon and len(words) == 1 and words[0] == 0):
                        words = []
                    if not words:
                        wi = e.current_word_idx
                        self._drop_refs_at(wi)
                        e.insn_reloc_hint.pop(wi, None)
                        e.insn_reloc_hint.pop(('v', wi), None)
                    objl += words
                    e.current_word_idx = -1
                else:
                    e.current_word_idx = len(objl)
                    if st.relax.pas == 1:
                        st.relax.pass1_size_mode = True
                    el = idx
                    st.expr_missing = False
                    x, idx = self.expr_eval.expression_pat(s, idx)
                    _pat_missing(st, 'binary_list', s[el:idx])
                    if st.relax.pas == 1:
                        st.relax.pass1_size_mode = False
                        st.error_undefined_label = False
                    if not drop and (not semicolon or x != 0):
                        objl.append(x)
                    else:
                        self._drop_refs_at(e.current_word_idx)
                if idx < len(s) and s[idx] == ',':
                    idx += 1
                    continue
                _pat_trailing(st, 'binary_list', 'an element', s, idx)
                break
        finally:
            e.current_word_idx = -1
            st._in_binary_list = False
            if st.relax.pas == 1:
                st.relax.pass1_size_mode = False
            st.error_undefined_label = st.error_undefined_label or prior_undef
            if txtacc:
                st.asmtext = ''.join(txtacc)
                st.asmtext_disp = ','.join(dispacc)
        return objl


def _pat_trailing(state, what, after, text, idx, allowed=''):
    """パターンファイルの式の後ろに残った文字をエラーにする（黙って捨てない）。caxx.c の pat_trailing()。

    空白・タブ・NUL だけか、残りが allowed のどれかで始まるなら何もしない。
    """
    rest = text[idx:].replace(chr(0), '').strip(' \t')
    if not rest or rest[0] in allowed:
        return False
    state.diag(f" error - {what}: unexpected text after {after}: {rest!r}.", set_error=True)
    return True


def _pat_missing(state, what, text):
    """パターンファイルの式で因子が欠けていれば（`1+` `n|`）エラーにする。caxx.c の pat_missing()。"""
    if not state.expr_missing:
        return False
    state.expr_missing = False
    t = text.replace(chr(0), '').strip(' \t')
    state.diag(f" error - {what}: an operand is missing in the expression {t!r}.", set_error=True)
    return True


def _is_ident(t):
    """ASCII の識別子（英字か `_` で始まり、英数字と `_` が続く）か。"""
    return t.isascii() and ObjectGenerator._IDENT_RE.fullmatch(t) is not None


def bare_name_of(text):
    """欄が裸の名前 1 個だけならその綴り（大文字化しない）、違えば None。"""
    t = (text or '').strip()
    return t if _is_ident(t) else None


def arr_items_from_text(expr_eval, q):
    """`[...]` を配列シンボルの項目に（`"..."` と裸の名前は文字列、ほかは式の値、空は 0）。"""
    out = []
    for item in ObjectGenerator._arr_split(q):
        nm = None if item.startswith('"') else bare_name_of(item)
        if item.startswith('"'):
            out.append(ObjectGenerator._txt_template_inner(item))
        elif nm is not None:
            out.append(nm)
        else:
            out.append(expr_eval.expression_pat(item, 0)[0] if item else 0)
    return out


def split_top_commas(text):
    """トップレベルのカンマだけで割る（括弧・ブラケットの中では割らない）。"""
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
    """集合リストの 1 項目として読める名前なら大文字にして返す。"""
    t = t.strip()
    if not t or not t.isascii() or t[0] in DIGIT or ' ' in t or '\t' in t:
        return None
    return StringUtils.upper(t)


def set_items_dedupe(items):
    """順序を保ったまま重複を落とす。"""
    return list(dict.fromkeys(items))


def set_literal_from_text(state, text):
    """`r0,r1,r2`（2 項目以上）を集合として読む。集合の項目は展開し、名前でない項目があれば None。"""
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
    """集合式のオペランド（既存の集合を指す識別子だけ。`-&|` は名前にも現れるため）。"""
    t = t.strip()
    if not _is_ident(t):
        return None
    arr = state.arrsymbols.get(StringUtils.upper(t))
    return None if arr is None else set_items_dedupe(list(arr))


def set_expr_from_text(state, text):
    """集合式 `a&b` `a|b` `a^b` `a+b` `a-b` を左から右へ計算する（読めなければ None）。

    結果は毎回新しいリストなので `.setsym::a::a|b` のような自己参照も安全。
    """
    toks = re.split('([' + re.escape(SET_OPS) + '])', text)
    if len(toks) < 3:
        return None
    acc = _set_operand(state, toks[0])
    if acc is None:
        return None
    for k in range(1, len(toks) - 1, 2):
        op = toks[k]
        rhs = _set_operand(state, toks[k + 1])
        if rhs is None:
            return None
        if op == '&':
            acc = [x for x in acc if x in rhs]
        elif op in '|+':
            acc = acc + [x for x in rhs if x not in acc]
        elif op == '^':
            acc = [x for x in acc if x not in rhs] + [x for x in rhs if x not in acc]
        else:
            acc = [x for x in acc if x not in rhs]
    return acc


def symbol_set_from_text(state, dst_upper, value_field):
    """値欄を集合として解釈して配列シンボルにする（中身が変わったときだけ世代番号を進める）。"""
    items = set_expr_from_text(state, value_field)
    if items is None:
        items = set_literal_from_text(state, value_field)
    if items is None:
        return False
    if state.arrsymbols.get(dst_upper) != items:
        state.arrsymbols[dst_upper] = items
        state.arrgen += 1
    return True


def symbol_copy_from_name(state, dst_upper, value_field):
    """値欄が裸の名前のときの `.setsym`。

    配列・文字列シンボルなら独立したコピー、どちらでもなければその名前を持つ文字列シンボル。
    """
    t = bare_name_of(value_field)
    if t is None:
        return False
    src = StringUtils.upper(t)
    if src in state.arrsymbols:
        if src != dst_upper:
            state.arrsymbols[dst_upper] = list(state.arrsymbols[src])
            state.arrgen += 1
    elif src in state.strsymbols:
        if src != dst_upper:
            state.strsymbols[dst_upper] = state.strsymbols[src]
    else:
        state.strsymbols[dst_upper] = t
    return True


class VLIWProcessor:
    """VLIW / EPIC のバンドルを組み立てる（`!!` で結んだ命令をスロットに詰め、空きは NOP）。"""

    def __init__(self, state, expr_eval, binary_writer):
        self.state = state
        self.expr_eval = expr_eval
        self.binary_writer = binary_writer

    def vliwprocess(self, line, idxs, objl, flag, idx, lineassemble2_func):
        """1 バンドルを組み立てて出力する。

        各スロットを lineassemble2_func でアセンブルし、インデックスコードの並びで `EPIC::`
        を引いてテンプレートを決める（幅が正なら右端、負なら左端）。バイト順は `.bits` に従う。
        """
        st = self.state
        vl = st.vliw
        objs = [objl]
        idxlst = [idxs]
        vl.stop = 0
        while True:
            idx = StringUtils.skipspc(line, idx)
            c = line[idx] if idx < len(line) else ''
            if c == VLIW_STOP:
                idx += 1
                vl.stop = 1
            elif c == VLIW_SEP:
                idx += 1
                peek = line[idx:].lstrip()
                # 空のスロット（`ad!!`、`ad!! !!!!`）はエラー。
                if peek[:1] in ('', VLIW_SEP, VLIW_STOP):
                    st.diag(_VLIW_EMPTY_SLOT_MSG, set_error=True)
                    return False
                if peek.startswith('.'):
                    st.diag(" error - directives (e.g. .section/.endsection/.INCLUDE) "
                            "are not allowed inside VLIW slots (the packet's PC has not "
                            "advanced yet at this point in the packet).", set_error=True)
                    return False
                idxs, objl, flag, idx = lineassemble2_func(line, idx)
                if not flag:
                    return False
                objs.append(objl)
                idxlst.append(idxs)
            else:
                break

        if vl.templatebits == 0:
            vl.slotset = [[[0], "0"]]
        vbits = abs(vl.bits)
        tbits = abs(vl.templatebits)
        if vl.instbits == 0:
            st.diag(" error - vliwinstbits is zero; cannot compute instruction slots.", set_error=True)
            return False
        k = next((k for k in vl.slotset if list(k[0]) == list(idxlst) or vl.templatebits == 0), None)
        if k is None:
            st.diag(" error - No vliw instruction-set defined.", set_error=True)
            return False
        prior = st.error_undefined_label
        st.error_undefined_label = False
        x, _ = self.expr_eval.expression_pat(k[1], 0)
        if st.error_undefined_label and st.should_report_errors():
            st.had_error = True
        st.error_undefined_label = prior or st.error_undefined_label
        templ = x & ((1 << tbits) - 1)
        ibyte = (vl.instbits + 7) // 8
        noi = (vbits - tbits) // vl.instbits
        if noi <= 0:
            st.diag(f" error - .vliw: vliwtemplatebits ({vl.templatebits}) "
                    f"leaves no room for instruction slots in a {vbits}-bit packet "
                    f"(vliwinstbits={vl.instbits}).", set_error=True)
            return False
        values = [m for j in objs for m in j]
        target_len = ibyte * noi
        if len(values) > target_len:
            # 入りきらない命令は黙って落とさずにエラー（caxx.c と同じ）。
            st.diag(f" error - VLIW: the packet's instructions take {len(values)} "
                    f"byte(s) but its slots hold only {target_len}.", set_error=True)
            values = values[:target_len]
        else:
            full, rem = divmod(target_len - len(values), ibyte)
            values += vl.nop * full + (vl.nop + [0] * rem)[:rem]
        order = 'little' if st.endian == 'little' else 'big'
        r = 0
        for j in range(noi):
            chunk = bytes(b & 0xff for b in values[j * ibyte:(j + 1) * ibyte])
            vv = int.from_bytes(chunk.ljust(ibyte, b'\0'), order)
            r = (r << vl.instbits) | (vv & ((1 << vl.instbits) - 1))
        r &= (1 << vbits) - 1
        res = r | (templ << (vbits - tbits)) if vl.templatebits < 0 else (r << vl.templatebits) | templ
        if vbits < 8:
            self.binary_writer.outbin(st.pc, res & ((1 << vbits) - 1))
            st.pc += 1
        else:
            nb = (vbits + 7) // 8
            for cnt, b in enumerate((res & ((1 << (8 * nb)) - 1)).to_bytes(nb, order)):
                self.binary_writer.outbin(st.pc + cnt, b)
            st.pc += nb
        return True


class AssemblyDirectiveProcessor:
    """アセンブリソース側の組み込みディレクティブ（`DB` などはパターンファイルが定義する）。"""

    def __init__(self, state, expr_eval, binary_writer, label_manager, parser):
        self.state = state
        self.expr_eval = expr_eval
        self.binary_writer = binary_writer
        self.label_manager = label_manager
        self.parser = parser

    def labelc_processing(self, l, ll):
        """`.labelc` — ラベルに使える文字を増やす。"""
        if l.translate(_AUPPER) != '.LABELC':
            return False
        if ll:
            self.state.lwordchars = ALPHABET + DIGIT + ll
        return True

    def label_processing(self, l):
        """行頭の `label:` と `label: .equ 式[::型]` を処理し、残りの行を返す。

        `.equ` のラベルは（型が無ければ）再配置を持たない定数。
        """
        if l == "":
            return ""
        st = self.state
        label, idx = self.parser.get_label_word(l, 0)
        lidx = idx
        if not (label != "" and idx > 0 and l[idx - 1] == ':'):
            return l
        e, idx = StringUtils.get_param_to_spc(l, StringUtils.skipspc(l, idx))
        if e.translate(_AUPPER) != '.EQU':
            if self.label_manager.put_value(label, st.pc, st.current_section, is_equ=False) is False:
                return ""
            st.label_text = l[:lidx]
            return l[lidx:]
        reloc_type = None
        expr_part = l[idx:].strip(' \t')     # 落とすのはスペースとタブだけ（caxx.c と同じ）
        if '::' in expr_part:
            expr_part, rt_str = (p.strip(' \t') for p in expr_part.split('::', 1))
            rt_str = rt_str.translate(_ALOWER)
            reloc_type = _reloc_named(st, elf_machine_table(st), rt_str)
            if reloc_type is None:
                st.diag(f" warning - unknown reloctype '{rt_str}' in .EQU"
                        f" for machine {st.elf.machine}", set_error=False)
        st.error_undefined_label = False
        saved_mode = st.relax.pass1_size_mode
        if st.relax.pas == 1:
            st.relax.pass1_size_mode = True
        track = reloc_type is None
        if track:
            st._equ_sections_touched = set()
        try:
            u, equ_end = self.expr_eval.expression_asm(expr_part, 0)
        finally:
            st.relax.pass1_size_mode = saved_mode
            touched = st._equ_sections_touched
            st._equ_sections_touched = None
        if track and touched and len(touched) > 1 and st.should_report_errors():
            st.diag(f" warning - .EQU '{label}': expression combines labels from "
                    f"multiple sections ({', '.join(sorted(touched))}) without an "
                    f"explicit ::reloctype; the resulting constant assumes a specific "
                    f"section layout and will NOT be relocated by the linker.", set_error=False)
        if st.error_undefined_label and st.should_report_errors():
            st.diag(f" error - .EQU '{label}': expression contains undefined label.", set_error=True)
        self._dir_trailing(f".EQU '{label}'", expr_part, equ_end)
        self.label_manager.put_value(label, u, st.current_section, is_equ=True, reloc_type=reloc_type)
        if st.textmode:
            st.label_text = l[:lidx]
            return l[lidx:]
        return ""

    _STR_ESC1 = {'0': '\0', 't': '\t', 'n': '\n', 'r': '\r', '\\': '\\', '"': '"'}

    def _string_words(self, l2, idx):
        """l2[idx] の `"` から始まる文字列を出力ワードの値の列に読む。caxx.c の string_words() と同じ。

        `.ascii` / `.asciz` と `.db` で共通。エスケープは `\\0 \\t \\n \\r \\\\ \\"`・`\\xHH`・
        `\\uXXXX`・`\\UXXXXXXXX`、ほかの文字は UTF-8 のバイト。返り値は (値の列, 閉じ `"` の
        次の位置（閉じなければ None）, ワード幅を超えた値があったか, 誤りの文面か None)。
        """
        idx += 1
        mask = (1 << self.state.bts) - 1 if self.state.bts > 0 else 0xFF
        vals = []
        n = len(l2)
        while idx < n and l2[idx] != '"':
            e = l2[idx + 1:idx + 2] if l2[idx] == '\\' else ''
            if e in self._STR_ESC1 and e:
                vals.append(ord(self._STR_ESC1[e]))
                idx += 2
            elif e in ('x', 'X'):
                j = idx = idx + 2
                while idx < n and idx < j + 2 and l2[idx] in _HEXCHARS:
                    idx += 1
                if idx == j:
                    return (vals, idx, any(v > mask for v in vals),
                            f" error - '\\x' escape requires at least one hex digit in string: {l2!r}")
                vals.append(int(l2[j:idx], 16))
            elif e in ('u', 'U'):
                nd = 4 if e == 'u' else 8
                j = idx = idx + 2
                while idx < n and idx < j + nd and l2[idx] in _HEXCHARS:
                    idx += 1
                if idx - j != nd:
                    return (vals, idx, any(v > mask for v in vals),
                            f" error - '\\{e}' escape requires "
                            f"{nd} hex digits in string: {l2!r}")
                try:
                    vals.append(ord(chr(int(l2[j:idx], 16))))
                except (ValueError, OverflowError):
                    return (vals, idx, any(v > mask for v in vals),
                            f" error - invalid \\u/\\U escape in string: {l2!r}")
            else:
                vals.extend(l2[idx].encode('utf-8', errors='surrogateescape'))
                idx += 1
        trunc = any(v > mask for v in vals)
        return vals, (None if idx >= n else idx + 1), trunc, None

    def asciistr(self, l2):
        """`.ascii` / `.asciz` の文字列をバイト列にする。"""
        if l2 == '' or l2[0] != '"':
            return False
        st = self.state
        vals, idx, truncated, err = self._string_words(l2, 0)
        for v in vals:
            self.binary_writer.outbin(st.pc, v)
            st.pc += 1
        if err is not None:
            st.diag(err, set_error=False)
            return False
        if idx is None:
            st.diag(f" warning - unterminated string literal in .ASCII/.ASCIZ: {l2!r}", set_error=False)
        else:
            self._dir_trailing(".ASCII/.ASCIZ", l2, idx)
        if truncated and st.should_report_errors():
            st.diag(f" warning - .ASCII/.ASCIZ: one or more characters exceed the output word "
                    f"width ({st.bts} bit(s)) and were truncated (high bits discarded): "
                    f"{l2!r}", set_error=False)
        return True

    def export_processing(self, l1, l2):
        """`.export` / `.global` — ラベルを TSV / ELF へ出す指定（`名前::型` で型も付く）。"""
        if StringUtils.upper(l1) not in (".EXPORT", ".GLOBAL"):
            return False
        st = self.state
        if not st.should_report_errors():
            return True
        idx = 0
        l2 += chr(0)
        while idx < len(l2) and l2[idx] != chr(0):
            idx = StringUtils.skipspc(l2, idx)
            s, idx = self.parser.get_label_word(l2, idx)
            if s == "":
                break
            rt_str, idx = self._type_suffix(l2, idx)
            if rt_str:
                rtype = _reloc_named(st, elf_machine_table(st), rt_str)
                if rtype is None:
                    st.diag(f" warning - unknown reloc type '{rt_str}' in .GLOBAL"
                            f" for machine {st.elf.machine}", set_error=False)
                else:
                    ent = st.labels.get(s)
                    if ent is not None:
                        ent.extend([None] * (5 - len(ent)))
                        ent[4] = rtype
            v = self.label_manager.get_value(s)
            sec = self.label_manager.get_section(s)
            lentry = st.labels.get(s, [])
            st.export_labels[s] = [v, sec, len(lentry) > 2 and lentry[2]]
            idx = StringUtils.skipspc(l2, idx)
            if l2[idx:idx + 1] == ',':
                idx += 1
        return True

    def _dir_trailing(self, name, text, idx):
        """指令の引数の後ろに残った文字（空白とタブ以外）をエラーにする。caxx.c の dir_trailing()。"""
        rest = text[idx:].strip(' \t')
        if not rest:
            return False
        self.state.diag(f" error - {name}: unexpected text after the argument: {rest!r}.",
                        set_error=True)
        return True

    def _int_arg(self, name, l2):
        """指令の整数の引数を 1 つ読む（後ろの文字・未定義・非有限は診断して None）。

        未定義を含む `.equ` の値（番兵）も未定義として扱う（caxx.c の u256_is_undef()）。
        """
        st = self.state
        st.error_undefined_label = False
        x, idx = self.expr_eval.expression_asm(l2, 0)
        if self._dir_trailing(name, l2, idx):
            return None
        if st.error_undefined_label or _undef(x):
            st.diag(f" error - {name} argument contains undefined label.", set_error=True)
            return None
        try:
            return int(x)
        except (OverflowError, ValueError):
            st.diag(f" error - {name} argument is non-finite or invalid.", set_error=True)
            return None

    _RES_UNITS = {'.RESB': 1, '.RESW': 2, '.RESD': 4, '.RESQ': 8}

    def resb_processing(self, l1, l2):
        """`.resb` / `.resw` / `.resd` / `.resq` — バイトを出さず領域だけ予約する。"""
        name = StringUtils.upper(l1)
        mul = self._RES_UNITS.get(name)
        if mul is None:
            return False
        x = self._int_arg(name, l2)
        if x is None:
            return True
        if x < 0:
            self.state.diag(f" error - {name} requires a non-negative count, got {x}.", set_error=True)
        elif x > (1 << 28) // mul:
            self.state.diag(f" error - {name} count {x} (x{mul}) exceeds maximum "
                            f"{1 << 28} words.", set_error=True)
        else:
            self.state.pc += x * mul
        return True

    def zero_processing(self, l1, l2):
        """`.zero` — ゼロバイトを並べる。"""
        if StringUtils.upper(l1) != ".ZERO":
            return False
        x = self._int_arg(".ZERO", l2)
        if x is None:
            return True
        if x < 0:
            self.state.diag(f" error - .ZERO requires a non-negative count, got {x}.", set_error=True)
        elif x > 1 << 28:
            self.state.diag(f" error - .ZERO count {x} exceeds maximum {1 << 28}.", set_error=True)
        else:
            for _ in range(x):
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

    # `.db` 〜 `.dz` の 1 つの値のワード数（`.do` `.dy` `.dz` は NASM と同じ名前）。
    _DATA_UNITS = {'.DB': 1, '.DW': 2, '.DD': 4, '.DQ': 8,
                   '.DO': 16, '.DY': 32, '.DZ': 64}
    # 値を取り込む内部の変数名（パターン変数とは重ならない）。
    _DATA_VAR = '\x01data'

    def data_processing(self, l1, l2):
        """`.db` 〜 `.dz` — 式の値をワード列にする（ディレクティブでなければ None）。caxx.c の adir_data()。

        1 つの値は 1〜64 ワードで `.bits` のバイト順に並ぶ。`.db` だけは `"..."` も書ける。
        ワード列は binary_list と同じ経路で書くので -o では同じ規則でリロケーションが付く
        （`.vliw` の中では直接書く）。誤りの値も 0 のワードを出し、行の大きさを保つ。
        """
        name = StringUtils.upper(l1)
        n = self._DATA_UNITS.get(name)
        if n is None:
            return None
        st = self.state
        st._data_dir_line = True
        bts = st.bts
        nbits = n * bts
        wmask = (1 << bts) - 1
        fmask = (1 << nbits) - 1
        report = st.should_report_errors()
        tracking = st.elf.tracking
        objl = []
        idx = StringUtils.skipspc(l2, 0)
        if idx >= len(l2):
            if report:
                st.diag(f" error - {name} requires at least one value.", set_error=True)
            return []
        while True:
            idx = StringUtils.skipspc(l2, idx)
            if idx >= len(l2):
                if report:
                    st.diag(f" error - {name}: missing value after ','.", set_error=True)
                break
            if l2[idx] == '"':
                if n != 1:
                    if report:
                        st.diag(f" error - {name}: string literals are allowed only in .DB.",
                                set_error=True)
                    break
                vals, idx2, _trunc, err = self._string_words(l2, idx)
                if err is not None:
                    if report:
                        st.diag(err, set_error=True)
                    break
                if idx2 is None:
                    if report:
                        st.diag(f" error - {name}: unterminated string literal.", set_error=True)
                    break
                if _trunc and report:
                    st.diag(f" warning - {name}: one or more characters exceed the output word "
                            f"width ({bts} bit(s)) and were truncated (high bits discarded).",
                            set_error=False)
                objl += [v & wmask for v in vals]
                idx = idx2
            else:
                st.error_undefined_label = False
                if tracking:
                    st.elf.var_to_label.pop(self._DATA_VAR, None)
                    st.elf.capturing_var = self._DATA_VAR
                if st.relax.pas == 1:
                    st.relax.pass1_size_mode = True
                _start = idx
                st._sec_frame = True
                try:
                    x, idx = self.expr_eval.expression_asm(l2, idx)
                finally:
                    st._sec_frame = False
                    st.elf.capturing_var = None
                    if st.relax.pas == 1:
                        st.relax.pass1_size_mode = False
                _undef_hit = (st.error_undefined_label or _undef(x)) and st.relax.pas != 1
                st.error_undefined_label = False
                if idx == _start:
                    if report:
                        st.diag(f" error - {name}: missing value.", set_error=True)
                    break
                if tracking:
                    _elf_v2l_finish(st, self._DATA_VAR, l2[_start:idx].strip(' \t'),
                                    self.expr_eval.loc_counter_value)
                v = 0
                xr = 0
                if _undef_hit:
                    if report:
                        st.diag(f" error - {name} argument contains undefined label.",
                                set_error=True)
                elif not _undef(x):
                    try:
                        v = int(x)
                    except (OverflowError, ValueError):
                        if report:
                            st.diag(f" error - {name} argument is non-finite or invalid.",
                                    set_error=True)
                        v = 0
                    xr = v
                    v = _float_int(v)      # 256 ビットの符号付きとして読む（6.4 節）
                    if not (-(1 << (nbits - 1)) <= v <= fmask):
                        if report:
                            st.diag(f" error - {name}: value out of range "
                                    f"({nbits}-bit field).", set_error=True)
                        v = 0
                u = v & fmask
                words = [(u >> (bts * k)) & wmask for k in range(n)]
                if st.endian == 'big':
                    words.reverse()
                base = len(objl)
                objl += words
                if tracking:
                    # 絶対型にするのは「ラベル＋定数」で `$$` を含まない欄だけ（`.dd ext-$$` は推測へ）。
                    _ent = st.elf.var_to_label.get(self._DATA_VAR)
                    if (isinstance(_ent, tuple) and len(_ent) == 2
                            and '$$' not in l2[_start:idx]):
                        st._elf_data_fields.add(base)
                    if base > 0:
                        st._elf_field_breaks.add(base)
                if tracking and not _undef_hit:
                    for k in range(n):
                        st.elf.current_word_idx = base + k
                        self.expr_eval.elf_note_var_ref(self._DATA_VAR, xr)
                    st.elf.current_word_idx = -1
            idx = StringUtils.skipspc(l2, idx)
            if idx >= len(l2):
                break
            if l2[idx] == ',':
                idx += 1
                continue
            self._dir_trailing(name, l2, idx)
            break
        if st.vliw.flag:
            for w in objl:
                self.binary_writer.outbin(st.pc, w)
                st.pc += 1
            return []
        return objl

    def section_processing(self, l1, l2):
        """`.section` / `.segment` — セクションを切り替える（`.text` のような短縮形は無い）。

        名前は 1 語。後ろの `,"aw"` などはエラーにする（caxx.c の adir_section()）。
        """
        if StringUtils.upper(l1) not in (".SECTION", ".SEGMENT"):
            return False
        st = self.state
        e = 0
        while e < len(l2) and l2[e] not in ' \t,':
            e += 1
        if e < len(l2) and self._dir_trailing(".SECTION", l2, e):
            return True
        if l2 == '':
            return True
        old = st.sections.setdefault(st.current_section, [0, 0, 0, False])
        entry_pc = old[2] if len(old) > 2 else old[0]
        tentative = st.pc - entry_pc
        if tentative > 0:
            old[1] += tentative
            st.section_ranges.append((st.current_section, entry_pc, tentative))
        st.current_section = l2
        cur = st.sections.get(l2)
        if cur is None:
            st.sections[l2] = [st.pc, 0, st.pc, False]
        else:
            confirmed = len(cur) > 3 and cur[3]
            start = st.pc if cur[1] == 0 and not confirmed else min(cur[0], st.pc)
            st.sections[l2] = [start, cur[1], st.pc, False]
        return True

    def align_processing(self, l1, l2):
        """`.align` — 整列する（引数なしなら前回か既定の値）。"""
        if StringUtils.upper(l1) != ".ALIGN":
            return False
        st = self.state
        if l2 != '':
            u = self._int_arg(".ALIGN", l2)
            if u is None:
                return True
            if u <= 0:
                st.diag(f" error - .ALIGN requires a positive value, got {u}.", set_error=True)
                return True
            st.align = u
        rel = (self.label_manager._section_relative_offset(st.current_section, st.pc)
               if _sectioned(st) else None)
        base = rel if rel is not None else st.pc
        st.pc += self.binary_writer.align_(base) - base
        return True

    def endsection_processing(self, l1, l2):
        """`.endsection` / `.endsegment` — セクションを閉じる。"""
        if StringUtils.upper(l1) not in (".ENDSECTION", ".ENDSEGMENT"):
            return False
        st = self.state
        cs = st.current_section
        if cs not in st.sections:
            st.diag(f" error - .ENDSECTION without matching .SECTION for '{cs}'.", set_error=True)
            return True
        entry = st.sections[cs]
        start = entry[0]
        entry_pc = entry[2] if len(entry) > 2 else start
        block = st.pc - entry_pc
        if block < 0:
            st.diag(f" warning - ENDSECTION: computed block size {block} < 0 for "
                    f"'{cs}'; keeping previous size.", set_error=False)
            return True
        if block > 0:
            st.section_ranges.append((cs, entry_pc, block))
        st.sections[cs] = [start, entry[1] + block, st.pc, True]
        return True

    @staticmethod
    def _type_suffix(l2, idx):
        """`名前::型` の `::型` を読む。返り値は (型の綴り（小文字、無ければ ''）, 次の位置)。"""
        if idx > 0 and l2[idx - 1] == ':' and l2[idx:idx + 1] == ':':
            idx -= 1
        rt = ''
        if l2[idx:idx + 2] == '::':
            idx += 2
            b = idx
            while idx < len(l2) and l2[idx] not in ' \t,:' + chr(0):
                idx += 1
            rt = l2[b:idx].strip().translate(_ALOWER)
        if l2[idx:idx + 1] == ':':
            idx += 1
        return rt, idx

    def extern_processing(self, l1, l2):
        """`.extern 名前[::型], ...` — シンボルを外部と結び付ける。"""
        if StringUtils.upper(l1) != ".EXTERN":
            return False
        st = self.state
        idx = 0
        l2 = l2 + chr(0)
        while idx < len(l2) and l2[idx] != chr(0):
            idx = StringUtils.skipspc(l2, idx)
            name, idx = self.parser.get_label_word(l2, idx)
            if not name:
                break
            mach = elf_machine_table(st)
            reloc_type = mach['extern_default']
            explicit = False
            rt_str, idx = self._type_suffix(l2, idx)
            if rt_str:
                reloc_type = _reloc_named(st, mach, rt_str)
                if reloc_type is None:
                    st.diag(f" warning - unknown reloc type '{rt_str}' in .EXTERN"
                            f" for machine {st.elf.machine}", set_error=False)
                else:
                    explicit = True
            existing = st.labels.get(name)
            if explicit:
                st.extern_untyped.discard(name)
            elif existing is None:
                st.extern_untyped.add(name)
            if existing is None:
                st.labels[name] = [0, '.text', False, True, reloc_type]
            elif len(existing) > 3 and existing[3]:
                if len(existing) >= 5 and explicit:
                    existing[4] = reloc_type
            else:
                st.diag(f" warning - .EXTERN: '{name}' is already defined"
                        f" locally; ignoring extern declaration", set_error=False)
            idx = StringUtils.skipspc(l2, idx)
            if l2[idx:idx + 1] == ',':
                idx += 1
        return True

    def _sym_decl_scan(self, l2, nfields):
        """シンボル属性ディレクティブの `名前[::欄...], ...` を [(名前, 欄のリスト)] に切り出す。"""
        out = []
        idx = 0
        buf = l2 + chr(0)
        while idx < len(buf) and buf[idx] != chr(0):
            idx = StringUtils.skipspc(buf, idx)
            name, idx = self.parser.get_label_word(buf, idx)
            if not name:
                break
            if idx > 0 and buf[idx - 1] == ':' and buf[idx:idx + 1] == ':':
                idx -= 1
            fields = []
            while len(fields) < nfields and buf[idx:idx + 2] == '::':
                idx += 2
                b = idx
                while idx < len(buf) and buf[idx] not in ' \t,:' + chr(0):
                    idx += 1
                fields.append(buf[b:idx].strip())
            fields += [''] * (nfields - len(fields))
            if buf[idx:idx + 1] == ':':
                idx += 1
            out.append((name, fields))
            idx = StringUtils.skipspc(buf, idx)
            if buf[idx:idx + 1] == ',':
                idx += 1
        return out

    def _sym_decl_num(self, dname, name, text, lo, hi):
        """シンボル属性の数値欄を lo..hi の整数として読む（だめなら診断して None）。"""
        st = self.state
        if not text:
            st.diag(f" error - {dname}: a number is required for '{name}'.", set_error=True)
            return None
        st.error_undefined_label = False
        v, _idx = self.expr_eval.expression_asm(text, 0)
        undef = _is_undef_derived(v)
        try:
            v = int(v)
        except (OverflowError, ValueError):
            v = None
        if st.error_undefined_label or undef or v is None or v < lo or v > hi:
            st.diag(f" error - {dname}: value for '{name}' must be an integer "
                    f"in {lo}..{hi}, got '{text}'.", set_error=True)
            v = None
        st.error_undefined_label = False
        return v

    def _sym_declare_extern(self, name):
        """その名前を（未定義なら）外部シンボルとして登録する。"""
        st = self.state
        if name not in st.labels:
            st.extern_untyped.add(name)
            st.labels[name] = [0, '.text', False, True, elf_machine_table(st)['extern_default']]

    def _cfi_num(self, op, text):
        """CFI 指令の数の引数（定数でなければ診断して None）。"""
        st = self.state
        st.error_undefined_label = False
        v, _idx = self.expr_eval.expression_asm(text, 0)
        undef = st.error_undefined_label or _is_undef_derived(v)
        st.error_undefined_label = False
        try:
            v = int(v)
        except (OverflowError, ValueError, TypeError):
            v = None
        if undef or v is None:
            st.diag(f" error - .cfi_{op}: '{text}' is not a constant.", set_error=True)
            return None
        return v

    def _cfi_reg(self, op, text):
        """CFI 指令のレジスタの引数（`.elfcfireg` の名前か、0 以上の数）。"""
        r = self.state.elf.decl_cfireg.get(text.translate(_ALOWER))
        if r is not None:
            return r
        v = self._cfi_num(op, text)
        if v is not None and v < 0:
            self.state.diag(f" error - .cfi_{op}: '{text}' is not a register.", set_error=True)
            return None
        return v

    def cfi_processing(self, l1, l2):
        """`.cfi_*` — CFI の指令をその位置（セクション先頭からのワード数）と一緒に記録する。

        記録はパス2で -o のときだけ。`.eh_frame` は write_elf_obj() が組む。caxx.c の dir_cfi()。
        """
        if not StringUtils.upper(l1).startswith('.CFI_'):
            return False
        st = self.state
        if not (st.should_report_errors() and st.elf.objfile):
            return True
        op = l1[5:].translate(_ALOWER)
        spec = _CFI_OPS.get(op)
        if spec is None:
            st.diag(f" error - unknown CFI directive '{l1}'.", set_error=True)
            return True
        if op == 'sections':
            return True
        e = st.elf
        args = [a.strip() for a in l2.split(',')] if l2.strip() else []
        sec = st.current_section
        off = self.label_manager._section_relative_offset(sec, st.pc)
        if off is None:
            off = st.pc
        if op == 'startproc':
            if e.cfi_cur is not None:
                st.diag(" error - .cfi_startproc: the previous .cfi_startproc has "
                        "no .cfi_endproc.", set_error=True)
            elif args and [a.translate(_ALOWER) for a in args] != ['simple']:
                st.diag(f" error - .cfi_startproc: unknown argument '{l2.strip()}'.", set_error=True)
            else:
                e.cfi_cur = {'sec': sec, 'start': off, 'end': off, 'simple': bool(args),
                             'ops': [], 'ra': None, 'signal': False, 'pers': None, 'lsda': None}
            return True
        cur = e.cfi_cur
        if cur is None:
            st.diag(f" error - .cfi_{op}: not inside .cfi_startproc.", set_error=True)
            return True
        if sec != cur['sec']:
            st.diag(f" error - .cfi_{op}: the section changed inside the function.", set_error=True)
            return True
        if spec == '*':
            if not args:
                st.diag(f" error - .cfi_{op}: at least one argument is required.", set_error=True)
                return True
        elif len(args) != len(spec):
            st.diag(f" error - .cfi_{op}: {len(spec)} argument(s) expected.", set_error=True)
            return True
        vals = []
        for k, a in enumerate(args):
            kind = '*' if spec == '*' else spec[k]
            if kind == 'r':
                v = self._cfi_reg(op, a)
            elif kind == 's':
                v = a
            else:
                v = self._cfi_num(op, a)
                if v is not None and kind == '*' and not 0 <= v <= 255:
                    st.diag(f" error - .cfi_{op}: '{a}' is not a byte.", set_error=True)
                    v = None
            if v is None:
                return True
            vals.append(v)
        if op == 'endproc':
            cur['end'] = off
            e.cfi_fdes.append(cur)
            e.cfi_cur = None
        elif op == 'return_column':
            cur['ra'] = vals[0]
        elif op == 'signal_frame':
            cur['signal'] = True
        elif op in ('personality', 'lsda'):
            if not 0 <= vals[0] <= 255:
                st.diag(f" error - .cfi_{op}: '{args[0]}' is not an encoding byte.", set_error=True)
                return True
            cur['pers' if op == 'personality' else 'lsda'] = \
                None if vals[0] == 0xff else (vals[0], vals[1])
        else:
            cur['ops'].append((off, op, tuple(vals)))
        return True

    def type_processing(self, l1, l2):
        """`.type` — ELF シンボルの種別（STT_*、名前か 0..15）。"""
        if StringUtils.upper(l1) != ".TYPE":
            return False
        if self.state.should_report_errors():
            for name, f in self._sym_decl_scan(l2, 1):
                kind = f[0].translate(_ALOWER)
                if not kind:
                    self.state.diag(f" error - .TYPE: a symbol type is required for "
                                    f"'{name}'.", set_error=True)
                    continue
                v = ELF_SYM_TYPES.get(kind)
                if v is None:
                    v = self._sym_decl_num('.TYPE', name, kind, 0, 15)
                if v is not None:
                    _sym_attr_slot(self.state, name)[_SA_TYPE] = v
        return True

    def size_processing(self, l1, l2):
        """`.size` — シンボルの大きさ（ワード数。出力時に幅をかける）。"""
        if StringUtils.upper(l1) != ".SIZE":
            return False
        if self.state.should_report_errors():
            for name, f in self._sym_decl_scan(l2, 1):
                v = self._sym_decl_num('.SIZE', name, f[0], 0, 0x7FFFFFFFFFFFFFFF)
                if v is not None:
                    a = _sym_attr_slot(self.state, name)
                    a[_SA_SIZE_SET] = 1
                    a[_SA_SIZE] = v
        return True

    def weak_processing(self, l1, l2):
        """`.weak` — 弱シンボル（STB_WEAK）にする。"""
        if StringUtils.upper(l1) != ".WEAK":
            return False
        st = self.state
        record = st.should_report_errors()
        for name, _f in self._sym_decl_scan(l2, 0):
            self._sym_declare_extern(name)
            if not record:
                continue
            _sym_attr_slot(st, name)[_SA_WEAK] = 1
            lentry = st.labels.get(name, [])
            if not (len(lentry) > 3 and lentry[3]):
                st.export_labels[name] = [self.label_manager.get_value(name),
                                          self.label_manager.get_section(name),
                                          len(lentry) > 2 and lentry[2]]
        return True

    _VIS_DIRS = {'.HIDDEN': 2, '.PROTECTED': 3, '.INTERNAL': 1}

    def visibility_processing(self, l1, l2):
        """`.hidden` / `.protected` / `.internal` — 可視性を書く。"""
        vis = self._VIS_DIRS.get(StringUtils.upper(l1))
        if vis is None:
            return False
        if self.state.should_report_errors():
            for name, _f in self._sym_decl_scan(l2, 0):
                a = _sym_attr_slot(self.state, name)
                a[_SA_OTHER] = (a[_SA_OTHER] & ~0x03) | vis
        return True

    def other_processing(self, l1, l2):
        """`.other` — st_other バイトを丸ごと置き換える。"""
        if StringUtils.upper(l1) != ".OTHER":
            return False
        if self.state.should_report_errors():
            for name, f in self._sym_decl_scan(l2, 1):
                v = self._sym_decl_num('.OTHER', name, f[0], 0, 255)
                if v is not None:
                    _sym_attr_slot(self.state, name)[_SA_OTHER] = v
        return True

    def comm_processing(self, l1, l2):
        """`.comm 名前::大きさ[::整列]` — 共通シンボル（SHN_COMMON）にする。"""
        if StringUtils.upper(l1) != ".COMM":
            return False
        st = self.state
        record = st.should_report_errors()
        for name, f in self._sym_decl_scan(l2, 2):
            self._sym_declare_extern(name)
            if not record:
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
                    st.diag(" error - .COMM: alignment must be 0 or a power "
                            f"of two, got '{al}' for '{name}'.", set_error=True)
                    continue
            a = _sym_attr_slot(st, name)
            a[_SA_COMMON] = a[_SA_SIZE_SET] = 1
            a[_SA_SIZE] = sz
            a[_SA_ALIGN] = al
            if a[_SA_TYPE] == 0:
                a[_SA_TYPE] = 1
        return True

    def reloctype_processing(self, l1, l2):
        """`.reloctype 8bit,16bit,32bit,64bit` — このソースでの幅推測の型を上書きする。"""
        if StringUtils.upper(l1) != ".RELOCTYPE":
            return False
        st = self.state
        mach = elf_machine_table(st)
        if not mach['named']:
            st.diag(f" warning - .RELOCTYPE: no relocation type is known for "
                    f"machine {st.elf.machine}; declare them with .elftype", set_error=False)
            return True
        for i, raw in enumerate(l2.split(',') if l2 else []):
            if i >= 4:
                st.diag(" warning - .RELOCTYPE: too many arguments (only "
                        "4 widths -- 8/16/32/64-bit -- are supported)", set_error=False)
                break
            name = raw.strip().translate(_ALOWER)
            if not name:
                continue
            rtype = _reloc_named(st, mach, name)
            if rtype is None:
                st.diag(f" warning - unknown reloc type '{name}' in "
                        f".RELOCTYPE for machine {st.elf.machine}", set_error=False)
                continue
            want = 1 << i
            actual = mach['reloc_bytes'].get(rtype)
            if actual is not None and actual != want:
                st.diag(f" warning - .RELOCTYPE: '{name}' is a "
                        f"{actual * 8}-bit relocation type, but was given "
                        f"in the {want * 8}-bit position; ignored", set_error=False)
                continue
            st.elf.reloctype_override[want] = rtype
        return True

    def org_processing(self, l1, l2):
        """`.org 番地[,p]` — ロケーションカウンタを設定する（`,p` は隙間を `.padding` で埋める）。

        -o / -E では後ろへ戻せない（GNU as と同じ。caxx.c の adir_org()）。
        """
        if StringUtils.upper(l1) != ".ORG":
            return False
        st = self.state
        st.error_undefined_label = False
        u, idx = self.expr_eval.expression_asm(l2, 0)
        fill = l2[idx:idx + 2].translate(_AUPPER) == ',P'
        if self._dir_trailing(".ORG", l2, idx + 2 if fill else idx):
            return True
        if st.error_undefined_label or _undef(u):
            st.diag(" error - .ORG argument contains undefined label.", set_error=True)
            return True
        try:
            u = int(u)
        except (OverflowError, ValueError):
            st.diag(" error - .ORG argument is non-finite or invalid.", set_error=True)
            return True
        if u < 0:
            st.diag(f" error - .ORG address must be non-negative, got {u}.", set_error=True)
            return True
        if (st.elf.objfile or st.expfile_elf) and u < st.pc:
            st.diag(f" error - .ORG moves the location counter backwards (from "
                    f"{st.pc} to {u}); an ELF object (-o, -E) cannot "
                    f"hold that.", set_error=True)
            return True
        if fill and u > st.pc:
            count = u - st.pc
            if count > 1 << 28:
                st.diag(f" error - .ORG ,P fill count {count} exceeds maximum {1 << 28}.", set_error=True)
                return True
            for i in range(count):
                self.binary_writer.outbin2(i + st.pc, st.padding)
        st.pc = u
        return True


# マクロ層で落とす空白はスペースとタブだけ（caxx.c の m_ 系の関数と同じ。引数なしの strip() は使わない）。
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
    """`!break` を `!while` へ伝える。"""


class _MacroContinue(Exception):
    """`!continue` を `!while` へ伝える。"""


class _MacroReturn(Exception):
    """`!return` を呼び出し元へ伝える（値を持つ）。"""

    def __init__(self, value):
        super().__init__(value)
        self.value = value


class _MacroFunc:
    """`!def` で定義されたマクロ 1 個（引数名・既定値・本文・定義位置）。"""

    __slots__ = ('name', 'params', 'defaults', 'body', 'pos')

    def __init__(self, name, params, defaults, body, pos):
        self.name = name
        self.params = params
        self.defaults = defaults
        self.body = body
        self.pos = pos


def _sext_tick_at(s, i):
    """その位置の `'` が符号拡張演算子か（直後が数字か `(`）。"""
    j = StringUtils.skipspc(s, i + 1)
    return j < len(s) and (_ad(s[j]) or s[j] == '(')


def _fmt_pos(pos):
    """診断に出す「ファイル:行」。"""
    return f"{pos[0]}:{pos[1]}"


def _strip_comment(text, pat_mode=False):
    """マクロ行のコメントを落とす（ソースは `;`、パターンは `/*`。文字列の中は触らない）。"""
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
        elif c == '"' or (c == "'" and text.find("'", i + 1) >= 0):
            quote = c
        elif (c == '/' and text[i + 1:i + 2] == '*') if pat_mode else c == ';':
            return text[:i].rstrip(' \t')
        i += 1
    return text.rstrip(' \t')


class _ExprParser:
    """マクロ層の式（値は整数と文字列、演算子は C に倣う）を評価する再帰下降。

    本体の評価器とは `%` の符号（被除数の符号）と `'` の結合位置が違う。`@` `'` `*(x,y)` は
    本体と同じ実装を呼ぶ。suppress は短絡・三項で読み飛ばす側（診断を出さない）。
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
        self.i = StringUtils.skipspc(self.s, self.i)

    def peek(self, n=1):
        """先の文字を消費せずに見る。"""
        self.skip()
        return self.s[self.i:self.i + n]

    def eat(self, tok):
        """次がそのトークンなら消費して真（英字で終わるトークンは語の途中では当たらない）。"""
        self.skip()
        if not self.s.startswith(tok, self.i):
            return False
        if _aa(tok[-1]):
            j = self.i + len(tok)
            if j < self.n and (_aan(self.s[j]) or self.s[j] == '_'):
                return False
        self.i += len(tok)
        return True

    def expect(self, tok):
        """そのトークンを必ず消費する。"""
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

    def skipped(self, fn):
        """fn を読み飛ばす側として評価する（診断を出さない）。"""
        self.suppress += 1
        try:
            return fn()
        finally:
            self.suppress -= 1

    def ternary(self):
        """`?:`（選ばれなかった側は読み飛ばす）。"""
        c = self.logic_or()
        if not self.eat('?'):
            return c
        if _truth(c):
            a = self.ternary()
            self.expect(':')
            self.skipped(self.ternary)
            return a
        self.skipped(self.ternary)
        self.expect(':')
        return self.ternary()

    def logic_or(self):
        """`||`（短絡）。"""
        v = self.logic_and()
        while self.eat('||'):
            if _truth(v):
                self.skipped(self.logic_and)
                v = 1
            else:
                v = 1 if _truth(self.logic_and()) else 0
        return v

    def logic_and(self):
        """`&&`（短絡）。"""
        v = self.sext()
        while self.eat('&&'):
            if not _truth(v):
                self.skipped(self.sext)
                v = 0
            else:
                v = 1 if _truth(self.sext()) else 0
        return v

    def sext(self):
        """`'` — 符号拡張。マクロ層ではビット演算より緩く `&&` よりきつい（C の優先順位に倣うため）。"""
        v = self.bit_or()
        while True:
            self.skip()
            if self.s[self.i:self.i + 1] != "'" or not _sext_tick_at(self.s, self.i):
                break
            self.i += 1
            t = self.bit_or()
            v, warn, go = op_sext(_as_int(self, v), _as_int(self, t))
            if warn and not self.suppress:
                self.pp.warn(f"{_fmt_pos(self.pos)}: {warn}")
            if not go:
                break
        return v

    def _bitop(self, sub, op, fn):
        """`|` `^` `&` の 1 段（`||` `&&` は食べない）。"""
        v = sub()
        while True:
            self.skip()
            if op != '^' and self.s.startswith(op + op, self.i):
                break
            if not self.eat(op):
                return v
            v = fn(_as_int(self, v), _as_int(self, sub()))
        return v

    def bit_or(self):
        return self._bitop(self.bit_xor, '|', int.__or__)

    def bit_xor(self):
        return self._bitop(self.bit_and, '^', int.__xor__)

    def bit_and(self):
        return self._bitop(self.equality, '&', int.__and__)

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
        """`<<` `>>`（シフト量は 0..4096）。"""
        v = self.additive()
        while True:
            op = '<<' if self.eat('<<') else '>>' if self.eat('>>') else None
            if op is None:
                return v
            r = _as_int(self, self.additive())
            if r < 0 or r > 4096:
                if not self.suppress:
                    self.err("shift count out of range")
                r = 0
            v = _as_int(self, v) << r if op == '<<' else _as_int(self, v) >> r

    def additive(self):
        """`+` `-`（どちらかが文字列なら `+` は連結）。"""
        v = self.multiplicative()
        while True:
            self.skip()
            c = self.s[self.i:self.i + 1]
            if c == '+':
                self.i += 1
                r = self.multiplicative()
                v = _mnorm(_as_str(v) + _as_str(r)) if isinstance(v, str) or isinstance(r, str) else v + r
            elif c == '-':
                self.i += 1
                v = _as_int(self, v) - _as_int(self, self.multiplicative())
            else:
                return v

    def multiplicative(self):
        """`*` `/` `%`（`/` `%` は C と同じゼロ方向の切り捨て。文字列 `*` 整数は繰り返し）。"""
        v = self.unary()
        while True:
            self.skip()
            c = self.s[self.i:self.i + 1]
            if c == '*':
                self.i += 1
                r = self.unary()
                if isinstance(v, str) and isinstance(r, int):
                    v = v * max(0, r)
                elif isinstance(v, int) and isinstance(r, str):
                    v = r * max(0, v)
                else:
                    v = _as_int(self, v) * _as_int(self, r)
            elif c in ('/', '%'):
                self.i += 1
                r = _as_int(self, self.unary())
                if r == 0:
                    if not self.suppress:
                        self.err("division by zero" if c == '/' else "modulo by zero")
                    v = 0
                else:
                    v = (_c_div if c == '/' else _c_mod)(_as_int(self, v), r)
            else:
                return v

    def unary(self):
        """単項 `!` `~` `-` `+` `@` と `*(x, n)`。"""
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
        if self.s.startswith('*(', self.i):
            self.i += 2
            x = self.ternary()
            self.expect(',')
            n = self.ternary()
            self.expect(')')
            v, err = op_byte(_as_int(self, x), _as_int(self, n))
            if err and not self.suppress:
                self.err(err)
            return v
        return self.primary()

    def primary(self):
        """項（数・文字列・名前・`(式)`・`$` `$$`・`defined(名前)`・関数呼び出し）。"""
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
            return _mb(t)[0] if len(_mb(t)) == 1 else t
        if c == '$':
            self.i += 2 if self.s[self.i + 1:self.i + 2] == '$' else 1
            return self.pp.loc_counter(self.pos)
        if _ad(c):
            return self.read_number()
        if c == '_' or _aa(c):
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
                        if not self.eat(','):
                            self.expect(')')
                            break
                return 0 if self.suppress else self.pp.call_value(name, args, self.pos)
            return 0 if self.suppress else self.pp.lookup(name, self.pos)
        self.err(f"unexpected character {c!r}")

    def read_ident(self):
        """識別子を 1 個読む。"""
        self.skip()
        j = self.i
        while j < len(self.s) and (_aan(self.s[j]) or self.s[j] == '_'):
            j += 1
        if j == self.i:
            self.err("expected a name")
        name = self.s[self.i:j]
        self.i = j
        return name

    _NUM_PFX = {'x': (16, '0123456789abcdefABCDEF_'), 'b': (2, '01_'), 'o': (8, '01234567_')}

    def read_number(self):
        """整数リテラル（10 進・`0x`・`0b`・`0o`、`_` 可）を読む。"""
        s = self.s
        j = self.i
        pfx = self._NUM_PFX.get(s[j + 1:j + 2].translate(_ALOWER)) if s[j] == '0' else None
        if pfx:
            base, digits = pfx
            k = j + 2
            while k < len(s) and s[k] in digits:
                k += 1
            txt = s[j + 2:k]
        else:
            base = 10
            k = j
            while k < len(s) and (_ad(s[k]) or s[k] == '_'):
                k += 1
            txt = s[j:k]
        txt = txt.replace('_', '')
        if txt == '':
            self.err("malformed number")
        self.i = k
        try:
            return int(txt, base)
        except ValueError:
            self.err("malformed number")

    _STR_ESC = {'n': '\n', 't': '\t', 'r': '\r', '0': '\0', '\\': '\\', '"': '"', "'": "'"}

    def read_string(self, q):
        """文字列リテラルを読む（`'A'` は呼び出し側で 1 バイトなら文字コードにする）。"""
        s = self.s
        j = self.i + 1
        out = []
        while j < len(s):
            ch = s[j]
            if ch == '\\' and j + 1 < len(s):
                out.append(self._STR_ESC.get(s[j + 1], s[j + 1]))
                j += 2
                continue
            if ch == q:
                self.i = j + 1
                return ''.join(out)
            out.append(ch)
            j += 1
        self.err("unterminated string literal")


def _truth(v):
    """マクロ層での真偽（文字列は空でなければ真）。"""
    return v != '' if isinstance(v, str) else v != 0


def _as_int(p, v):
    """値を整数として要求する（読み飛ばし中は 0）。"""
    if isinstance(v, str):
        if getattr(p, 'suppress', 0):
            return 0
        p.err(f"expected an integer, got the string {v!r}")
    return v


def _as_str(v):
    """値を文字列として読む。"""
    return v if isinstance(v, str) else str(v)


def _echo_write(items):
    """`!echo` / `.echo` の出力を標準エラーへ書く（マクロ層とミニ言語で同じ体裁）。"""
    print(' '.join(_as_str(x) for x in items), file=sys.stderr)


_ECHO_CACHE = {}


def _echo_str_unescape(s):
    """`.echo` の文字列リテラルのエスケープを開く。返り値は (文字列, 誤りか None)。"""
    out = []
    k = 0
    n = len(s)
    while k < n:
        c = s[k]
        if c != '\\':
            out.append(c)
            k += 1
            continue
        if k + 1 >= n:
            return None, "dangling '\\' in a string"
        e = _MINI_ESC.get(s[k + 1])
        if e is None:
            return None, f"unknown escape '\\{s[k + 1]}' in a string"
        out.append(e)
        k += 2
    return ''.join(out), None


def _echo_items_parse(text):
    """`.echo(項目, ...)` の引数を [('s', 文字列) か ('e', 式)] に割る。返り値は (並び, 誤りか None)。"""
    n = len(text)
    i = StringUtils.skipspc(text, 0)
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
        elif c == '"':
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
    if text[end + 1:].strip(' \t'):
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
    if len(parts) == 1 and parts[0].strip(' \t') == '':
        return [], None

    items = []
    for p in parts:
        p = p.strip(' \t')
        if p == '':
            return None, "empty item in the argument list"
        if p[0] != '"':
            items.append(('e', p))
            continue
        j = 1
        while j < len(p) and p[j] != '"':
            j += 2 if p[j] == '\\' else 1
        if j >= len(p):
            return None, f"unterminated string: '{p}'"
        if j != len(p) - 1:
            return None, f"unexpected text after a string: '{p}'"
        sv, err = _echo_str_unescape(p[1:j])
        if err is not None:
            return None, err
        items.append(('s', sv))
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


# マクロ層の文字列はミニ言語と同じく UTF-8 のバイトの並び（長さ・添字・大文字化・比較・
# 1 文字の文字定数はバイトで決める。caxx.c は C 文字列をそのまま持つ）。
def _mb(s):
    """マクロ層の文字列を UTF-8 のバイト列にする。"""
    return s.encode('utf-8', 'surrogateescape')


def _mt(b):
    """バイト列を文字列に戻す（切れた UTF-8 は surrogateescape の文字になる）。"""
    return b.decode('utf-8', 'surrogateescape')


def _mnorm(s):
    """連結などで割れた UTF-8 をつなぎ直す。"""
    return _mt(_mb(s))


def _ad(c):
    """ASCII の数字か（str.isdigit() は全角数字なども数字とみなす）。"""
    return '0' <= c <= '9'


def _aa(c):
    """ASCII の英字か。"""
    return ('a' <= c <= 'z') or ('A' <= c <= 'Z')


def _aan(c):
    """ASCII の英数字か（caxx.c の isalnum() と同じ範囲）。"""
    return _ad(c) or _aa(c)


def _alow(s):
    """ASCII だけを小文字にする（caxx.c の strcasecmp() と同じ範囲）。"""
    return s.translate(_ALOWER)


def _cmp_eq(a, b):
    """`==` の比較（整数と文字列は等しくない。文字列はバイトで比べる）。"""
    if isinstance(a, str) != isinstance(b, str):
        return False
    return _mb(a) == _mb(b) if isinstance(a, str) else a == b


def _cmp_lt_eq(p, a, b, or_equal):
    """`<` と `<=` の比較（文字列と整数は比べられない）。"""
    if isinstance(a, str) != isinstance(b, str):
        if getattr(p, 'suppress', 0):
            return False
        p.err("cannot order a string against an integer")
    if isinstance(a, str):
        a, b = _mb(a), _mb(b)
    return (a <= b) if or_equal else (a < b)


def _c_div(a, b):
    """C と同じゼロ方向の切り捨て除算（`-7/2 == -3`）。"""
    q = abs(a) // abs(b)
    return q if (a >= 0) == (b >= 0) else -q


def _c_mod(a, b):
    """C と同じ剰余（被除数の符号。`-7%3 == -1`）。"""
    return a - _c_div(a, b) * b


class MacroPreprocessor:
    """行指向のマクロ層（アセンブル前のソース間変換）。

    文は行頭の `!`（`!def` `!if` `!while` `!set` ...）、補間は `!{式}`（`!{式:04x}` は
    Python の書式指定）。ソース側は前回のリラクゼーション反復のラベル値・`$$` を読める
    （収束はリラクゼーションが強制する）。パターン側（pat_mode）にはラベルも `$$` も無い。
    数は多倍長（caxx.c は int64。食い違うのは 64bit を超えるときだけ）。
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

        'val' 前回の反復の値がある / 'unk' 名前はあるが値がまだ無い / 'no' 無い（パターン側は常に）。
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
        """`$` / `$$` の値（前回の反復で記録した行ごとの PC。パターン側ではエラー）。"""
        if self.pat_mode or self.state is None:
            raise MacroError(f"{_fmt_pos(pos)}: '$'/'$$' is not available in "
                             f"pattern-file macros (there is no location counter "
                             f"before the source is assembled)")
        lst = (self.state._macro_line_pcs or {}).get(self._expand_key)
        i = len(self.out)
        return lst[i] if lst and i < len(lst) else 0

    def lookup(self, name, pos):
        """名前を解決する。内側のスコープから外側へたどる。"""
        for sc in reversed(self.scopes):
            if name in sc:
                return sc[name]
        if name in self.funcs:
            raise MacroError(f"{_fmt_pos(pos)}: macro '{name}' used as a variable "
                             f"(call it as '{name}(...)')")
        kind, v = self.asm_label(name)
        if kind != 'no':
            return v
        raise MacroError(f"{_fmt_pos(pos)}: undefined macro variable '{name}'")

    def is_defined(self, name):
        """その名前が定義済みか。"""
        return (name in self.funcs or any(name in sc for sc in self.scopes)
                or self.asm_label(name)[0] == 'val')

    def assign(self, name, value):
        """`!set` の代入。内側から外側へ探し、無ければ現在のスコープに作る。"""
        for sc in reversed(self.scopes):
            if name in sc:
                sc[name] = value
                return
        self.scope()[name] = value

    def eval(self, text, pos):
        """マクロ式を 1 個評価する。"""
        text = text.strip(' \t')
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
                             f"({emitted[0].strip(' \t')!r}) but was called from inside an "
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
        """`!{式:書式}` の書式指定（Python の書式ミニ言語。文面は caxx.c と同じ）を適用する。

        指定の前後の空白は落とすので `!{5: d}` は書けない。`!{0:c}` は NUL（caxx.c は空文字）。
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
                spec = body[k + 1:].strip(' \t')
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
        t = text.lstrip(' \t')
        if not t.startswith('!') or t.startswith('!!'):
            return None, None
        j = 1
        while j < len(t) and (_aan(t[j]) or t[j] == '_'):
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
            stripped = text.strip(' \t')

            if stripped.startswith('}') and depth > 0:
                return nodes, i

            word, rest = self.statement_word(_strip_comment(text, self.pat_mode))
            if word is None:
                nodes.append(('text', text, pos))
                i += 1
                continue

            lw = _alow(word)
            if lw not in _MACRO_KEYWORDS and word not in self.funcs \
                    and word not in self.declared and not self.looks_like_call(rest):
                nodes.append(('text', text, pos))
                i += 1
                continue

            if lw in ('if', 'while', 'def'):
                node, i = getattr(self, 'parse_' + lw)(lines, i, depth)
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
        return rest.strip(' \t').startswith('(')

    def parse_simple(self, lw, word, rest, pos):
        """単純文 1 個を解析する。"""
        r = rest.strip(' \t')
        if lw == 'set':
            if '=' not in rest:
                raise MacroError(f"{_fmt_pos(pos)}: '!set' needs 'name = expression'")
            name, expr = rest.split('=', 1)
            return ('set', name.strip(' \t'), expr, pos)
        if lw == 'local':
            if '=' in rest:
                name, expr = rest.split('=', 1)
                return ('local', name.strip(' \t'), expr, pos)
            return ('local', r, None, pos)
        if lw == 'return':
            return ('return', r or None, pos)
        if lw in ('break', 'continue'):
            return (lw, pos)
        if lw in ('undef', 'error', 'warning', 'echo', 'include'):
            return (lw, r, pos)
        return ('call', word, r, pos)

    def parse_header(self, text, kw, pos):
        """ブロック文のヘッダの中身（`!if` / `!elif` は `!then` の前まで）。開き `{` は行の最後に要る。"""
        body = text.strip(' \t')[len(kw) + 1:].rstrip(' \t')
        if not body.endswith('{'):
            raise MacroError(f"{_fmt_pos(pos)}: '!{kw}' header must end with '{{'")
        body = body[:-1]
        if kw in ('if', 'elif'):
            k = _alow(body).rfind('!then')
            if k < 0:
                raise MacroError(f"{_fmt_pos(pos)}: '!{kw}' needs '!then' before '{{'")
            body = body[:k]
        return body.strip(' \t')

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
            tail = _strip_comment(close, self.pat_mode).strip(' \t')[1:].strip(' \t')
            if tail == '' or tail.startswith(';'):
                return ('if', arms, else_body, pos), i + 1
            w, rest = self.statement_word(tail)
            if w is None:
                raise MacroError(f"{_fmt_pos(cpos)}: unexpected text after '}}': {tail!r}")
            if _alow(w) == 'elif':
                cond = self.parse_header(tail, 'elif', cpos)
                continue
            if _alow(w) == 'else':
                r = rest.strip(' \t')
                if r.startswith('!if'):
                    cond = self.parse_header(r, 'if', cpos)
                    continue
                if not r.startswith('{'):
                    raise MacroError(f"{_fmt_pos(cpos)}: '!else' must be followed by '{{'")
                else_body, i = self.parse_block(lines, i + 1, depth + 1)
                if i >= len(lines):
                    raise MacroError(f"{_fmt_pos(cpos)}: '!else' block is never closed")
                self._check_trailer(lines, i)
                return ('if', arms, else_body, pos), i + 1
            raise MacroError(f"{_fmt_pos(cpos)}: unexpected '!{w}' after '}}'")

    def _check_trailer(self, lines, i):
        """ブロックを閉じる `}` の後ろに余計な文字があればエラー。"""
        trailer = _strip_comment(lines[i][0], self.pat_mode).strip(' \t')[1:].strip(' \t')
        if trailer and not trailer.startswith(';'):
            raise MacroError(f"{lines[i][1]}:{lines[i][2]}: unexpected text after "
                             f"'}}': {trailer!r}")

    def parse_while(self, lines, i, depth):
        """`!while` を解析する。"""
        text, fn, ln = lines[i]
        pos = (fn, ln)
        cond = self.parse_header(_strip_comment(text, self.pat_mode), 'while', pos)
        body, i = self.parse_block(lines, i + 1, depth + 1)
        if i >= len(lines):
            raise MacroError(f"{_fmt_pos(pos)}: '!while' block is never closed with '}}'")
        self._check_trailer(lines, i)
        return ('while', cond, body, pos), i + 1

    def parse_def(self, lines, i, depth):
        """`!def 名前(p1, p2=既定値, ...) {` を解析する。"""
        text, fn, ln = lines[i]
        pos = (fn, ln)
        t = _strip_comment(text, self.pat_mode).strip(' \t')[4:].strip(' \t')
        if not t.rstrip(' \t').endswith('{'):
            raise MacroError(f"{_fmt_pos(pos)}: '!def' header must end with '{{'")
        t = t.rstrip(' \t')[:-1].strip(' \t')
        if '(' not in t or not t.endswith(')'):
            raise MacroError(f"{_fmt_pos(pos)}: '!def' needs 'name(p1, p2, ...)'")
        name, plist = t.split('(', 1)
        name = name.strip(' \t')
        plist = plist[:-1].strip(' \t')
        if not name or not (_aa(name[0]) or name[0] == '_') \
                or not all(_aan(c) or c == '_' for c in name):
            raise MacroError(f"{_fmt_pos(pos)}: bad macro name {name!r}")
        if _alow(name) in _MACRO_KEYWORDS or name in _BUILTINS:
            raise MacroError(f"{_fmt_pos(pos)}: '{name}' is a reserved macro name")
        params, defaults = [], []
        if plist:
            for p in plist.split(','):
                p = p.strip(' \t')
                if '=' in p:
                    pn, dv = p.split('=', 1)
                    params.append(pn.strip(' \t'))
                    defaults.append(dv.strip(' \t'))
                else:
                    params.append(p)
                    defaults.append(None)
                if not params[-1] or not (_aa(params[-1][0]) or params[-1][0] == '_'):
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
        self._check_trailer(lines, i)
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
            if self.state is None or self.state.relax.pas != 1:
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
        t = argtext.strip(' \t')
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
                if not p.eat(','):
                    p.expect(')')
                    break
        rest = p.s[p.i:].strip(' \t')
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
        # 行末の `\` の継続もソースと同じにつなぐ（caxx.c の m_read_lines()）。
        raw = StringUtils.join_backslash_continuations(raw)
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
        return any('!' in t or t.lstrip(' \t').startswith('}') for t in raw)

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
            s = t.lstrip(' \t')
            if s.startswith('}'):
                return True
            if self.has_interpolation(t):
                return True
            word, rest = self.statement_word(s)
            if word is None:
                continue
            if _alow(word) in _MACRO_KEYWORDS or word in self.funcs \
                    or word in self.declared or self.looks_like_call(rest):
                return True
        return False

    def expand(self, raw, filename):
        """行の並びをマクロ展開して [(行, ファイル, 行番号)] を返す。

        展開すべきものが無ければ解析せずにそのまま返す（マクロを使わない場合の速さ）。
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
    return len(_mb(a[0])) if isinstance(a[0], str) else len(str(a[0]))


def _bi_hex(pp, a, pos):
    """`hex(n)` — 16 進表記。"""
    _bi_check(pp, a, pos, 'hex', 1, 2)
    v = a[0]
    if isinstance(v, str):
        raise MacroError(f"{_fmt_pos(pos)}: hex() needs an integer")
    width = a[1] if len(a) > 1 else 0
    if not isinstance(width, int):
        raise MacroError(f"{_fmt_pos(pos)}: hex() width must be an integer")
    return ('-' if v < 0 else '') + format(abs(v), 'x').rjust(width, '0')


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
    if not isinstance(base, int):
        raise MacroError(f"{_fmt_pos(pos)}: int() base must be an integer")
    # ASCII だけを数として読む（caxx.c の m_py_int() と同じ受理範囲）。
    if not a[0].isascii():
        raise MacroError(f"{_fmt_pos(pos)}: int({a[0]!r}) is not a number")
    try:
        return int(a[0].strip(), base)
    except ValueError:
        raise MacroError(f"{_fmt_pos(pos)}: int({a[0]!r}) is not a number")


def _bi_case(pp, a, pos, name):
    """`upper(s)` / `lower(s)`（バイト単位、ASCII だけ）。"""
    _bi_check(pp, a, pos, name, 1)
    b = _mb(_as_str(a[0]))
    return _mt(b.upper() if name == 'upper' else b.lower())


def _bi_substr(pp, a, pos):
    """`substr(s, start[, len])`（バイト単位、範囲は切り詰める）。"""
    _bi_check(pp, a, pos, 'substr', 2, 3)
    s = _mb(_as_str(a[0]))
    start = a[1]
    if not isinstance(start, int):
        raise MacroError(f"{_fmt_pos(pos)}: substr() index must be an integer")
    ln = len(s)
    start = min(max(start, 0), ln)
    if len(a) > 2:
        if not isinstance(a[2], int):
            raise MacroError(f"{_fmt_pos(pos)}: substr() length must be an integer")
        cnt = a[2]
    else:
        cnt = ln - start
    cnt = min(max(cnt, 0), ln - start)
    return _mt(s[start:start + cnt])


def _bi_abs(pp, a, pos):
    """`abs(n)`。"""
    _bi_check(pp, a, pos, 'abs', 1)
    if isinstance(a[0], str):
        raise MacroError(f"{_fmt_pos(pos)}: abs() needs an integer")
    return abs(a[0])


def _bi_minmax(pp, a, pos, name):
    """`min(...)` / `max(...)`（同じ値なら先のもの）。"""
    _bi_check(pp, a, pos, name, 1, 64)
    p = _ExprParser('', pp, pos)
    best = a[0]
    for v in a[1:]:
        lt = _cmp_lt_eq(p, v, best, False)
        if lt if name == 'min' else (not lt and not _cmp_eq(v, best)):
            best = v
    return best


def _bi_uid(pp, a, pos):
    """`uid()` — 展開ごとに違う番号（生成したラベル名の衝突を避ける）。"""
    _bi_check(pp, a, pos, 'uid', 0)
    pp.uid += 1
    return pp.uid


def _bi_label(pp, a, pos):
    """`label(name)` — ラベルの値（前回の反復の値）。"""
    _bi_check(pp, a, pos, 'label', 1)
    name = a[0]
    if not isinstance(name, str):
        raise MacroError(f"{_fmt_pos(pos)}: label() needs a string")
    kind, v = pp.asm_label(name)
    if kind == 'no':
        raise MacroError(f"{_fmt_pos(pos)}: no such label or .equ: '{name}'")
    return v


_BUILTINS = {
    'len': _bi_len, 'hex': _bi_hex, 'str': _bi_str, 'int': _bi_int,
    'upper': lambda pp, a, pos: _bi_case(pp, a, pos, 'upper'),
    'lower': lambda pp, a, pos: _bi_case(pp, a, pos, 'lower'),
    'substr': _bi_substr, 'abs': _bi_abs,
    'min': lambda pp, a, pos: _bi_minmax(pp, a, pos, 'min'),
    'max': lambda pp, a, pos: _bi_minmax(pp, a, pos, 'max'),
    'uid': _bi_uid, 'label': _bi_label,
}


class Assembler:
    """アセンブラ全体の組み立てと駆動（入口は run()）。部品をつなぎ、パス1とパス2を回して出力を書く。"""

    def __init__(self):
        st = self.state = AssemblerState()
        self.parser = Parser(st)
        self.var_manager = VariableManager(st)
        self.label_manager = LabelManager(st)
        self.symbol_manager = SymbolManager(st)
        self.expr_eval = ExpressionEvaluator(st, self.var_manager, self.label_manager,
                                             self.symbol_manager, self.parser)
        self.binary_writer = BinaryWriter(st)
        self.directive_proc = DirectiveProcessor(st, self.expr_eval, self.binary_writer,
                                                 self.symbol_manager, self.parser)
        self.pattern_matcher = PatternMatcher(st, self.expr_eval, self.var_manager,
                                              self.symbol_manager, self.parser)
        self.pat_macro_proc = MacroPreprocessor(st, pat_mode=True)
        self.pattern_reader = PatternFileReader(self.parser, self.pat_macro_proc)
        self.obj_gen = ObjectGenerator(st, self.expr_eval, self.binary_writer)
        self.vliw_proc = VLIWProcessor(st, self.expr_eval, self.binary_writer)
        self.asm_directive_proc = AssemblyDirectiveProcessor(st, self.expr_eval, self.binary_writer,
                                                             self.label_manager, self.parser)
        self.macro_proc = MacroPreprocessor(st)
        self._imp_sections: list = []      # (名前, 開始, 大きさ) をファイルの順に
        d = self.asm_directive_proc
        self._adir_first = (d.section_processing, d.endsection_processing,
                            d.resb_processing, d.zero_processing)
        self._adir_rest = (d.align_processing, d.org_processing, d.labelc_processing,
                           d.extern_processing, d.reloctype_processing, d.export_processing,
                           d.cfi_processing, d.type_processing, d.size_processing,
                           d.weak_processing, d.visibility_processing, d.other_processing,
                           d.comm_processing)

    def include_asm(self, l1, l2):
        """ソース側の `.include`（相対パスはいまのファイルの場所から）。"""
        if StringUtils.upper(l1) != ".INCLUDE":
            return False
        st = self.state
        s = StringUtils.get_string(l2)
        if not s:
            raw = l2.strip()
            fallback = StringUtils.get_param_to_spc(raw, 0)[0] if raw else ''
            if not fallback:
                st.diag(f" error - .INCLUDE directive has no filename: {l2!r}", set_error=True)
                return True
            st.diag(f" warning - .INCLUDE filename not quoted: {fallback!r}. "
                    "Please use double quotes.", set_error=False)
            s = fallback
        if s != "stdin" and not os.path.isabs(s):
            cur = st.current_file
            if cur and cur not in ("(stdin)", ""):
                s = os.path.join(os.path.dirname(os.path.abspath(cur)), s)
        self.fileassemble(s)
        return True

    def _dir_line_done(self, l, l2, idx):
        """ディレクティブ行を処理し終えたときの後片付け。"""
        if self.state.textmode:
            return self._passthru_line(l, l2, idx)
        return 0, [], True, idx

    _DIR_SCALAR_FIELDS = ('endian', 'bts', 'padding', 'swordchars')
    _DIR_DICT_FIELDS = ('symbols', 'check_constraints', 'reloc_constraints',
                        'reloc_masks', 'reloc_pairs', 'enum_defs')

    def _snap_dirstate(self):
        """照合中のディレクティブ行が変えうる状態を写し取る。"""
        st = self.state
        snap = {f: getattr(st, f) for f in self._DIR_SCALAR_FIELDS}
        snap.update((f, dict(getattr(st, f))) for f in self._DIR_DICT_FIELDS)
        snap['vliw'] = st.vliw.save()
        return snap

    def _restore_dirstate(self, snap):
        """_snap_dirstate() の状態へ戻す。"""
        st = self.state
        for f in self._DIR_SCALAR_FIELDS:
            setattr(st, f, snap[f])
        for f in self._DIR_DICT_FIELDS:
            setattr(st, f, dict(snap[f]))
        st.vliw.load(snap['vliw'])

    def _clear_vars(self):
        """パターン変数の束縛を消す。"""
        st = self.state
        st.vars, st.vars_undef, st.vars_float, st.vars_text = {}, {}, {}, {}

    _MATCH_EXC = (ArithmeticError, KeyError, IndexError, ValueError,
                  TypeError, AttributeError, OverflowError, struct.error)

    def lineassemble2(self, line, idx):
        """1 命令（VLIW なら 1 スロット）をアセンブルする。返り値は (インデックス, ワード列, 成否, 次の位置)。

        候補のパターンをすべて照合し、特異度スコアが最良のものの error_patterns を評価して、
        通れば binary_list からワード列を作る。
        """
        st = self.state
        l, idx = StringUtils.get_param_to_spc(line, idx)
        l2, idx = StringUtils.get_param_to_eon(line, idx)
        # 落とすのはスペースとタブだけ（caxx.c の lineassemble2_impl() と同じ）。
        l = l.rstrip(' \t').replace(' ', '')
        l2 = l2.rstrip(' \t')
        # 未定義ラベルの印はこの命令の評価だけのもの（前の行から持ち越さない）。
        st.error_undefined_label = False
        # 組み込みディレクティブ（`.org $$+4` など）は通し番地で読む。
        st._sec_frame = False

        if st.textmode and StringUtils.upper(l) in _TEXTMODE_TEXT_ONLY_DIRS:
            return self._passthru_line(l, l2, idx)
        for h in self._adir_first:
            if h(l, l2):
                return self._dir_line_done(l, l2, idx)
        data_words = self.asm_directive_proc.data_processing(l, l2)
        if data_words is not None:
            return 0, data_words, True, idx
        lu = StringUtils.upper(l)
        if lu in ('.ASCII', '.ASCIZ'):
            ok = (self.asm_directive_proc.ascii_processing if lu == '.ASCII'
                  else self.asm_directive_proc.asciiz_processing)(l, l2)
            if not ok and st.should_report_errors():
                st.diag(f" error - {lu}: failed to process string argument: {l2!r}", set_error=True)
            return 0, [], True, idx
        if self.include_asm(l, l2):
            st.comment_text = ''
            st.indent_text = ''
            return 0, [], True, idx
        for h in self._adir_rest:
            if h(l, l2):
                return self._dir_line_done(l, l2, idx)

        if l == "":
            if st.textmode and (st.label_text or st.comment_text):
                return 0, [], True, idx
            return 0, [], False, idx

        # ここからはパターンの照合。-o / -E ではセクション相対で読む（_sec_frame）。
        st._sec_frame = True
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

        if self.state.unordered:
            # `.unordered` ではディレクティブ行を決めておいた順に全部処理してから、パターンだけを試す。
            for _row in self.state.pat_dirorder:
                self._clear_vars()
                _fn = _dirfn[_row]
                if _fn is not None:
                    _fn(_pat[_row])

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
                if self.state.vars_float:
                    self.state.vars_float = {}
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
                    self._clear_vars()
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
                        if _AUP1.get(_ch, _ch) != _pfx[_k]:
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

            self._clear_vars()
            self.state.error_undefined_label = False
            self.state.expcaps = CAPS_ASM
            saved = self.pattern_matcher._try_save()

            _cand_diags = []
            try:
                self.state._in_match_attempt = True
                self.state.diag_capture_begin()
                _match_result = self.pattern_matcher.match0(lin, i[0])
            except self._MATCH_EXC as _pat_exc:
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
                        'vars_float': dict(self.state.vars_float),
                        'vars_text': dict(self.state.vars_text),
                        'refs':  self.state.elf.label_refs_seen[saved[4]:],
                        'v2l':   dict(self.state.elf.var_to_label),
                        'hint':  dict(self.state.elf.insn_reloc_hint),
                        'dir':   self._snap_dirstate(),
                        'error_undefined_label': self.state.error_undefined_label,
                        'diags': _cand_diags,
                    }

                self.pattern_matcher._try_restore(saved)

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

            self._restore_dirstate(best['dir'])
            self.state.vars = dict(best['vars'])
            self.state.vars_undef = dict(best['vars_undef'])
            self.state.vars_float = dict(best['vars_float'])
            self.state.vars_text = dict(best['vars_text'])
            self.state.elf.label_refs_seen.extend(best['refs'])
            self.state.elf.var_to_label = dict(best['v2l'])
            self.state.elf.insn_reloc_hint = dict(best['hint'])
            self.state.error_undefined_label = best.get('error_undefined_label', False)
            self.state.diag_replay(best.get('diags', ()))
            self.state.expcaps = CAPS_ASM

            try:
                self.state.pc_instr_start = self.state.pc
                self.state.pc_instr_end   = self.state.pc_instr_start
                _probe_sm_saved    = self.state.relax.pass1_size_mode
                _probe_refs_len    = len(self.state.elf.label_refs_seen)
                _probe_widx_saved  = self.state.elf.current_word_idx
                _probe_hint_saved  = dict(self.state.elf.insn_reloc_hint)
                self.state.relax.pass1_size_mode = True
                try:
                    _probe_objl = self.obj_gen.makeobj(i[2])
                    self.state.pc_instr_end = self.state.pc_instr_start + len(_probe_objl)
                except Exception:
                    pass
                finally:
                    self.state.relax.pass1_size_mode = _probe_sm_saved
                    del self.state.elf.label_refs_seen[_probe_refs_len:]
                    self.state.elf.current_word_idx = _probe_widx_saved
                    self.state.elf.insn_reloc_hint = _probe_hint_saved
                    self.state.error_undefined_label = best.get('error_undefined_label', False)
                err_triggered, _err_code = self.directive_proc.error(i[1])
                if not err_triggered:
                    objl = self.obj_gen.makeobj(i[2])
                else:
                    objl = []
                idxs, _ = self.expr_eval.expression_pat(i[3], 0)
            except self._MATCH_EXC as _exc:
                if self.state.relax.pas == 1:
                    if self.state.debug:
                        import traceback as _tb
                        print(f" [pass1 forward-ref fallback] {type(_exc).__name__}: {_exc}", file=sys.stderr)
                        _tb.print_exc()
                    try:
                        self.state.relax.pass1_size_mode = True
                        objl = self.obj_gen.makeobj(i[2])
                        idxs, _ = self.expr_eval.expression_pat(i[3], 0)
                    except self._MATCH_EXC:
                        objl = []
                    finally:
                        self.state.relax.pass1_size_mode = False
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
                and not self.state.relax.pass1_size_mode
                and self.state.should_report_errors()):
            self.state.diag(f" warning - .passthru: one or more bytes exceed the "
                            f"output word width ({self.state.bts} bit(s)) and were "
                            f"truncated (high bits discarded): {txt!r}", set_error=False)
        return words

    def _passthru_line(self, l, l2, idx):
        """`.passthru` のとき、当たらなかった行をそのまま出す。"""
        txt = (l + ' ' + l2) if l2 else l
        self.state.error_undefined_label = False
        objl = self._text_words(txt)
        self.state.asmtext = txt
        self.state.asmtext_disp = '"%s"' % asmtext_escaped(txt)
        return 0, objl, True, idx

    def lineassemble(self, line):
        """ソース 1 行を処理する（ラベル・`!!` の分解・テキスト置換モード・-o のリロケーション）。"""
        _ind = line[:len(line) - len(line.lstrip(' \t'))][:511]
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
            for d in (self.state.check_constraints, self.state.reloc_constraints,
                      self.state.reloc_masks, self.state.reloc_pairs, self.state.enum_defs,
                      self.state.freed_subs):
                d.clear()
            self.state.symbols = dict(self.state.patsymbols)

        self.state.label_text = ''
        self.state._data_dir_line = False
        line = self.asm_directive_proc.label_processing(line)

        _vparts = line.replace(VLIW_STOP, VLIW_SEP).split(VLIW_SEP)
        self.state.vliw.cnt = sum(1 for _p in _vparts if _p != '')

        if self.state.elf.objfile and self.state.relax.pas == 2:
            e = self.state.elf
            e.tracking = True
            e.label_refs_seen = []
            e.current_word_idx = -1
            e.var_to_label = {}
            e.capturing_var = None
            e.insn_reloc_hint = {}
            self.state._elf_field_breaks = set()
            self.state._elf_data_fields = set()

        try:
            idxs, objl, flag, idx = self.lineassemble2(line, 0)
        finally:
            self.state.elf.tracking = False
            self.state._sec_frame = False

        if not flag:
            # 先頭のスロットが空の行（`!!ad ...`、`!!!!` だけ）はエラー（caxx.c の lineassemble()）。
            _vl = line.lstrip(' \t')
            if _vl[:1] in (VLIW_SEP, VLIW_STOP) and self.state.should_report_errors():
                self.state.diag(_VLIW_EMPTY_SLOT_MSG, set_error=True)
            return False

        if (self.state.textmode and self.state.label_text
                and not self.state.vliw.flag
                and (self.state.asmtext is not None or not objl)):
            _lpfx = self.state.label_text
            _ltxt = self.state.asmtext
            if _ltxt:
                _lpfx += ' '
            _lbytes = list(_lpfx.encode('utf-8', errors='surrogateescape'))
            objl[0:0] = _lbytes
            self.state.asmtext = _lpfx + (_ltxt or '')
            self.state.asmtext_disp = '"%s"' % asmtext_escaped(self.state.asmtext)
            self._shift_refs(len(_lbytes))

        if (self.state.textmode and self.state.comment_text
                and not self.state.vliw.flag
                and (self.state.asmtext is not None or not objl)):
            _ctxt = self.state.comment_text
            _cur = self.state.asmtext or ''
            _csfx = (' ' + _ctxt) if _cur else _ctxt
            objl.extend(self._text_words(_csfx))
            self.state.asmtext = _cur + _csfx
            self.state.asmtext_disp = '"%s"' % asmtext_escaped(self.state.asmtext)

        if (self.state.textmode and self.state.indent_text
                and not self.state.vliw.flag
                and self.state.asmtext):
            _itxt = self.state.indent_text
            _ibytes = list(_itxt.encode('utf-8', errors='surrogateescape'))
            objl[0:0] = _ibytes
            self.state.asmtext = _itxt + self.state.asmtext
            self.state.asmtext_disp = '"%s"' % asmtext_escaped(self.state.asmtext)
            self._shift_refs(len(_ibytes))

        if (self.state.eol and objl and not self.state.vliw.flag
                and not self.state._data_dir_line):
            objl.append(ord('\n'))

        # `.vliw` の無いパターンファイルで `!!` が続く行はエラー（caxx.c の lineassemble()）。
        _vrest = line[idx:].lstrip(' ')
        if not self.state.vliw.flag and _vrest[:1] in (VLIW_SEP, VLIW_STOP):
            if self.state.should_report_errors():
                self.state.diag(_VLIW_NO_VLIW_MSG, set_error=True)
            return False

        if not self.state.vliw.flag or (idx >= len(line) or line[idx] not in (VLIW_SEP, VLIW_STOP)):
            of = len(objl)
            if self.state.elf.objfile and self.state.relax.pas == 2 and objl and self.state.elf.label_refs_seen:
                bpw_r = max(1, (self.state.bts + 7) // 8)
                sec_name_r = self.state.current_section

                _completed_words = 0
                _entry_pc_cur = 0
                if sec_name_r in self.state.sections:
                    _sentry = self.state.sections[sec_name_r]
                    _completed_words = _sentry[1]
                    _entry_pc_cur = _sentry[2] if len(_sentry) > 2 else _sentry[0]

                valid_refs = sorted((r for r in self.state.elf.label_refs_seen if r[2] >= 0),
                                    key=lambda r: r[2])
                # 同じ（ラベル, ワード位置）は最初の 1 つだけ。
                _seen = set()
                valid_refs = [r for r in valid_refs
                              if (r[0], r[2]) not in _seen and not _seen.add((r[0], r[2]))]

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
                    while (gj < len(valid_refs) and valid_refs[gj][0] == lname
                           and valid_refs[gj][2] == widx + (gj - gi)
                           and valid_refs[gj][2] not in self.state._elf_field_breaks):
                        gj += 1
                    groups.append((lname, abs_w, widx, gj - gi))
                    gi = gj

                _mach_tbl_la = elf_machine_table(self.state)
                _rmap = {**_mach_tbl_la['width_guess'], **self.state.elf.reloctype_override}
                _pc_rel_types_all = _mach_tbl_la['pc_rel']
                # 加数の単位（byte ならワードのバイト数を掛ける）。
                _scale = 1 if _mach_tbl_la['unit'] == 'word' else bpw_r
                _bts = self.state.bts
                _wm = (1 << _bts) - 1
                _little = self.state.endian == 'little'

                def _wsh(k, nw):
                    # 欄の k 番目のワードの、欄の値の中でのシフト量（バイト順に従う）。
                    return _bts * k if _little else _bts * (nw - 1 - k)

                def _field_raw(first, nwords):
                    # 欄のワード列を 1 つの整数に読み、符号を付ける。
                    rv = 0
                    for k in range(nwords):
                        if first + k < len(objl):
                            rv |= (int(objl[first + k]) & _wm) << _wsh(k, nwords)
                    fb = nwords * _bts
                    if fb > 0 and rv >= (1 << (fb - 1)):
                        rv -= (1 << fb)
                    return rv

                def _zero(first, nwords):
                    # RELA では加数を項目が持つので欄は 0 で出す（GNU as と llvm-mc の形）。
                    for k in range(nwords):
                        if first + k < len(objl):
                            objl[first + k] = 0

                def _clear_mask(w, nw, mask):
                    # 命令欄のマスクのビットだけを消す。
                    for k in range(nw):
                        objl[w + k] = int(objl[w + k]) & ~((mask >> _wsh(k, nw)) & _wm) & _wm

                def _sec_off(w):
                    # 出力ワード w のセクションの中のバイト位置。
                    return (_completed_words + (self.state.pc + w - _entry_pc_cur)) * bpw_r

                def _local_here(nm):
                    # 同じセクションの局所ラベル（外部・.equ・.global・.weak でない）か。
                    le = self.state.labels.get(nm)
                    return (le is not None and not (len(le) > 3 and le[3])
                            and not (len(le) > 2 and le[2]) and le[1] and le[1] == sec_name_r
                            and nm not in self.state.export_labels
                            and not _sym_attr(self.state, nm)[_SA_WEAK])

                def _src_type(le, nm, nbytes):
                    # ラベルに付いた型（幅が合うときだけ。型を書かない .extern は除く）。
                    src = le[4] if (le and len(le) > 4 and le[4] is not None) else None
                    if src is not None and nm not in self.state.extern_untyped:
                        ex = _mach_tbl_la['reloc_bytes'].get(src)
                        if ex is None or ex == nbytes:
                            return src
                    return None

                for lname, abs_w, first_widx, num_words in groups:
                    num_bytes = num_words * bpw_r

                    _dinfo = self.state.elf.insn_reloc_hint.get(('d', first_widx))
                    if _dinfo is not None:
                        # ラベル差（ラベルの 1 次結合）。足す項には足す型、引く項には引く型を同じ位置に。
                        # 定数部は最初の足す項（無ければ最初の引く項に符号を反転して）の加数。
                        if first_widx >= len(objl):
                            continue
                        _dterms, _drt, _dcst, _dfmask = _dinfo
                        if _drt is None and len(_dterms) == 2:
                            # 「ラベル − `$$`」（`.elfpcguess::1`）。同じセクションのラベルなら欄の値のまま、
                            # 違えばその幅の PC 相対の型で加数は定数部（caxx.c の lineassemble() と同じ）。
                            _pl = next((n for sg, n in _dterms if sg > 0), None)
                            if _pl is not None and any(sg < 0 and n == '$$' for sg, n in _dterms):
                                _ple = self.state.labels.get(_pl)
                                _same = (_ple is not None and not (len(_ple) > 3 and _ple[3])
                                         and _ple[1] == sec_name_r)
                                if not _same:
                                    _prt = _src_type(_ple, _pl, num_bytes)
                                    # その幅の `.elfdiff` があれば対にし、引く項はこの欄のアンカー
                                    # （llvm-mc が RISC-V の `.quad ext-.` に付ける形）。
                                    _ppair = (_mach_tbl_la['diff'].get(num_bytes)
                                              if _prt is None else None)
                                    if _prt is None and _ppair is None:
                                        _prt = _reloc_data_pcrel(_mach_tbl_la, num_bytes)
                                    if _prt is None and _ppair is None:
                                        if self.state.debug:
                                            self.state.diag(
                                                f" warning - no PC-relative relocation type for a "
                                                f"{num_bytes}-byte reference to '{_pl}'; relocation "
                                                f"omitted.", set_error=False)
                                    else:
                                        if _mach_tbl_la['is_rela']:
                                            _zero(first_widx, num_words)
                                        _psec = _sec_off(first_widx)
                                        self.state.elf.relocations.append(
                                            (sec_name_r, _psec, _pl,
                                             _ppair[0] if _ppair is not None else _prt,
                                             _dcst * _scale, num_bytes, 0))
                                        if _ppair is not None:
                                            _anc = _elf_anchor_at(self.state, sec_name_r, _psec)
                                            self.state.elf.relocations.append(
                                                (sec_name_r, _psec, _anc, _ppair[1], 0, num_bytes, 0))
                                continue
                        _dexpr = ''.join(('+' if sg > 0 else '-') + n for sg, n in _dterms)
                        _dexpr = _dexpr[1:] if _dexpr.startswith('+') else _dexpr
                        # 緩和しない機種で、全ラベルが 1 つのセクションにあり足す項と引く項の数が同じ差は
                        # 定数（欄の値のまま。caxx.c の lineassemble() と同じ）。
                        if not _elf_relaxing(self.state):
                            _dsecs = set()
                            _dok = True
                            for _sg, _n in _dterms:
                                _dle = self.state.labels.get(_n)
                                if (_dle is None or (len(_dle) > 3 and _dle[3])
                                        or not _dle[1]):
                                    _dok = False
                                    break
                                _dsecs.add(_dle[1])
                            if _dok and len(_dsecs) == 1 and sum(sg for sg, _n in _dterms) == 0:
                                continue
                        # `.elfpcguess::1` でその幅の `.elfdiff` が無いとき、「ラベル − いまのセクションの
                        # ラベル」はその位置からの PC 相対（GNU as と llvm-mc の形）。加数は定数部に
                        # 「欄の位置 − 引くラベルの位置」を足したもの（caxx.c の lineassemble() と同じ）。
                        if (_drt is None and len(_dterms) == 2 and _mach_tbl_la['pcrel_guess']):
                            _pl = next((n for sg, n in _dterms if sg > 0), None)
                            _pm = next((n for sg, n in _dterms if sg < 0), None)
                            _mle = self.state.labels.get(_pm) if _pm is not None else None
                            _mw = None
                            if (_pl is not None and _mle is not None
                                    and not (len(_mle) > 3 and _mle[3]) and _mle[1]
                                    and _mle[1] == sec_name_r
                                    and _mach_tbl_la['diff'].get(num_bytes) is None):
                                _mw = self.label_manager._section_relative_offset(
                                    sec_name_r, int(_mle[0]))
                            if _mw is not None:
                                _prt = _src_type(self.state.labels.get(_pl), _pl, num_bytes)
                                if _prt is None:
                                    _prt = _reloc_data_pcrel(_mach_tbl_la, num_bytes)
                                if _prt is None:
                                    if self.state.debug:
                                        self.state.diag(
                                            f" warning - no PC-relative relocation type for a "
                                            f"{num_bytes}-byte reference to '{_pl}'; relocation "
                                            f"omitted.", set_error=False)
                                else:
                                    _pwo = _completed_words + (self.state.pc + first_widx - _entry_pc_cur)
                                    if _mach_tbl_la['is_rela']:
                                        _zero(first_widx, num_words)
                                    self.state.elf.relocations.append(
                                        (sec_name_r, _pwo * bpw_r, _pl, _prt,
                                         (_dcst + (_pwo - _mw)) * _scale, num_bytes, 0))
                                continue
                        _dfd = None
                        if _drt is not None:
                            _dpair = _mach_tbl_la['diff_t'].get(_drt)
                            _dfd = _mach_tbl_la['field'].get(_drt)
                            if _dfd is not None and _dfmask:
                                _dfd = (_dfmask,) + tuple(_dfd[1:])
                        else:
                            _dpair = _mach_tbl_la['diff'].get(num_bytes)
                        if _dpair is None:
                            if self.state.debug:
                                self.state.diag(
                                    f" warning - no .elfdiff pair for the difference "
                                    f"'{_dexpr}'; relocation omitted.", set_error=False)
                            continue
                        if _drt is not None:
                            # 型付きの差: 欄は `.elffield` があればその位置と幅、無ければこの参照のワード列。
                            _dconst = _dcst * _scale
                            _dw = first_widx + (_dfd[1] // bpw_r if _dfd is not None else 0)
                            _dnb = (_mach_tbl_la['reloc_bytes'].get(_drt, 0) or num_bytes) \
                                if _dfd is not None else num_bytes
                            if _dfd is not None and _mach_tbl_la['is_rela']:
                                _nw = max(1, _dnb // bpw_r)
                                if _dw + _nw <= len(objl):
                                    _clear_mask(_dw, _nw, _dfd[0])
                        else:
                            _dconst = (_field_raw(first_widx, num_words) - int(abs_w)) * _scale
                            _dw = first_widx
                            _dnb = num_bytes
                            if _mach_tbl_la['is_rela']:
                                _zero(first_widx, num_words)
                        _dsec = _sec_off(_dw)
                        # 足す項を先に（SET 型のように欄を上書きする足す型が先に効くように）。
                        _dput = False
                        _has_plus = any(sg > 0 for sg, _n in _dterms)
                        _dord = [t for t in _dterms if t[0] > 0] + [t for t in _dterms if t[0] < 0]
                        for sg, n in _dord:
                            _da = 0
                            if not _dput and (sg > 0 or not _has_plus):
                                _da = _dconst if sg > 0 else -_dconst
                                _dput = True
                            self.state.elf.relocations.append(
                                (sec_name_r, _dsec, n, _dpair[0] if sg > 0 else _dpair[1],
                                 _da, _dnb, _dfmask if _dfd is not None else 0))
                        continue

                    _hint = self.state.elf.insn_reloc_hint.get(first_widx)
                    lentry = self.state.labels.get(lname)
                    _src_rtype = lentry[4] if (lentry and len(lentry) > 4
                                               and lentry[4] is not None) else None
                    _forced_rtype = None
                    if _hint is not None:
                        _hint_rtype, _hint_addend, _hint_fmask, _hint_pair = _hint
                        if _src_rtype is not None and lname not in self.state.extern_untyped:
                            _hint_rtype = _src_rtype
                        _fdecl = insn_reloc_field_decl(self.state, _hint_rtype)
                        # `.reloc` の第 4 欄があれば、その行の欄のマスクはそれ。
                        if _fdecl is not None and _hint_fmask:
                            _fdecl = (_hint_fmask,) + tuple(_fdecl[1:])
                        if _fdecl is None:
                            _forced_rtype = _hint_rtype
                        else:
                            _fmask, _foff, _fsh, _fbias = _fdecl
                            _insn_bytes = _mach_tbl_la['reloc_bytes'].get(_hint_rtype, 4)
                            _insn_words = max(1, _insn_bytes // bpw_r)
                            _fw = first_widx + _foff // bpw_r
                            # `.elfresolve`: 同じセクションの局所ラベルへの PC 相対の欄は、リンカが書く値
                            # （ラベル + 加数 + 補正 − 位置）をシフトしてマスクへ詰め、リロケーションは
                            # 出さない（収まらなければエラー。caxx.c の lineassemble() と同じ）。
                            if (_mach_tbl_la.get('resolve') and not _elf_relaxing(self.state)
                                    and _hint_rtype in _mach_tbl_la['resolve']
                                    and _fw + _insn_words <= len(objl)):
                                _lw = None
                                if _local_here(lname):
                                    _rle = self.state.labels[lname]
                                    _lw = self.label_manager._section_relative_offset(
                                        sec_name_r, int(_rle[0]))
                                    # `.section` の無いソースでは範囲の記録が無いので番地のまま。
                                    if _lw is None:
                                        _lw = int(_rle[0])
                                if _lw is not None:
                                    _pw = _completed_words + (self.state.pc + _fw - _entry_pc_cur)
                                    _val = (_lw - _pw) * _scale + _hint_addend * _scale + _fbias
                                    _sv = _val >> _fsh
                                    _nb = bin(_fmask).count('1')
                                    _fits = _nb >= 64 or (-(1 << (_nb - 1)) <= _sv < (1 << (_nb - 1)))
                                    if 0 < _fsh < 63 and (_val & ((1 << _fsh) - 1)) != 0:
                                        _fits = False
                                    if not _fits and self.state.should_report_errors():
                                        self.state.diag(
                                            f" error - the reference to '{lname}' resolved in its "
                                            f"section does not fit the field.  "
                                            f"[{self.state.current_file}:{self.state.ln}]",
                                            set_error=True)
                                    _iv = 0
                                    for _k in range(_insn_words):
                                        _iv |= (int(objl[_fw + _k]) & _wm) << _wsh(_k, _insn_words)
                                    # ビットが並び替わる型（AArch64 の adr、RISC-V の B / J）は `.elfencode`。
                                    _renc = _mach_tbl_la['encode'].get(_hint_rtype)
                                    if _renc is not None:
                                        _rnv = self._elf_call_func('.elfencode', _renc, [_iv, _val])
                                        if _rnv is not None:
                                            _iv = int(_rnv)
                                    else:
                                        _iv = (_iv & ~_fmask) | _field_deposit(_fmask, _sv)
                                    for _k in range(_insn_words):
                                        objl[_fw + _k] = (_iv >> _wsh(_k, _insn_words)) & _wm
                                    continue
                            if _fw + _insn_words <= len(objl):
                                _clear_mask(_fw, _insn_words, _fmask)
                            _sec_rel_h = _sec_off(_fw)
                            # 加数は「オペランドの値 − ラベルの値」に補正を足したもの。
                            self.state.elf.relocations.append(
                                (sec_name_r, _sec_rel_h, lname, _hint_rtype,
                                 _hint_addend * _scale + _fbias, _insn_bytes, _hint_fmask))
                            # `.reloc` の追加の再配置（同じシンボルと加数。`.elfanchor` の型はこの位置の
                            # アンカーを指し、加数は補正だけ）。
                            for _prt_p, _poff_p in (_hint_pair or ()):
                                _pfd = insn_reloc_field_decl(self.state, _prt_p)
                                if _pfd is None:
                                    continue
                                _pbytes = _mach_tbl_la['reloc_bytes'].get(_prt_p, 0) or 4
                                _pwords = max(1, _pbytes // bpw_r)
                                _pw = first_widx + _poff_p // bpw_r
                                if _pw + _pwords > len(objl):
                                    continue
                                if _mach_tbl_la['is_rela']:
                                    _clear_mask(_pw, _pwords, _pfd[0])
                                _panc = _prt_p in _mach_tbl_la.get('anchor', ())
                                _psym = (_elf_anchor_at(self.state, sec_name_r, _sec_rel_h)
                                         if _panc else lname)
                                _psec_p = _sec_off(_pw)
                                self.state.elf.relocations.append(
                                    (sec_name_r, _psec_p, _psym, _prt_p,
                                     (0 if _panc else _hint_addend * _scale) + _pfd[3],
                                     _pbytes, 0))
                            continue

                    rtype = 0
                    _rtype_is_default_guess = False
                    # `.reloctype` はその幅の推測の型（型を書かない `.extern` の既定の型も）を上書きし、
                    # 上書きした型は絶対／PC 相対の選び直しにかけない（caxx.c と同じ）。
                    _rt_src_ovr = self.state.elf.reloctype_override.get(num_bytes)
                    if _forced_rtype is not None:
                        rtype = _forced_rtype
                    elif (_src_rtype is not None
                          and not (_rt_src_ovr is not None and lname in self.state.extern_untyped)):
                        rtype_override = _src_rtype
                        expected = _mach_tbl_la['reloc_bytes'].get(rtype_override)
                        if expected is None or expected == num_bytes:
                            rtype = rtype_override
                        else:
                            rtype = _rmap.get(num_bytes, 0)
                            _rtype_is_default_guess = _rt_src_ovr is None
                    else:
                        rtype = _rmap.get(num_bytes, 0)
                        _rtype_is_default_guess = _rt_src_ovr is None
                    # `.db` などの欄は式の値そのものなので、推測の型は同じ幅の絶対型にする（x86-64 の
                    # 4 バイトの推測は rel32 向けの PC 相対のため）。caxx.c の lineassemble() と同じ。
                    if (first_widx in self.state._elf_data_fields
                            and _forced_rtype is None and _rt_src_ovr is None
                            and (_src_rtype is None or lname in self.state.extern_untyped)):
                        _dabs = _reloc_same_width(_mach_tbl_la, num_bytes, False)
                        if _dabs is not None:
                            rtype = _dabs
                            _rtype_is_default_guess = False

                    if first_widx >= len(objl):
                        continue
                    if rtype == 0:
                        # `.db` などの行では -d が無くても知らせる（caxx.c と同じ）。
                        if self.state.debug or self.state._data_dir_line:
                            self.state.diag(
                                f" warning - no relocation type available for a {num_bytes}-byte "
                                f"reference to '{lname}'; relocation omitted.", set_error=False)
                        continue

                    sec_rel = _sec_off(first_widx)
                    raw_val = 0
                    for k in range(num_words):
                        if first_widx + k < len(objl):
                            if _little:
                                raw_val |= (int(objl[first_widx + k]) & _wm) << (_bts * k)
                            else:
                                raw_val = (raw_val << _bts) | (int(objl[first_widx + k]) & _wm)

                    if (isinstance(abs_w, float) and not math.isfinite(abs_w)) or \
                       _is_undef_derived(abs_w):
                        continue

                    _field_bits = num_words * self.state.bts
                    if _field_bits > 0 and raw_val >= (1 << (_field_bits - 1)):
                        raw_val -= (1 << _field_bits)

                    abs_wi = int(abs_w)

                    if (_rtype_is_default_guess and rtype in _pc_rel_types_all
                            and raw_val == abs_wi):
                        _alt = _reloc_same_width(_mach_tbl_la, num_bytes, False)
                        if _alt is not None:
                            rtype = _alt

                    # 欄がオペランドの値（ラベル＋綴りの定数）を持たなければ、パターンが変位を計算した
                    # として PC 相対の型にする（欄の幅のビットで比べる）。caxx.c の lineassemble() と同じ。
                    _pcg_d = raw_val - (abs_wi + self.state.elf.insn_reloc_hint.get(
                        ('v', first_widx), 0))
                    if 0 < _field_bits < 64:
                        _pcg_d &= (1 << _field_bits) - 1
                    if (_rtype_is_default_guess and _mach_tbl_la['pcrel_guess']
                            and rtype not in _pc_rel_types_all
                            and _pcg_d != 0):
                        _alt = _reloc_data_pcrel(_mach_tbl_la, num_bytes)
                        if _alt is not None:
                            rtype = _alt

                    # `.elfunaligned`: 位置が欄の幅の倍数でなければその型（SPARC の UA64。llvm-mc と同じ）。
                    _ua = _mach_tbl_la.get('unaligned', {}).get(rtype)
                    if _ua is not None and num_bytes > 0 and sec_rel % num_bytes != 0:
                        rtype = _ua

                    # `.elfresolve`: この型が同じセクションの局所ラベルを指すなら、欄はパターンが
                    # 書いたまま（-b と同じ計算）でリロケーションは出さない（緩和する機種は除く）。
                    # `.elffield` の無い型（x86-64 の pc32 など）はここで見る。caxx.c と同じ。
                    if (_mach_tbl_la.get('resolve') and not _elf_relaxing(self.state)
                            and rtype in _mach_tbl_la['resolve'] and _local_here(lname)):
                        continue

                    # 加数はワードで求めてから単位（.elfunit）に直す。
                    if rtype in _pc_rel_types_all:
                        _P_adj = self.label_manager._section_relative_offset(
                            self.state.current_section, self.state.pc + first_widx)
                        _P_w = _P_adj if _P_adj is not None else self.state.pc + first_widx
                        # 欄は幅で切られているので、綴りの定数を除いた部分（位置と変位の基点の差）を
                        # 欄の幅で符号付きに折り返す（caxx.c の lineassemble() と同じ）。
                        _cst = self.state.elf.insn_reloc_hint.get(('v', first_widx), 0)
                        _pd = raw_val - abs_wi + _P_w - _cst
                        if 0 < _field_bits < 64:
                            _pd &= (1 << _field_bits) - 1
                            if _pd >= (1 << (_field_bits - 1)):
                                _pd -= 1 << _field_bits
                        addend = (_cst + _pd) * _scale
                    else:
                        addend = (raw_val - abs_wi) * _scale

                    # REL では書き出しのときに加数を欄へ書き戻す。
                    if _mach_tbl_la['is_rela']:
                        _zero(first_widx, num_words)
                    self.state.elf.relocations.append((sec_name_r, sec_rel, lname, rtype, addend, num_bytes, 0))

            if self.state.elf.gen_debug and self.state.relax.pas == 2 and of > 0:
                self.state.elf.line_map.append(
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

    def _shift_refs(self, n):
        """行の頭に n ワード足したぶん、積んだラベル参照のワード位置をずらす。"""
        if n:
            self.state.elf.label_refs_seen = [
                (nm, v, (w + n) if w >= 0 else w) for (nm, v, w) in self.state.elf.label_refs_seen]

    def lineassemble0(self, line):
        """1 行を処理する外枠。行の前処理と診断の文脈を整える。"""
        self.state._diag_line_seen.clear()
        cleaned = line.replace('\n', '').replace('\r', '')
        _show = (self.state.relax.pas == 2 and self.state.verbose) or self.state.relax.pas == 0
        if _show:
            # 外側の行（.include）の一覧が閉じていなければここで改行する（caxx.c の listing_open）。
            if self.state._listing_open:
                print("")
            self.state.cl = cleaned
            print("%016x " % self.state.pc, end='')
            print(f"{self.state.current_file} {self.state.ln} {self.state.cl} //", end='')
            self.state._listing_open = True
        self.state.asmtext = None
        self.state.asmtext_disp = None
        f = self.lineassemble(cleaned)
        if self.state.asmtext is not None and self.state.relax.pas in (0, 2):
            if _show:
                print(' %s' % (self.state.asmtext_disp or ''), end='')
            elif self.state.text_output:
                print(self.state.asmtext)
        self.state.asmtext = None
        self.state.asmtext_disp = None
        if _show and self.state._listing_open:
            print("")
        if _show:
            self.state._listing_open = False
        self.state.ln += 1
        return f

    _ELF_DECLS = ('.elftype', '.elfmachine', '.elfclass', '.elfrela', '.elfwidth', '.elfextern',
                  '.elfdwarf', '.elfheader', '.elfsection', '.elffield', '.elfpcguess', '.elfrelax',
                  '.elfanchor', '.elfresolve', '.elfbuiltin', '.elfextra', '.elfdiff', '.elfencode',
                  '.elfrinfo', '.elfunit', '.elflink', '.elfgroup', '.elfcfi', '.elfcfiinit',
                  '.elfcfireg', '.elfunaligned')

    def register_elfdecls(self, pat):
        """パターンファイル中の ELF 記述ディレクティブを先に読んでおく。"""
        table = {n: getattr(self.directive_proc, n[1:] + '_processing') for n in self._ELF_DECLS}
        for i in pat:
            if i and i[0] in table:
                table[i[0]](i)
        self.check_elfdecls()

    def elf_desc_text(self):
        """`--elfdesc` — 実効の ELF マシン記述を `.elfbuiltin::0` から始まる宣言の形で返す。

        組み込みの表なしで同じ ELF が出る。型は名前（無ければ番号）。caxx.c の elf_desc_print() と同じ。
        """
        st = self.state
        e = st.elf
        tbl = elf_machine_table(st)
        named = tbl['named']

        def tname(rt):
            nm = tbl['reverse'].get(rt, '')
            if nm and named.get(nm) == rt:
                return nm
            return str(rt)

        out = ['.elfbuiltin::0']
        nm = tbl['name']
        if nm and nm != "machine %d" % e.machine:
            out.append(".elfmachine::%d::%s" % (e.machine, nm))
        else:
            out.append(".elfmachine::%d" % e.machine)
        out.append(".elfclass::%d" % (64 if tbl['elfclass'] == 2 else 32))
        out.append(".elfrela::%d" % (1 if tbl['is_rela'] else 0))
        for tn, rt in named.items():
            w = tbl['reloc_bytes'].get(rt, 0)
            pc = rt in tbl['pc_rel']
            line = ".elftype::%s::%d" % (tn, rt)
            if w or pc:
                line += "::%s" % (str(w) if w else '')
            if pc:
                line += "::1"
            out.append(line)
        # 型 0（その幅には型が無い）は書かない。
        for nb in sorted(tbl['width_guess']):
            if tbl['width_guess'][nb]:
                out.append(".elfwidth::%d::%s" % (nb, tname(tbl['width_guess'][nb])))
        out.append(".elfextern::%s" % tname(tbl['extern_default']))
        out.append(".elfdwarf::%s" % tname(tbl['dwarf_abs']))
        out.append(".elfpcguess::%d" % (1 if tbl['pcrel_guess'] else 0))
        if e.decl_relax is not None:
            out.append(".elfrelax::%d" % e.decl_relax)
        out += [".elfanchor::%s" % t for t in e.decl_anchor]
        out += [".elfresolve::%s" % t for t in e.decl_resolve]
        for rt in sorted(tbl['unaligned']):
            out.append(".elfunaligned::%s::%s" % (tname(rt), tname(tbl['unaligned'][rt])))
        out.append(".elfunit::%s" % tbl['unit'])
        for w in sorted(tbl['diff']):
            ra, rb = tbl['diff'][w]
            out.append(".elfdiff::%d::%s::%s" % (w, tname(ra), tname(rb)))
        for rt in sorted(tbl['diff_t']):
            ra, rb = tbl['diff_t'][rt]
            out.append(".elfdiff::%s::%s::%s" % (tname(rt), tname(ra), tname(rb)))
        for rt in sorted(tbl['extra']):
            for crt, csym in tbl['extra'][rt]:
                out.append(".elfextra::%s::%s::%d" % (tname(rt), tname(crt), csym))
        for rt in sorted(tbl['encode']):
            out.append(".elfencode::%s::%s" % (tname(rt), tbl['encode'][rt]))
        if tbl['rinfo']:
            out.append(".elfrinfo::%s" % tbl['rinfo'])
        if e.decl_cfi is not None:
            ra, ca, da, pad = e.decl_cfi
            out.append(".elfcfi::%d::%d::%d%s" % (ra, ca, da, ("::%d" % pad) if pad else ''))
        for t in e.decl_cfiinit:
            out.append(".elfcfiinit::%s" % t)
        for nm in sorted(e.decl_cfireg):
            out.append(".elfcfireg::%s::%d" % (nm, e.decl_cfireg[nm]))
        for rt in sorted(tbl['field']):
            m, off, sh, bias = tbl['field'][rt]
            out.append(".elffield::%s::0x%x::%d::%d::%d" % (tname(rt), m, off, sh, bias))
        for fld in ('type', 'flags', 'version', 'entry', 'osabi', 'abiversion'):
            if fld in e.decl_hdr:
                out.append(".elfheader::%s::0x%x" % (fld, e.decl_hdr[fld]))
        for sn in sorted(e.decl_sec):
            d = e.decl_sec[sn]
            line = ".elfsection::%s::0x%x" % (sn, d[0])
            rest = [d[k] if len(d) > k else None for k in (1, 2, 3)]
            while rest and rest[-1] is None:
                rest.pop()
            for v in rest:
                line += "::" + ('' if v is None else "%d" % v)
            out.append(line)
        for sn in sorted(e.decl_link):
            lk, inf = e.decl_link[sn]
            out.append(".elflink::%s::%s%s" % (sn, lk, ("::" + inf) if inf else ''))
        for (gn, sig, fl, mem) in e.decl_group.values():
            out.append(".elfgroup::%s::%s::0x%x::%s" % (gn, sig, fl, ','.join(mem)))
        return '\n'.join(out) + '\n'

    def check_elfdecls(self):
        """ELF 記述の宣言に未知の型や無い関数が無いかを検査する（-o のときだけ）。"""
        if not self.state.elf.objfile:
            return
        st = self.state
        e = st.elf
        tbl = elf_machine_table(st)
        named = tbl['named']
        checks = [('.elfwidth', e.decl_width[w]) for w in sorted(e.decl_width)]
        checks += [(dn, t) for dn, t in (('.elfextern', e.decl_extern), ('.elfdwarf', e.decl_dwarf)) if t]
        checks += [('.elffield', t) for t in e.decl_field]
        checks += [('.elfextra', tt) for t, comps in e.decl_extra.items() for tt in (t,) + tuple(comps)]
        checks += [('.elfdiff', tt) for w in sorted(e.decl_diff) for tt in e.decl_diff[w]]
        checks += [('.elfdiff', tt) for t, pair in e.decl_diff_t.items() for tt in (t,) + pair]
        checks += [('.elfunaligned', tt) for t, u in e.decl_unaligned.items() for tt in (t, u)]
        checks += [('.elfencode', t) for t in e.decl_encode]
        for dname, t in checks:
            if _elf_decl_type(st, named, t) is None:
                st.diag(f" warning - {dname}: unknown relocation type '{t}' "
                        f"for {tbl['name']}; ignored.", set_error=False)
        fchk = [('.elfencode', fn) for fn in e.decl_encode.values()]
        if e.decl_rinfo:
            fchk.append(('.elfrinfo', e.decl_rinfo))
        for dname, fn in fchk:
            f = st.func_defs.get(fn)
            if f is None:
                st.diag(f" error - {dname}: no function named '{fn}'.", set_error=True)
            elif len(f.params) != 2:
                st.diag(f" error - {dname}: function '{fn}' must take 2 arguments.", set_error=True)

    def setpatsymbols(self, pat):
        """パターンファイルが定義するシンボルを先に集める（ソースのラベルとの衝突を検査するため）。"""
        st = self.state
        fresh = {}
        st.strsymbols = {}
        st.arrsymbols = {}
        st.arrgen += 1

        def drop(key):
            fresh.pop(key, None)
            st.strsymbols.pop(key, None)
            st.arrsymbols.pop(key, None)
            st.arrgen += 1

        for i in pat:
            if not i:
                continue
            nm = i[0]
            if nm == '.setsym':
                if len(i) >= 2 and i[1]:
                    key = StringUtils.upper(i[1])
                    st.symbols = dict(fresh)
                    value_field = i[2] if len(i) >= 3 else ''
                    vf = value_field.lstrip(' \t')
                    if vf.startswith('"'):
                        st.strsymbols[key] = ObjectGenerator._txt_template_inner(vf)
                    elif vf.startswith('['):
                        st.arrsymbols[key] = arr_items_from_text(self.expr_eval, vf)
                    elif not (symbol_copy_from_name(st, key, vf)
                              or symbol_set_from_text(st, key, value_field)):
                        fresh[key] = self.expr_eval.expression_pat(value_field, 0)[0] if value_field else 0
                elif len(i) >= 3 and i[2]:
                    fresh[StringUtils.upper(i[2])] = 0
            elif nm == '.clearsym':
                if len(i) >= 3 and i[2] != '':
                    drop(StringUtils.upper(i[2]))
                else:
                    fresh = {}
                    st.strsymbols = {}
                    st.arrsymbols = {}
                    st.arrgen += 1
            elif nm == '.map':
                if not st.unordered:
                    st.symbols = dict(fresh)
                    self.directive_proc.map_apply(i, into=fresh, set_check=False)
            elif nm == '.free':
                names = (i[2] if len(i) >= 3 and i[2] else (i[1] if len(i) >= 2 else ''))
                for n in names.split(','):
                    if n.strip():
                        drop(StringUtils.upper(n.strip()))
            elif nm == '.bits':
                self.directive_proc.bits(i)
        st.patsymbols = fresh
        st.symbols = dict(fresh)

    def fileassemble(self, fn):
        """ソースファイル 1 つを 1 行ずつアセンブルする（`.include` は 100 段まで、循環はエラー）。"""
        st = self.state
        if not st.fnstack:
            self.macro_proc.reset_pass()
        if len(st.fnstack) >= 100:
            st.diag(f" error - .INCLUDE nesting depth exceeds 100: '{fn}'", set_error=True)
            return

        def absname(f, special):
            try:
                return f if f in special else os.path.abspath(f)
            except Exception:
                return f
        abs_fn = absname(fn, ("stdin", ""))
        if any(abs_fn == absname(a, ("stdin", "", "(stdin)")) for a in st.fnstack):
            st.diag(f" error - circular .INCLUDE detected: '{fn}' is already being assembled.", set_error=True)
            return

        _caller_file = st.current_file
        st.fnstack.append(fn)
        st.lnstack.append(st.ln)
        # 現在のファイルを切り替えるのは開けた後（開けない診断には .include の行の場所が付く）。
        _self_file = fn

        try:
            if fn == "stdin":
                if self.state.stdin_tmp_path is None:
                    fd, tmp_path = tempfile.mkstemp(prefix="axx_", suffix=".tmp", text=True)
                    os.close(fd)
                    self.state.stdin_tmp_path = tmp_path
                    af = self.file_input_from_stdin()
                    with open(self.state.stdin_tmp_path, "wb") as stdintmp:
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
            self.state.current_file = _self_file
            self.state.ln = 1
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
        """ソースが `stdin` のとき標準入力をバイトのまま読む（一時ファイル経由で普通に読む）。"""
        return sys.stdin.buffer.read()

    _IMP_HEX_RE = re.compile(r'[ \t]*([+-]?)(?:0[xX])?([0-9A-Fa-f]+)[ \t]*\Z')

    @classmethod
    def _imp_hex(cls, s):
        """インポートファイルの値の欄（空白・符号・`0x` は任意、16 進、|値| < 2**192）。caxx.c の imp_parse_hex()。"""
        m = cls._IMP_HEX_RE.match(s)
        if not m:
            return None
        v = int(m.group(2), 16)
        if v >= 1 << 192:
            return None
        return -v if m.group(1) == '-' else v

    def imp_label(self, l):
        """`-i` のインポートファイルの 1 行（セクションの行か `ラベル[::型]\t値`）を取り込む。"""
        l = l.rstrip('\r\n')
        if not l:
            return False
        fields = l.split('\t')
        if len(fields) >= 3:
            start = self._imp_hex(fields[1])
            size = self._imp_hex(fields[2])
            if start is None or size is None:
                return False
            self._imp_sections.append((fields[0], start, size))
            return True
        if len(fields) != 2 or not fields[0]:
            return False
        label = fields[0]
        reloc_type = None
        if '::' in label:
            label, rt_str = label.split('::', 1)
            reloc_type = _reloc_named(self.state, elf_machine_table(self.state), rt_str)
            if reloc_type is None:
                self.state.diag(f" warning - unknown reloc type '{rt_str}' for imported label '{label}'", set_error=False)
        if not label:
            return False
        v = self._imp_hex(fields[1])
        if v is None:
            return False
        # セクションの行はファイルに書かれた順に見る（caxx.c と同じ）。
        section = next((sn for sn, start, size in self._imp_sections
                        if ((start <= v < start + size) if size > 0 else (size == 0 and v == start))),
                       '.text')
        entry = [v // max(1, (self.state.bts + 7) // 8), section, False, True]
        if reloc_type is not None:
            entry.append(reloc_type)
        self.state.labels[label] = entry
        return True

    def printaddr(self, pc):
        """リスティングの行頭のアドレスを出す。"""
        print("%016x: " % pc, end='')

    def _section_word_ranges(self, name):
        """そのセクションが占めるワード範囲の並び。"""
        ranges = [(rs, rl) for (rn, rs, rl) in self.state.section_ranges if rn == name]
        if ranges:
            return ranges
        entry = self.state.sections.get(name)
        return [(entry[0], entry[1])] if entry and entry[1] > 0 else []

    def _addr_to_word_offset(self, name, word_pc):
        """絶対番地をそのセクションの中のワード位置に直す（範囲外は None）。"""
        if not self.state.sections:
            return word_pc
        cum = 0
        for rs, rl in self._section_word_ranges(name):
            if rs <= word_pc <= rs + rl:
                return cum + (word_pc - rs)
            cum += rl
        return None

    def _build_dwarf_sections(self, csecs, sec_name_to_idx, bpw, machine):
        """`-g` の `.debug_info` / `.debug_abbrev` / `.debug_line` を組む（行表は line_map から）。"""
        line_map = self.state.elf.line_map
        if not self.state.elf.gen_debug or not line_map:
            return [], []

        _mach_tbl_dw = elf_machine_table(self.state)
        _native_dw   = _mach_tbl_dw['elfclass']
        _eff_class_dw = self.state.elf.elf_class or _native_dw
        if not _mach_tbl_dw['dwarf_abs']:
            self.state.diag(f" warning - DWARF debug info (-g) needs an absolute "
                 f"relocation type for machine {machine}; declare it with .elfdwarf. "
                 f"Skipping debug sections.", set_error=False)
            return [], []

        _struct = struct
        _pk = '<' if self.state.endian != 'big' else '>'

        is_elf64_dw = (_eff_class_dw == 2)
        addr_sz = 8 if is_elf64_dw else 4
        is_rela_dw = _mach_tbl_dw.get('is_rela', True)

        def _pack_addr(v):
            return _struct.pack(_pk + ('I' if addr_sz == 4 else 'Q'), v & ((1 << (addr_sz * 8)) - 1))

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

        _uleb, _sleb = _cfi_uleb, _cfi_sleb

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

        # min_inst_length, max_ops, default_is_stmt, line_base, line_range, opcode_base,
        # standard_opcode_lengths, include_directories（空）。
        hbody = bytearray([1, 1, 1, 0xfb, 14, 13, 0, 1, 1, 1, 1, 0, 0, 0, 1, 0, 0, 1, 0])
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
            bits = 63 if is_elf64_dw else 31
            fmt = _pk + ('QQ' if is_elf64_dw else 'II')
            for (off, sym, rtype, addend) in entries:
                r_info = self._elf_r_info(sym, rtype, is_elf64_dw)
                if is_rela_dw:
                    a = min((1 << bits) - 1, max(-(1 << bits), addend))
                    out += _struct.pack(fmt + ('q' if is_elf64_dw else 'i'), off, r_info, a)
                else:
                    out += _struct.pack(fmt, off, r_info)
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

    def _elf_call_func(self, dname, fname, args):
        """`.elfencode` / `.elfrinfo` のミニ言語の関数を呼び、返した数を返す（失敗は None）。caxx.c の elf_call_func()。"""
        fn = self.state.func_defs.get(fname)
        if fn is None:
            return None
        saved_reclimit = sys.getrecursionlimit()
        if saved_reclimit < _MINI_RECLIMIT:
            sys.setrecursionlimit(_MINI_RECLIMIT)
        try:
            _words, ret = MiniInterp(self.state, self.expr_eval).run(
                fn, list(args), (fn.file, fn.line))
        except MiniLangError as e:
            self.state.diag(f" error - {dname}: {e}", set_error=True)
            return None
        except RecursionError:
            self.state.diag(f" error - {dname}: '{fname}': expression nesting too deep.",
                            set_error=True)
            return None
        finally:
            sys.setrecursionlimit(saved_reclimit)
        if ret is None or isinstance(ret, (list, bytes)):
            self.state.diag(f" error - {dname}: function '{fname}' must return a number.",
                            set_error=True)
            return None
        return _mini_wrap(ret)

    def _cfi_relax(self, mach):
        """CFI の範囲をリロケーションで書くか（`.elfdiff::4` があるとき）。"""
        if not _elf_relaxing(self.state):
            return None
        return mach['diff'].get(4) if self.state.elf.cfi_fdes else None

    def _cfi_points(self, bpw):
        """リンカ緩和の機種で CFI が局所シンボルを要る (セクション, バイト位置) の並び。caxx.c の cfi_points() と同じ。

        各 FDE の先頭・位置の進む命令の位置・終わりを、初めて現れた順に。
        """
        out = []
        seen = set()
        for fde in self.state.elf.cfi_fdes:
            sec = fde['sec']
            pts = [fde['start'] * bpw]
            cur = fde['start'] * bpw
            for (off, _op, _v) in fde['ops']:
                ob = off * bpw
                if ob > cur:
                    pts.append(ob)
                    cur = ob
            pts.append(fde['end'] * bpw)
            for b in pts:
                if (sec, b) not in seen:
                    seen.add((sec, b))
                    out.append((sec, b))
        return out

    def _build_eh_frame(self, mach, is_elf64, is_rela, pk, bpw, sec_sym, synth, sym_name_to_idx):
        """ソースの `.cfi_*` から `.eh_frame` を組む。caxx.c の build_eh_frame() と同じ。

        返り値は (バイト列, [(位置, シンボル番号, 型, 加数)])。CIE の欄は `.elfcfi`、初期命令は
        `.elfcfiinit`、FDE の開始番地は 4 バイトの PC 相対型。`.elfdiff::4` があれば長さと位置の
        進みを足す型・引く型の対で書き、synth の局所シンボルを使う。
        """
        e = self.state.elf
        if not e.cfi_fdes:
            return b'', []
        if e.decl_cfi is None:
            self.state.diag(" error - CFI: the pattern file has no .elfcfi declaration.",
                            set_error=True)
            return b'', []
        ra0, code, da, pad = e.decl_cfi
        psize = 8 if is_elf64 else 4
        if not pad:
            pad = psize
        pcrel4 = _reloc_data_pcrel(mach, 4)
        if pcrel4 is None:
            self.state.diag(" error - CFI: no 4-byte PC-relative relocation type for the "
                            "FDE address; declare one with .elftype.", set_error=True)
            return b'', []
        relax = self._cfi_relax(mach)
        if relax and code != 1:
            self.state.diag(" error - CFI: relocated advances need a code alignment "
                            "factor of 1.", set_error=True)
            return b'', []
        init_ops = []
        for t in e.decl_cfiinit:
            w = t.split(' ', 1)
            op = w[0].translate(_ALOWER)
            spec = _CFI_OPS.get(op)
            args = [a.strip() for a in w[1].split(',')] if len(w) > 1 and w[1].strip() else []
            ok = spec is not None and op not in ('startproc', 'endproc', 'sections',
                                                 'return_column', 'signal_frame',
                                                 'personality', 'lsda', 'adjust_cfa_offset',
                                                 'rel_offset', 'remember_state',
                                                 'restore_state')
            if ok and spec != '*' and len(args) != len(spec):
                ok = False
            vals = []
            for a in args if ok else []:
                r = e.decl_cfireg.get(a.translate(_ALOWER))
                if r is None:
                    m = re.match(r'^([+-]?)(0[xX][0-9a-fA-F]+|[0-9]+)$', a)
                    if m is None:
                        ok = False
                        break
                    r = int(m.group(2), 0 if m.group(2)[:2].translate(_ALOWER) == '0x' else 10)
                    if m.group(1) == '-':
                        r = -r
                if spec == '*' and not 0 <= r <= 255:
                    ok = False
                    break
                vals.append(r)
            if not ok:
                self.state.diag(f" error - .elfcfiinit: cannot use '{t}'.", set_error=True)
                return b'', []
            init_ops.append((op, tuple(vals)))

        data = bytearray()
        relocs = []

        def ptr(enc, symname, at):
            # 符号化 enc のポインタを 0 で置き、リロケーションを足す。
            n = _cfi_ptr_size(enc, psize)
            app = enc & 0x70
            if n == 0 or app not in (0x00, 0x10):
                self.state.diag(f" error - CFI: pointer encoding 0x{enc:02x} is not supported.",
                                set_error=True)
                return bytes(n)
            rt = (_reloc_data_pcrel(mach, n) if app == 0x10
                  else _reloc_data_abs(mach, n))
            if not rt:
                self.state.diag(f" error - CFI: no relocation type for a {n}-byte pointer "
                                f"(encoding 0x{enc:02x}).", set_error=True)
                return bytes(n)
            si = sym_name_to_idx.get(symname)
            if si is None:
                self.state.diag(f" error - CFI: unknown symbol '{symname}'.", set_error=True)
                return bytes(n)
            relocs.append((at, si, rt, 0))
            return bytes(n)

        def emit(body):
            # 長さの欄を付け、詰めて足す。
            tot = 4 + len(body)
            body += bytes((-tot) % pad)
            data.extend(_struct_pack(f'{pk}I', len(body)) + body)

        def run_ops(ops, stt, body_len_base, body):
            for (op, vals) in ops:
                b = _cfi_op_bytes(op, vals, stt, da)
                if isinstance(b, str):
                    self.state.diag(f" error - CFI: .cfi_{op}: {b}.", set_error=True)
                    continue
                body += b

        cies = {}
        for fde in e.cfi_fdes:
            sec = fde['sec']
            if sec not in sec_sym:
                self.state.diag(f" error - CFI: section '{sec}' of a function is not in "
                                f"the output.", set_error=True)
                continue
            ra = fde['ra'] if fde['ra'] is not None else ra0
            lenc = fde['lsda'][0] if fde['lsda'] else None
            key = (ra, fde['signal'], fde['simple'], fde['pers'], lenc)
            if key not in cies:
                c_off = len(data)
                cies[key] = c_off
                ver = 1 if ra <= 255 else 3
                body = bytearray(_struct_pack(f'{pk}I', 0))
                body.append(ver)
                aug = 'z' + ('P' if fde['pers'] else '') + ('L' if fde['lsda'] else '') \
                    + 'R' + ('S' if fde['signal'] else '')
                body += aug.encode() + b'\x00' + _cfi_uleb(code) + _cfi_sleb(da)
                body += bytes([ra]) if ver == 1 else _cfi_uleb(ra)
                augd = bytearray()
                p_pos = None
                if fde['pers']:
                    augd.append(fde['pers'][0])
                    p_pos = len(augd)
                    augd += bytes(_cfi_ptr_size(fde['pers'][0], psize))
                if fde['lsda']:
                    augd.append(lenc)
                augd.append(0x1b)
                lb = _cfi_uleb(len(augd))
                if p_pos is not None:
                    at = c_off + 4 + len(body) + len(lb) + p_pos
                    pb = ptr(fde['pers'][0], fde['pers'][1], at)
                    augd[p_pos:p_pos + len(pb)] = pb
                body += lb + augd
                if not fde['simple']:
                    run_ops(init_ops, [0, 0, []], 0, body)
                emit(body)
            c_off = cies[key]
            f_off = len(data)
            stt = [0, 0, []]
            if not fde['simple']:
                scratch = bytearray()
                run_ops(init_ops, stt, 0, scratch)
                stt[2] = []
            sb = fde['start'] * bpw
            eb = fde['end'] * bpw
            body = bytearray(_struct_pack(f'{pk}I', (f_off + 4) - c_off))
            at = f_off + 4 + len(body)
            if relax:
                relocs.append((at, synth[(sec, sb)], pcrel4, 0))
                body += bytes(4)
            else:
                relocs.append((at, sec_sym[sec], pcrel4, sb))
                body += _struct_pack(f'{pk}I', 0 if is_rela else sb & 0xFFFFFFFF)
            at = f_off + 4 + len(body)
            if relax:
                relocs.append((at, synth[(sec, eb)], relax[0], 0))
                relocs.append((at, synth[(sec, sb)], relax[1], 0))
                body += bytes(4)
            else:
                body += _struct_pack(f'{pk}I', (eb - sb) & 0xFFFFFFFF)
            if fde['lsda']:
                n = _cfi_ptr_size(lenc, psize)
                body += _cfi_uleb(n)
                at = f_off + 4 + len(body)
                body += ptr(lenc, fde['lsda'][1], at)
            else:
                body += _cfi_uleb(0)
            cur = sb
            for (off, op, vals) in fde['ops']:
                ob = off * bpw
                if ob < cur:
                    self.state.diag(f" error - CFI: a .cfi_{op} is placed before the "
                                    f"previous one.", set_error=True)
                    continue
                if ob > cur:
                    if relax:
                        at = f_off + 4 + len(body) + 1
                        relocs.append((at, synth[(sec, ob)], relax[0], 0))
                        relocs.append((at, synth[(sec, cur)], relax[1], 0))
                        body += bytes([0x04]) + bytes(4)
                    else:
                        d = ob - cur
                        if d % code != 0:
                            self.state.diag(f" error - CFI: an advance of {d} bytes is not a "
                                            f"multiple of the code alignment factor {code}.",
                                            set_error=True)
                        f = d // code
                        if f < 64:
                            body.append(0x40 | f)
                        elif f <= 0xff:
                            body += bytes([0x02, f])
                        elif f <= 0xffff:
                            body += bytes([0x03]) + _struct_pack(f'{pk}H', f)
                        else:
                            body += bytes([0x04]) + _struct_pack(f'{pk}I', f & 0xFFFFFFFF)
                    cur = ob
                run_ops([(op, vals)], stt, 0, body)
            emit(body)
        return bytes(data), relocs

    def _elf_r_info(self, sym, rtype, is_elf64):
        """r_info を組む。`.elfrinfo` があればその関数、無ければ ELF の決まりの形。"""
        fn = elf_machine_table(self.state)['rinfo']
        if fn:
            v = self._elf_call_func('.elfrinfo', fn, [sym, rtype])
            v = 0 if v is None else v
            return v & (0xFFFFFFFFFFFFFFFF if is_elf64 else 0xFFFFFFFF)
        if is_elf64:
            return (sym << 32) | (rtype & 0xffffffff)
        return ((sym & 0xffffff) << 8) | (rtype & 0xff)

    def write_elf_obj(self, path: str, machine: int = 62) -> None:
        """ELF 再配置可能オブジェクトを書く（セクション・シンボル表・リロケーション、-g なら DWARF）。

        マシン記述は elf_machine_table() の実表から取る。型の決まらない参照はリロケーションを出さない。
        """
        import struct as _struct

        bpw = max(1, (self.state.bts + 7) // 8)
        buf = self.binary_writer._buffer

        _is_le    = (self.state.endian != 'big')
        _ei_data  = 1 if _is_le else 2
        _pk       = '<' if _is_le else '>'

        _mach_tbl_w = elf_machine_table(self.state)
        _native_elfclass = _mach_tbl_w['elfclass']
        _elfclass  = self.state.elf.elf_class or _native_elfclass
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
        _ei_osabi   = _hdr.get('osabi', self.state.elf.osabi) & 0xFF
        _ei_abiver  = _hdr.get('abiversion', 0) & 0xFF

        def _pack_ehdr(e_type, e_machine, e_shoff, e_shnum, e_shstrndx):
            e_type = _hdr.get('type', e_type) & 0xFFFF
            ident = (b'\x7fELF'
                     + bytes([2 if _is_elf64 else 1, _ei_data, 1, _ei_osabi, _ei_abiver])
                     + b'\x00' * 7)
            # e_phoff は 0、プログラムヘッダは無い。e_shentsize は 64 / 40。
            return ident + _struct.pack(_pk + ('HHIQQQIHHHHHH' if _is_elf64 else 'HHIIIIIHHHHHH'),
                                        e_type, e_machine, _e_version, _e_entry, 0, e_shoff,
                                        _e_flags, _ehdr_size, 0, 0, 64 if _is_elf64 else 40,
                                        e_shnum, e_shstrndx)

        def _pack_shdr(sh_name, sh_type, sh_flags, sh_addr, sh_offset,
                       sh_size, sh_link, sh_info, sh_addralign, sh_entsize):
            return _struct.pack(_pk + ('IIQQQQIIQQ' if _is_elf64 else 'IIIIIIIIII'),
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

        _order = 'little' if self.state.endian == 'little' else 'big'

        def _extract(w_start, w_count):
            # ワード w_start から w_count 個を、隙間は `.padding` で埋めたバイト列にする。
            if w_count * bpw == 0:
                return b''
            pad = int(self.state.padding) & ((1 << self.state.bts) - 1)
            data = bytearray(pad.to_bytes(bpw, _order) * w_count if pad else w_count * bpw)
            for pos, val in buf.items():
                if w_start <= pos < w_start + w_count:
                    off = (pos - w_start) * bpw
                    data[off:off + bpw] = (val & ((1 << (8 * bpw)) - 1)).to_bytes(bpw, _order)
            return bytes(data)

        class _CSec:
            """ELF へ書くセクション 1 つぶん（名前・位置・中身・属性）。"""
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

        # 中身の大きさに -b と同じ上限を置く（caxx.c の write_elf_obj() と同じ数え方）。
        _MAX_OUTPUT_BYTES = 1 << 30
        # .section を使わないとき、暗黙の .text は語 0 から最後の位置カウンタまで（末尾の .org で
        # 進めた分も入れる。caxx.c の write_elf_obj() の _end_w と同じ）。
        _end_w = self.state.pc if isinstance(self.state.pc, int) and self.state.pc > 0 else 0
        if self.state.sections:
            _tot_w = sum(rl for _sn in self.state.sections
                         for _rs, rl in self._section_word_ranges(_sn))
        else:
            _tot_w = max(max(buf.keys(), default=-1) + 1, _end_w)
        if _tot_w * bpw > _MAX_OUTPUT_BYTES:
            self.state.diag(f" error - output size {_tot_w * bpw} bytes exceeds maximum "
                            f"{_MAX_OUTPUT_BYTES}. Check for incorrect .ORG or address "
                            f"values.", set_error=True, force=True)
            return

        csecs = []
        max_w = max(buf.keys(), default=-1)

        if not self.state.sections:
            w_count = max(max_w + 1 if max_w >= 0 else 0, _end_w)
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
        _extra_w = _mach_tbl_w['extra']
        for (sname, off, sym_name, rtype, addend, nbytes, fmask) in self.state.elf.relocations:
            sidx = sec_name_to_idx.get(sname, 0)
            if sidx:
                rela_entries[sidx].append((off, sym_name, rtype, addend, nbytes, fmask))
                # `.elfextra` の添えるリロケーション。同じ位置、加数 0。
                for (_crt, _csym) in _extra_w.get(rtype, ()):
                    rela_entries[sidx].append(
                        (off, sym_name if _csym else None, _crt, 0, nbytes, 0))
            else:
                if self.state.should_report_errors():
                    self.state.diag(
                        f" error - relocation references unknown section '{sname}'; dropped from output.",
                        set_error=True)

        if not _is_rela:
            _wmask_r = (1 << self.state.bts) - 1
            _enc_w = _mach_tbl_w['encode']

            def _rd_field(patched, off, nw):
                # 欄の nw ワードを 1 つの値に読む。
                v = 0
                for k in range(nw):
                    w = int.from_bytes(patched[off + k * bpw: off + (k + 1) * bpw], _order)
                    v |= (w & _wmask_r) << (self.state.bts * (k if _is_le else (nw - 1 - k)))
                return v

            def _wr_field(patched, off, nw, v):
                # 値を欄の nw ワードへ書き戻す。
                for k in range(nw):
                    w = (v >> (self.state.bts * (k if _is_le else (nw - 1 - k)))) & _wmask_r
                    patched[off + k * bpw: off + (k + 1) * bpw] = w.to_bytes(bpw, _order)
            for sidx, entries in rela_entries.items():
                csec = csecs[sidx - 1]
                patched = bytearray(csec.data)
                # 同じ位置に複数の項目があるとき（`.elfdiff` の対、`.elfextra`）は
                # 最初の項目の加数だけを書き戻す。後の項目の 0 で消さないため。
                _written = set()
                for (off, _sym_name, _rtype, addend, nbytes, _fmask) in entries:
                    if off in _written:
                        continue
                    _written.add(off)
                    _fd = _mach_tbl_w['field'].get(_rtype)
                    if _fd is not None and _fmask:
                        _fd = (_fmask,) + tuple(_fd[1:])
                    _enc = _enc_w.get(_rtype)
                    if _enc is not None or _fd is not None:
                        # `.elfencode` の関数が (欄の値, 加数) から新しい欄を作るか、命令欄の型なら
                        # 加数をシフトしてマスクのビットへ下から詰める（欄の外はそのまま）。
                        _nw = max(1, nbytes // bpw)
                        if not (0 <= off and off + _nw * bpw <= len(patched)):
                            continue
                        _iv = _rd_field(patched, off, _nw)
                        if _enc is not None:
                            _iv = self._elf_call_func('.elfencode', _enc, [_iv, addend])
                            if _iv is None:
                                continue
                        else:
                            _iv = (_iv & ~_fd[0]) | _field_deposit(_fd[0], addend >> _fd[2])
                        _wr_field(patched, off, _nw, _iv)
                        continue
                    if 0 <= off and off + nbytes <= len(patched):
                        patched[off:off + nbytes] = \
                            (addend & ((1 << (nbytes * 8)) - 1)).to_bytes(nbytes, _order)
                csec.data = bytes(patched)

        rela_sec_order = [i + 1 for i, s in enumerate(csecs) if (i + 1) in rela_entries]
        nrela = len(rela_sec_order)

        # `.elfgroup` のグループのセクションはメンバーより前に要る（gABI）ので、セクション
        # ヘッダ表の先頭に置き、残りの番号を G だけずらす。
        _groups = []
        for (_gn, _gsig, _gfl, _gmem) in self.state.elf.decl_group.values():
            _nums = []
            for _m in _gmem:
                _k = next((i + 1 for i, cs in enumerate(csecs)
                           if cs.name.translate(_ALOWER) == _m.translate(_ALOWER)), None)
                if _k is None:
                    self.state.diag(f" warning - .elfgroup: member section '{_m}' of group "
                                    f"'{_gn}' is not in the output; ignored.", set_error=False)
                elif _k not in _nums:
                    _nums.append(_k)
            if _nums:
                _groups.append((_gn, _gsig, _gfl, _nums))
            else:
                self.state.diag(f" warning - .elfgroup: group '{_gn}' has no member in the "
                                f"output; not written.", set_error=False)
        G = len(_groups)
        _grp_members = set()
        for (_gn, _gsig, _gfl, _nums) in _groups:
            for _k in _nums:
                csecs[_k - 1].flags |= 0x200
                _grp_members.add(_k)

        dbg_prog, dbg_rela = self._build_dwarf_sections(
            csecs, sec_name_to_idx, bpw, machine)

        shstrtab = bytearray(b'\x00')

        def _shname(nm):
            off = len(shstrtab)
            shstrtab.extend(nm.encode() + b'\x00')
            return off
        _rela_prefix = '.rela' if _is_rela else '.rel'
        sec_name_offs = [_shname(s.name) for s in csecs]
        rela_name_offs = [_shname(_rela_prefix + csecs[sidx - 1].name) for sidx in rela_sec_order]
        symtab_name_off = _shname('.symtab')
        strtab_name_off = _shname('.strtab')
        shstrtab_name_off = _shname('.shstrtab')
        dbg_prog_name_offs = [_shname(dname) for (dname, _ddata) in dbg_prog]
        dbg_rela_name_offs = [_shname(rname) for (rname, _tname, _rdata) in dbg_rela]
        grp_name_offs = [_shname(g[0]) for g in _groups]
        # 節番号が SHN_LORESERVE (0xff00) 以上になるなら、st_shndx は SHN_XINDEX にして本当の
        # 番号を `.symtab_shndx` に置く（どのセクションにもセクションシンボルがあるので数で決まる）。
        _need_xidx = (ncs + G) >= 0xff00
        # `.cfi_*` があれば `.eh_frame` とそのリロケーションセクションを足す。
        if self.state.elf.cfi_cur is not None:
            self.state.diag(" error - .cfi_startproc without .cfi_endproc.", set_error=True)
        _has_eh = bool(self.state.elf.cfi_fdes)
        eh_name_off = ehr_name_off = 0
        if _has_eh:
            eh_name_off = _shname('.eh_frame')
            ehr_name_off = _shname(_rela_prefix + '.eh_frame')
        xidx_name_off = _shname('.symtab_shndx') if _need_xidx else 0
        shstrtab = bytes(shstrtab)

        def _find_shndx(byte_addr, sec_name=None):
            word_pc = byte_addr // bpw if bpw else 0
            if sec_name is not None:
                _idx = sec_name_to_idx.get(sec_name)
                if _idx is not None:
                    _woff = self._addr_to_word_offset(sec_name, word_pc)
                    if _woff is not None:
                        return _idx + G, _woff * bpw
            for i, s in enumerate(csecs):
                _woff = self._addr_to_word_offset(s.name, word_pc)
                if _woff is not None:
                    return i + 1 + G, _woff * bpw
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
                return best_i + 1 + G, sym_val
            return 0xfff1, byte_addr

        strtab = bytearray(b'\x00')
        syms   = []
        sym_xidx = []

        def _psym(nm, info, oth, shndx, special, val, sz):
            # special は SHN_ABS / SHN_COMMON などの特別な番号。それ以外で
            # 0xff00 以上の節番号は SHN_XINDEX にし、本当の番号を控える。
            if not special and shndx >= 0xff00:
                sym_xidx.append(shndx)
                shndx = 0xffff
            else:
                sym_xidx.append(0)
            syms.append(_pack_sym(nm, info, oth, shndx, val, sz))

        # `.elfunit::word` ならシンボルの値と大きさはワード単位で書く。
        _word_unit = (_mach_tbl_w['unit'] == 'word')
        _bpw_sym = 1 if _word_unit else bpw

        _psym(0, 0, 0, 0, True, 0, 0)

        for i in range(ncs):
            _psym(0, 0x03, 0, i + 1 + G, False, 0, 0)

        # リンカ緩和の機種の CFI が使う局所シンボル（.Lcfi<n>）。
        _cfi_synth = {}
        if self._cfi_relax(_mach_tbl_w):
            for _n, _pt in enumerate(self._cfi_points(bpw)):
                _nm = '.Lcfi%d' % _n
                while _nm in self.state.labels or _nm in self.state.export_labels:
                    _nm += '_'
                _cfi_synth[_pt] = _nm

        export_keys = set(self.state.export_labels.keys())

        for name, *_lentry in sorted(self.state.labels.items()):
            val         = _lentry[0][0]
            _lsec       = _lentry[0][1]
            is_equ      = len(_lentry[0]) > 2 and _lentry[0][2]
            is_imported = len(_lentry[0]) > 3 and _lentry[0][3]
            if name in export_keys or is_imported:
                continue
            _equ_has_reloc = is_equ and len(_lentry[0]) > 4 and _lentry[0][4] is not None
            _special = True
            if is_equ and not _equ_has_reloc:
                shndx, sym_val = 0xfff1, val
            else:
                byte_addr = val * bpw
                shndx, sym_val = _find_shndx(byte_addr, _lsec)
                _special = not csecs
                if _word_unit:
                    sym_val = int(sym_val) // bpw
            sym_val = int(sym_val) & _word_mask
            _sa = _sym_attr(self.state, name)
            _sz = _sym_size_of(self.state, name, _bpw_sym)
            shndx, sym_val, _sz = _sym_common_override(
                self.state, name, _bpw_sym, shndx, sym_val, _sz)
            name_off = len(strtab)
            strtab += name.encode() + b'\x00'
            _psym(name_off, _sym_st_info(self.state, name, 0),
                  _sa[_SA_OTHER], shndx, _special or bool(_sa[_SA_COMMON]),
                  int(sym_val) & _word_mask, _sz)

        for (_csec, _cb), _nm in _cfi_synth.items():
            if _csec not in sec_name_to_idx:
                continue
            name_off = len(strtab)
            strtab += _nm.encode() + b'\x00'
            _psym(name_off, 0, 0, sec_name_to_idx[_csec] + G, False,
                  (_cb // bpw if _word_unit else _cb) & _word_mask, 0)

        # アンカー（.Lanchor<n>）。対のリロケーションと `ラベル − $$` の引く項が指す。
        for _anm, _asec, _aoff in self.state.elf.anchors:
            if _asec not in sec_name_to_idx:
                continue
            name_off = len(strtab)
            strtab += _anm.encode() + b'\x00'
            _psym(name_off, 0, 0, sec_name_to_idx[_asec] + G, False,
                  (_aoff // bpw if _word_unit else _aoff) & _word_mask, 0)

        first_global = len(syms)

        for name, *_lentry in sorted(self.state.labels.items()):
            is_imported = len(_lentry[0]) > 3 and _lentry[0][3]
            if not is_imported or name in export_keys:
                continue
            _sa = _sym_attr(self.state, name)
            _shndx, _sval, _sz = _sym_common_override(
                self.state, name, _bpw_sym, 0, 0, _sym_size_of(self.state, name, _bpw_sym))
            name_off = len(strtab)
            strtab += name.encode() + b'\x00'
            _psym(name_off, _sym_st_info(self.state, name, 1),
                  _sa[_SA_OTHER], _shndx, True,
                  int(_sval) & _word_mask, _sz)

        for name, *_eentry in sorted(self.state.export_labels.items()):
            val, _sec = _eentry[0][0], _eentry[0][1]
            if _is_undef_derived(val):
                continue
            is_equ = len(_eentry[0]) > 2 and _eentry[0][2]
            _lbl = self.state.labels.get(name, [])
            _equ_has_reloc = is_equ and len(_lbl) > 4 and _lbl[4] is not None
            _special = True
            if is_equ and not _equ_has_reloc:
                shndx, sym_val = 0xfff1, val
            else:
                byte_addr = val * bpw
                shndx, sym_val = _find_shndx(byte_addr, _sec)
                _special = not csecs
                if _word_unit:
                    sym_val = int(sym_val) // bpw
            sym_val = int(sym_val) & _word_mask
            _sa = _sym_attr(self.state, name)
            shndx, sym_val, _sz = _sym_common_override(
                self.state, name, _bpw_sym, shndx, sym_val,
                _sym_size_of(self.state, name, _bpw_sym))
            name_off = len(strtab)
            strtab += name.encode() + b'\x00'
            _psym(name_off, _sym_st_info(self.state, name, 1),
                  _sa[_SA_OTHER], shndx, _special or bool(_sa[_SA_COMMON]),
                  int(sym_val) & _word_mask, _sz)

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

        _cfi_synth_idx = {}
        for _pt, _nm in _cfi_synth.items():
            if _pt[0] not in sec_name_to_idx:
                continue
            _cfi_synth_idx[_pt] = _si
            _si += 1

        for _anm, _asec, _aoff in self.state.elf.anchors:
            if _asec not in sec_name_to_idx:
                continue
            sym_name_to_idx[_anm] = _si
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
            r_info = self._elf_r_info(r_sym, r_type, _is_elf64)
            if _is_elf64:
                _MAX, _MIN = (1 << 63) - 1, -(1 << 63)
                if r_addend > _MAX:
                    r_addend = _MAX
                elif r_addend < _MIN:
                    r_addend = _MIN
                return _struct.pack(f'{_pk}QQq', r_offset, r_info, r_addend)
            _MAX, _MIN = (1 << 31) - 1, -(1 << 31)
            if r_addend > _MAX:
                r_addend = _MAX
            elif r_addend < _MIN:
                r_addend = _MIN
            return _struct.pack(f'{_pk}IIi', r_offset, r_info, r_addend)

        def _pack_rel(r_offset, r_sym, r_type):
            r_info = self._elf_r_info(r_sym, r_type, _is_elf64)
            if _is_elf64:
                return _struct.pack(f'{_pk}QQ', r_offset, r_info)
            return _struct.pack(f'{_pk}II', r_offset, r_info)

        # `.elfrinfo` が r_info の形を決めているときは、型欄の幅の警告は出さない。
        if not _is_elf64 and not _mach_tbl_w['rinfo']:
            _warned_rt = set()
            _warned_sym = False
            for sidx in rela_sec_order:
                for (_off, _sn, _rt, _ad, _nb, _fm) in rela_entries[sidx]:
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
                    for (off, sn, rtype, addend, _nbytes, _fm) in entries
                )
            else:
                data = b''.join(
                    _pack_rel(off, sym_name_to_idx.get(sn, 0), rtype)
                    for (off, sn, rtype, _addend, _nbytes, _fm) in entries
                )
            rela_datas.append(data)

        # `.eh_frame`（ソースの `.cfi_*` から）。
        eh_data, eh_rdata = b'', b''
        if _has_eh:
            _eh_d, _eh_r = self._build_eh_frame(
                _mach_tbl_w, _is_elf64, _is_rela, _pk, bpw,
                {s.name: i + 1 for i, s in enumerate(csecs)}, _cfi_synth_idx,
                sym_name_to_idx)
            eh_data = _eh_d
            if _is_rela:
                eh_rdata = b''.join(_pack_rela(o, si, rt, a) for (o, si, rt, a) in _eh_r)
            else:
                eh_rdata = b''.join(_pack_rel(o, si, rt) for (o, si, rt, _a) in _eh_r)

        def _is_nobits(s):
            return s.sh_type == 8

        offset = _ehdr_size
        sec_offsets = []
        for s in csecs:
            # ファイル内の位置も sh_addralign に合わせる（16 を下限）。
            # `.elfsection` で 64 などの大きな整列を書いたセクションも、
            # GNU as と同じくファイル上でその境界から始まる。
            _al_f = s.align if s.align is not None \
                else _elf_default_align(s.sh_type, _is_elf64)
            offset = _align_up(offset, max(16, _al_f or 1))
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

        base_idx = ncs + nrela + 3 + G
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

        ndbg = len(dbg_prog) + len(dbg_rela)
        total_shdrs = 1 + ncs + nrela + 3 + ndbg + G
        shstrndx    = ncs + nrela + 3 + G
        symtab_shidx = ncs + nrela + 1 + G
        strtab_shidx = ncs + nrela + 2 + G
        symtab_link = strtab_shidx

        # グループの中身: フラグの語、続いてメンバーのセクション番号（メンバーの
        # リロケーションセクションも同じグループに入れる）。sh_info は署名の
        # シンボル番号。署名がセクション名ならそのセクションシンボル。
        _rela_hidx = {sidx: ncs + 1 + ri + G for ri, sidx in enumerate(rela_sec_order)}
        grp_datas = []
        grp_info = []
        for (_gn, _gsig, _gfl, _nums) in _groups:
            _words = [_gfl]
            for _k in _nums:
                _words.append(_k + G)
            for _k in _nums:
                if _k in _rela_hidx:
                    _words.append(_rela_hidx[_k])
            grp_datas.append(b''.join(_struct.pack(f'{_pk}I', w & 0xFFFFFFFF) for w in _words))
            _si = sym_name_to_idx.get(_gsig)
            if _si is None:
                _si = next((i + 1 for i, cs in enumerate(csecs) if cs.name == _gsig), None)
            if _si is None:
                self.state.diag(f" warning - .elfgroup: signature symbol '{_gsig}' of group "
                                f"'{_gn}' is not in the symbol table.", set_error=False)
                _si = 0
            grp_info.append(_si)
        grp_offsets = []
        for gd in grp_datas:
            offset = _align_up(offset, 4)
            grp_offsets.append(offset)
            offset += len(gd)

        eh_off = ehr_off = eh_shidx = 0
        eh_fl, eh_ty, eh_al, eh_es = _elf_section_attrs(self.state, '.eh_frame')
        if eh_al is None:
            eh_al = (self.state.elf.decl_cfi[3] if self.state.elf.decl_cfi
                     and self.state.elf.decl_cfi[3] else (8 if _is_elf64 else 4))
        if _has_eh:
            offset = _align_up(offset, max(1, eh_al))
            eh_off = offset
            offset += len(eh_data)
            offset = _align_up(offset, 8)
            ehr_off = offset
            offset += len(eh_rdata)
            eh_shidx = total_shdrs
            total_shdrs += 2

        xidx_data = b''
        xidx_off = 0
        xidx_shidx = 0
        if _need_xidx:
            xidx_data = b''.join(_struct.pack(f'{_pk}I', x & 0xFFFFFFFF) for x in sym_xidx)
            offset = _align_up(offset, 4)
            xidx_off = offset
            offset += len(xidx_data)
            xidx_shidx = total_shdrs
            total_shdrs += 1

        shdr_off    = _align_up(offset, 8)

        # `.elflink` の sh_link / sh_info。値はセクション名か数（10 進か 0x 付き 16 進）。
        def _shidx_of(text, sname, what):
            if not text:
                return 0
            t = text.strip()
            if (t.isascii() and t.isdigit()):
                return int(t, 10)
            if t[:2].translate(_ALOWER) == '0x' and len(t) > 2 and all(c in '0123456789abcdefABCDEF' for c in t[2:]):
                return int(t, 16)
            tl = t.translate(_ALOWER)
            for i, cs in enumerate(csecs):
                if cs.name.translate(_ALOWER) == tl:
                    return i + 1 + G
            for ri, sidx in enumerate(rela_sec_order):
                if (_rela_prefix + csecs[sidx - 1].name).translate(_ALOWER) == tl:
                    return ncs + 1 + ri + G
            if tl == '.symtab':
                return symtab_shidx
            if tl == '.strtab':
                return strtab_shidx
            if tl == '.shstrtab':
                return shstrndx
            for dname in dbg_prog_shndx:
                if dname.translate(_ALOWER) == tl:
                    return dbg_prog_shndx[dname]
            self.state.diag(f" warning - .elflink: {what} of '{sname}': no section "
                            f"named '{t}'; written as 0.", set_error=False)
            return 0

        try:
            _elf_file = open(path, 'wb')
        except OSError as _e:
            self.state.diag(f" error - cannot create ELF output file '{path}': {_e}", set_error=True)
            return
        with _elf_file as f:
            # SHN_LORESERVE 以上の数は 0 番目のセクションヘッダに置く（ELF の決まり）。
            f.write(_pack_ehdr(1, machine, shdr_off,
                               0 if total_shdrs >= 0xff00 else total_shdrs,
                               0xffff if shstrndx >= 0xff00 else shstrndx))

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

            for i, gd in enumerate(grp_datas):
                cur = f.tell()
                f.write(b'\x00' * (grp_offsets[i] - cur))
                f.write(gd)

            if _has_eh:
                cur = f.tell()
                f.write(b'\x00' * (eh_off - cur))
                f.write(eh_data)
                cur = f.tell()
                f.write(b'\x00' * (ehr_off - cur))
                f.write(eh_rdata)

            if _need_xidx:
                cur = f.tell()
                f.write(b'\x00' * (xidx_off - cur))
                f.write(xidx_data)

            cur = f.tell()
            f.write(b'\x00' * (shdr_off - cur))

            f.write(_pack_shdr(0, 0, 0, 0, 0,
                               total_shdrs if total_shdrs >= 0xff00 else 0,
                               shstrndx if shstrndx >= 0xff00 else 0, 0, 0, 0))

            for i, gd in enumerate(grp_datas):
                f.write(_pack_shdr(
                    grp_name_offs[i], 17, 0, 0, grp_offsets[i], len(gd),
                    symtab_shidx, grp_info[i], 4, 4))

            for i, s in enumerate(csecs):
                _sh_type_i = s.sh_type
                _al_i = (s.align if s.align is not None
                         else _elf_default_align(_sh_type_i, _is_elf64))
                _lk_t, _inf_t = self.state.elf.decl_link.get(s.name.translate(_ALOWER), ('', ''))
                f.write(_pack_shdr(
                    sec_name_offs[i], _sh_type_i, s.flags, 0,
                    sec_offsets[i], s.byte_size,
                    _shidx_of(_lk_t, s.name, 'sh_link'),
                    _shidx_of(_inf_t, s.name, 'sh_info'), _al_i, s.entsize))

            _word_align = 8 if _is_elf64 else 4
            _sym_entsize = 24 if _is_elf64 else 16
            _rela_sh_type = 4 if _is_rela else 9
            for ri, sidx in enumerate(rela_sec_order):
                f.write(_pack_shdr(
                    rela_name_offs[ri], _rela_sh_type,
                    0x40 | (0x200 if sidx in _grp_members else 0), 0,
                    rela_offsets[ri], len(rela_datas[ri]),
                    symtab_shidx, sidx + G, _word_align, _REL_ENTSIZE_ACTIVE))

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
            if _has_eh:
                f.write(_pack_shdr(
                    eh_name_off, eh_ty, eh_fl, 0, eh_off, len(eh_data),
                    0, 0, eh_al, eh_es))
                f.write(_pack_shdr(
                    ehr_name_off, _rela_sh_type, 0x40, 0, ehr_off, len(eh_rdata),
                    symtab_shidx, eh_shidx, _word_align, _REL_ENTSIZE_ACTIVE))
            if _need_xidx:
                f.write(_pack_shdr(
                    xidx_name_off, 18, 0, 0, xidx_off, len(xidx_data),
                    symtab_shidx, 0, 4, 4))

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
        ap.add_argument('--elfdesc', dest='elf_desc', action='store_true',
                        default=False,
                        help='Print the effective ELF machine description (the '
                             'built-in table of the -m machine with the pattern '
                             'file\'s .elf* declarations laid over it) as pattern-'
                             'file declarations headed by .elfbuiltin::0, and exit '
                             'without assembling. Pasting the output into a pattern '
                             'file reproduces the same ELF output with no built-in '
                             'table (manual 3.7.9).')
        ap.add_argument('-p', '--macro-expand-pattern', dest='macro_expand_pattern',
                        nargs='?', const='-', default=None, metavar='FILE',
                        help='The pattern-file counterpart of -P: macro-expand the '
                             'pattern file and write the resulting pattern text to '
                             'FILE (or stdout if FILE is omitted or "-") without '
                             'assembling. Useful for debugging pattern-file macros.')
        return ap

    _HOIST_SCALARS = {'bits': ('endian', 'bts'), 'padding': ('padding',), 'symbolc': ('swordchars',)}

    def _hdrsnap_take(self):
        """持ち上げたディレクティブを処理し終えた状態を写し取る（反復ごとにここへ巻き戻す）。"""
        st = self.state
        snap = {f: dict(getattr(st, f)) for f in self._DIR_DICT_FIELDS}
        for key, names in self._HOIST_SCALARS.items():
            if key in st.hoist_fields:
                snap.update((n, getattr(st, n)) for n in names)
        if 'vliw' in st.hoist_fields:
            snap['vliw'] = st.vliw.save(slotset=False)
        st.hdrsnap = snap

    def _hdrsnap_restore(self):
        """写し取った状態へ戻す。"""
        st = self.state
        snap = st.hdrsnap
        for f in self._DIR_DICT_FIELDS:
            setattr(st, f, dict(snap[f]))
        for key, names in self._HOIST_SCALARS.items():
            if key in st.hoist_fields:
                for n in names:
                    setattr(st, n, snap[n])
        if 'vliw' in st.hoist_fields:
            st.vliw.load(snap['vliw'])

    def _build_dir_dispatch(self, pat, isdir):
        """ディレクティブ行ごとに呼ぶハンドラを先に決めておく（毎行すべてを試さないため）。"""
        d = self.directive_proc
        table = {
            '.setsym': d.set_symbol, '.clearsym': d.clear_symbol, '.padding': d.paddingp,
            '.bits': d.bits, '.symbolc': d.symbolc, '.vliw': d.vliwp,
            '.check': d.check_processing, '.clrcheck': d.clrcheck_processing,
            '.reloc': d.reloc_processing, '.clrreloc': d.clrreloc_processing,
            '.map': d.map_processing, '.free': d.free_processing,
            '.passthru': d.passthru_processing, '.eol': d.eol_processing,
            '.textmode': d.textmode_processing, '.enum': d.enum_processing,
            '.clrenum': d.clrenum_processing, '.error': d.errmsg_processing,
            '.echo': d.echo_processing, '.unordered': d.unordered_processing,
        }
        table.update((n, getattr(d, n[1:] + '_processing')) for n in self._ELF_DECLS)
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

        パス1は最大 MAX_RELAX (16) 回のリラクゼーション。各反復の終わりの「ラベル → (番地,
        セクション)」が前回と同じなら収束、過去の写しと同じなら振動として中断する（誤った番地の
        コードは出さない）。パス2は確定した番地で 1 回だけ回し、パス1と食い違えばエラー。
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
        self.state.elf.objfile  = args.elf_objfile

        if args.elf_machine is not None:
            if not 0 <= args.elf_machine <= 65535:
                self.state.diag(f" error - -m/--machine value {args.elf_machine} is out of "
                     f"range (an ELF e_machine number is 0..65535).",
                     set_error=False, force=True)
                return False
            self.state.elf.machine = args.elf_machine
            self.state.elf.machine_from_cli = True
            if args.elf_machine not in ELF_MACHINES and args.elf_objfile:
                _known = ', '.join(f"{m} ({ELF_MACHINES[m]['name']})" for m in sorted(ELF_MACHINES))
                self.state.diag(f" warning - -m/--machine value {args.elf_machine} is not one of "
                     f"the machines axx has built-in relocation numbering for ({_known}); "
                     f"relocation types must come from the pattern file (.elftype / "
                     f".elfwidth / .elfextern). References whose type is not declared get "
                     f"no relocation entry, rather than a guessed (and wrong) one.",
                     set_error=False, force=True)

        self.state.elf.elf_class    = None if args.elf_format is None else \
                                  (2 if args.elf_format == 64 else 1)

        _osabi_key = args.elf_osabi.translate(_ALOWER)
        if _osabi_key not in osabitbl:
            print(f"warning: unknown --osabi value '{args.elf_osabi}'; "
                  f"valid choices are {list(osabitbl.keys())} (case-insensitive). Using 'Linux'.",
                  file=sys.stderr)
        self.state.elf.osabi        = osabitbl.get(_osabi_key, 0)
        self.state.verbose      = args.verbose
        self.state.text_output  = args.text_output
        self.state.debug        = args.debug
        self.state.elf.gen_debug    = args.gen_debug
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
            _dirorder = _pat_unordered_plan(self.state.pat, self.state.pat_isdir)
            self.state.unordered = _dirorder is not None
            self.state.pat_dirorder = _dirorder or []
            if self.state.unordered:
                self.state.pat_always = [_r for _r in self.state.pat_always
                                         if not self.state.pat_isdir[_r]]
                self.state.hoist_rows = 0
                self.state.hoist_first_ai = 0
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
            if self.state.unordered:
                self.setpatsymbols([self.state.pat[_r] for _r in self.state.pat_dirorder])
            else:
                self.setpatsymbols(self.state.pat)
            self.register_elfdecls(self.state.pat)
            if self.state.had_error:
                self.state.diag(" error - one or more errors were reported while reading "
                                "the pattern file; output would be incomplete or wrong.",
                                set_error=False, force=True)
                self.state.diag("         Aborting: no output file written.",
                                set_error=False, force=True)
                return False
            if args.elf_desc:
                sys.stdout.write(self.elf_desc_text())
                return True

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
                self.state.relax.pas = 0
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
                self.state.relax.pass1_prev_label_pcs = _RELAXATION_SENTINEL
                self.state.relax.relax_prev_values = {}
                self.state.relax.relax_optimistic = False

                _seen_pcs_history = {}

                _imported_labels = dict(self.state.labels)

                _initial_vars = dict(self.state.vars)
                _initial_vars_undef = dict(self.state.vars_undef)
                _initial_vars_float = dict(self.state.vars_float)

                # 前の反復から値の変わったラベルの数が最小を更新した反復は上限に
                # 数えない。前方参照の `.equ` の連鎖は反復ごとに 1 段ずつ決まるので、
                # 16 段を超える連鎖でも動くラベルが減っている限り回す。その数は
                # 有限なので必ず止まる。振動では減らないので、従来どおり上限で止まる。
                # caxx.c の main() の relax_budget / min_moving と同じ規則である。
                _relax_budget = MAX_RELAX
                _min_moving = None
                relax_iter = 0
                while relax_iter < _relax_budget:
                    self.state.relax.relax_optimistic = (relax_iter == 0)
                    self.state._macro_line_pcs_cur = {}
                    self.state.pc = 0
                    self.state.relax.pas = 1
                    self.state.ln = 1
                    # ソースの `.reloctype` と `.labelc` はパスごとに先頭から効く
                    # （前のパスの最後の設定を持ち越さない。caxx.c と同じ）。
                    self.state.elf.reloctype_override = {}
                    self.state.lwordchars = DIGIT + ALPHABET + "_."
                    self.state.labels = dict(_imported_labels)
                    self.state.sections = {}
                    self.state.export_labels = {}
                    self.state.current_section = '.text'
                    self.state.symbols = dict(self.state.patsymbols)
                    self.state.vars = dict(_initial_vars)
                    self.state.vars_undef = dict(_initial_vars_undef)
                    self.state.vars_float = dict(_initial_vars_float)
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
                    _prev_pcs = self.state.relax.pass1_prev_label_pcs
                    if isinstance(_prev_pcs, dict):
                        _n_moving = sum(
                            1 for k, (pc, _sec) in current_pcs.items()
                            if _is_undef_derived(pc) or k not in _prev_pcs
                            or _prev_pcs[k][0] != pc)
                        # 0 は前の反復と同じ値（収束）なので、下の検出に任せる。
                        if _n_moving and (_min_moving is None or _n_moving < _min_moving):
                            if _min_moving is not None:
                                _relax_budget += 1
                                # 振動の検出に使う履歴はここから取り直す。振動が
                                # 続くなら動く数は減らないので、次の周で見つかる。
                                # 履歴が反復の数だけ膨らむのも防ぐ。
                                _seen_pcs_history.clear()
                            _min_moving = _n_moving
                    has_undef = any(
                        _is_undef_derived(pc)
                        for k, (pc, _sec) in current_pcs.items()
                        if not (len(self.state.labels[k]) > 2 and self.state.labels[k][2])
                    )

                    self.state.relax.relax_prev_values = {
                        k: v[0] for k, v in self.state.labels.items()
                        if not _is_undef_derived(v[0])
                    }

                    self.state._macro_label_values = dict(self.state.relax.relax_prev_values)
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
                    self.state.relax.pass1_prev_label_pcs = current_pcs
                    relax_iter += 1
                else:

                    self.state.diag(" error - Pass1 relaxation did not converge after {0} iterations.".format(_relax_budget), set_error=False, force=True)
                    print("         Generated code would have incorrect addresses for", file=sys.stderr)
                    print("         variable-length instructions with forward references.", file=sys.stderr)
                    print("         Aborting: no output file written.", file=sys.stderr)
                    if isinstance(self.state.relax.pass1_prev_label_pcs, dict):
                        changed = []
                        for k in current_pcs:
                            if k in self.state.relax.pass1_prev_label_pcs:
                                if current_pcs[k] != self.state.relax.pass1_prev_label_pcs[k]:
                                    changed.append(k)
                        if changed:
                            print(f"         Labels still changing: {', '.join(changed[:10])}", file=sys.stderr)
                    return False

                self.state.relax.relax_optimistic = False

                _pass1_final_addrs = {
                    k: v[0] for k, v in self.state.labels.items()
                    if not (len(v) > 2 and v[2])
                }

                self.state.pc = 0
                self.state.relax.pas = 2
                self.state.ln = 1
                self.state.elf.reloctype_override = {}
                self.state.lwordchars = DIGIT + ALPHABET + "_."
                self.state.elf.relocations = []
                self.state.elf.anchors = []
                self.state.elf.line_map = []
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
                    elif self.state.had_error:
                        # 誤りのある行は pass2 で何も出さないので、その後ろの番地がずれる。
                        # リラクゼーションのせいではない。caxx.c と同じ文面。
                        print("         This is a consequence of the error(s) reported above "
                              "(a line in error emits nothing, so the addresses after it "
                              "move); fix those first.", file=sys.stderr)
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

            if self.state.elf.objfile:
                try:
                    self.write_elf_obj(self.state.elf.objfile, self.state.elf.machine)
                except OSError as _we:
                    self.state.diag(f" error - cannot write "
                                    f"'{self.state.elf.objfile}': {_we}", set_error=True)
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

        return True


class _StdoutGuard:
    """標準出力の書き込みの失敗を覚え、以後の書き込みを捨てる。

    caxx.c は最後の fflush で失敗を見て「cannot write to standard output」を一度だけ出すので、
    print() の OSError をここで受け止め、main() の終わりで同じ文言を一度だけ出す。
    """

    def __init__(self, stream):
        # 標準出力が閉じたまま起動されると sys.stdout は None になる。書こうと
        # したときに caxx.c の fflush と同じく EBADF として報告する。
        self._stream = stream
        self.error = None

    def write(self, text):
        if self.error is None:
            if self._stream is None:
                if text:
                    self.error = OSError(errno.EBADF, os.strerror(errno.EBADF))
                return len(text)
            try:
                return self._stream.write(text)
            except OSError as e:
                self.error = e
        return len(text)

    def flush(self):
        if self.error is None and self._stream is not None:
            try:
                self._stream.flush()
            except OSError as e:
                self.error = e

    def __getattr__(self, name):
        return getattr(self._stream, name)


def main():
    """コマンドとしての入口。終了コードを決める。"""
    # ソースは surrogateescape で読むので、UTF-8 でないバイトは代用の文字のまま
    # 運ばれる。一覧や診断に書くときもそのバイトに戻す（caxx.c は元のバイトを
    # そのまま書く）。既定の strict では UnicodeEncodeError で落ちる。
    for _stream in (sys.stdout, sys.stderr):
        try:
            _stream.reconfigure(errors='surrogateescape')
        except (AttributeError, ValueError):
            pass
    if sys.getrecursionlimit() < _EXPR_RECLIMIT:
        sys.setrecursionlimit(_EXPR_RECLIMIT)
    # 読み手が先に閉じたパイプ（`-v | head` など）では、caxx.c と同じく
    # SIGPIPE で黙って終わる。Python の既定は無視なので BrokenPipeError になる。
    if hasattr(signal, 'SIGPIPE'):
        signal.signal(signal.SIGPIPE, signal.SIG_DFL)
    guard = _StdoutGuard(sys.stdout)
    sys.stdout = guard
    assembler = Assembler()
    ok = assembler.run()
    guard.flush()
    if guard.error is not None:
        print(f" error - cannot write to standard output: {guard.error}", file=sys.stderr)
        # 書けなかった分がバッファに残り、終了時の flush でもう一度失敗して
        # 「Exception ignored」を出さないよう、標準出力を捨て先へ付け替える。
        try:
            _devnull = os.open(os.devnull, os.O_WRONLY)
            os.dup2(_devnull, 1)
            os.close(_devnull)
        except OSError:
            sys.stderr.flush()
            os._exit(1)
        return False
    return ok


if __name__ == '__main__':
    ok = main()
    exit(0 if ok else 1)
