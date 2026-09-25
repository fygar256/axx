#!/usr/bin/env python3
"""axx — パターンファイル駆動の汎用アセンブラ。

通常のアセンブラが特定の命令セットをコードに埋め込むのに対し、axx は
命令セットの仕様を外部のテキストファイル（`.axx` パターンファイル）から
読み込む。パターンファイルは「ニーモニックの書式 → バイナリエンコーディング」
の対応を1行1エントリで記述したもので、これを差し替えるだけで同じエンジンが
任意の ISA（x86_64 / ARM64 / Z80 / VLIW・EPIC 等）を扱える。

    axx.py <パターンファイル.axx> <ソース.s> -o <出力.o>

全体の流れ（Assembler.run() が入口）:

  1. パターンファイル読み込み        PatternFileReader.readpat()
       `.INCLUDE` を再帰展開し、各行を "::" 区切りで最大6フィールドに分解する。
  2. マクロ展開                      MacroPreprocessor.expand()
       `!if` / `!while` / `!def` 等の行指向マクロを先に潰しておく。
  3. パス1（サイズ収束）             最大 MAX_RELAX 回反復
       前方参照ラベルの値が確定しないと命令長が決まらない（可変長命令）ため、
       「前回の反復で得た値」を推定値として使い、全ラベルのアドレスが前回と
       一致するまで繰り返す。これをリラクゼーションと呼ぶ。
  4. パス2（コード生成）             1回のみ
       確定したアドレスで実際のバイト列と ELF リロケーションを生成する。
       パス1とパス2でアドレスがずれていたら明示的にエラーにする（誤ったバイナリを
       黙って出力しない安全策）。
  5. 出力                            ELF オブジェクト / 生バイナリ / ラベル TSV

対になる C 移植版が同じディレクトリの caxx.c にあり、両者は同一の入力に対して
同一のバイト列を出すことを目標に保守されている。
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


# パス1のリラクゼーション中、「まだ一度も値が確定していない」ことを
# 「値が 0 である」と区別するための番兵。None や 0 を使うと、正当に 0 番地に
# あるラベルと区別できなくなる。
_RELAXATION_SENTINEL = object()


# 現在動作中の AssemblerState。モジュール関数の diag() から参照される。
# 「エラーを今表示してよいパスか（パス2か対話モードか）」の判定と had_error の
# 設定は AssemblerState 側が持っているため、状態を持たない場所から診断を出す
# ときの橋渡しとして使う。
_ACTIVE_STATE = None


def diag(text, set_error=True, force=False):
    """診断メッセージを1本化して出す入口。

    状態がまだ無い（起動直後など）ときは素直に stderr へ出し、そうでなければ
    AssemblerState.diag() に委譲して「表示してよいパスか」の判定と had_error の
    設定を任せる。set_error=True なら、表示された時点でビルドは失敗扱いになる。
    """
    st = _ACTIVE_STATE
    if st is None:
        print(text, file=sys.stderr)
        return True
    return st.diag(text, set_error=set_error, force=force)


def diag_error(msg, force=False):
    """" error - ..." 形式のエラー。表示されるとビルドは失敗（出力を書かない）。"""
    return diag(f" error - {msg}", set_error=True, force=force)


def diag_warning(msg, force=False):
    """" warning - ..." 形式の警告。表示されてもビルドは継続する。"""
    return diag(f" warning - {msg}", set_error=False, force=force)


# 式を評価している文脈。パターンファイル側の式か、アセンブリソース側の式かで
# 使える記法（`!!!` 等のパターン専用トークン）が変わる。
EXP_PAT = 0
EXP_ASM = 1


class ExprCaps:
    """式評価器の「この場では何が書けるか」を表す能力記述子。

    本体・マクロ層・ミニ言語の 3 つの層が同じ式評価器を呼ぶが、呼ぶ時点で
    意味を成す項目は層ごとに違う。たとえばパターン変数 `a` は、パターン行を
    符号化している最中にしか束縛されていないし、`!!!` は VLIW のパターン行
    でしか意味がない。どの項目が生きているかを 1 か所にまとめ、評価器は
    `state.expcaps` を見て判断する。呼ぶタイミングが変われば記述子が変わり、
    使える機能が変わる。

    - `patvars` … パターン変数（`a` でも `var_2` でも同じ）
    - `vliw`    … `!!!` / `!!!!`
    - `labels`  … ラベル名・`.equ` 名の参照
    - `loc`     … `$$` / `$.`
    - `syms`    … `#name` と `.setsym` の記号
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


# パターンファイルの式。すべて使える。
CAPS_PAT = ExprCaps('pattern', patvars=True, vliw=True)
# アセンブリソース行の式。パターン変数と VLIW 計数は無い。
CAPS_ASM = ExprCaps('assembly')
# ミニ言語 (`.func` 本体) から呼ぶとき。ラベル・`$$`・`#記号` は読めるが、
# パターン変数はその場で束縛されていないので落とす。
CAPS_MINI = ExprCaps('mini language')
exp_typ = 'i'          # 'i'=整数モード / 'f'=浮動小数点モード


# パターン中の "[[" / "]]"（省略可能グループ）を1文字に潰した内部表現。
# 2文字のままだと以降の走査が全て2文字先読みを強いられるため、
# 印字不可能な1文字に置き換えてから扱う。
OB = chr(0x90)
CB = chr(0x91)

# ソース行の「本物の」VLIW スロット区切り "!!" / 終端 "!!!!" を1文字に潰した内部表現。
# `\!\!` とエスケープされた「文字としての !!」と区別するために使う。
# 詳しくは StringUtils.resolve_vliw_escapes() を参照。
VLIW_SEP = chr(0x92)
VLIW_STOP = chr(0x93)


# 未定義ラベルの値を表す番兵。None ではなく巨大な整数にしてあるのは、
# ラベル値が `label+4` や `label-$$` のように普通の算術に流れ込むため。
# 整数にしておけば例外を出さずに「未定義性」が計算結果へ伝播していく。
UNDEF = (1 << 1024) - 1
VAR_UNDEF = 0

# .check の許可リストに `""` が書かれたときに積む印。
# 「そのオペランドは省略可、省略時は VAR_UNDEF(0)」を意味する。
# シンボル名は get_symbol_word で必ず1文字以上・大文字化されるため、
# 空文字は実在のシンボル名と衝突しない。
CHECK_OMIT = ''

# UNDEF から算術で派生した値を「未定義由来」と判定する閾値。
# UNDEF そのものと完全一致しなくても（UNDEF+4 等）、この大きさなら未定義由来とみなす。
_UNDEF_DERIVED_THRESHOLD = 1 << 768


# axx は 256bit 整数・128bit 浮動小数点まで正当に扱うため、2**256 程度までは
# 本物の値でありうる。その帯域に入った値については、上の閾値ヒューリスティックが
# 誤判定しうることを一度だけ警告する。
_UNDEF_SANE_CEILING = 1 << 256
_undef_ceiling_warned = False

# `*(値, 位置)` のバイト抽出でシフトさせる最大ビット数。これを超えると結果は
# 符号（0 か -1）にしかならないので、頭打ちにしても値は変わらず、
# 巨大なシフト量を渡されたときの暴走だけを防げる。
_BYTE_EXTRACT_SHIFT_MAX = 1 << 20
_SEXT_MAX_BITS = 128


# 本体の式評価器が持つ単項/後置演算子の実装。マクロ層からも同じ意味で呼べる
# ように、評価器の外へ出して 1 か所にまとめてある。どれも診断は出さず、
# 「値と、あれば伝えるべき文言」を返すだけにして、報告はそれぞれの層に任せる。

def op_msb(v):
    """`@v` … 最上位の立っているビットの位置を右から数えた値。"""
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
    """`x'bits` … ビット `bits-1` を符号ビットとみなした符号拡張。

    返り値は (値, 警告文 or None, 続行してよいか)。非有限の浮動小数点値が
    来たときだけ「続行してよいか」が False になり、呼び出し側は連鎖を打ち切る。
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
    """`*(x, index)` … 下位から数えて `index` バイト目より上を残した値。

    返り値は (値, エラー文 or None)。上限を超える分は符号で埋まるだけなので
    頭打ちにする（caxx.c の 256bit 算術シフトと同じ結果になる）。
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
    """C の pow(a,b) と同じ IEEE754 のべき乗セマンティクスで計算する。

    Python の ** / math.pow は範囲外（OverflowError）や定義域外
    （負の底に非整数指数、ValueError）で例外を投げるが、Cの pow() は
    例外を投げず ±inf / nan を返す。caxx.c の浮動小数点モード(exp_typ_float)
    はまさに pow() をそのまま呼ぶので、同一入力で「Python はエラーで0、
    C は inf/nan のビットパターン」という食い違いが起きないよう揃える。
    """
    a = float(a)
    b = float(b)
    if math.isnan(a) or math.isnan(b):
        return float('nan')
    if a == 0.0 and b < 0.0:
        return float('inf')
    if a < 0.0 and b != math.floor(b):
        # glibc の pow() は負の底・非整数指数の定義域エラーで、符号ビットが
        # 立った nan (0xfff8...) を返す。実測で caxx.c と突き合わせて確認済み。
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
    """値が UNDEF（未定義ラベル）に由来するか判定する。"""
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
    """パターン先頭の連続する大文字（＝ニーモニック部分）と、その直後が
    「英数字を食える書き方か」を返す。

    パターン照合は1行につき数千個のパターンを試すため、本格的な照合に入る前の
    足切りに使う。ソース行の先頭がこの文字列で始まっていなければ、そのパターンは
    絶対にマッチしないので即座に捨てられる。結果は lru_cache で使い回す。

    第2要素 closed が True なら、ニーモニック直後のパターン文字は英数字を
    絶対に食えない（`.` `,` `(` `#` 等のリテラル、またはパターン終端）。この場合
    ソース側がそこで英数字を続けていれば不一致が確定するので、`MOVE` 系の
    パターンを `MOVEM` の行に試す、といった無駄打ちを消せる。
    小文字（シンボル）・`!`（式）・`\\`（エスケープ）・`[`（省略可グループ）・
    数字は英数字を食いうるので closed は False にする。
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


# パターン記法の基本規約: 大文字＝そのまま照合するリテラル（ニーモニック）、
# 小文字＝.setsym で定義されたシンボル（レジスタ名等）を取るプレースホルダ。
CAPITAL = "ABCDEFGHIJKLMNOPQRSTUVWXYZ"
LOWER = "abcdefghijklmnopqrstuvwxyz"
# 集合式の演算子（`.setsym::x::a&b` など）。
SET_OPS = "&|^+-"
DIGIT = '0123456789'
XDIGIT = "0123456789ABCDEF"
ALPHABET = LOWER + CAPITAL

# _lead_caps 用。ニーモニック直後に来ると「英数字を食いうる」パターン文字。
#   小文字 … .setsym シンボルのプレースホルダ
#   '!'    … 式
#   '\'    … 次の1文字をリテラル化するエスケープ
#   '['    … [[ ]] 省略可グループの開き
#   数字   … リテラルの数字
_PFX_OPEN = frozenset(LOWER + DIGIT + '!\\[')
# 足切りで「ニーモニックが途中で終わっていないか」を見るときの語構成文字。
_PFX_WORD = frozenset(ALPHABET + DIGIT + '_')


def _is_sub_name(s):
    """`.sub::名前` / `!S{{名前}}` に書けるサブ表の名前か。"""
    return bool(s) and all(c in _PFX_WORD for c in s)


def _dot_kw(s):
    """行頭の `.word` を大文字で返す。`.` で始まらなければ空文字。"""
    t = s.strip()
    if not t.startswith('.'):
        return ''
    j = 1
    while j < len(t) and (t[j].isalnum() or t[j] == '_'):
        j += 1
    return StringUtils.upper(t[:j])


def _parse_func_header(l):
    """`.func 名前(引数, 引数)` の見出しを (名前, 引数リスト, エラー文) に分解する。

    引数欄は丸ごと省略できる（`.func name`）。空の括弧 `.func name()` も同じ
    意味。`.call 名前(引数)` の呼び出し側と同じ書き方にそろえるための形。

    旧来の `.func::名前::引数,引数` も読める。`.func` の直後が `::` のときだけ
    そちらに切り替えるので、新しい形と取り違えることはない。
    """
    t = l.strip()
    i = 1
    while i < len(t) and (t[i].isalnum() or t[i] == '_'):
        i += 1
    i = StringUtils.skipspc(t, i)

    if t[i:i + 2] == '::':
        # 旧形式。`::` で最大3欄に割る。
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


# ミニ言語のブロック開始・終了キーワード。パターンファイルを読む段階で
# `.endfunc`（関数本体を閉じる）が `.if`/`.while`/`.for` の中で来ていないか
# 見分けるために使う。`.return` はここでは特別扱いしない（早期リターン文と
# して本体にそのまま積むだけで、関数を閉じるのは常に `.endfunc`）。
_MINI_OPEN = frozenset(('.IF', '.FOR', '.WHILE'))
_MINI_CLOSE = frozenset(('.ENDIF', '.NEXT', '.ENDWHILE'))


class _MiniFunc:
    """`.func::名前::引数 … .endfunc` で定義されたミニ言語の関数。

    入れ子で定義された関数は children に入り、名前解決は自分 → 親 → … →
    トップレベルの順に外側へたどる。body は読み込み時に文の木へ変換する。
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


# パターンファイルの第2フィールド（エラー条件）が返す番号 → メッセージ。
# 例: `ADD A,R!n :: n>7;5 :: ...` は n>7 のとき番号5（レジスタ範囲外）を報告する。
ERRORS = [
    "",
    "Invalid syntax.",
    "Address out of range.",
    "Value out of range.",
    "",
    "Register out of range.",
    "Port number out of range."
]


# ---------------------------------------------------------------------------
# アーキテクチャ別 ELF 情報テーブル
#
# キーは ELF ヘッダの e_machine 値（-m オプションで指定する番号）。
# 各エントリの意味:
#
#   elfclass       1=ELF32 / 2=ELF64。ヘッダ・シンボル・リロケーション各構造体の
#                  サイズとフィールド並びが変わる（Elf32_Sym と Elf64_Sym は
#                  幅だけでなくフィールドの順序自体が異なる点に注意）。
#   is_rela        True=RELA（加数を専用フィールドに持つ）/ False=REL（加数を
#                  命令バイト列自体に埋め込む）。i386 と ARM(32) だけが REL。
#   width_guess    リロケーション対象フィールドのバイト幅 → 既定のリロケーション型。
#                  ソース側が `::型名` を明示しなかったときに使う。
#   pc_rel         PC 相対のリロケーション型番号の集合。加数の計算に命令アドレスを
#                  含める必要があるかどうかの判定に使う。
#   extern_default `.extern` で宣言された外部シンボル参照の既定型。
#   named          ソースに書ける記号名（`label::pc32` 等）→ (型番号, バイト幅)。
#   dwarf_abs      DWARF セクション内の絶対アドレス参照に使う型番号。
#
# reloc_bytes（型番号→幅）と reverse（型番号→名前）は named から自動生成される。
# 下の _build_elf_machine_tables() を参照。
# ---------------------------------------------------------------------------
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
        # 幅2の既定は R_ARM_ABS16(5)。かつて 4 と書かれていたが、ARM の 4 は
        # R_ARM_LDR_PC_G0（32bit 命令フィールド用）で 16bit データ参照ではなく、
        # 下の named にも reloc_bytes にも現れない値だった。
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
            # 命令フィールド型。値は命令語のビット欄に詰められるため、素の整数が
            # 並ぶデータ型とは扱いが異なる（AARCH64_INSN_RELOCS を参照）。
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
            # GOT 経由。リンカが GOT エントリを作るので、値はアセンブル時には
            # 決まらない。欄は 0 で出し、リンカが埋める。
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
    """_ELF_MACHINE_RAW から派生ビューを作って完成形のテーブルを返す。

    `named` は "名前 → (型番号, バイト幅)" という1つの表に情報をまとめてあるが、
    実際に引きたい向きは3通りあるので、ここで展開しておく:

      named       名前 → 型番号          （ソースの `::pc32` を解決する）
      reloc_bytes 型番号 → バイト幅      （加数の計算に必要）
      reverse     型番号 → 名前          （-E での TSV 書き出しに使う）

    reverse は setdefault なので、同じ型番号に別名が複数ある場合（`pc32` と
    `rel32` が同じ型番号を指す等）は先に書いた方が正式名として採用される。
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


# 対応アーキテクチャ: i386(3) m68k(4) PowerPC(20) PowerPC64(21) s390x(22)
# ARM(40) SuperH(42) SPARCV9(43) x86-64(62) AArch64(183) RISC-V(243)
ELF_MACHINES = _build_elf_machine_tables(_ELF_MACHINE_RAW)


# AArch64 の「命令フィールド型」リロケーション。
#
# データ型（ABS64 など）は対象の値がそのまま連続バイトに並ぶが、こちらは 32bit
# 命令語の中の飛び飛びのビット欄に、しかも語単位・ページ単位に縮めた形で詰まる。
# そのため加数を「出力バイト列 − ラベル値」で逆算する通常の経路が使えない。
# 該当する型では代わりに、パターンが捕らえたオペランド値とラベル値の差をそのまま
# 加数とし、命令語側のビット欄は 0 にして出す（GNU as と同じ形。RELA なので
# リンカが欄を埋める）。
#
#   fields  値を詰めるビット欄を「値の下位側から」 (命令語の開始ビット, ビット数)
#           で並べたもの。ADR/ADRP だけは immlo(2bit)/immhi(19bit) に分かれる。
_A64_ADR_FIELDS = ((29, 2), (5, 19))
_A64_LO12_FIELD = ((10, 12),)
_A64_MOVW_FIELD = ((5, 16),)
AARCH64_INSN_RELOCS = {
    263: _A64_MOVW_FIELD, 264: _A64_MOVW_FIELD,   # MOVW_UABS_G0 / _NC
    265: _A64_MOVW_FIELD, 266: _A64_MOVW_FIELD,   # MOVW_UABS_G1 / _NC
    267: _A64_MOVW_FIELD, 268: _A64_MOVW_FIELD,   # MOVW_UABS_G2 / _NC
    269: _A64_MOVW_FIELD,                         # MOVW_UABS_G3
    287: _A64_MOVW_FIELD, 288: _A64_MOVW_FIELD,   # MOVW_PREL_G0 / _NC
    289: _A64_MOVW_FIELD, 290: _A64_MOVW_FIELD,   # MOVW_PREL_G1 / _NC
    291: _A64_MOVW_FIELD, 292: _A64_MOVW_FIELD,   # MOVW_PREL_G2 / _NC
    293: _A64_MOVW_FIELD,                         # MOVW_PREL_G3
    274: _A64_ADR_FIELDS,                         # ADR_PREL_LO21
    275: _A64_ADR_FIELDS, 276: _A64_ADR_FIELDS,   # ADR_PREL_PG_HI21 / _NC
    277: _A64_LO12_FIELD,                         # ADD_ABS_LO12_NC
    278: _A64_LO12_FIELD,                         # LDST8_ABS_LO12_NC
    279: ((5, 14),),                              # TSTBR14
    280: ((5, 19),),                              # CONDBR19
    282: ((0, 26),), 283: ((0, 26),),             # JUMP26 / CALL26
    284: _A64_LO12_FIELD, 285: _A64_LO12_FIELD,   # LDST16 / LDST32
    286: _A64_LO12_FIELD, 299: _A64_LO12_FIELD,   # LDST64 / LDST128
    309: ((5, 19),),                              # GOT_LD_PREL19
    311: _A64_ADR_FIELDS,                         # ADR_GOT_PAGE
    312: _A64_LO12_FIELD,                         # LD64_GOT_LO12_NC
    313: _A64_LO12_FIELD,                         # LD64_GOTPAGE_LO15
}


def insn_reloc_field_mask(rtype):
    """命令フィールド型なら、その値が占める 32bit 命令語中のビットマスクを返す。

    データ型や未知の型では None。呼び出し側はこれで「通常の加数計算をするか、
    命令フィールドとして扱うか」を振り分ける。
    """
    fields = AARCH64_INSN_RELOCS.get(rtype)
    if fields is None:
        return None
    mask = 0
    for lo, nbits in fields:
        mask |= ((1 << nbits) - 1) << lo
    return mask


class VLIWState:
    """VLIW / EPIC パケット組み立ての設定と作業状態。

    パターンファイルの `.vliw::<パケット幅>::<命令幅>::<テンプレート幅>::<NOP値>`
    ディレクティブで設定され、1行に `!!` で区切って並べた複数命令を1つの固定幅
    パケットに詰め込むために使う。
    """

    def __init__(self):
        self.instbits = 41        # 命令スロト1個のビット幅
        self.nop = []             # スロットが余ったときに詰める NOP のバイト列
        self.bits = 128           # パケット全体のビット幅
        self.slotset = []         # EPIC: スロットの組み合わせ → テンプレート値
        self.flag = False         # .vliw が宣言済みか
        self.templatebits = 0x00  # テンプレートフィールドのビット幅
                                  # （負ならパケットの上位側に配置する）
        self.stop = 0             # この行が `!!!!`（ストップビット）で終わったか
        self.cnt = 1              # この行に含まれるスロット数


class ElfState:
    """ELF オブジェクト出力（-o）に関わる設定と、パス2で集める情報。"""

    def __init__(self):
        self.osabi: int = 0        # ELF ヘッダの OSABI（0=Linux, 9=FreeBSD）
        self.objfile: str = ""     # -o の出力先。空なら ELF 出力しない
        self.machine: int = 62     # e_machine（62=x86-64）。ELF_MACHINES のキー
        self.elf_class: int = 2    # 1=ELF32 / 2=ELF64

        # --- パス2でのリロケーション収集 ---
        self.relocations = []          # 確定した (セクション, 位置, 名前, 型, 加数, 幅)
        self.tracking = False          # いま収集中か（パス2かつ -o のときだけ真）
        self.label_refs_seen = []      # 1命令分の (ラベル名, 生値, ワード番号)
        self.current_word_idx: int = -1  # 生成中のオブジェクトコードの何ワード目か
        self.var_to_label: dict = {}   # パターン変数 → 束縛元のラベル名
        self.capturing_var: str | None = None  # いま `!x` で捕捉中の変数
        # .reloc 宣言付きの変数がラベルを運んだ箇所。
        # ワード番号 → (型番号, 加数)。加数は「変数が持っていた値 − ラベル値」で、
        # `bl func` なら 0、`bl func+8` なら 8 になる。
        self.insn_reloc_hint: dict = {}

        # --- DWARF デバッグ情報（-g） ---
        self.gen_debug: bool = False
        self.line_map: list = []   # (セクション, pc, ファイル, 行) の対応表

        self.reloctype_override: dict = {}  # `.EQU 値::型名` で明示指定された型


class RelaxationState:
    """パス1のサイズ収束（リラクゼーション）に関する状態。

    可変長命令では「ジャンプ先が遠いか近いか」で命令長が変わり、その命令長が
    後続ラベルのアドレスを動かし、それがまたジャンプ距離を変える……という
    循環がある。そこでパス1を複数回まわし、全ラベルのアドレスが前回と一致
    （＝収束）するまで繰り返す。
    """

    def __init__(self):
        self.pas = 0   # 0=対話モード / 1=パス1（収束中） / 2=パス2（最終）

        # サイズだけ知りたい試行中か。真のときは実バイトを出力しない。
        self.pass1_size_mode = False

        # 前回反復での「ラベル→アドレス」。これが今回と一致したら収束とみなす。
        # 番兵は「まだ1回も反復していない」ことを表す（空辞書と区別するため）。
        self.pass1_prev_label_pcs = _RELAXATION_SENTINEL

        # 前方参照ラベルの推定値（前回反復の確定値）。
        self.relax_prev_values = {}

        # 収束を早めるため、未確定の前方参照を「近い」と楽観的に仮定するモード。
        self.relax_optimistic = False

        # `[[...]]` の組み合わせ爆発を警告済みのパターンを覚えておき、
        # 同じ警告を何度も出さないようにする。
        self.combo_budget_warned = set()


class AssemblerState:
    """アセンブル中の全状態を1か所に集めた入れ物。

    パターン照合・式評価・ディレクティブ処理・出力生成の各クラスは、
    自前の状態を持たずに全てこのオブジェクトを共有して読み書きする。
    """

    def __init__(self):
        global _ACTIVE_STATE
        # モジュール関数 diag() がここへ委譲できるように自身を登録する。
        _ACTIVE_STATE = self

        # パターン照合の試行中に出た診断を溜めておく箱（None なら捕捉していない）。
        # 「試したが不採用だったパターン」のエラーを表示しないために使う。
        self._diag_pending = None

        # --- 出力先 ---
        self.outfile = ""       # -b 生バイナリ
        self.expfile = ""       # -e ラベル TSV（素の形式）
        self.expfile_elf = ""   # -E ラベル TSV（ELF セクションフラグ付き）
        self.impfile = ""       # -i ラベル TSV の取り込み

        # --- 位置カウンタ ---
        self.pc = 0             # 現在のプログラムカウンタ（ワード単位）
        self.padding = 0        # .padding の詰め物バイト値

        self.pc_instr_start = 0   # いま組み立て中の命令の先頭アドレス（`$$`）
        self.pc_instr_end = 0     # その次の命令のアドレス（`$.`）
        self._in_binary_list = False  # オブジェクトコード生成の最中か

        # 識別子に使える文字集合。パターンファイルの .labelc 等で変更できる。
        self.lwordchars = DIGIT + ALPHABET + "_."   # ラベル名
        self.swordchars = DIGIT + ALPHABET + "_%$-~&|"  # .setsym シンボル名

        self.current_section = ".text"
        self.current_file = ""

        # --- 記号表 ---
        self.labels = {}         # ソース側ラベル 名 → [値, セクション, is_equ, ...]
        self.sections = {}       # セクション名 → [開始, ワード数, 入口pc]
        self.symbols = {}        # 現在有効なシンボル（patsymbols のコピー＋α）
        self.patsymbols = {}     # パターンファイルの .setsym で定義されたもの
        self.export_labels = {}  # .global 等で外部公開するラベル
        self.pat = []            # 読み込んだパターン表

        self.vliw = VLIWState()

        self.expmode = EXP_PAT   # いま評価中の式がパターン側かソース側か
        self.expcaps = CAPS_PAT  # いま評価中の式で使える項目（ExprCaps）

        # 直近の式評価で未定義ラベルを踏んだか。重要な約束として、この旗は
        # 「失敗したときに立てる」だけで、成功しても勝手に降ろさない。
        # 1つの式の途中で複数のラベルを引くため、途中で降ろすと先に立った
        # 失敗の情報が消えてしまう。降ろすのは、真新しく判定したい側
        # （.ORG/.RESB/.ZERO/.ALIGN/.EQU 等）が評価直前に自分で行う。
        self.error_undefined_label = False

        # 既に報告したラベル定義の誤り。パス1はリラクゼーションで何度も走るので、
        # 同じ誤りを反復回数だけ並べないための記録（LabelManager が使う）。
        self.reported_label_errors = set()

        # ユーザ向けの " error - ..." を1度でも表示したら立ち、以後降ろさない。
        # run() はパス2の後にこれを見て、エラーが出ていたら出力を書かずに
        # 終了コード1で終わる（不完全・誤ったバイナリを黙って残さないため）。
        self.had_error = False

        # パターン照合の試行中か。試行中のエラーは本物の失敗とは限らないので
        # 表示を抑制する。
        self._in_match_attempt = False

        # --- 出力語の形 ---
        self.align = 16          # .align の既定値
        self.bts = 8             # 1ワードのビット幅（.bits。8以外も可）
        self.endian = 'little'
        self.byte = 'yes'
        self.debug = False

        # --- 現在行の位置情報（エラー表示と DWARF 用） ---
        self.cl = ""             # 現在行のテキスト
        self.ln = 0              # 行番号
        self.fnstack = []        # .INCLUDE のファイル名スタック
        self.lnstack = []        # 同、行番号スタック

        # パターン変数 a〜z の束縛値。
        # 変数名（小文字1文字でも `var_2` のように長くてもよい）→ 値。
        self.vars = {}

        # 同じ添字で「その値が未定義ラベル由来か」を覚えておく札。
        # 値そのものの大きさ（_is_undef_derived）だけでは、`UNDEF-UNDEF` や
        # `UNDEF%UNDEF`、`UNDEF&0` のように算術で番兵が消えた場合を取りこぼす。
        # 束縛した時点で判っている事実なので、値とは別に持ち回る
        # （caxx.c の PatVar.is_undef に対応）。
        # vars を退避・復元する箇所は必ずこちらも一緒に扱うこと。
        self.vars_undef = {}

        # `!L<名前>` が拾った「ソースに書かれていたままの式・ラベルの文字」。
        # 変数名 → 文字列。テキストテンプレートの `{{.exp(<名前>)}}` がこれを
        # そのまま出す（3.5.2 節）。値（vars）とは別物で、vars を退避・復元する
        # 箇所では必ずこちらも一緒に扱うこと（caxx.c の PatVar.text_off に対応）。
        self.vars_text = {}

        self.deb1 = ""           # 照合デバッグ用（ソース側の残り）
        self.deb2 = ""           # 同（パターン側の残り）

        self.exp_typ: str = 'i'  # 'i'=整数 / 'f'=浮動小数点

        self.relax = RelaxationState()

        self.verbose: bool = False
        # パターンのエンコーディング欄が文字列テンプレート "..." だったときに、
        # そこから組み立てたアセンブリ結果のテキスト。1行ごとに作り直す。
        self.asmtext = None
        self.asmtext_disp = None
        # テキスト置換モード（`.textmode`）で、その行の先頭にあった `label:` の
        # 綴りをそのまま覚えておく置き場。書き換えたテキストの前に付け直す。
        # 1行ごとに作り直す。
        self.label_text = ''
        # `.setsym::名前::"文字列"` で登録された文字列シンボル。値が数値では
        # ないので式には出せず、文字列テンプレート（3.5.2）の中でだけ使える。
        # 名前は大文字化して持つ（`.setsym` の数値シンボルと同じ規約）。
        self.strsymbols = {}
        # `.setsym::名前::[項目,項目,…]` で登録された配列シンボル。項目は数値
        # (int/float) でも文字列 (str) でもよく、`x[3]` や `#x[3]` で引く。
        self.arrsymbols = {}
        # `.passthru` の設定。0=切（マッチしない行は Syntax error）、
        # 1=素通し（マッチしない行をそのままテキストとして出す）。
        self.passthru = 0
        # `.eol` の設定。真なら、出力を出した行ごとに改行を1ワード足す。
        self.eol = 0
        # `.textmode` の設定。真なら「テキスト置換モード」。ソースを別の書式の
        # テキストへ書き換えるための設定で、`.passthru` と `.eol` を一緒に立て、
        # `!L<名前>` が拾った式・ラベルの中の未定義ラベルをエラーにしない
        # （値は 0 になり、文字は書かれたとおりに出る）。
        self.textmode = 0

        # 標準入力から読んだソースを置く一時ファイル（全パスで再利用する）。
        self.stdin_tmp_path: str | None = None

        self.elf = ElfState()

        self.init_func: str | None = None
        self.fini_func: str | None = None

        # .check で登録された「この変数はこの条件を満たすこと」という制約。
        # パターンが宣言した変数名（`a` でも `var_2` でも同じ）。式の中で
        # 変数と読むかどうかは綴りだけで決まるので、この集合は `.free` の
        # 取り消しと診断のための記録である。
        self.varnames: set = set()
        self.check_constraints: dict = {}

        # .reloc で登録された「この変数が捕らえたラベル参照は、この ELF
        # リロケーション型で外に出す」という宣言。変数名 -> 型番号。
        # 型はオペランドの位置ごとに決まる（AArch64 では同じシンボルを adrp が
        # ADR_PREL_PG_HI21、add が ADD_ABS_LO12_NC で参照する）ため、シンボル側
        # ではなくパターン側の、この変数単位でしか表せない。
        self.reloc_constraints: dict = {}
        # 未知の型名を報告済みかどうか。(型名, マシン) の集合。
        self._reloc_badname_seen: set = set()

        # .enum で登録された列挙。変数1文字 -> (要素名のタプル, 式の文字列)。
        # `!Ex` の照合と値の算出に使う。
        self.enum_defs: dict = {}

        # .enum の式を評価している間だけ立つ束縛表。[(要素名, 値), ...]。
        # 要素名は「出現していれば .setsym の値、非出現なら 0」に束縛される。
        self.enum_bindings: list | None = None

        # `.sub::名前 ... .return` で登録されたサブ表。
        # 名前 -> [(照合パターン, 値欄), ...]。`!S{{名前}}変数` の展開に使う。
        self.sub_defs: dict = {}
        # `.free` で「この行から先は使わない」と印を付けたサブ表の名前
        # (大文字化)。`.sub` はパターンを読むときに一度だけ組み立てられ、
        # `.setsym` のようにソース1行ごとに作り直されはしないので、消して
        # しまうと `.free` より前に書かれたパターンまで2行目以降に使えなく
        # なる。印は行の頭で落とす。
        self.freed_subs: set = set()

        # `.func::名前::引数 ... .endfunc` で登録されたミニ言語の関数。
        # 名前 -> _MiniFunc。`binary_list` 欄の `.call` から呼ぶ。
        self.func_defs: dict = {}

        # error_patterns 欄（例: `n>7;5`）が返すエラーコード → メッセージ文字列。
        # 実行ごとに独立した可変コピーとして持ち、モジュール定数 ERRORS を汚さない。
        # .error::n::"Message" ディレクティブで上書き・拡張できる。
        self.errors: list = list(ERRORS)

        # セクションは .section / .endsection の出入りで断片化しうる。
        # その断片ごとの (名前, 開始, ワード数) を順に記録する。
        self.section_ranges: list = []

        # .EQU の右辺が複数セクションのラベルにまたがっていないかの検査用。
        self._equ_sections_touched = None

        # マクロ層からラベル値・.equ・$/$$ を参照するための、前回リラクゼーション
        # 反復のスナップショット。マクロ展開はアドレス確定より前に走るので、
        # 「今回の値」は原理的に存在しない。代わりに前回反復の値を使い、収束は
        # リラクゼーションループ（反復上限・振動検出・未収束なら出力しない）に
        # 委ねる。None は「まだ一度も反復していない＝何も分からない」の意味で、
        # このとき未知の名前は 0・defined() は偽になる。
        #   _macro_label_values : 名前 -> 値（値が確定しているものだけ）
        #   _macro_label_names  : 前回反復で存在が確認できたラベル名の集合。
        #                         値が未確定でも「綴り間違いではない」と判定する
        #                         ために、値とは別に持つ。
        #   _macro_line_pcs     : 展開後の行番号 -> その行のアドレス($$ 用)
        self._macro_label_values = None
        self._macro_label_names = None
        self._macro_line_pcs = None
        self._macro_line_pcs_cur: dict = {}


    def diag(self, text, set_error=True, force=False):
        """診断メッセージを表示し、必要なら had_error を立てる。

        表示するかどうかは3段階で決まる:
          1. force=True なら常に表示する（コマンドライン引数の誤り等、
             パスの概念より前に起きる問題用）。
          2. パターン照合の試行中なら表示しない。捕捉中（_diag_pending）なら
             溜めておき、そのパターンが最終的に採用されたときだけ再生する。
          3. それ以外は should_report_errors()、すなわちパス2か対話モードのときだけ。
             パス1で表示しないのは、前方参照が「まだ解決していない」だけで
             本当のエラーではない場合が多いため。

        表示できたときに限り True を返す。set_error=True なら同時に had_error を
        立てるので、以降 run() は出力を書かなくなる。
        """
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
        """以後の診断を表示せず溜め始める（パターン照合の試行前に呼ぶ）。"""
        self._diag_pending = []

    def diag_capture_take(self):
        """溜めた診断を取り出して捕捉を終える。"""
        out = self._diag_pending if self._diag_pending is not None else []
        self._diag_pending = None
        return out

    def diag_replay(self, items):
        """捕捉しておいた診断を実際に表示する。

        採用が確定したパターンの分だけを後から出すために使う。
        """
        for text, set_error in items:
            if self.should_report_errors():
                print(text, file=sys.stderr)
                if set_error:
                    self.had_error = True

    def diag_error(self, msg, force=False):
        return self.diag(f" error - {msg}", set_error=True, force=force)

    def diag_warning(self, msg, force=False):
        return self.diag(f" warning - {msg}", set_error=False, force=force)

    def should_report_errors(self):
        """ユーザ向けエラーを今表示してよいパスか。

        パス2（最終）と対話モードのみ。パス1のリラクゼーション中は同じエラーが
        反復回数だけ重複するうえ、前方参照が未解決なだけの偽エラーも多い。
        """
        return self.pas == 2 or self.pas == 0

    # 旧来のフラットな属性名（state.vliwbits 等）を、分割後のサブ状態
    # （state.vliw.bits 等）へ転送するための対応表。呼び出し側を一斉に
    # 書き換えずに状態を整理できるようにしてある。実際の転送は、この表から
    # クラス定義時に生成する property（すぐ下のループ）が行う。
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
    """行の前処理（コメント除去・エスケープ解決・トークン切り出し）の小道具。

    axx は字句解析器を持たず、1文字ずつ見ながら照合する設計なので、
    「どこまでが1つの語か」を決める処理がこのクラスに集まっている。
    """

    # ASCII 専用の大文字化テーブル。str.upper() を使わないのは、
    # 非 ASCII（日本語等）を変換してしまうと .ascii 文字列の内容が壊れるため。
    _ASCII_UPPER = str.maketrans(LOWER, CAPITAL)

    @staticmethod
    def upper(s):
        """ASCII 英小文字だけを大文字化する（非 ASCII はそのまま）。"""
        return s.translate(StringUtils._ASCII_UPPER)

    @staticmethod
    def join_backslash_continuations(raw_lines):
        """行末が '\\' で終わる行を、次の行と1つの論理行に連結する。

        パターンファイル・ソースファイルのどちらも1物理行=1パターン/1命令が
        前提の実装なので、複雑な式を複数行に分けて書くとそこで暗黙に切れて
        しまう(README Appendix A.3 の AND immediate 例がまさにこれで、警告
        も出さずに後半のフィールドを取りこぼしていた)。'\\' を末尾に置けば
        次の行と連結されるようにして、書き手が意図して複数行に分けられる
        ようにする。

        要素数は変えない: 継続元の行は空文字列に置き換え、連結された内容は
        継続が終わった行の位置にまとめる。呼び出し側は行番号を「リスト内で
        の位置」で数えていることが多いので、これで既存の行番号処理に影響を
        与えない。
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
        """s の idx 位置が文字列 t で始まるか（大小文字を無視して）判定する。"""
        return StringUtils.upper(s[idx:idx + len(t)]) == StringUtils.upper(t)

    @staticmethod
    def skipspc(s, idx):
        """空白・タブを読み飛ばした位置を返す。"""
        while idx < len(s) and s[idx] in ' \t':
            idx += 1
        return idx

    @staticmethod
    def skip_squote_literal(s, i):
        """i が開き引用符の文字リテラル（'a' '\\n' '\\x41'）の直後位置を返す。

        コメント除去が、文字リテラル中の ';' をコメント開始と誤認しないために使う。
        閉じ引用符が見つからなければ「ただの引用符1文字」とみなして i+1 を返す。
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
        """'\\xHH' 形式の文字リテラルを評価する（16進1〜2桁）。

        戻り値は (成功したか, 値, 次の位置)。形が違えば idx を変えずに
        (False, 0, idx) を返すので、呼び出し側は他のリテラル形式へ進める。
        """
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
        return StringUtils._SPACE_RUNS.sub(' ', text)

    @staticmethod
    def normalize_ws(l):
        """アセンブリソース1行の空白を整える（引用符の中は手を付けない）。

        引用符の外では タブ・CR・LF を空白に直し、連続する空白を1個に潰す。
        照合は空白の個数を見ないので、こうしておくと `MOV  A , B` のような
        書き方の揺れを吸収できる。

        破綻点修正: 以前は行全体に一律で適用していたため、文字列リテラルの
        中身まで潰していた。`.ascii "a    b"` が 3 バイトの `a b` になり、
        生のタブは空白へ化けていた（診断は一切出ない）。文字列は「そのままの
        バイト列を置く」のがアセンブラの仕事なので、引用符の中は素通しする。

        `"..."` と `'x'` の扱いは remove_comment_asm() と同じ規約に従う。
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
        """パターンファイルのコメント `/* ... */` を落とす。

        破綻点修正: 以前は「行単位で扱うので閉じ記号は不要」という設計で、
        その行に現れた `/*` から行末までを問答無用で切り捨てるだけだった。
        実際のパターンファイルは何十行にもまたがる本物の C 形式ブロック
        コメントを書いており、開始行以降・終了行までの中身が「'::' の
        無い迷子の行」として毎行 warning を出していた。呼び出し元が
        ファイル全体で共有する in_comment を渡し、複数行にまたがる
        ブロックコメントとして正しく扱う。戻り値は (削った行, 更新後の
        in_comment) のタプル。同じ行内に閉じ記号があれば、その後ろの
        内容は通常どおり生かす。
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
    def remove_comment_asm(l):
        """アセンブリソースの `;` コメントを落とす。

        ただし文字列 "..." や文字リテラル 'x' の中の `;` は本物のデータなので
        残す。引用符の外の `\\;` はエスケープとして扱い、バックスラッシュを外した
        リテラルな `;` に変える（コメントを開始させない）。
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
                return ''.join(out).rstrip()

            out.append(ch)
            i += 1
        if in_dquote:
            diag(f" warning - unterminated string literal in line: {l!r}", set_error=False)
        return ''.join(out).rstrip()

    @staticmethod
    def resolve_vliw_escapes(l):
        """ソース行の `\\!` を解決し、本物の VLIW 区切りを番兵に置き換える。

        処理は2つあるが、必ず1回の左→右走査で同時に行う必要がある:

          * `\\!` → リテラルな `!`（バックスラッシュを外す）
          * 本物の（エスケープされていない）`!!` → VLIW_SEP
            同じく `!!!!` → VLIW_STOP

        なぜ同時でなければならないか。仮に先に `\\!\\!` を `!!` へ戻してしまうと、
        後から区切りを探す別の走査からは、それが「エスケープ由来のただの !!」なのか
        「本物の区切り」なのか区別できない。後続の走査は「どの !! がエスケープ
        だったか」を覚えていないからである。ここで一度だけ判定して本物だけを
        番兵にしておけば、以降の全ての箇所（lineassemble() の後処理、
        VLIWProcessor のスロット走査、get_param_to_spc()/get_param_to_eon()）は
        番兵だけを見ればよく、取り違えが原理的に起きない。

        文字列 "..." と文字リテラル 'x' の中身はそのまま素通しする。
        呼ぶのは remove_comment_asm() が `\\;` を解決しコメントを落とした後なので、
        ここで面倒を見るのは `\\!` だけでよい。
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
        """空白区切りで1語（ニーモニック部分）を切り出す。

        VLIW 区切りの番兵でも切る。番兵で切らないと、`NOP!!NOP` のように
        空白なしで next スロットが続く書き方でニーモニックが隣のスロットを
        飲み込んでしまう。

        素の "!!" では切らないことに注意。ここへ来る時点で本物の区切りは
        resolve_vliw_escapes() が番兵に変換済みなので、残っている "!!" は
        `\\!\\!` を解決したただの文字列であり、区切りとして扱ってはいけない。
        """
        t = ""
        idx = StringUtils.skipspc(s, idx)
        while idx < len(s) and s[idx] != ' ' and s[idx] not in (VLIW_SEP, VLIW_STOP):
            t += s[idx]
            idx += 1
        return t, idx

    @staticmethod
    def get_param_to_eon(s, idx):
        """行の残り（空白を含む＝オペランド部分）を、VLIW 区切りの手前まで取る。"""
        t = ""
        idx = StringUtils.skipspc(s, idx)
        while idx < len(s) and s[idx] not in (VLIW_SEP, VLIW_STOP):
            t += s[idx]
            idx += 1
        return t, idx

    @staticmethod
    def get_string(l2):
        """`"..."` 形式の文字列リテラルを解釈して中身を返す。

        C 風のエスケープ \\n \\t \\r \\" \\\\ と、\\xHH / \\uHHHH / \\UHHHHHHHH に対応する。
        先頭が `"` でなければ空文字列を返す（.ascii 等の引数検査に使う）。
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
    """パターン/ソース双方から「1つの語」を切り出す下位パーサ群。
    
    数値リテラル・浮動小数点リテラル・`{...}` で囲まれた本体・シンボル名・
    ラベル名など、文字種の規約に従って可変長のトークンを読み取る。
    どれも (取り出した文字列, 次の位置) の形で返すのが共通の約束。
    """

    def __init__(self, state):
        self.state = state

    def get_intstr(self, s, idx):
        fs = ''
        while idx < len(s) and s[idx] in DIGIT:
            fs += s[idx]
            idx += 1
        return fs, idx

    def get_floatstr(self, s, idx):
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
        sidx = idx
        v, idx = self.get_floatstr(s, idx)
        if idx == sidx:
            return False
        else:
            return True

    def get_curlb(self, s, idx):
        idx = StringUtils.skipspc(s, idx)
        f = False
        t = ''

        if idx < len(s) and s[idx] == '{':
            idx += 1
            idx = StringUtils.skipspc(s, idx)
            while idx < len(s) and s[idx] != '}':
                t += s[idx]
                idx += 1
            # 末尾の空白と、式文字列に付く終端 NUL を落とす（caxx.c の
            # axx_get_curlb() と揃える）。`}` が閉じていない失敗経路では
            # 行末までを取り込むためこれらが混ざり、エラーメッセージに
            # そのまま出ていた。
            t = t.rstrip(' \t\r\n\x00')
            if idx >= len(s):
                # 破綻点修正: 通常の diag() はパターン照合の試行中は抑制されるため、
                # この「`}` が閉じていない」という具体的な原因が握り潰され、
                # 呼び出し元の総称的な "Illegal syntax ..." だけが出ていた
                # （caxx.c は照合中でも表示するので、両実装で診断が食い違っていた）。
                # 閉じ括弧の欠落はどのパターンで試しても同じく失敗する構文上の誤りで、
                # 特定パターンの不採用とは無関係なので、照合中の抑制を迂回して報告する。
                if self.state.should_report_errors():
                    self.state.diag(f" error - missing closing '}}' in expression: '{{{t}'",
                                    set_error=True, force=True)
                return False, '', len(s)
            idx += 1
            f = True

        return f, t, idx

    def get_symbol_word(self, s, idx):
        t = ""
        if idx < len(s) and s[idx] not in DIGIT and s[idx] in self.state.swordchars:
            t = s[idx]
            idx += 1
            while idx < len(s) and s[idx] in self.state.swordchars:
                t += s[idx]
                idx += 1
        return StringUtils.upper(t), idx

    def get_label_word(self, s, idx, eat_colon=True):
        """ラベル名を1語切り出す。

        eat_colon=True のときは、名前の直後の `:` も一緒に読み飛ばす。
        `foo: NOP` の行頭ラベルや `.EXTERN foo::pc32` を切り出すための約束で、
        呼び出し側は `l[idx-1] == ':'` を見て「ラベル定義だったか」を判定する。

        破綻点修正: 式の評価（ExpressionEvaluator.factor1）からも同じ関数を
        呼んでいたため、三項演算子の `:` がラベル名の一部として食われていた。
        `0?foo:bar` は bar ではなく 0 になり（term11 が `:` を見つけられず
        else 節ごと消える）、しかも診断は一切出なかった。`foo :bar` のように
        空白を入れたときだけ正しく動くという再現条件の分かりにくい誤りだったので、
        式の文脈からは eat_colon=False で呼ぶ。"""
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
    try:
        float_value = struct.unpack('f', struct.pack('I', int(a) & 0xFFFFFFFF))[0]
    except (struct.error, OverflowError, ValueError):
        float_value = 0.0
    return float_value


def endouble(a):
    try:
        double_value = struct.unpack('d', struct.pack('Q', int(a) & 0xFFFFFFFFFFFFFFFF))[0]
    except (struct.error, OverflowError, ValueError):
        double_value = 0.0
    return double_value


enflt = enfloat
endbl = endouble


class IEEE754Converter:
    """10進表記の数値を IEEE754 のビットパターンへ変換する。
    
    32/64bit は struct で足りるが、128bit（四倍精度）は Python に型が無いため
    Decimal を高精度モードで使って手組みで組み立てる。
    decimal_eval_expr() は `3.14*2+1` のような定数式を、途中で float に落とさず
    Decimal のまま評価するためのもの（丸め誤差を持ち込まないため）。
    """

    @staticmethod
    def decimal_to_ieee754_32bit_hex(a):
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
        with localcontext() as _ctx:
            _ctx.prec = 60
            return IEEE754Converter._decimal_to_ieee754_128bit_hex_impl(a)

    @staticmethod
    def _decimal_to_ieee754_128bit_hex_impl(a):
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

            # 破綻点修正: 従来は scaled = int(d * 2**112) で2進指数を求めていたが、
            # d の指数が巨大な場合（qad{1e500000} や qad{1e-500000} 等）、
            # Decimal→巨大整数の変換や以降の1ビットずつの正規化ループが指数の
            # 桁数にほぼ比例して重くなり、事実上ハングしていた。
            # d.adjusted()（10進の桁指数。内部タプルの参照だけで求まり O(1)）を
            # 2進指数へ換算した近似値から出発すれば、以降の補正ループは
            # 桁数によらず数回で 1<=normalized<2 に収束する。
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
        with localcontext() as _ctx:
            _ctx.prec = 60
            return IEEE754Converter._decimal_eval_expr_impl(text)

    @staticmethod
    def _decimal_eval_expr_impl(text):
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
                    v = -dval if neg else dval
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
            return (-v if neg else v), i

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
                return -v, i
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
                    tq = v // t  # Decimal '//' truncates toward zero, not floor
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
    """パターン変数の束縛を管理する。
    
    `!x` や `!Fx` でソースから捕捉した値の置き場。状態は state.vars（名前→値の表）で、
    このクラスは名前の正規化と未定義判定を隠すだけの薄い層。捕捉されていない
    名前を引くと 0 を返す。

    値とは別に「未定義ラベル由来か」の札（state.vars_undef）も持つ。put() は
    札を降ろし、put_tagged() は明示した札を立てる。捕捉時に判っている事実を
    そのまま覚えておくためで、理由は state.vars_undef のコメントを参照。
    """

    def __init__(self, state):
        self.state = state

    @staticmethod
    def _index(s):
        """変数名を正規化する。小文字1文字でも `var_2` のように長くてもよい。

        名前として読めなければ None。caxx.c の var_slot() にあたる。
        """
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
        i = self._index(s)
        if i is None:
            return VAR_UNDEF
        return self.state.vars.get(i, VAR_UNDEF)

    def is_undef(self, s):
        i = self._index(s)
        if i is None:
            return False
        return self.state.vars_undef.get(i, False)

    def put(self, s, v):
        self.put_tagged(s, v, False)

    def put_tagged(self, s, v, is_undef):
        # 破綻点修正: `'' in CAPITAL` は True なので、空文字を渡されると
        # 直後の ord('') が TypeError になっていた（`len == 1` の判定が要る）。
        c = self._index(s)
        if c is None:
            return
        # caxx.c が束縛のときスロットを作るのに合わせ、名前を覚えておく。
        # 文字列テンプレートが「これは変数の名前か」を見るのに使う。
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
    """ソース側ラベルの定義と参照を管理する。
    
    値の取得（get_value）で未定義だった場合は state.error_undefined_label を
    「立てる」だけで、成功しても降ろさないのが重要な約束。
    1つの式が複数のラベルを引くため、途中で降ろすと先に起きた失敗が消えてしまう。
    
    put_value はパスによって意味が変わる:
      パス1 … 新規定義。既に在れば二重定義エラー（.extern の仮登録だけは上書き可）。
      パス2 … 既にパス1で在るはず。無ければ両パスで見た入力が違うという異常。
    """

    def __init__(self, state):
        self.state = state

    def _section_relative_offset(self, name, word_pc):
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
        try:
            v = self.state.labels[k][1]
        except (KeyError, IndexError):
            v = UNDEF
            self.state.error_undefined_label = True
        return v

    def get_value(self, k):
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
                # 破綻点修正: set_error=False で出していたため had_error が立たず、
                # この診断だけが出る経路（パターンファイル側ディレクティブの式など）
                # では「エラーを表示しながら終了コード0」になっていた。
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
        """ラベル定義の誤りを、1つにつき1回だけ必ず表示する。

        破綻点修正: これらは had_error を立てながら通常の diag() で出していた。
        しかし定義の衝突が見つかるのはパス1で、パス1の診断は抑制される。
        パス2では「既に在るラベル」に見えるので二度と検出されず、結果として
        ユーザには具体的な原因が一度も表示されないまま、
        " error - one or more errors were reported during assembly" だけ、
        あるいは（値がずれた場合）「パス1/パス2のアドレス不一致 ＝ リラクゼーション
        未収束」という全く無関係なメッセージが出ていた。
        パス1の抑制を迂回して出す代わりに、リラクゼーションの反復回数だけ
        重複しないよう、同じ誤りは1回に抑える。
        """
        self.state.had_error = True
        if key in self.state.reported_label_errors:
            return
        self.state.reported_label_errors.add(key)
        _fn = self.state.current_file or ""
        self.state.diag(f" error - {msg}  [{_fn}:{self.state.ln}]",
                        set_error=True, force=True)

    def put_value(self, k, v, s, is_equ=False, reloc_type=None):
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
        if reloc_type is not None:
            entry.append(reloc_type)

        self.state.labels[k] = entry
        return True

    def printlabels(self):
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
    """パターンファイルの `.setsym` で定義されたシンボルを引く。
    
    レジスタ名などの「小文字で始まる名前のパターン」が照合時にここを参照する。
    名前は大小文字を区別せずに解決する。
    """

    def __init__(self, state):
        self.state = state

    def get(self, w):
        w = StringUtils.upper(w)
        return self.state.symbols.get(w, "")


# 列挙要素名が「語として」そこで終わっているかの判定に使う文字集合。
# 記号文字（.symbolc の既定に含まれる `-` など）を入れると `A0-A1` の `-` が
# 語の一部に見えて範囲指定も減算も書けなくなるので、英数字と下線に限る。
_ENUM_WORD_CHARS = set(DIGIT + ALPHABET + '_')


def _enum_name_at(s, idx, names):
    """s の idx 位置に一致する列挙要素名のうち最長のものを返す。

    返り値は (要素番号, 終了位置)。一致しなければ (-1, idx)。
    直後が英数字・下線なら語の途中なので一致とみなさない。
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


class ExpressionEvaluator:
    """式評価器。優先順位ごとの再帰下降パーサ。
    
    下から順に:
      factor / factor1  リテラル・ラベル・`$$`/`$.`・`#sym`・qad{}/dbl{}/flt{}・
                        単項 -,~,@・バイト抽出 *(値,位置)・not(...)
      term0_0           `**`
      term0             `*` `/` `//` `%`
      term1             `+` `-`
      term2             `<<` `>>`
      term3/4/5         `&` `|` `^`
      term6             `'`（任意ビット位置からの符号拡張）
      term7             比較
      term8〜11         論理演算と三項演算子
    
    xeval() だけは系統が違い、qad{}/dbl{}/flt{} の中身専用の制限付き評価器。
    Python の ast で解析し、`:ラベル名` 参照と enfloat/endouble 等の呼び出しを許す。
    """

    def __init__(self, state, var_manager, label_manager, symbol_manager, parser):
        self.state = state
        self.var_manager = var_manager
        self.label_manager = label_manager
        self.symbol_manager = symbol_manager
        self.parser = parser

    def nbit(self, l):
        # 実装は共有関数 op_msb() 側。マクロ層も同じものを呼ぶ。
        return op_msb(l)

    def err(self, m):
        print(m, file=sys.stderr)
        return -1

    def factor(self, s, idx):
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
                # 破綻点修正: idx を '*' の次へ進めないと、呼び出し元の乗算ループ
                # (term0)が同じ未消費の '*' を通常の乗算演算子として再度読み、
                # "5+*x" のような壊れた式が 0 * <次の因子> という誤った値へ
                # 静かに縮退してしまう。エラー後は '*' を読み飛ばす。
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
        x = 0
        idx = StringUtils.skipspc(s, idx)

        if idx >= len(s):
            return x, idx

        # .enum の式を評価している間だけ、列挙要素名をその束縛値として読む。
        # `#name` は先に別の枝で処理されるので、そちらは素の .setsym 値になる。
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
            # `#x[3]` は配列シンボルの項目。添字は式で、0 から数える。
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
                # 破綻点修正: str.isdigit() は '²'（上付き2）のような Unicode の
                # 「digit」だが「decimal」ではない文字にも True を返す。
                # 一方 get_intstr() は ASCII の '0'-'9' しか消費しないため、
                # そのような文字では fs='' のまま返ってきて int('') が
                # 未捕捉の ValueError を投げ、生のトレースバックで落ちていた
                # （caxx.c は ASCII のみを見るので同じ入力を正しく構文エラーに
                # する）。ここを get_intstr が実際に消費する文字集合（DIGIT、
                # ASCII '0'-'9'）と揃え、Unicode digit を「数字の先頭ではない」
                # として後続の一般トークン処理に委ねる。
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
                # 代入の右辺だけが未定義かどうかを見たいので、旗を一度降ろして
                # 評価し、結果を変数の札にしてから元の旗と OR で戻す。
                _assign_prior = self.state.error_undefined_label
                self.state.error_undefined_label = False
                x, idx = self.expression(s, idx + _vnl + 2)
                _assign_undef = self.state.error_undefined_label
                self.state.error_undefined_label = _assign_prior or _assign_undef
                self.var_manager.put_tagged(ch, x, _assign_undef)
            else:
                x = self.var_manager.get(ch)
                idx += _vnl
                # 破綻点修正: 値の大きさ（_is_undef_derived）だけで判定していたため、
                # `UNDEF-UNDEF` や `UNDEF%UNDEF` のように算術で番兵が消える式では
                # 未定義を見逃し、0 を黙って出力していた。束縛時に付けた札も見る。
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
                            # 加数は「変数が持っていた値 − ラベル値」。`bl func` なら
                            # 0、`bl func+8` なら 8。命令語のビット欄を逆算しなくて
                            # 済むので、欄の分割や語単位の縮尺に左右されない。
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
        x, idx = self.factor(s, idx)
        while idx < len(s) and StringUtils.q(s, '**', idx):
            t, idx = self.factor(s, idx + 2)

            if self.state.exp_typ == 'f':
                # 浮動小数点モードでは caxx.c の pow(a,b) と同じ、実数のべき乗を
                # そのまま計算する。以下の桁数上限・負指数拒否ガードは、任意精度
                # Python整数が際限なく育つのを防ぐための整数モード専用の安全策で、
                # 有限精度のdoubleしか扱わない浮動小数点モードには無関係。
                # (このガードを素通りさせないと、x が float であるという理由だけで
                # _base_bits が「不明な巨大さ」を意味する1024にフォールバックし、
                # 指数の値に関係なく常にエラー・結果0になっていた。)
                #
                # C の pow(a,b) は範囲外・定義域外でも例外を投げず ±inf/nan を
                # 返す（IEEE754のpowのセマンティクス）。Python の ** / math.pow は
                # 同じ入力で OverflowError / ValueError を投げるため、そのまま
                # 使うとエラー終了と inf/nan のビットパターンとで出力が食い違う。
                # _ieee_pow() で C 側と同じ「例外を投げず ±inf/nan を返す」挙動に
                # 揃える。
                x = _ieee_pow(x, t)
                continue

            _EXP_MAX = 1024
            # axx が本物の値として保証するのは 2**256 まで（_UNDEF_SANE_CEILING）。
            # これを超えて _UNDEF_DERIVED_THRESHOLD (2**768) に近づくと、
            # 正当な ** の結果が「未定義ラベル由来」に誤判定されてしまうため、
            # 上限もこの設計に合わせて 256bit に揃える。
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

            # 指数 0/1 は結果がベースより大きくならない（0乗は常に1、1乗は
            # ベースそのもの）ので、ベースの桁数がどうであれ「掛け合わせで
            # 際限なく育つ」ことはない。既に成立しているベースの値をこの
            # チェックで巻き戻さないよう、桁数ガードの対象から外す。
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
        try:
            return int(v)
        except (OverflowError, ValueError):
            if self.state.should_report_errors():
                self.state.diag(f" error - non-finite value {v!r} in bitwise '{op_name}' operation; treated as 0.", set_error=False)
                self.state.had_error = True
            return 0

    def term3(self, s, idx):
        x, idx = self.term2(s, idx)
        while idx < len(s) and s[idx] == '&' and (idx + 1 >= len(s) or s[idx + 1] != '&'):
            t, idx = self.term2(s, idx + 1)
            x = self._safe_int(x, '&') & self._safe_int(t, '&')
        return x, idx

    def term4(self, s, idx):
        x, idx = self.term3(s, idx)
        while idx < len(s) and s[idx] == '|' and (idx + 1 >= len(s) or s[idx + 1] != '|'):
            t, idx = self.term3(s, idx + 1)
            x = self._safe_int(x, '|') | self._safe_int(t, '|')
        return x, idx

    def term5(self, s, idx):
        x, idx = self.term4(s, idx)
        while idx < len(s) and s[idx] == '^':
            t, idx = self.term4(s, idx + 1)
            x = self._safe_int(x, '^') ^ self._safe_int(t, '^')
        return x, idx

    def term6(self, s, idx):
        x, idx = self.term5(s, idx)
        while idx < len(s) and s[idx] == '\'':
            next_idx = idx + 1
            next_idx = StringUtils.skipspc(s, next_idx)
            if next_idx >= len(s) or (s[next_idx] not in DIGIT and s[next_idx] != '('):
                break
            t, idx = self.term5(s, idx + 1)
            # 実装は共有関数 op_sext() 側。マクロ層も同じものを呼ぶ。
            x, _warn, _go = op_sext(x, t)
            if _warn:
                self.state.diag(f" warning - {_warn}.", set_error=False)
            if not _go:
                break
        return x, idx

    def term7(self, s, idx):
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
        return self.term7(s, idx)

    def term9(self, s, idx):
        x, idx = self.term8(s, idx)
        while idx < len(s) and StringUtils.q(s, '&&', idx):
            t, idx = self.term8(s, idx + 2)
            x = 1 if x and t else 0
        return x, idx

    def term10(self, s, idx):
        x, idx = self.term9(s, idx)
        while idx < len(s) and StringUtils.q(s, '||', idx):
            t, idx = self.term9(s, idx + 2)
            x = 1 if x or t else 0
        return x, idx

    # 三項演算子の「取らない側」を、評価せずに字面だけで読み飛ばすための走査。
    # 括弧・角括弧・省略可グループの入れ子は数えて、深さ0の `?` `,` `;` と、
    # `:=`（代入）ではない `:` で止まる。
    @staticmethod
    def _skip_subexpr(s, idx):
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
        """三項演算子 `cond ? a : b`。

        破綻点修正: 以前は両辺を必ず評価し、取らなかった側の副作用
        （変数束縛・未定義ラベル旗・ELF リロケーション参照）を後から巻き戻して
        いた。しかし diag() で「表示済み」になった診断だけは巻き戻せないため、
        `1 ? 5 : nosuchlabel` のように取らない側に未定義ラベルがあると、
        値は正しいのに " error - Label undefined: 'nosuchlabel'" が出て
        ビルドが失敗していた。加えて、取らない側の解析位置に依存する作りだった
        ので、真側がラベルで終わると `:` を見失って else 節ごと消えていた。

        caxx.c と同じく、取らない側は評価せず字面で読み飛ばす短絡評価に統一する。
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
        try:
            idx0 = StringUtils.skipspc(s, idx)
            x, idx0 = self.term11(s, idx0)
            return x, idx0
        except RecursionError:
            self.state.diag(" error - expression nesting too deep (RecursionError).", set_error=True)
            return 0, idx

    def _terminate(self, s):
        if not s or s[-1] != chr(0):
            return s + chr(0)
        return s

    def _patvar_len_at(self, s, idx):
        """位置 idx から読めるパターン変数名の長さ。変数でなければ 0。

        小文字で始まり小文字・数字・`_` が続くひと続きを、長さによらず
        パターン変数の名前とする。`a` も `var_2` も同じ規則で、宣言や
        捕捉の有無は問わない（捕捉されていない変数は 0 を返す）。
        直後にラベル構成文字（大文字や `.`）が続くときだけ、変数ではなく
        ラベルとして読む。caxx.c の pat_var_len_at() と同じ規則である。
        """
        n = PatternMatcher._var_name_at(s, idx)
        if n == 0:
            return 0
        if idx + n < len(s) and s[idx + n] in self.state.lwordchars:
            return 0
        return n

    def expression_pat(self, s, idx):
        return self._expression_in(s, idx, EXP_PAT, CAPS_PAT)

    def expression_caps(self, s, idx, caps):
        """能力記述子を指定して評価する。マクロ層・ミニ言語からの委譲用。"""
        return self._expression_in(s, idx, EXP_PAT, caps)

    def _expression_in(self, s, idx, mode, caps):
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
        return self._expression_in(s, idx, EXP_ASM, CAPS_ASM)

    def expression_esc(self, s, idx, stopchar):
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
                # 種類が不一致でも（例: "(...]"）深さは1段閉じたものとして扱う。
                # 型を厳密に照合してポップを拒否すると、不正な入力に対して
                # stack が空に戻らなくなり、以降 stopchar が永久に見つからなく
                # なってしまう（未対応の閉じ括弧のまま行末まで飲み込まれる）。
                if stack:
                    stack.pop()
                result.append(ch)
            else:
                result.append(ch)

        replaced = ''.join(result)
        return self.expression(self._terminate(replaced), idx)

    def expression_esc_float(self, s, idx, stopchar):
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
    """生成したワードを出力バッファへ書き込む。
    
    アドレスをキーにした疎な辞書で保持するので、`.ORG` でアドレスが飛んでも
    その間を無駄に埋めずに済む。1ワードのビット幅（state.bts）は 8 とは限らず、
    書き込み時にその幅でマスクし、エンディアンに従ってバイトへ展開する。
    """

    def __init__(self, state):
        self.state = state
        self._buffer = {}

    def _store(self, position, word_val):
        if self.state.bts <= 0:
            return
        if position < 0:
            return
        mask = (1 << self.state.bts) - 1
        self._buffer[position] = word_val & mask

    def flush(self):
        if not self.state.outfile:
            return

        # 破綻点修正: この検査は `not self._buffer` の後ろに置かれていたが、
        # bts<=0 のときは _store() が何も溜めないので _buffer は必ず空であり、
        # 警告に到達できないデッドコードだった（結果として何も言わずに
        # 出力ファイルが作られないだけになる）。バッファ判定より前に出す。
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

        with open(self.state.outfile, 'wb') as f:
            f.write(data)
        print(f"wrote raw binary {self.state.outfile} ({len(data)} bytes)", file=sys.stderr)

        # 命令フィールド型のリロケーションを出した箇所は、RELA の作法どおり命令語の
        # ビット欄を 0 にしてある（リンカが埋める）。同じ実行で -b も書いていると、
        # その 0 がそのまま生バイナリに残り、リンカを通さない側だけが壊れる。
        # 黙って壊れた方が困るので、どの箇所かを添えて知らせる。
        if self.state.elf_objfile:
            _zeroed = [r for r in self.state.relocations
                       if insn_reloc_field_mask(r[3]) is not None]
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
        if self.state.should_report_errors():
            try:
                self.fwrite(a, int(x), 0)
            except (OverflowError, ValueError):
                self.state.diag(f" error - non-finite value {x!r} cannot be written as binary word.", set_error=True)

    def outbin(self, a, x):
        if self.state.should_report_errors():
            _prt = 1 if ((self.state.pas == 2 and self.state.verbose) or self.state.pas == 0) else 0
            try:
                self.fwrite(a, int(x), _prt)
            except (OverflowError, ValueError):
                self.state.diag(f" error - non-finite value {x!r} cannot be written as binary word.", set_error=True)

    def align_(self, addr):
        if self.state.align <= 0:
            return addr
        a = addr % self.state.align
        if a == 0:
            return addr
        return addr + self.state.align - a


class DirectiveProcessor:
    """パターンファイル側のディレクティブを処理する。
    
    `.setsym`（シンボル定義）、`.bits`（語長とエンディアン）、`.vliw` / `EPIC`
    （VLIW パケットの形）、`.padding`、`.check` / `.clrcheck`（オペランド制約）など、
    「命令表そのものではなく、命令表の読み方を決める」指示を扱う。
    
    これらはパターン走査の途中でも出現順に副作用を及ぼすため、採用パターンが
    確定したときには「そのパターンに到達した時点の状態」へ巻き戻す必要がある。
    """

    def __init__(self, state, expr_eval, binary_writer, symbol_manager=None, parser=None):
        self.state = state
        self.expr_eval = expr_eval
        self.binary_writer = binary_writer
        self.symbol_manager = symbol_manager
        self.parser = parser

    def add_avoiding_dup(self, l, e):
        if e not in l:
            l.append(e)
        return l

    def clear_symbol(self, i):
        if len(i) == 0 or i[0] != '.clearsym':
            return False

        if len(i) >= 3 and i[2] != '':
            key = StringUtils.upper(i[2])
            self.state.symbols.pop(key, None)
            self.state.strsymbols.pop(key, None)
            self.state.arrsymbols.pop(key, None)
        else:
            self.state.symbols = {}
            self.state.strsymbols = {}
            self.state.arrsymbols = {}

        return True

    def set_symbol(self, i):
        if len(i) == 0 or i[0] != '.setsym':
            return False

        if i[1]:
            key = StringUtils.upper(i[1])
            value_field = i[2]
        elif i[2]:
            key = StringUtils.upper(i[2])
            value_field = ''
        else:
            self.state.diag(" error - .setsym directive requires at least a symbol name", set_error=True)
            return False

        # 値が `"..."` なら文字列シンボル、`[...]` なら配列シンボル。
        _vf = value_field.lstrip(' \t')
        if _vf.startswith('"'):
            self.state.strsymbols[key] = ObjectGenerator._txt_template_inner(_vf)
            return True
        if _vf.startswith('['):
            self.state.arrsymbols[key] = arr_items_from_text(self.expr_eval, _vf)
            return True
        # `.setsym::y::x` — x が文字列／配列シンボルなら、その写しを作る。
        if symbol_copy_from_name(self.state, key, _vf):
            return True
        # `名前,名前,…` は名前の集合、`a&b` などは集合どうしの演算。
        if symbol_set_from_text(self.state, key, value_field):
            return True
        if value_field:
            v, idx = self.expr_eval.expression_pat(value_field, 0)
        else:
            v = 0
        self.state.symbols[key] = v
        return True

    def bits(self, i):
        """`.bits[::<big|little>][::<幅>]` — ワード長とエンディアン。

        破綻点修正: 幅の検証が一切無かった。パターン表の行は常に6要素なので
        `len(i) >= 3` が必ず真になり、`.bits::big`（幅の書き忘れ。この形では
        'big' は i[2] に入る）でも i[2] を式として評価してしまい、未定義ラベル
        'big' の番兵 (1<<1024)-1 がそのままワード長になっていた。以降の出力は
        1ワードごとに OverflowError で潰れ、しかもその診断は had_error を
        立てないため「エラーを表示しながら終了コード0・出力ファイル無し」という
        無言の失敗になっていた。欄の解釈を整理し、1..64 の整数だけを受け付ける。
        """
        if len(i) == 0 or i[0] != '.bits':
            return False

        # 破綻点修正: 欄の意味を位置(第1欄=エンディアン,第2欄=幅)で固定していたため
        # `.bits::<幅>::<big|little>`（順序が逆）を書くと、幅の値が捨てられた上で
        # 診断なしにエンディアンだけが適用されていた。位置ではなく内容
        # ('big'/'little' かどうか)でフィールドの役割を判定し、順序に依らず両方
        # 正しく解釈する。
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
        if len(i) == 0 or i[0] != '.symbolc':
            return False

        if len(i) > 2 and i[2] != '':
            self.state.swordchars = ALPHABET + DIGIT + i[2]
        return True

    def vliwp(self, i):
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

        # 破綻点修正: v1〜v3 だけ int() を通していて v4（NOP 値）は生のまま
        # `v4 & 0xff` / `v4 >>= 8` に渡していた。float なら TypeError、負値なら
        # Python の算術シフトが 0xff を無限に生み続けて caxx.c（uint64 で
        # いずれ 0 になる）と食い違っていた。64bit の符号なし値に揃える。
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
        """この条件式は、リンカが値を決める変数を見ているか。

        `-o` で命令フィールド型のリロケーションを出す箇所では、命令語のビット欄は
        0 で出してリンカが埋める。つまり `t` の値はアセンブル時には確定しておらず、
        axx が持っているのは自分の仮レイアウト上の値にすぎない。その値に対する
        整列・範囲チェックは判定できないものを判定していることになり、正しいソース
        まで弾く。範囲や整列が本当に外れていればリンカが報告する（例:
        `improper alignment for relocation R_AARCH64_LDST64_ABS_LO12_NC`）ので、
        ここでは黙って通す。

        対象は「その変数を読んでいる条件」だけ。同じ行の他のオペランドを見る条件
        （PRFM の `p<0` 等）はそのまま働く。
        """
        if not self.state.elf_objfile or not self.state.reloc_constraints:
            return False
        for var, rtype in self.state.reloc_constraints.items():
            if insn_reloc_field_mask(rtype) is None:
                continue
            for m in re.finditer(re.escape(var), cond_src):
                b, e = m.start(), m.end()
                # 変数名は単独の語として現れたときだけ。`t` が `tmp` や `xt` の
                # 一部であるものを拾わない。
                if b > 0 and (cond_src[b - 1].isalnum() or cond_src[b - 1] == '_'):
                    continue
                if e < len(cond_src) and (cond_src[e].isalnum() or cond_src[e] == '_'):
                    continue
                return True
        return False

    def error(self, s):
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
        """ディレクティブの変数欄を読む。1文字でも `var_2` のように長くてもよい。

        名前として読めなければ None。caxx.c の dir_var_slot() にあたる。
        """
        v = (field or '').strip().lower()
        if not v or not v.isascii() or not ('a' <= v[0] <= 'z'):
            return None
        for ch in v[1:]:
            if not ('a' <= ch <= 'z' or ch.isdigit() or ch == '_'):
                return None
        self.state.varnames.add(v)
        return v

    def elem_list_expand(self, text):
        """要素の列挙欄（`.check` `.enum` `.map` の「名前の並び」）を項目に切る。

        項目が配列シンボルの名前なら、その内容をその場に展開する。つまり
            .setsym::regs::["R0","R1","R2"]
            .check::x::regs
        は `.check::x::R0,R1,R2` と同じ意味になる。配列と素の名前は混ぜて
        書ける。名前は大文字化して積み、`""` `''`（省略可の印）と空欄は
        空文字の項目にする。caxx.c の elem_list_expand() と同じ規則である。
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
        syms = []
        for nm in self.elem_list_expand(syms_field):
            if nm == '':
                # 空文字リテラルは「このオペランドは省略してよい」印。
                # 省略時、変数には VAR_UNDEF(0) が入る。
                if CHECK_OMIT not in syms:
                    syms.append(CHECK_OMIT)
                continue
            syms.append(nm)
        self.state.check_constraints[var] = syms
        return True

    def reloc_processing(self, i):
        """`.reloc::<変数>::<型名>`

        その変数が捕らえたラベル参照を、指定の ELF リロケーション型で書き出す。
        `.check` と同じく位置依存で、後の `.reloc` が前のものを置き換える。

        型名は `-m` で選んだマシンの名前表（`::pc32` などに使うものと同じ）から
        引く。AArch64 の `call26` のような命令フィールド型は、値が命令語のビット欄
        に詰まっていて出力バイト列から加数を逆算できないため、この宣言が要る。
        """
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
        # リロケーションは `-o` の ELF 出力にしか現れない。`-b` などでは宣言は
        # 無意味なので、型名を照合せずに受け流す。パターンファイルは複数の `-m`
        # で使い回せるべきで、対象外のときに落ちてはいけない。
        if not self.state.elf_objfile:
            return True
        mach = ELF_MACHINES.get(self.state.elf_machine)
        rtype = mach['named'].get(tname.lower()) if mach else None
        if rtype is None:
            _mname = mach['name'] if mach else self.state.elf_machine
            # パターン行は1ソース行ごとに読み直されるので、同じ名前で何度も
            # 出さないよう一度だけ報告する。
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
        """`.map::<変数>::<名前の並び>::<式>`
        `.map::<変数>::<名前の並び>::<値,値,…>`

        並びの各名前に値を与える `.setsym` と、その変数の `.check` をまとめて
        書くための省略形。式の中の変数は「その名前が並びの何番目か」
        (0 から数える) を指す。

            .map::x::R0,R1,R2::1<<x
        は
            .setsym::R0::1<<(0)
            .setsym::R1::1<<(1)
            .setsym::R2::1<<(2)
            .check::x::R0,R1,R2
        と等価である。式を省くと変数そのもの、すなわち 0 からの連番になる。

        値欄を最上位のカンマで区切って書くと、並びと1対1で対応する値の
        リストになる。

            .map::x::R0,R1,R2,R3::9,7,14,41
        は
            .setsym::R0::9
            .setsym::R1::7
            .setsym::R2::14
            .setsym::R3::41
            .check::x::R0,R1,R2,R3
        と等価である。個数が合わないときはエラーにする。各項目は式なので、
        変数（＝並びの番号）を書いてもよい。

        並びには配列シンボルの名前を書ける（elem_list_expand() が展開する）。

        into が与えられればシンボルはそこへ、なければ state.symbols へ入れる。
        caxx.c の map_apply() と同じ規則である。
        """
        var_str = i[1].strip() if len(i) >= 2 else ''
        syms_str = i[2] if len(i) >= 3 else ''
        expr_str = i[3] if (len(i) >= 4 and i[3].strip()) else var_str
        var = self._dir_var(var_str)
        if var is None:
            return
        target = self.state.symbols if into is None else into

        elems = self.elem_list_expand(syms_str)
        # 値欄が最上位のカンマで区切られていれば、並びと1対1の値のリスト。
        # 1項目しか無ければ従来どおり「変数を含む式」1本として扱う。
        vals = split_top_commas(expr_str)
        if len(vals) > 1 and len(vals) != len(elems):
            self.state.diag(f" error - .map: the value list has {len(vals)} items "
                            f"but the name list has {len(elems)}.", set_error=True)
            return
        for n, nm in enumerate(elems):
            # 空の要素（`""` の省略可印など）は番号だけ消費して何も定義しない。
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
        """`.map` をパターン走査中に適用する。"""
        if len(i) == 0 or i[0] != '.map':
            return False
        self.map_apply(i)
        return True

    def free_processing(self, i):
        """`.free::名前,名前,…`

        その名前を、パターン層のあらゆる表から外す。置き場所ごとに
        `.clearsym` `.clrcheck` `.clrenum` と書き分けなくても、名前ひとつで
        「もうこの名前は使わない」と宣言できるようにするためのもの。外すのは
          - `.setsym` の数値シンボル・文字列シンボル・配列シンボル
          - `.sub` の表
          - `.check` の候補（どの変数の一覧に入っていても取り除く）
          - 名前が変数として読める綴りなら、その変数の `.check` と `.enum` ごと
        で、`.clearsym` などと同じく書かれた位置から先に効く。
        caxx.c の dir_free() と同じ規則である。
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
            self.state.freed_subs.add(key)
            # `.check` の候補からも外す。候補は大文字で積まれている。
            for var, syms in self.state.check_constraints.items():
                self.state.check_constraints[var] = [x for x in syms if x != key]
            # 名前が変数そのものなら、その変数の制約と列挙ごと外す。
            _v = nm.lower()
            if _v and PatternMatcher._var_name_at(_v, 0) == len(_v):
                self.state.check_constraints.pop(_v, None)
                self.state.reloc_constraints.pop(_v, None)
                self.state.enum_defs.pop(_v, None)
        return True

    def passthru_processing(self, i):
        """`.passthru[::on|nonl|off]`

        どのパターンにもマッチしなかったソース行を、エラーにする代わりに
        そのままテキストとして出す（トランスレータとしての使い方のため）。
        その行はパターンのエンコーディング欄が `"<行>"` というテキスト
        テンプレートだったのと同じ扱いになり、UTF-8 の 1 バイトが 1 ワードに
        なってロケーションカウンタもその分進む。

            .passthru          on と同じ
            .passthru::on      素通しする
            .passthru::off     素通しをやめる（既定）

        行末の改行はこのディレクティブの仕事ではない。1行が1行になるように
        したいときは `.eol` を併せて書く。

        パターンファイルは1行ごとに全部走査されるので、これはファイル全体に
        かかる設定として働く（同じファイルに複数書いた場合は最後のものが
        効く）。caxx.c の dir_passthru() と同じ規則である。
        """
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
        """`.eol[::on|off]`

        テキスト変換のための設定で、出力を出した行ごとに改行（`\n`）を
        1ワード足す。パターンのテキストテンプレートに `\n` を書いて回らなくても、
        ソースの1行が出力の1行になる。

            .eol          on と同じ
            .eol::on      行ごとに改行を足す
            .eol::off     足さない（既定）

        足すのは出力ワード列の側だけで、標準出力へ流すテキスト（トランスレータ
        としての出力）には足さない。そちらは行ごとに改行して出しているので、
        二重に改行してしまわないようにしてある。出力ワードを1つも出さなかった行
        （コメントだけの行や、何も出さないパターン）には足さない。`.vliw` が
        有効なときは、パケットを壊さないよう何もしない。

        パターンファイルは1行ごとに全部走査されるので、これはファイル全体に
        かかる設定として働く（同じファイルに複数書いた場合は最後のものが
        効く）。caxx.c の dir_eol() と同じ規則である。
        """
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
        """`.textmode[::on|off]`

        テキスト置換モード。ソースを別の書式のテキストへ書き換える
        （トランスレータとしての）使い方のための設定で、次の3つをまとめて行う。

          1. `.passthru` を立てる（マッチしない行はそのまま出す）
          2. `.eol` を立てる（出力を出した行ごとに改行を1ワード足す）
          3. `!L<名前>`（式・ラベル捕捉子）の中の未定義ラベルをエラーにしない。
             値は 0 になり、`{{.exp(<名前>)}}` が書かれたとおりの文字を出す。

            .textmode          on と同じ
            .textmode::on      テキスト置換モードにする
            .textmode::off     やめる（既定）

        3 つまとめて動くので、`.passthru` や `.eol` だけを別にしたいときは
        この行の後ろでそちらを書けばよい（ディレクティブは書いた順に効く）。

        パターンファイルは1行ごとに全部走査されるので、これはファイル全体に
        かかる設定として働く（同じファイルに複数書いた場合は最後のものが
        効く）。caxx.c の dir_textmode() と同じ規則である。
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
        """`.enum::<変数>::<要素名の並び>::<式>`。

        `!E<変数>` が拾う「要素名のリスト」の語彙と、そこから値を作る式を決める。
        式の中では各要素名が「そのリストに現れていれば .setsym の値、
        現れていなければ 0」に束縛される。
        """
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
        """`.error::n::"Message"` — error_patterns 欄（`n>7;5` の `5` のような
        エラーコード）に対応するメッセージ文字列を ERRORS テーブルに登録する。

        組み込みの ERRORS が文言を持たないコード（4 や 7 以上）にも新しく
        メッセージを追加できるし、既存コード（1・2・3・5・6）の文言を
        上書きすることもできる。n がテーブルの現在の大きさを超える場合は
        空文字列で埋めて拡張する（README 9章の「文言の無いコードは空文字列で
        表示される」という既定動作と整合する）。
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
        if n_int is None or n_int != n or n_int < 0:
            self.state.diag(f" error - .error: error code must be a non-negative integer, got {n_field!r}.", set_error=True)
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

# テキスト置換モード（`.textmode`）で、処理せずテキストとしてだけ出す組み込み
# アセンブリディレクティブ。いずれも自分でワードや領域を出す（あるいは
# ロケーションカウンタを飛ばす）ものなので、テキストとして出したうえで
# さらに出させると中身が二重になり、翻訳結果のテキストに詰め物や生データが
# 混ざってしまう。テキスト置換モードでの出力は「書き換えたテキストそのもの」
# なので、行はテキストとして残し、出力の側は何も出さない。
# caxx.c の textmode_text_only_dir() と同じ表である。
_TEXTMODE_TEXT_ONLY_DIRS = frozenset((
    '.ORG', '.ALIGN', '.ZERO', '.ASCII', '.ASCIZ',
    '.RESB', '.RESW', '.RESD', '.RESQ'))


def _expects_expr(t, idx):
    while idx < len(t) and t[idx] in ' \t':
        idx += 1
    return idx < len(t) and t[idx] == '!'


class PatternMatcher:
    r"""ソース行とパターンの照合を行う。
    
    字句解析をせず1文字ずつ突き合わせる。パターン側の文字の意味は:
      大文字        大小無視でリテラル一致（ニーモニック）
      小文字の名前  .setsym のシンボル（レジスタ名等）を取る
      `!x`          任意の式を読んで変数 x に束縛
      `!!x`         式ではなく factor 1個だけを束縛
      `!Fx`/`!Dx`/`!Qx`  浮動小数点式を IEEE754 の 32/64/128bit として束縛
      `!Lx`         式・ラベル捕捉子。`!x` と同じに値を束縛し、そのうえで
                    ソースに書かれていたままの文字も覚える（`{{.exp(x)}}`）
      `!S{{名前}}x` `.sub::名前 … .return` のサブ表のどれか1項目に一致させ、
                    その項目の値欄を評価した結果を変数 x に束縛
      `\c`          次の1文字をリテラル扱い（エスケープ）
      `[[ ... ]]`   省略可能グループ。含む/含まないの全組合せを試す
    
    照合が成功すると具体度スコア (式の数, -リテラル文字数, シンボル数) を残す。
    呼び出し側はこれが最小のパターンを採用する（＝最も具体的なものが勝つ）ので、
    パターンファイル内の記述順に依存しない。
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
        """パターン文字列 t の位置 i から変数名を読む。長さを返す（0 なら無し）。

        名前は小文字で始まり、小文字・数字・`_` が続く。
        caxx.c の var_name_len() と同じ規則である。
        """
        if i >= len(t) or not ('a' <= t[i] <= 'z'):
            return 0
        n = 1
        while i + n < len(t) and ('a' <= t[i + n] <= 'z'
                                  or t[i + n].isdigit() or t[i + n] == '_'):
            n += 1
        return n

    def _var_declare(self, name):
        """名前を「この表の変数」として登録する。長さは問わない。"""
        if name:
            self.state.varnames.add(name)
        return name

    def _enum_capture(self, s, idx, edef):
        """`!E<変数>` の位置から列挙要素のリストを読み、式の値を返す。

        受け付けるのは `A0`、`A0-A2`（列挙順での範囲）、およびそれらを `,` か
        `/` で並べたもの。区切り記号は「その先に要素名が続くとき」だけ消費する
        ので、`MOVEM !Ex,-(SP)` のようにパターン側が後ろで `,` を使っていても
        リストの一部と取り違えない。

        返り値は (値, 読み終えた位置)。一致しなければ None。
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
                    # 範囲として読めない `-` は、減算などパターン側の続きに残す。
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
        """列挙の式を、出現した要素だけ .setsym の値に束縛して評価する。"""
        names, expr = edef
        values = []
        for k, nm in enumerate(names):
            if k not in present:
                values.append(0)
                continue
            v = self.symbol_manager.get(nm)
            if v == "":
                # 現れた要素に .setsym が無い ＝ パターンファイル側の書き損じ。
                # 0 を黙って混ぜて誤ったバイトを出すより、不一致にして知らせる。
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
                # 破綻点修正: 上限を len(t) で見ていたが、t は末尾に番兵の
                # chr(0) を1個足してある。パターン欄が `\` で終わると
                # その番兵を「エスケープされた文字」として b（同じく番兵）に
                # 一致させてしまい、idx_s が s の外へ出て IndexError になった。
                # 例外は呼び出し元が握り潰すので、症状は「そのパターンが
                # 永久に一致しない」＋原因不明の Illegal syntax だった。
                # caxx.c と同じく、番兵の手前までを本文として扱う。
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
                    # `!L<名前>` — 式・ラベル捕捉子。`!<名前>` と同じように式を
                    # 1つ読んで値を束縛し、そのうえで「ソースに書かれていたまま
                    # の文字」も覚えておく。テキストテンプレートの
                    # `{{.exp(<名前>)}}` がその文字をそのまま出す（3.5.2 節）。
                    # テキスト置換モード（`.textmode`）では、拾った式の中の
                    # 未定義ラベルをエラーにせず値を 0 にする。書き換え先の
                    # テキストに要るのは値ではなく綴りそのものだからである。
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
                        # テキストへ書き換えるだけの行なので、値が決まらない
                        # ことは誤りではない。番兵を持ち回らず 0 にしておく。
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
                elif a == '!':
                    if idx_t >= len(t):
                        return False
                    _nl = self._var_name_at(t, idx_t)
                    if _nl == 0:
                        return False
                    a = self._var_declare(t[idx_t:idx_t + _nl])
                    idx_t += _nl
                    self.state._elf_capturing_var = a
                    # 捕捉した式だけが未定義だったかを見たいので旗を一度降ろす。
                    # 結果は変数の札に移し、外側の旗は OR で戻す。
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
                    # `!name` の名前。直前で1文字読み進めてあるので測り直す。
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
                # シンボルを取る位置。名前は1文字でも `var_2` のように長くてもよい。
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
                    # 語として切り出せなかった／許可リストに無かった場合、
                    # 許可リストの名前そのものを前方一致で取り直す。
                    # `MOVa1c3` のように区切り文字なしで連結された書き方を通すため。
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
                    # 省略とみなす。ソースは1文字も消費せず、変数は未代入(0)。
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
        """`!S{{名前}}変数` を探し、(開始, 終了, 名前, 変数) を返す。無ければ None。"""
        i = start
        while True:
            i = t.find('!S{{', i)
            if i < 0:
                return None
            j = t.find('}}', i + 4)
            if j < 0:
                return None
            # `\!` とエスケープされていれば式ではなくリテラルの `!`。
            if i > 0 and t[i - 1] == '\\':
                i = j + 2
                continue
            name = t[i + 4:j]
            k = j + 2
            # 変数名は1文字でも `var_2` のように長くてもよい。
            vl = PatternMatcher._var_name_at(t, k)
            if _is_sub_name(name) and vl > 0:
                return i, k + vl, name, t[k:k + vl]
            i = j + 2

    def _sub_variants(self, t, depth=0):
        """`!S{{名前}}x` をサブ表の各項目で置換した候補を、表の記述順に生成する。

        返すのは (置換後のパターン, ((変数, 値欄), ...)) の組。値欄は照合が
        成功してから評価する（項目のパターンが束縛した変数を使えるように）。
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
            entries = None          # `.free` で解放済み
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
        """サブ表の値欄を評価する。

        カンマ区切りで複数書かれていれば、先頭を上位として `.bits` 幅ずつ
        詰めた1つの整数にする（`0x01,0x02` は 8bit 幅なら 0x0102）。
        1つだけなら値そのもの。
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
        for vt, binds in self._sub_variants(t):
            saved_vars = dict(self.state.vars)
            saved_vars_undef = dict(self.state.vars_undef)
            saved_vars_text = dict(self.state.vars_text)
            saved_refs_len = len(self.state._elf_label_refs_seen)
            saved_v2l = dict(self.state._elf_var_to_label)
            saved_hint = dict(self.state._elf_insn_reloc_hint)
            if self.match0_brackets(s, vt):
                # 入れ子のときは内側から。外側の値欄が内側の変数を使える。
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
    """`.axx` パターンファイルを読み、パターン表に変換する。
    
    各行を "::" 区切りで最大6フィールドに分解する。`.INCLUDE` は再帰的に展開し、
    循環と深すぎる入れ子は検出して打ち切る。
    
    ソース側とは別インスタンスのマクロ層を通す。名前空間を分けてあるので、
    パターンファイルのマクロがソースの展開に影響することはない。
    """

    def __init__(self, parser, macro_proc=None):
        self.parser = parser
        self.macro_proc = macro_proc if macro_proc is not None \
            else MacroPreprocessor(None, pat_mode=True)
        # `.sub::名前 ... .return` で集めたサブ表。名前 -> [(パターン, 値欄), ...]。
        self.subs = {}
        # `.func::名前::引数 ... .endfunc` で集めたミニ言語の関数。名前 -> _MiniFunc。
        self.funcs = {}

    def readpat(self, fn, base_dir=None, _depth=0, _chain=None):
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

        # 破綻点修正: 「本物の複数行ブロックコメント(閉じ記号が後の行にあり、
        # 中身の行は '/*' で始まらない)」と「開始記号を単なる行末コメントの
        # 目印として毎行書くだけの古い流儀(コメントの各行が '/*' で始まり、
        # 閉じ記号は無いか、あっても離れた場所にある別の無関係なコメントの
        # ものでしかない)」の2つの書き方が実在のパターンファイルに混在している。
        # 「次の1行だけ」を見て判定すると、旧来スタイルの連続コメントの最後の
        # 1行(次の行はもう普通のコード)を誤って「本物のブロックコメント開始」
        # と誤認し、たまたま遠く離れた場所にある無関係な閉じ記号まで実際の
        # パターン行を丸ごと呑み込んでしまう(8080.axx で発生)。そこで、
        # 「直前の行も '/*' で始まる行で、かつ単発扱い(旧来スタイル)と
        # 判定されていたか」を legacy_chain として引き継ぎ、旧来スタイルの
        # 連続コメントは何行続いても・最後の1行であっても単発行として扱う。
        # legacy_chain が途切れた(=直前が普通のコードだった)場合のみ、次の
        # 行が '/*' で始まらずかつこの位置より後ろに閉じ記号が本当に存在する
        # ときに限り、新規のブロックコメントとして正しく閉じるまで追跡する。
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
                # このコメントはこの行の中で完結した(あるいは元々コメントで
                # なかった)ので、旧来スタイルの連鎖はここで途切れる。
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

            # ミニ言語の `.func` 本体は `::` で分解せず、行のまま集める。
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
                        # 名前が壊れていても本体を取り込んで `.endfunc` の対応を保つ。
                        func_stack.append(_MiniFunc('?', [], parent, fn, _mln))
                    continue
                cur = func_stack[-1]
                if _dk == '.ENDFUNC':
                    # 本体を閉じるのは `.endfunc` のみ。`.if`/`.while`/`.for` が
                    # 閉じきらないまま来たら壊れたパターンなので報告するが、
                    # 後続行を巻き込まないよう関数はここで閉じてしまう。
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
                if _kw == '.RETURN':
                    if cur_sub is None:
                        diag(" error - '.return' without a matching '.sub'.",
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

                # `.map::<変数>::<名前の並び>::<式>` の書式検査。展開は
                # setpatsymbols() と map_processing() で行う（並びに配列
                # シンボルを書けるようにするため。配列はパターンを読み終えて
                # から登録される）。
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
                 f"is still open (missing '.return').", set_error=True)
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
        """ディレクティブの変数欄として読めるなら正規化した名前、駄目なら None。"""
        v = (field or '').strip().lower()
        if not v or not v.isascii() or not ('a' <= v[0] <= 'z'):
            return None
        for ch in v[1:]:
            if not ('a' <= ch <= 'z' or ch.isdigit() or ch == '_'):
                return None
        return v

    @staticmethod
    def _map_subst_index(expr, var, i):
        """`.map` の式の中の変数を、並びの番号に置き換えた新しい式を作る。

        置き換えるのは語として独立している出現だけで、`0xff` の `x` のように
        英数字に挟まれたものは触らない。番号は `(3)` と括って埋めるので、
        `1<<x` は `1<<(3)` となり、前後の演算子の優先順位は変わらない。
        caxx.c の map_subst_index() と同じ規則である。
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
        """集めた関数の本体を、読み込み時に文の木へ変換する。

        1ソース行ごとに解析し直すのは無駄なので一度だけ。文法の誤りも
        組み立てが始まる前にまとめて報告できる。

        ブロックの入れ子と括弧の深さはそのまま Python の再帰になるので、
        マクロ展開と同じように上限を一時的に上げ、それでも足りなければ
        トレースバックではなく診断として報告する。
        """
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
        """`!S{{名前}}` の参照を読み込み時に検算する。

        照合中に出した診断は「採用されなかった候補のもの」として捨てられるので、
        名前の綴り違いや循環参照はそのままだと全行が素の Syntax error になる。
        パターンファイル側の誤りはここで一度だけ報告する。
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

        # 展開が終わらなくなる循環参照。
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
    """ミニ言語の構文・実行時エラー。読み込み時と組み立て時の両方で使う。"""


class _MiniBreak(Exception):
    """`.break` 文。いちばん内側の `.while` / `.for` を抜ける。"""

    __slots__ = ()


class _MiniContinue(Exception):
    """`.continue` 文。いちばん内側の `.while` / `.for` の次の反復へ進む。"""

    __slots__ = ()


class _MiniReturn(Exception):
    """`.return` 文。関数1段ぶんだけ脱出する。

    `.return 式` なら value にその値（整数か配列）を運ぶ。値のない `.return`
    は value が None で、呼び出し元が `var = .call ...` の形だとエラーになる。
    """

    __slots__ = ('value',)

    def __init__(self, value=None):
        super().__init__()
        self.value = value


# ミニ言語の解析・実行中だけ上げる再帰上限。ブロックの入れ子と括弧の深さが
# そのまま Python の再帰になるので、既定の 1000 では浅い入れ子で尽きてしまう。
# caxx 側は再帰の深さに固定の上限を持たないので、届く範囲を揃えておく。
_MINI_RECLIMIT = 20000

# ミニ言語の整数は axx の式と同じ 256bit 2の補数。Python と C で同じ値に
# なるよう、演算のたびに幅を合わせる。
_MINI_BITS = 256
_MINI_MASK = (1 << _MINI_BITS) - 1


def _mini_wrap(v):
    return int(v) & _MINI_MASK


def _mini_signed(v):
    v = int(v) & _MINI_MASK
    return v - (1 << _MINI_BITS) if v >> (_MINI_BITS - 1) else v


_MINI_OPS2 = ('**', '<<', '>>', '<=', '>=', '==', '!=', '&&', '||')
_MINI_OPS1 = frozenset('+-*/%&|^~<>!()[]:,=')

# 文字列リテラルで使える逃げ記号。値は整数と配列だけなので、文字列が書けるのは
# `.echo` の引数欄だけである。
_MINI_ESC = {'\\': '\\', '"': '"', 'n': '\n', 't': '\t'}


def _mini_lex(text, pos):
    """1行を字句に分解する。返すのは (種別, 値) の並び。"""
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
            # `$$` / `$.` は本体の式評価器が持つ項。ここでは字面を覚えるだけで、
            # 実際の値は評価時に本体へ渡して求める。
            if t[i:i + 2] in ('$$', '$.'):
                toks.append(('core', t[i:i + 2]))
                i += 2
                continue
            raise MiniLangError(f"{pos[0]}:{pos[1]}: '$' must be written "
                                f"'$$' (location counter) or '$.' "
                                f"(start of the next instruction)")
        if c == '#':
            # `#name` も本体の式評価器が持つ項（`.setsym` の記号）。
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
    """字句列から式の木を作る再帰下降パーサ。

    優先順位は低いほうから `|| && ! 比較 | ^ & シフト +- */% 単項 ** 添字`。
    返す木は ('num',値) ('var',名) ('arr',[式]) ('index',式,式)
    ('slice',式,式|None,式|None) ('len',式) ('callexpr',名,[式])
    ('bin',演算子,左,右) ('un',演算子,式)。
    """

    def __init__(self, toks, pos):
        self.toks = toks
        self.i = 0
        self.pos = pos

    def fail(self, msg):
        raise MiniLangError(f"{self.pos[0]}:{self.pos[1]}: {msg}")

    def peek(self):
        return self.toks[self.i] if self.i < len(self.toks) else ('end', None)

    def at_op(self, *ops):
        k, v = self.peek()
        return k == 'op' and v in ops

    def eat_op(self, op):
        if self.at_op(op):
            self.i += 1
            return True
        return False

    def expect_op(self, op):
        if not self.eat_op(op):
            k, v = self.peek()
            self.fail(f"expected {op!r}, found {v if k != 'end' else 'end of line'!r}")

    def at_end(self):
        return self.i >= len(self.toks)

    def parse(self):
        e = self.or_()
        if not self.at_end():
            k, v = self.peek()
            self.fail(f"unexpected {v!r} in expression")
        return e

    def or_(self):
        e = self.and_()
        while self.at_op('||'):
            self.i += 1
            e = ('bin', '||', e, self.and_())
        return e

    def and_(self):
        e = self.not_()
        while self.at_op('&&'):
            self.i += 1
            e = ('bin', '&&', e, self.not_())
        return e

    def not_(self):
        if self.at_op('!'):
            self.i += 1
            return ('un', '!', self.not_())
        return self.cmp_()

    def cmp_(self):
        e = self.bitor_()
        while self.at_op('==', '!=', '<=', '>=', '<', '>'):
            op = self.peek()[1]
            self.i += 1
            e = ('bin', op, e, self.bitor_())
        return e

    def bitor_(self):
        e = self.bitxor_()
        while self.at_op('|'):
            self.i += 1
            e = ('bin', '|', e, self.bitxor_())
        return e

    def bitxor_(self):
        e = self.bitand_()
        while self.at_op('^'):
            self.i += 1
            e = ('bin', '^', e, self.bitand_())
        return e

    def bitand_(self):
        e = self.shift_()
        while self.at_op('&'):
            self.i += 1
            e = ('bin', '&', e, self.shift_())
        return e

    def shift_(self):
        e = self.add_()
        while self.at_op('<<', '>>'):
            op = self.peek()[1]
            self.i += 1
            e = ('bin', op, e, self.add_())
        return e

    def add_(self):
        e = self.mul_()
        while self.at_op('+', '-'):
            op = self.peek()[1]
            self.i += 1
            e = ('bin', op, e, self.mul_())
        return e

    def mul_(self):
        e = self.unary_()
        while self.at_op('*', '/', '%'):
            op = self.peek()[1]
            self.i += 1
            e = ('bin', op, e, self.unary_())
        return e

    def unary_(self):
        if self.at_op('-', '+', '~'):
            op = self.peek()[1]
            self.i += 1
            return ('un', op, self.unary_())
        return self.power_()

    def power_(self):
        e = self.postfix_()
        if self.at_op('**'):
            self.i += 1
            return ('bin', '**', e, self.unary_())
        return e

    def postfix_(self):
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
                # 式の途中の `.call 名前(引数, ...)`。呼んだ関数の返り値になる。
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
        """カンマ区切りの式の並び。空なら空リスト。"""
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
    """`.func` 本体の行の並びを文の木にする。"""

    _ENDERS = frozenset(('.ELIF', '.ELSE', '.ENDIF', '.NEXT', '.ENDWHILE'))

    def __init__(self, func):
        self.func = func
        self.lines = func.lines
        self.loopdepth = 0   # `.break` / `.continue` が書ける深さ

    def parse_body(self):
        body, i = self._block(0, ())
        if i < len(self.lines):
            text, f, ln = self.lines[i]
            raise MiniLangError(f"{f}:{ln}: '{text.strip()}' has no matching opener")
        return body

    def _block(self, i, enders):
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
        """`.if`／`.elif` の 1 段を読む。戻り値は (文, `.endif` の行番号)。

        `.elif` は「`.else` の中に `.if` が 1 つだけある」形に展開する。連鎖の
        途中では `.endif` を読み飛ばさないので、いちばん外側の呼び出し元だけが
        1 行進めればよい。
        """
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
            rest = _mini_lex(self.lines[i][0], pos)[1:]
            if rest:
                raise MiniLangError(f"{f}:{ln}: unexpected text after '.else'")
            else_b, i = self._block(i + 1, ('.ENDIF',))
            if i >= len(self.lines):
                raise MiniLangError(f"{f}:{ln}: '.if' is never closed with '.endif'")
        return ('if', cond, then_b, else_b, pos), i

    def _for_header(self, text, pos):
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
                # `.raise n` … error_patterns 欄の `条件;n` と同じ形でエラーコード n を
                # 報告する。`.error::n::"文言"` で登録した文言もそのまま使われる。
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
                # 項目は文字列リテラルか式。文字列はそのまま、式は値を表示する。
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
        # 代入。左辺は名前か、名前への添字1つ。
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
        # `var = .call f(...)` は呼んだ関数の返り値を代入する。
        if rest and rest[0] == ('dot', '.CALL'):
            fname, args = self._call_tail(rest, pos)
            return ('callassign', name, idx, fname, args, pos)
        val = _MiniExprParser(rest, pos).parse()
        return ('assign', name, idx, val, pos)

    def _call_tail(self, toks, pos):
        """`.call 名前(引数, ...)` を読んで (名前, 引数の式) を返す。"""
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
    """ミニ言語を実行して `.emit` されたワードを集める。

    変数は関数呼び出しごとのフレームに持つ。`.nonlocal` を宣言した名前は、
    外側の呼び出しフレームのうち、その名前を持つ一番内側のものを指す。
    """

    MAX_STEPS = 4_000_000
    MAX_DEPTH = 128
    MAX_EMIT = 1 << 20
    MAX_ARRAY = 1 << 20

    def __init__(self, state, expr_eval=None):
        self.state = state
        self.expr_eval = expr_eval   # 本体の式評価器。`$$`・`#記号`・ラベルの委譲先
        self.out = []
        self.steps = 0
        self.frames = []

    # --- 値の入れ物 --------------------------------------------------------
    @staticmethod
    def _is_arr(v):
        return isinstance(v, list)

    @classmethod
    def _echo_value(cls, v):
        """`.echo` の 1 項目を `_echo_write` に渡せる値にする。

        ミニ言語の整数は 256bit を符号なしで持っているので、表示のために符号つき
        へ直す。配列はそのまま渡せば `_as_str` が `[1, 2, 3]` の体裁にする。
        """
        if cls._is_arr(v):
            return [_mini_signed(e) for e in v]
        return _mini_signed(v)

    def _need_int(self, v, pos, what):
        if self._is_arr(v):
            raise MiniLangError(f"{pos[0]}:{pos[1]}: {what} must be a number, not an array")
        return _mini_wrap(v)

    # --- 変数 --------------------------------------------------------------
    def _frame_for(self, name):
        """`.nonlocal` 宣言があれば外側のフレームを、なければ現フレームを返す。"""
        top = self.frames[-1]
        if name not in top['nonlocal']:
            return top
        for fr in reversed(self.frames[:-1]):
            if name in fr['vars']:
                return fr
        return None

    def _core_eval(self, text, pos):
        """`$$` `$.` `#記号` ラベル名を本体の式評価器に評価してもらう。

        ミニ言語は本体と同じ 256bit の値を扱うので、結果はそのまま使える。
        能力記述子は CAPS_MINI を渡す。パターン変数 `a`〜`z` と `!!!` は、
        `.func` の本体が走っている時点では束縛されていないか意味を持たない
        ので、ここで落とす。未定義ラベル由来の値は 0 にする。`.call` の引数を
        評価するときと同じ扱いで、番兵の巨大な値で反復回数が爆発するのを防ぐ。
        """
        if self.expr_eval is None:
            raise MiniLangError(f"{pos[0]}:{pos[1]}: {text!r} is not available here")
        v, _ = self.expr_eval.expression_caps(text, 0, CAPS_MINI)
        if _is_undef_derived(v):
            return 0
        return _mini_wrap(v)

    def _core_name(self, name):
        """その名前をアセンブラ本体が知っているか（ラベル / `.setsym` 記号）。"""
        st = self.state
        if st is None:
            return False
        if name in st.labels:
            return True
        if StringUtils.upper(name) in st.symbols:
            return True
        return name in st._relax_prev_values

    def _get(self, name, pos):
        fr = self._frame_for(name)
        if fr is None:
            raise MiniLangError(f"{pos[0]}:{pos[1]}: '.nonlocal {name}' found no "
                                f"enclosing definition of {name!r}")
        if name not in fr['vars']:
            # ローカルに無い名前は、アセンブラ本体のラベル / `.setsym` 記号として
            # 読み直す。パス2では本体の表が揃っているので「そんな名前は無い」と
            # 断定でき、綴り間違いは従来どおりミニ言語のエラーになる。パス1では
            # まだ前方参照が埋まっていないので、判断を本体側に預ける。
            if self.expr_eval is not None and self.state is not None \
                    and (self._core_name(name) or self.state.pas != 2):
                return self._core_eval(name, pos)
            raise MiniLangError(f"{pos[0]}:{pos[1]}: {name!r} is used before it is set")
        return fr['vars'][name]

    def _set(self, name, value, pos):
        fr = self._frame_for(name)
        if fr is None:
            raise MiniLangError(f"{pos[0]}:{pos[1]}: '.nonlocal {name}' found no "
                                f"enclosing definition of {name!r}")
        fr['vars'][name] = value

    # --- 式 ----------------------------------------------------------------
    def eval(self, e, pos):
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
            # 範囲外の読み出しは 0。配列は書き込みで伸びるので、読みでは伸ばさない。
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
            # 剰余つきべき乗。C 側の u256_pow（2乗しながら 256bit で回る）と
            # 同じ値になり、指数が大きくても計算量が爆発しない。
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

    # --- 文 ----------------------------------------------------------------
    def _store(self, name, idx, v, pos):
        """`name = v` / `name[idx] = v` を実行する。v は整数か配列。"""
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
        # 足りない分は 0 で埋めて伸ばす。
        if i >= len(arr):
            arr.extend([0] * (i + 1 - len(arr)))
        arr[i] = self._need_int(v, pos, 'an array element')

    def _tick(self, pos):
        self.steps += 1
        if self.steps > self.MAX_STEPS:
            raise MiniLangError(f"{pos[0]}:{pos[1]}: mini language ran more than "
                                f"{self.MAX_STEPS} statements; assuming a runaway loop")

    def exec_block(self, body):
        for st in body:
            self._exec(st)

    def _exec(self, st):
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
            # 命令長を測るだけの試し打ちと、収束途中のパス1では黙る（`.echo` と同じ）。
            # 同じ行が反復回数だけ重複して報告されるのを防ぐため。
            # 報告の体裁は error_patterns 欄（error()）と揃えてある。
            if (self.state is not None
                    and self.state.should_report_errors()
                    and not self.state._pass1_size_mode):
                # caxx.c の u256_to_i64（下位64bitを符号つきで読む）と同じ値にする。
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
            # 命令長を測るだけの試し打ちと、収束途中のパス1では黙る。
            # 同じ行が反復回数だけ重複して出るのを防ぐため。
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

    # --- 関数 --------------------------------------------------------------
    def _lookup(self, name, pos):
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
        """関数を1回走らせ、(`.emit` したワード列, 返り値) を返す。

        返り値は整数か配列。値を返さずに戻った場合は None。
        """
        self.out = []
        self.steps = 0
        self.frames = []
        ret = self.call(func, args, pos)
        return self.out, ret


# 文字列テンプレート（3.5.2）の中で解くエスケープ。ここに無い `\x` は
# x をそのままの字として出す（小文字の逃げ道）。caxx.c の txt_render() と同じ。
_TXT_ESCAPES = {'n': '\n', 't': '\t', 'r': '\r', '\\': '\\', '"': '"'}

_ASMTEXT_SHOW = {'\n': '\\n', '\t': '\\t', '\r': '\\r', '\\': '\\\\', '"': '\\"'}


def asmtext_escaped(s):
    """-v の診断行に埋める文字列。

    行が折れないよう、テキストの中の改行やタブは `\\n` `\\t` と書いたまま
    見せる。素のまま流す方（トランスレータとしての標準出力）は解いた文字の
    ままで、こちらは表示用の写しだけを変える。caxx.c の
    txt_add_escaped() と同じ規則である。
    """
    return ''.join(_ASMTEXT_SHOW.get(c, c) for c in s)


class ObjectGenerator:
    """パターンのエンコーディング欄を評価してワード列を作る。
    
      replace_percent_with_index  `%%` を 0,1,2,... の連番に置き換える
      e_p                         `@@[個数, 式]` を個数分だけ展開する
      makeobj                     カンマ区切りの各式を評価してワード列にする
    
    `;` で始まる要素は条件付き出力で、値が 0 なら何も出さない
    （x86 の REX プレフィックスの有無のような分岐に使う）。
    """

    def __init__(self, state, expr_eval, binary_writer):
        self.state = state
        self.expr_eval = expr_eval
        self.binary_writer = binary_writer

    def replace_percent_with_index(self, s):
        count = 0
        result = []
        i = 0
        while i < len(s):
            # `"..."` の中身は文字列テンプレート（3.5.2）の材料なので、
            # 連番置換の対象にせずそのまま写す。
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
                    # `"..."` の中の `[` `]` `,` は区切りとして数えない。
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

                    # 破綻点修正: 繰り返し回数の未定義判定のために旗を降ろした
                    # まま復元していなかったため、オペランド捕捉の段階で立った
                    # 「未定義ラベルを踏んだ」という情報が、`@@[]` を含むパターン
                    # では必ず消えていた。makeobj() は e_p() の呼び出し「後」に
                    # 旗を退避するので、呼び出し元の状態ごと失われ、未定義ラベル
                    # を含む命令が診断なしで 0 として出力されていた。
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
                        # 表示だけで had_error を立てないと、切り詰めた誤った
                        # バイト列がそのまま出力されてしまうので失敗扱いにする。
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
                # `"..."` の中は `@@[` の展開対象にせず、そのまま写す。
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
        # 命令長を測るだけの試し打ちでも makeobj が走るので、同じエラーが
        # 二重に出る。試し打ちのときは黙って、本番の評価でだけ報告する。
        if not self.state._pass1_size_mode:
            self.state.diag(msg, set_error=True)

    def mini_call(self, s, idx):
        """`binary_list` 欄の `.call 名前(引数, ...)` を実行し、(ワード列, 次の位置)。

        引数はパターン層の式として評価するので、`a` や `b` は捕捉済みの
        パターン変数を指す。未定義ラベル由来の値は 0 として渡す。パス1で
        大きさを測るときに、番兵の巨大な値で反復回数が爆発しないようにするため。
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
            # `[式, 式, ...]` は配列の引数。要素もパターン層の式。
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
        # 返り値もワードになる。配列なら添字 0 から順に、スカラーなら 1 ワード。
        if ret is not None:
            words = words + (list(ret) if isinstance(ret, list) else [ret])
        return words, idx

    def _mini_arg_array(self, t, a, name):
        """`.call` の引数欄の `[式, 式, ...]` を読んで配列の値にする。

        戻り値は (要素のリスト, `]` の次の位置)。読めなければ (None, 末尾)。
        """
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

    # ==================== 文字列テンプレートのエンコーディング欄 ====================
    # パターンの3欄目が `"..."` で始まるとき、その行は式の並びではなく
    # 「アセンブリ結果のテキスト」を作る。別の書式のニーモニックへ書き換える
    # ための欄で、たとえば
    #
    #     MOV R!r,!e:: "LD R{{r}},0x{{.hex(e)}}"
    #
    # に `MOV R1,0x10` を与えると `LD R1,0x10` を出す。
    #
    # 置き換わるのは `{{ }}` で囲んだところだけで、それ以外は書いたままの字
    # が出る。`{{ }}` の中には
    #   - `式`                          … 評価して10進で埋める
    #   - `.hex(式)` `.dec(式)` `.bin(式)` `.float(式)`
    #                                   … 16進/10進/2進/浮動小数の文字列にする
    #                                     （桁だけで、`0x` などの接頭辞は付か
    #                                      ないので、要るなら外に書く）
    #   - `名前` `名前[添字]`           … 文字列シンボル／配列シンボル、
    #                                     どちらでもなければパターン変数の値
    #   - `.index 名前[添字]`           … その参照が使う添字そのもの
    #                                     （名前から番号を引くのに使う）
    #                                     （添字は名前・`"名前"`・式のいずれでもよい）
    #   - `.exp(変数)`                  … `!L変数` が拾った式・ラベルを、ソースに
    #                                     書かれていたままの文字で出す
    # が書ける。文字列の外と同じく `\n` `\t` `\r` `\\` `\"` は解く。
    #
    # 組み上がったテキストはそのままバイナリとしても出る。`.ascii` と同じく
    # UTF-8 の 1 バイトが 1 ワードになり、ロケーションカウンタもその分進んで
    # バイナリ／ELF 出力に載る。標準出力へのテキスト出力（トランスレータと
    # しての使い方）はそのまま残るので、同じパターンで両方が得られる。
    _TXT_CONVS = (('float', 3), ('hex', 0), ('dec', 1), ('bin', 2))

    @staticmethod
    def _arr_split(q):
        """`[...]` の中身を項目の文字列に切る。

        区切りは最上位のカンマだけで、`"..."` の中や入れ子の括弧の中のカンマは
        区切りにしない（`[1,(2,3)]` のような書き方で崩れないようにするため）。
        caxx.c の arrsym_set_from_text() と同じ規則である。
        """
        items = []
        i = 1                      # `[` の次から
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
        """`"..."` の中身を取り出す。`\` は残して展開側に任せる。"""
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
        """radix 進の桁だけの文字列。接頭辞は付けず、負なら `-` を付ける。"""
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

    # `.float(式)` は値を10進128ビット浮動小数点数（有効数字34桁）として書く。
    _TXT_FLOAT_PREC = 34

    @classmethod
    def _txt_float_parts(cls, neg, digits, exp10):
        """digits を d1.d2d3… ×10^exp10 と読んで文字列にする。

        指数が小さいうちは普通の小数表記にし、小数部が無ければ `.0` を付ける
        （16 なら `16.0`）。caxx.c の txt_float_emit() と同じ規則である。
        """
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
        """整数・実数のどちらで束縛された値でも、34桁に丸めて書く。"""
        prec = cls._TXT_FLOAT_PREC
        if isinstance(v, float):
            if v != v or v in (float('inf'), float('-inf')):
                return 'nan' if v != v else ('inf' if v > 0 else '-inf')
            d = Context(prec=prec).create_decimal(Decimal(v))
        else:
            d = Context(prec=prec).create_decimal(Decimal(int(v)))
        sign, digits, dexp = d.as_tuple()
        digits = ''.join(str(x) for x in digits) or '0'
        # as_tuple() の指数は最下位桁の重み。d1.d2… ×10^exp10 の形へ直す。
        return cls._txt_float_parts(sign == 1, digits, len(digits) - 1 + dexp)

    @staticmethod
    def _txt_close_paren(s, i):
        """丸括弧の対応を取り、閉じ括弧の位置を返す。無ければ -1。"""
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
        """`.hex` などなら (名前の長さ, 種別) を返す。違えば (0, -1)。"""
        u = StringUtils.upper(s)
        for name, kind in cls._TXT_CONVS:
            if u.startswith(StringUtils.upper(name)) and s[len(name):len(name) + 1] == '(':
                return len(name), kind
        return 0, -1

    def _txt_emit_expr(self, parts, expr, kind):
        """式を評価し、kind に従って parts に積む。"""
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
        """テンプレート本文を展開して文字列にする。"""
        parts = []
        i = 0
        while i < len(s):
            c = s[i]
            if c == '\\' and i + 1 < len(s):
                # `.ascii` と同じ逃げ方をする制御文字だけを解き、それ以外の
                # `\x` は x をそのままの字として出す（小文字の逃げ道）。
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
                    # `.exp(変数)` は `!L変数` が拾った式・ラベルの文字そのもの。
                    en = self._txt_exp_call(inner[j + 1:])
                    if en is not None:
                        parts.append(self._txt_exp_text(en))
                        done = True
                if not done and inner[j:j + 1] == '.':
                    # `.index 配列[式]` は、その参照が使う添字そのものを返す。
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
                    # `{{x[3]}}` のように名前と添字なら、配列シンボルを引く。
                    nm, ix = self._txt_bare_indexed(inner)
                    if nm is not None:
                        parts.append(self._txt_indexed_text(nm, ix))
                        done = True
                if not done:
                    # `{{x}}` のように名前ひとつなら、文字列／配列シンボルを先に見る。
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
        """`{{...}}` の中身が `名前[式]` だけなら (名前, 添字の式) を返す。"""
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
        """`{{...}}` の中身が名前ひとつだけなら、大文字化した名前を返す。"""
        t = inner.strip()
        if not t.isascii() or not (t[:1].isalpha() or t[:1] == '_'):
            return None
        for ch in t[1:]:
            if not (ch.isalnum() or ch == '_'):
                return None
        return StringUtils.upper(t)

    def _txt_name_text(self, name):
        """テンプレートの中の名前を解決する。

        優先順位は
          1. `.setsym::名前::"文字列"` の文字列シンボル … その文字列
          2. 変数として使われている名前                 … パターン変数の値（10進）
          3. どれでもない                               … 書かれたままの文字
        で、`Rr` の `r` は 2 に、`{{x}}` の `x` は 1 に当たる。
        数値シンボルをここで引かないのは、`num=` のような普通の文（たまたま
        `.setsym::NUM` がある）が黙って数字に化けるのを避けるため。数値が要る
        ときは `{{#NUM}}` と書けば本体の式評価器が引く。
        caxx.c の txt_emit_name() と同じ規則である。
        """
        key = StringUtils.upper(name)
        if key in self.state.strsymbols:
            return self.state.strsymbols[key]
        # 添字なしの配列は、全項目を `,` でつないで出す。
        if key in self.state.arrsymbols:
            return ','.join(v if isinstance(v, str) else self._txt_radix(v, 10)
                            for v in self.state.arrsymbols[key])
        # パターン変数（`a` でも `var_2` でも同じ規則）。パターンファイルが
        # その名前を変数として使っていれば値を、そうでなければ書かれたままの
        # 文字を出す。ふつうの単語が黙って数字に化けないようにするためで、
        # 変数と決まっている名前が未束縛なら 0 になる。
        _v = name.lower()
        if _v == name and _v in self.state.varnames:
            return self._txt_radix(self.state.vars.get(_v, VAR_UNDEF), 10)
        return name

    @staticmethod
    def _txt_close_bracket(s, i):
        """名前の直後の `[...]` の閉じ位置を返す。無ければ -1。"""
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
        """`x[3]` のような添字つきの参照。添字は 0 から数える。

        配列でない名前や範囲外の添字は診断して空文字を返す。添字の解き方は
        `_arr_index_of()` にまとめてあり、`.index` と同じである。
        """
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
        """`.index 配列[式]` なら (配列名, 添字の式) を返す。違えば (None, None)。

        `.index(配列[式])` と括弧で括って書いてもよい。
        caxx.c の txt_index_call() と同じ規則である。
        """
        if StringUtils.upper(s[:5]) != 'INDEX':
            return None, None
        rest = s[5:]
        if rest[:1] not in (' ', '\t', '('):
            return None, None          # `.indexof` のような別の名前
        rest = rest.strip()
        if rest.startswith('('):
            cp = cls._txt_close_paren(rest, 0)
            if cp < 0 or rest[cp + 1:].strip() != '':
                return None, None
            rest = rest[1:cp]
        return cls._txt_bare_indexed(rest)

    def _txt_index_text(self, name, idxtext):
        """`.index 配列[式]` の値。0 から数えた添字を10進で返す。

        `{{arr[e]}}` が引く項目の、その添字そのものである。配列でない名前や
        解けない添字は診断して空文字を返す。
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
        """`.exp(変数)` なら変数名を返す。違えば None。

        中に書けるのは変数名ひとつだけで、式は書けない。`!L変数` が拾った
        「ソースに書かれていたままの式・ラベルの文字」を指す名前である。
        caxx.c の txt_exp_call() と同じ規則である。
        """
        if StringUtils.upper(s[:3]) != 'EXP':
            return None
        rest = s[3:]
        if rest[:1] not in (' ', '\t', '('):
            return None                # `.expand` のような別の名前
        rest = rest.strip()
        if rest[:1] != '(':
            return None
        cb = cls._txt_close_paren(rest, 0)
        if cb < 0 or rest[cb + 1:].strip() != '':
            return None
        nm = rest[1:cb].strip()
        if not nm or PatternMatcher._var_name_at(nm, 0) != len(nm):
            return None                # 変数名でなければ `.exp` ではない
        return nm

    def _txt_exp_text(self, name):
        """`.exp(変数)` の中身。`!L変数` が拾った文字をそのまま返す。

        その行で拾っていなければ（省略可部分に入っていた等）空文字を返す。
        そもそも変数として使われていない名前なら書き損じなので診断する。
        """
        if name not in self.state.varnames:
            self.state.diag(f" error - '{name}' is not a pattern variable; "
                            f"'.exp({name})' needs '!L{name}' in the "
                            f"instruction field.", set_error=True)
            return ''
        return self.state.vars_text.get(name, '')

    @staticmethod
    def _txt_quoted_text(t):
        """欄が `"..."` ひとつだけなら、逃げ方を解いた中身を返す。でなければ None。

        `.index arrb["CX"]` の `"CX"` のように、名前をそのまま書くための形である。
        テンプレートの中では `"` が文字列の終わりなので `\"CX\"` と逃がして書く
        ことになる。その形も同じに受ける。
        caxx.c の txt_quoted_text() と同じ規則である。
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
        return None                    # 閉じ `"` が無い

    def _arr_index_of(self, key, idxtext):
        """添字の欄を配列 key の添字（0 起点）に解く。解けなければ None。

        まず `"..."` と書かれた欄はその中身に開く（`arrb["CX"]` は `arrb[CX]` と
        同じに読む）。そのうえで
          1. 文字列シンボルの名前ひとつ … その文字列を添字の欄として読み直す
          2. パターン変数の名前ひとつ   … 4 へ（変数の値で引く）
          3. 配列の項目名そのもの       … その項目の位置
             それが無ければ同じ名前の `.setsym`／`.map` の数値シンボル … その値
          4. どれでもない               … ふつうの式として評価した値
        の順に解く。`.setsym::var1::BX` のときの `arrb[var1]` は 1 を通り、`BX`
        が `.map::r::AX,BX,CX` で 1 になっているので添字 1 になる。`arrb["CX"]`
        なら同じく 3 の後半で 2 になる。名前の並びをそのまま持つ配列
        （`[AX,BX,CX]`）なら 3 の前半で位置が決まる。
        caxx.c の txt_arr_index_of() と同じ規則である。
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
        # 変数の綴り（小文字で書かれ、パターンファイルが変数として使っている
        # 名前）は、名前ではなく値として読む。
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
        """添字が配列の範囲に入っていれば int で返す。外なら診断して None。"""
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
        # 行に現れた `"..."` の展開結果をつないでおく。_txtacc は素のまま流す
        # 用（トランスレータとしての使い方）、_dispacc は -v の診断行に見せる
        # 用で、`"A","B"` のように欄に書いたとおり分けて括る。
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
                    # `;;要素` は評価だけして何も出さない。
                    if idx < len(s) and s[idx] == ';':
                        drop = True
                        idx += 1

                # `"..."` はテキストとして展開し、そのバイト列をワードとして出す。
                _qs = idx
                while _qs < len(s) and s[_qs] in ' \t':
                    _qs += 1
                if _qs < len(s) and s[_qs] == '"':
                    # s の末尾には番兵の chr(0) が付いている。閉じ `"` を欠く
                    # 文字列でそれを拾わないよう、最初の chr(0) で切る。
                    _src = s[_qs:]
                    _nul = _src.find(chr(0))
                    if _nul >= 0:
                        _src = _src[:_nul]
                    _txt = self._txt_render(self._txt_template_inner(_src))
                    # `;;` は何も出さず、`;` は中身が空なら出さない。
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
                    # 閉じ `"` の次まで読み飛ばす。
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
                    # 引数はふつうのパターン式なので、ここでも何ワード目かを
                    # 立てておく。そうしないと `.call` に渡したラベル参照が
                    # 追跡されず、`.reloc` を宣言してもリロケーションが出ない。
                    self.state._elf_current_word_idx = len(objl)
                    words, idx = self.mini_call(s, idx)
                    # `;` 付きは、出したワードが 1 個で 0 のときだけ何も出さない。
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
    """欄が識別子ひとつなら、その名前を書かれたまま返す。でなければ None。

    先頭は英字か `_`、続きは英数字か `_` で、前後の空白は無視する。
    caxx.c の bare_name_of() と同じ規則である。
    """
    t = (text or '').strip()
    if not t.isascii() or not (t[:1].isalpha() or t[:1] == '_'):
        return None
    for ch in t[1:]:
        if not (ch.isalnum() or ch == '_'):
            return None
    return t


def arr_items_from_text(expr_eval, q):
    """`.setsym` の `[...]` を項目の並びにする。

    項目は
      - `"文字列"`           … そのまま文字列 (str)
      - 素の名前（`R0` など） … 書かれたままの文字列 (str)
      - それ以外              … 式として評価した数値
    になる。`[R0,R1,R2]` と `["R0","R1","R2"]` が同じ意味になるのは2番目の枝で、
    名前は綴りをそのまま持つ（`[r0,r1]` なら小文字のまま出る）。その名前に
    `.setsym`／`.map` で与えた数値が要るときは `[#R0,#R1]` と書く。
    caxx.c の arrsym_set_from_text() と同じ規則である。
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
    """文字列を最上位のカンマで切る。

    括弧の中のカンマは区切りにしない（`*(x,1)` のような式がそのまま1項目に
    なるようにするため）。深さの数え方は expression_esc() と同じで、閉じ括弧の
    種類は厳密に照合しない。caxx.c の split_top_commas() と同じ規則である。
    """
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
    """集合の要素として書ける名前なら大文字化して返す。でなければ None。

    数字で始まるものと空白を含むものは名前とみなさない。`.setsym::X::1,2` の
    ような数式が集合に化けないようにするためである。
    """
    t = t.strip()
    if not t or not t.isascii() or t[0] in DIGIT:
        return None
    for ch in t:
        if ch in ' \t':
            return None
    return StringUtils.upper(t)


def set_items_dedupe(items):
    """並び順は保ったまま重複を落とす。集合なので同じ要素は1つだけ持つ。"""
    out = []
    for it in items:
        if it not in out:
            out.append(it)
    return out


def set_literal_from_text(state, text):
    """`名前,名前,…` を集合の項目にする。集合として読めなければ None。

    項目に既存の集合の名前を書くと、その中身をその場に展開する。
    caxx.c の set_literal_from_text() と同じ規則である。
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
    """集合式の被演算子。素の識別子で、既にある集合ならその項目を返す。"""
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
    """集合どうしの演算を評価する。集合式として読めなければ None。

        a&b   積集合（and 集合）
        a|b   和集合（or 集合）
        a^b   対称差（xor 集合）
        a+b   和集合
        a-b   差集合

    被演算子はすべて既にある集合であること。演算子は左から順に適用し、
    優先順位は無い。caxx.c の set_expr_from_text() と同じ規則である。
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
        return None                     # 演算子が1つも無い
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
    """値欄が集合の書き方なら、その集合を作って True を返す。

        .setsym::a::a1,a2,a3      名前の集合
        .setsym::x::a&b           既にある集合どうしの演算

    結果は写しなので、あとで元の集合を書き換えても影響しない。
    caxx.c の symbol_set_from_text() と同じ規則である。
    """
    items = set_expr_from_text(state, value_field)
    if items is None:
        items = set_literal_from_text(state, value_field)
    if items is None:
        return False
    state.arrsymbols[dst_upper] = items
    return True


def symbol_copy_from_name(state, dst_upper, value_field):
    """値欄が「名前ひとつ」のときの `.setsym`。拾ったら True を返す。

    その名前が文字列／配列シンボルなら写しを作り（`.setsym::y::x`）、どちらでも
    なければ「その名前そのもの」を指す文字列シンボルにする。つまり

        .setsym::var1::BX

    は `var1` が BX という名前を指す、という意味になり、`{{var1}}` は `BX` と
    出る。名前に与えた数値が要るときは `#BX`、ラベルの値が要るときは `BX+0` の
    ように式にして書く（素の名前はここで文字列として拾われる）。
    caxx.c の symbol_copy_from_name() と同じ規則である。
    """
    t = bare_name_of(value_field)
    if t is None:
        return False
    src = StringUtils.upper(t)
    if src in state.arrsymbols:
        if src != dst_upper:
            # 項目は数値か文字列なので、浅い複製で独立した配列になる。
            state.arrsymbols[dst_upper] = list(state.arrsymbols[src])
        return True
    if src in state.strsymbols:
        if src != dst_upper:
            state.strsymbols[dst_upper] = state.strsymbols[src]
        return True
    # どの表にも無い素の名前は、その名前そのものを指す文字列シンボルにする。
    state.strsymbols[dst_upper] = t
    return True


class VLIWProcessor:
    """`!!` 区切りで並んだ複数命令を1つの VLIW パケットに詰める。
    
    各スロットを vliwinstbits 幅のフィールドに詰め、余ったスロットは NOP で埋め、
    EPIC ならスロットの組み合わせに対応するテンプレート値を合成して、
    パケット幅ぶんのバイト列として出力する。
    テンプレート幅が負のときはテンプレートをパケットの上位側に置く。
    """

    def __init__(self, state, expr_eval, binary_writer):
        self.state = state
        self.expr_eval = expr_eval
        self.binary_writer = binary_writer

    def vliwprocess(self, line, idxs, objl, flag, idx, lineassemble2_func):
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
                # 破綻点修正: VLIW/EPIC テンプレート式が未定義値を踏んでも
                # error_undefined_label は factor1 側で立つだけで、lineassemble2
                # の通常経路と違ってここでは誰も had_error に変換していなかった。
                # メッセージは出るのに exit 0 になり、不完全な出力が書かれていた。
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
    
    `.section`/`.endsection`、`.EQU`、`.RESB`/`.ZERO`（領域確保）、
    `.ASCII`/`.ASCIZ`（文字列）、`.ORG`（配置アドレス）、`.ALIGN`、
    `.global`/`.extern`（外部シンボル）など。
    
    領域確保や配置系は引数に未定義ラベルが混ざっていると意味を成さないため、
    評価の直前に state.error_undefined_label を自分で降ろしてから評価し、
    立っていたらエラーにする（LabelManager の「立てるだけ」規約との対）。
    """

    def __init__(self, state, expr_eval, binary_writer, label_manager, parser):
        self.state = state
        self.expr_eval = expr_eval
        self.binary_writer = binary_writer
        self.label_manager = label_manager
        self.parser = parser

    def labelc_processing(self, l, ll):
        if l.upper() != '.LABELC':
            return False
        if ll:
            self.state.lwordchars = ALPHABET + DIGIT + ll
        return True

    def label_processing(self, l):
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

                    _mach_tbl = ELF_MACHINES.get(self.state.elf_machine)
                    reloc_type = _mach_tbl['named'].get(rt_str) if _mach_tbl else None
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
                # テキスト置換モードでは `label: .equ 式` の行もテキストとして
                # 出す。ラベルの綴りは lineassemble() が前に付け直し、残りの
                # `.equ 式` はどのパターンにも当たらないので素通しで出る。
                if self.state.textmode:
                    self.state.label_text = l[:lidx]
                    return l[lidx:]
                return ""
            else:
                ok = self.label_manager.put_value(label, self.state.pc, self.state.current_section, is_equ=False)
                if ok is False:
                    return ""
                # テキスト置換モードでは、落とした `label:` を出力の先頭に
                # 付け直すため、書かれていたとおりの綴りを覚えておく。
                self.state.label_text = l[:lidx]
                return l[lidx:]
        return l

    def asciistr(self, l2):
        idx = 0
        if l2 == '' or l2[idx] != '"':
            return False
        idx += 1

        _word_mask = (1 << self.state.bts) - 1 if self.state.bts > 0 else 0xFF
        _truncated = False

        while idx < len(l2) and not l2[idx] == '"':
            ch = None
            _is_literal = False   # ソース中の生の文字か、エスケープ由来か
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
                # 破綻点修正: 以前は文字を常に ord(ch)（コードポイント）1個として
                # 出力していたため、ソースに直接書かれた非ASCII文字が語長で
                # 切り捨てられ無意味な値になっていた（"こ"=U+3053 → 0x53）。
                # アセンブラとしては元のバイト列をそのまま置くのが正しく、
                # caxx.c もそう動く（C はバイト列で処理するため自然にそうなる）。
                # ソース中の生の文字だけを UTF-8 バイト列に展開する。
                # \xHH などのエスケープは「バイト値の指定」なので1バイトのまま扱う
                # （ここを UTF-8 符号化すると \xFF が 2 バイトになってしまう）。
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
        _l1u = StringUtils.upper(l1)
        if _l1u != ".EXPORT" and _l1u != ".GLOBAL":
            return False
        # 破綻点修正: パス1では False（＝未処理）を返していたため、`.global foo`
        # の行がパス1だけパターン照合へ流れ、たまたま一致するパターンがあると
        # パス1でだけバイトが出てパス1/パス2のアドレスがずれた。
        # ディレクティブとしては必ず消費し、記録だけをパス2/対話時に限る。
        if not (self.state.should_report_errors()):
            return True

        idx = 0
        l2 += chr(0)
        while idx < len(l2) and l2[idx] != chr(0):
            idx = StringUtils.skipspc(l2, idx)
            s, idx = self.parser.get_label_word(l2, idx)
            if s == "":
                break
            if idx < len(l2) and l2[idx] == ':':
                idx += 1
            v = self.label_manager.get_value(s)
            sec = self.label_manager.get_section(s)
            _lentry = self.state.labels.get(s, [])
            is_equ = len(_lentry) > 2 and _lentry[2]
            self.state.export_labels[s] = [v, sec, is_equ]
            if idx < len(l2) and l2[idx] == ',':
                idx += 1
        return True

    _RES_UNITS = {'.RESB': 1, '.RESW': 2, '.RESD': 4, '.RESQ': 8}

    def resb_processing(self, l1, l2):
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
        if StringUtils.upper(l1) != ".ASCII":
            return False
        return self.asciistr(l2)

    def asciiz_processing(self, l1, l2):
        if StringUtils.upper(l1) != ".ASCIZ":
            return False
        if not self.asciistr(l2):
            self.state.diag(" error - .ASCIZ requires a quoted string.", set_error=True)
            return False
        self.binary_writer.outbin(self.state.pc, 0x00)
        self.state.pc += 1
        return True

    def section_processing(self, l1, l2):
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
            _mach_tbl_ext = ELF_MACHINES.get(_em_ext)
            reloc_type = _mach_tbl_ext['extern_default'] if _mach_tbl_ext else 2
            # このEXTERN文自身が `::型名` を明示したかどうか。reloc_type は
            # 明示指定が無ければデフォルト型で埋まってしまうため、reloc_type
            # 自体では「明示されたか」を区別できない。既存ラベルの
            # reloc_type_override は明示指定があったときだけ上書きしたいので、
            # 別のフラグで覚えておく。
            explicit_reloc_type = False
            if idx < len(l2) and l2[idx:idx + 2] == '::':
                idx += 2
                rt_start = idx
                while idx < len(l2) and l2[idx] not in ' \t,:' + chr(0):
                    idx += 1
                rt_str = l2[rt_start:idx].strip().lower()

                if rt_str:
                    reloc_type = _mach_tbl_ext['named'].get(rt_str) if _mach_tbl_ext else None
                    if reloc_type is None:
                        self.state.diag(f" warning - unknown reloc type '{rt_str}' in .EXTERN"
                             f" for machine {_em_ext}", set_error=False)
                    else:
                        explicit_reloc_type = True

            if idx < len(l2) and l2[idx] == ':':
                idx += 1

            existing = self.state.labels.get(label_part)

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

    def reloctype_processing(self, l1, l2):
        if StringUtils.upper(l1) != ".RELOCTYPE":
            return False

        _mach_tbl_rt = ELF_MACHINES.get(self.state.elf_machine)
        if _mach_tbl_rt is None:
            self.state.diag(f" warning - .RELOCTYPE: no relocation table for machine "
                 f"{self.state.elf_machine}", set_error=False)
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
            _rtype = _mach_tbl_rt['named'].get(_name)
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

    def __init__(self, msg):
        super().__init__(msg)
        self.msg = msg


class _MacroBreak(Exception):
    pass


class _MacroContinue(Exception):
    pass


class _MacroReturn(Exception):
    def __init__(self, value):
        super().__init__(value)
        self.value = value


class _MacroFunc:

    __slots__ = ('name', 'params', 'defaults', 'body', 'pos')

    def __init__(self, name, params, defaults, body, pos):
        self.name = name
        self.params = params
        self.defaults = defaults
        self.body = body
        self.pos = pos


def _sext_tick_at(s, i):
    """`s[i]` の `'` が符号拡張の演算子か（右に幅が続くか）を見分ける。

    文字定数 `'A'` と区別するため、本体の評価器と同じく「続く文字が数字か `(`」
    を条件にする。`!{...}` の走査とマクロ式パーサの両方から使う。
    """
    j = i + 1
    while j < len(s) and s[j] in ' \t':
        j += 1
    return j < len(s) and (s[j].isdigit() or s[j] == '(')


def _fmt_pos(pos):
    return f"{pos[0]}:{pos[1]}"


def _strip_comment(text, pat_mode=False):
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
            # 破綻点修正: `'` を無条件に引用符の開きとして扱っていた。しかし
            # パターンファイルでは `'` は「任意ビット位置からの符号拡張」演算子
            # （`!x'8` 等）でもあり、行に1個しか無い場合そこから行末までが
            # 「引用符の中」とみなされ、以降の `/*` コメントが除去されなくなって
            # マクロ層の行判定が狂っていた。対になる `'` が同じ行にあるときだけ
            # 文字リテラルとみなす。
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

    def __init__(self, text, pp, pos):
        self.s = text
        self.i = 0
        self.pp = pp
        self.pos = pos
        self.suppress = 0


    def err(self, msg):
        raise MacroError(f"{_fmt_pos(self.pos)}: macro expression: {msg} in {self.s!r}")

    def skip(self):
        while self.i < len(self.s) and self.s[self.i] in ' \t':
            self.i += 1

    def peek(self, n=1):
        self.skip()
        return self.s[self.i:self.i + n]

    def eat(self, tok):
        self.skip()
        if self.s.startswith(tok, self.i):
            if tok[-1].isalpha():
                j = self.i + len(tok)
                if j < len(self.s) and (self.s[j].isalnum() or self.s[j] == '_'):
                    return False
            self.i += len(tok)
            return True
        return False

    def expect(self, tok):
        if not self.eat(tok):
            self.err(f"expected {tok!r}")

    def at_end(self):
        self.skip()
        return self.i >= len(self.s)


    def parse(self):
        v = self.ternary()
        if not self.at_end():
            self.err(f"unexpected trailing text {self.s[self.i:]!r}")
        return v

    def ternary(self):
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
        """本体の `'`（任意ビット位置からの符号拡張）をマクロ式でも使えるようにする。

        実装は本体と同じ共有関数 op_sext()。位置はビット演算子より緩く `&&` より
        きつい段に置く。本体では `^` と比較のあいだだが、マクロ層の優先順位は C
        に合わせてあり比較のほうがビット演算子よりきついので、同じ相対位置は
        取れない。`'` の右は幅を書くところなので、`'` に続く文字が数字か `(`
        のときだけ演算子として読む（`'A'` の文字定数と衝突させないため）。
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
        v = self.bit_and()
        while self.eat('^'):
            v = _as_int(self, v) ^ _as_int(self, self.bit_and())
        return v

    def bit_and(self):
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
        v = self.relational()
        while True:
            if self.eat('=='):
                v = 1 if _cmp_eq(v, self.relational()) else 0
            elif self.eat('!='):
                v = 0 if _cmp_eq(v, self.relational()) else 1
            else:
                return v

    def relational(self):
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
        self.skip()
        if self.eat('!'):
            return 0 if _truth(self.unary()) else 1
        if self.eat('~'):
            return ~_as_int(self, self.unary())
        if self.eat('-'):
            return -_as_int(self, self.unary())
        if self.eat('+'):
            return self.unary()
        # 本体の `@`（最上位ビット位置）。実装は共有関数 op_msb()。
        if self.eat('@'):
            return op_msb(_as_int(self, self.unary()))
        # 本体の `*(値, 位置)`（バイト抽出）。値が来る位置の `*` だけが
        # これで、中置の `*` は従来どおり掛け算（本体の評価器と同じ見分け方）。
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
            # 位置カウンタ。`$` と `$$` は同義（アセンブラ本体では `$$` が
            # 位置カウンタなので、そちらの綴りも受ける）。空白を挟んだ
            # `$ $` を `$$` と読まないよう、次の文字は素で見る。
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
    if isinstance(v, str):
        return v != ''
    return v != 0


def _as_int(p, v):
    if isinstance(v, str):
        if getattr(p, 'suppress', 0):
            return 0
        p.err(f"expected an integer, got the string {v!r}")
    return v


def _as_str(v):
    return v if isinstance(v, str) else str(v)


def _echo_write(items):
    """マクロ層の `!echo` とミニ言語の `.echo` に共通の出力ルーチン。

    項目を `_as_str` で文字列にし、空白区切りで 1 行にまとめて標準エラーへ出す。
    体裁を 1 か所に集めておくため、どちらの層もここを通す。
    """
    print(' '.join(_as_str(x) for x in items), file=sys.stderr)


def _cmp_eq(a, b):
    if isinstance(a, str) != isinstance(b, str):
        return False
    return a == b


def _cmp_lt_eq(p, a, b, or_equal):
    if isinstance(a, str) != isinstance(b, str):
        if getattr(p, 'suppress', 0):
            return False
        p.err("cannot order a string against an integer")
    return (a <= b) if or_equal else (a < b)


def _c_div(a, b):
    q = abs(a) // abs(b)
    return q if (a >= 0) == (b >= 0) else -q


def _c_mod(a, b):
    return a - _c_div(a, b) * b



class MacroPreprocessor:

    def __init__(self, state=None, pat_mode=False):
        self.state = state
        self.pat_mode = pat_mode
        self.reset()


    def reset(self):
        self.enabled = True
        self.had_error = False
        self._reported = set()
        self.reset_pass()

    def reset_pass(self):
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
        return self.scopes[-1]

    def asm_label(self, name):
        """アセンブラ側のラベル / .equ を引く。

        マクロ展開はアドレス確定より前に走るので「今の値」は存在しない。
        前回リラクゼーション反復のスナップショット（AssemblerState 側が反復
        ごとに更新する）を見て、次の3状態を返す。

          ('val', 値) … 前回反復で値が確定していた
          ('unk', 0)  … ラベルとしては存在するが値がまだ確定していない
                        （初回反復では全ての名前がこれになる）
          ('no',  0)  … そんなラベルは無い（＝綴り間違い）

        パターンファイル側のマクロ層はソースのアセンブル前に走るため、
        ここは常に 'no' を返してラベル参照そのものを認めない。
        """
        if self.pat_mode or self.state is None:
            return ('no', 0)
        values = self.state._macro_label_values
        if values is None:
            # まだ一度も反復していない。この時点では「前方参照でまだ値が
            # 無い」のか「綴り間違い」なのか区別できないので、エラーにせず
            # 未確定として扱う。綴り間違いは次の反復で 'no' として捕まる。
            return ('unk', 0)
        if name in values:
            return ('val', values[name])
        if name in (self.state._macro_label_names or ()):
            return ('unk', 0)
        return ('no', 0)

    def loc_counter(self, pos):
        """マクロ展開時の位置カウンタ（$ / $$）。

        ラベルと違って名前ではなく位置で決まる値なので、前回反復で記録した
        「展開後 N 行目のアドレス」を返す。初回反復や、展開行数が変わって
        対応する行がまだ無い場合は 0。
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
        if name in self.funcs:
            return True
        if any(name in sc for sc in self.scopes):
            return True
        return self.asm_label(name)[0] == 'val'

    def assign(self, name, value):
        for sc in reversed(self.scopes):
            if name in sc:
                sc[name] = value
                return
        self.scope()[name] = value


    def eval(self, text, pos):
        text = text.strip()
        if text == '':
            raise MacroError(f"{_fmt_pos(pos)}: empty macro expression")
        return _ExprParser(text, self, pos).parse()

    def call_value(self, name, args, pos):
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
                    # 符号拡張の `'`（右が数字か `(`）は文字定数の開始では
                    # ないので、引用符として数えない。式パーサ側の見分け方と
                    # 同じにしておかないと `!{v'8}` が閉じられなくなる。
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
        spec = None
        quote = ''
        par = 0
        k = 0
        # 破綻点修正: 引用符の中の `\` を見たとき次の1文字を飛ばさずに continue
        # していたため（interpolate() は j += 2 で正しく飛ばしている）、
        # `!{ "a\"b" : spec }` のようにエスケープされた引用符を含むと
        # そこで引用符が閉じたと誤認し、書式指定の `:` の位置を取り違えていた。
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
        r = rest.strip()
        return r.startswith('(')

    def parse_simple(self, lw, word, rest, pos):
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
        if len(self.out) >= _MACRO_MAX_LINES:
            raise MacroError(f"{_fmt_pos(pos)}: macro expansion produced more than "
                             f"{_MACRO_MAX_LINES} lines; assuming a runaway macro")
        self.out.append((text, pos[0], pos[1]))

    def exec_block(self, nodes):
        for node in nodes:
            self.exec_node(node)

    def exec_node(self, node):
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
        if msg in self._reported:
            return
        self._reported.add(msg)
        diag(f" warning - {msg}", set_error=False, force=True)

    def fail(self, msg):
        # 破綻点修正: None 検査より前に self.state.diag() を呼んでいた。
        # PatternFileReader は既定でマクロ層を state=None で作る（3行下の
        # コンストラクタ）ので、その経路でマクロエラーが起きると
        # AttributeError で落ちていた。warn() と同じくモジュール関数の diag()
        # に委ねる（状態が無ければそのまま stderr へ出る）。
        if msg not in self._reported:
            self._reported.add(msg)
            diag(f" error - {msg}", set_error=False, force=True)
        self.had_error = True
        if self.state is not None:
            self.state.had_error = True


    def contains_macros(self, raw):
        for t in raw:
            if '!' in t or t.lstrip().startswith('}'):
                return True
        return False

    @staticmethod
    def has_interpolation(t):
        i = t.find('!{')
        while i >= 0:
            if i == 0 or t[i - 1] != '\\':
                return True
            i = t.find('!{', i + 2)
        return False

    def has_macro_constructs(self, raw):
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
        # $/$$ は「展開後の何行目か」で引くので、どのファイルの展開中かを
        # 覚えておく（AssemblerState 側の記録も同じキーで積まれている）。
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
    hi = lo if hi is None else hi
    if not (lo <= len(args) <= hi):
        raise MacroError(f"{_fmt_pos(pos)}: {name}() takes {lo}..{hi} argument(s), "
                         f"got {len(args)}")


def _bi_len(pp, a, pos):
    _bi_check(pp, a, pos, 'len', 1)
    return len(a[0]) if isinstance(a[0], str) else len(str(a[0]))


def _bi_hex(pp, a, pos):
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
    _bi_check(pp, a, pos, 'str', 1)
    return _as_str(a[0])


def _bi_int(pp, a, pos):
    _bi_check(pp, a, pos, 'int', 1, 2)
    if isinstance(a[0], int):
        return a[0]
    base = a[1] if len(a) > 1 else 0
    try:
        return int(a[0].strip(), base)
    except ValueError:
        raise MacroError(f"{_fmt_pos(pos)}: int({a[0]!r}) is not a number")


def _bi_upper(pp, a, pos):
    _bi_check(pp, a, pos, 'upper', 1)
    return _as_str(a[0]).upper()


def _bi_lower(pp, a, pos):
    _bi_check(pp, a, pos, 'lower', 1)
    return _as_str(a[0]).lower()


def _bi_substr(pp, a, pos):
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
    _bi_check(pp, a, pos, 'abs', 1)
    if isinstance(a[0], str):
        raise MacroError(f"{_fmt_pos(pos)}: abs() needs an integer")
    return abs(a[0])


def _bi_minmax(pp, a, pos, want_min):
    # 破綻点修正: 組込 min()/max() をそのまま呼んでいたため、文字列と整数が
    # 混ざると MacroError ではなく素の TypeError が飛び、expand() の捕捉対象外
    # なので Python のトレースバックがそのままユーザに出ていた。
    # 他の比較（`<` 等）と同じ経路を通して同じ診断を出す。
    p = _ExprParser('', pp, pos)
    best = a[0]
    for v in a[1:]:
        lt = _cmp_lt_eq(p, v, best, False)
        if lt if want_min else (not lt and not _cmp_eq(v, best)):
            best = v
    return best


def _bi_min(pp, a, pos):
    _bi_check(pp, a, pos, 'min', 1, 64)
    return _bi_minmax(pp, a, pos, True)


def _bi_max(pp, a, pos):
    _bi_check(pp, a, pos, 'max', 1, 64)
    return _bi_minmax(pp, a, pos, False)


def _bi_uid(pp, a, pos):
    _bi_check(pp, a, pos, 'uid', 0)
    pp.uid += 1
    return pp.uid


def _bi_label(pp, a, pos):
    """label("名前") — アセンブラ側のラベル / .equ の値。

    裸の識別子でも同じ値を引けるが、`.L1` のようにマクロの識別子として
    書けない名前はこちらでしか参照できない。解決規則は裸の識別子と同一で、
    存在しない名前はエラーになる。
    """
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
        """組み込みアセンブリディレクティブを処理し終えた行の返り値。

        テキスト置換モード（`.textmode`）では、その行もテキストとして出す。
        翻訳結果から `.section` や `.global` のような行が消えないようにするため
        である。そうでなければ今までどおり、出力を出さない行として返す。
        caxx.c の adir_done() と同じ規則である。
        """
        if self.state.textmode:
            return self._passthru_line(l, l2, idx)
        return 0, [], True, idx

    def lineassemble2(self, line, idx):
        l, idx = StringUtils.get_param_to_spc(line, idx)
        l2, idx = StringUtils.get_param_to_eon(line, idx)
        l = l.rstrip()
        l2 = l2.rstrip()
        l = l.replace(' ', '')

        # テキスト置換モードでは、自分でワードや領域を出すディレクティブは
        # 処理せず、行をテキストとしてだけ出す（_TEXTMODE_TEXT_ONLY_DIRS の
        # コメントを参照）。
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
        # `.include` は取り込んだ行そのものが訳されて出るので、この行は出さない。
        if self.include_asm(l, l2):
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

        if l == "":
            # テキスト置換モードでラベルだけの行は、落とした `label:` を出力に
            # 戻す仕事が残っているので、出力なしの成功として返す
            # （付け直すのは lineassemble() の側）。
            if self.state.textmode and self.state.label_text:
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


        for i in self.state.pat:
            pln += 1
            pl = i
            self.state.vars = {}
            self.state.vars_undef = {}
            self.state.vars_text = {}

            if i is None:
                continue
            if self.directive_proc.set_symbol(i):
                continue
            if self.directive_proc.clear_symbol(i):
                continue
            if self.directive_proc.paddingp(i):
                continue
            if self.directive_proc.bits(i):
                continue
            if self.directive_proc.symbolc(i):
                continue
            if self.directive_proc.epic(i):
                continue
            if self.directive_proc.vliwp(i):
                continue
            if self.directive_proc.check_processing(i):
                continue
            if self.directive_proc.clrcheck_processing(i):
                continue
            if self.directive_proc.reloc_processing(i):
                continue
            if self.directive_proc.clrreloc_processing(i):
                continue
            if self.directive_proc.map_processing(i):
                continue
            if self.directive_proc.free_processing(i):
                continue
            if self.directive_proc.passthru_processing(i):
                continue
            if self.directive_proc.eol_processing(i):
                continue
            if self.directive_proc.textmode_processing(i):
                continue
            if self.directive_proc.enum_processing(i):
                continue
            if self.directive_proc.clrenum_processing(i):
                continue
            if self.directive_proc.errmsg_processing(i):
                continue

            lw = len([_ for _ in i if _])
            if lw == 0:
                continue

            lin = (l + ' ' + l2) if l2 else l
            lin = StringUtils.reduce_spaces(lin)

            if i[0] == '':
                hit_sentinel = True
                if best is None:
                    idxs, _ = self.expr_eval.expression_pat(i[3], 0)
                break

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
                    # パターン側はここでニーモニックが終わっているのに、ソース側は
                    # まだ語が続いている（`MOVE` パターン vs `MOVEM` 行）。
                    _ok = False
                if not _ok:
                    continue

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

                # 破綻点修正: 以前は「式もシンボルも0個」なら即打ち切っていたが、
                # スコアは (式の数, -リテラル数, シンボル数) の辞書順最小が勝ちで、
                # あとからもっとリテラルの多い（＝より具体的な）パターンが
                # 現れうるため、これでは取りこぼしがあった。健全な打ち切り条件を
                # 作るのは `+`/`-` の読み替え（ソースを消費せずリテラル数だけ
                # 増える）があるため難しく、全パターンを見ても実測で十分速いので、
                # 打ち切り自体をやめて常に最良スコアを選ぶ。

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

        # `.passthru` が有効なら、マッチしなかった行はエラーにせずそのまま出す。
        # 診断の抑止（パス1）に関わらず出すので、両パスで行の大きさが揃う。
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
                # 破綻点修正: パターン番号と生の6フィールド配列という内部表現を
                # 常にユーザ向けメッセージへ混ぜており、-d の有無に関わらず
                # 出力されていた。さらに " error - " より前に "; pat ..." が付くため、
                # 他の全診断が従う書式からも外れていた。
                # 詳細は -d 指定時だけ、本文とは別行で出す。
                self.state.diag(f" error - Illegal syntax in assemble line or pattern line.{_loc}", set_error=False)
                if self.state.debug:
                    self.state.diag(f"   (pattern {pln}: {pl})", set_error=False)
                return 0, [], False, idx

        return idxs, objl, True, idx

    def _passthru_line(self, l, l2, idx):
        """`.passthru` のとき、マッチしなかった行をそのままテキストとして出す。

        出るのは照合にかけた形の行、つまり空白を1つに詰め、`;` コメントと
        行頭のラベル定義を落としたあとの行である。行末の改行は付けない —
        1行が1行になるようにしたいときは `.eol` を書く。
        caxx.c の passthru_line() と同じ規則である。
        """
        txt = (l + ' ' + l2) if l2 else l
        # 素通しする行は式として読まないので、照合の途中で立った未定義ラベルの
        # 印はこの行には関わらない。
        self.state.error_undefined_label = False
        objl = list(txt.encode('utf-8', errors='surrogateescape'))
        _word_mask = (1 << self.state.bts) - 1 if self.state.bts > 0 else 0xFF
        if (any(_v > _word_mask for _v in objl)
                and not self.state._pass1_size_mode
                and self.state.should_report_errors()):
            self.state.diag(f" warning - .passthru: one or more bytes exceed the "
                            f"output word width ({self.state.bts} bit(s)) and were "
                            f"truncated (high bits discarded): {txt!r}", set_error=False)
        self.state.asmtext = txt
        self.state.asmtext_disp = '"%s"' % asmtext_escaped(txt)
        return 0, objl, True, idx

    def lineassemble(self, line):
        line = StringUtils.normalize_ws(line)
        line = StringUtils.remove_comment_asm(line)
        if line == '':
            return False
        line = StringUtils.resolve_vliw_escapes(line)

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

        # テキスト置換モードでは、行頭にあった `label:` をそのまま出力の先頭に
        # 付け直す。照合のために落としてあるので、ここで書かれていたとおりの
        # 綴りで戻す。テキストを作った行と、ラベルだけの行が対象で、テキスト
        # ではなく数値を出した行（`.ascii` などの組み込みディレクティブ）は
        # データを壊さないようそのままにする。
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
            # 前に足したぶん、その行のワード位置がずれる。ELF の再配置は
            # ワード位置で覚えているので、同じだけ送っておく。
            if _lbytes:
                self.state._elf_label_refs_seen = [
                    (_n, _v, (_w + len(_lbytes)) if _w >= 0 else _w)
                    for (_n, _v, _w) in self.state._elf_label_refs_seen]

        # `.eol` が有効なら、出力を出した行ごとに改行を1ワード足す。標準出力へ
        # 流すテキストには足さない（そちらは行ごとに改行して出しているので、
        # 二重になってしまう）。
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

                _mach_tbl_la = ELF_MACHINES[self.state.elf_machine]
                _rmap = {**_mach_tbl_la['width_guess'], **self.state.reloctype_override}
                _pc_rel_types_all = _mach_tbl_la['pc_rel']

                for lname, abs_w, first_widx, num_words in groups:
                    num_bytes = num_words * bpw_r

                    # `.reloc` が宣言された変数が運んだ参照は、命令語のビット欄に
                    # 値が詰まっていて出力バイト列から加数を逆算できない。型と加数
                    # は宣言側で決まっているので、通常の推定経路を通さずに出す。
                    _hint = self.state._elf_insn_reloc_hint.get(first_widx)
                    _forced_rtype = None
                    if _hint is not None:
                        _hint_rtype, _hint_addend = _hint
                        _fmask = insn_reloc_field_mask(_hint_rtype)
                        if _fmask is None:
                            # データ型を宣言した場合。加数は通常どおり出力バイト列
                            # から求まるので、型だけを固定して下の経路へ渡す。
                            _forced_rtype = _hint_rtype
                        else:
                            _insn_bytes = _mach_tbl_la['reloc_bytes'].get(_hint_rtype, 4)
                            _insn_words = max(1, _insn_bytes // bpw_r)
                            if first_widx + _insn_words <= len(objl):
                                # RELA ではリンカが欄を埋めるので、命令語側は 0 に
                                # しておく（GNU as と同じ形）。
                                _wmask = (1 << self.state.bts) - 1
                                for _k in range(_insn_words):
                                    _sh = self.state.bts * _k if self.state.endian == 'little' \
                                        else self.state.bts * (_insn_words - 1 - _k)
                                    _clear = (_fmask >> _sh) & _wmask
                                    objl[first_widx + _k] = int(objl[first_widx + _k]) & ~_clear & _wmask
                            _sec_rel_h = (_completed_words
                                          + (self.state.pc + first_widx - _entry_pc_cur)) * bpw_r
                            self.state.relocations.append(
                                (sec_name_r, _sec_rel_h, lname, _hint_rtype,
                                 _hint_addend, _insn_bytes))
                            continue

                    rtype = 0
                    _rtype_is_default_guess = False
                    lentry = self.state.labels.get(lname)
                    if _forced_rtype is not None:
                        rtype = _forced_rtype
                    elif lentry and len(lentry) > 4 and lentry[4] is not None:
                        rtype_override = lentry[4]
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
                        # この幅のリロケーション型を持たない ISA では、アセンブラが
                        # 自分で解決し終えた参照（分岐や adrp/:lo12: 等）が必ずここに
                        # 落ちる。出力は正しいのに毎回警告が出て本物の診断を埋めて
                        # しまうため、詳細は -d 指定時だけ出す。
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
                            and raw_val == abs_w_bytes and self.state.elf_machine == 62):
                        _rmap_abs_default = {8: 1, 4: 10, 2: 12, 1: 14}
                        rtype = _rmap_abs_default.get(num_bytes, rtype)

                    if _rtype_is_default_guess and self.state.elf_machine == 4:
                        _m68k_abs_default = {4: 1, 2: 2, 1: 3}
                        _m68k_pc_default = {4: 4, 2: 5, 1: 6}
                        if rtype in _pc_rel_types_all and raw_val == abs_w_bytes:
                            rtype = _m68k_abs_default.get(num_bytes, rtype)
                        elif rtype not in _pc_rel_types_all and raw_val != abs_w_bytes:
                            rtype = _m68k_pc_default.get(num_bytes, rtype)

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
        cleaned = line.replace('\n', '').replace('\r', '')
        _show = (self.state.pas == 2 and self.state.verbose) or self.state.pas == 0
        if _show:
            self.state.cl = cleaned
            print("%016x " % self.state.pc, end='')
            print(f"{self.state.current_file} {self.state.ln} {self.state.cl} //", end='')
        self.state.asmtext = None
        self.state.asmtext_disp = None
        f = self.lineassemble(cleaned)
        # パターンが文字列テンプレートだった行は、バイナリ出力とは別に、
        # アセンブリ結果をテキストでも出す。
        # -v の診断行の中では `` ではなく "" で括って見せ、診断を出さないときは
        # その行だけを素のまま標準出力へ流す（トランスレータとしての出力）。
        if self.state.asmtext is not None and self.state.pas in (0, 2):
            if _show:
                print(' %s' % (self.state.asmtext_disp or ''), end='')
            else:
                print(self.state.asmtext)
        self.state.asmtext = None
        self.state.asmtext_disp = None
        if _show:
            print("")
        self.state.ln += 1
        return f

    def setpatsymbols(self, pat):
        fresh = {}
        self.state.strsymbols = {}
        self.state.arrsymbols = {}
        for i in pat:
            if i is None:
                continue
            if len(i) > 0 and i[0] == '.setsym':
                if len(i) >= 2 and i[1]:
                    key = StringUtils.upper(i[1])
                    self.state.symbols = dict(fresh)
                    value_field = i[2] if len(i) >= 3 else ''
                    # 値が `"..."` なら数値ではなく文字列シンボル。式には出せない
                    # が、文字列テンプレート（3.5.2）の中から名前で呼び出せる。
                    _vf = value_field.lstrip(' \t')
                    if _vf.startswith('"'):
                        self.state.strsymbols[key] = \
                            ObjectGenerator._txt_template_inner(_vf)
                        continue
                    if _vf.startswith('['):
                        self.state.arrsymbols[key] = arr_items_from_text(self.expr_eval, _vf)
                        continue
                    # `.setsym::y::x` — x が文字列／配列シンボルなら写しを作る。
                    if symbol_copy_from_name(self.state, key, _vf):
                        continue
                    # `名前,名前,…` は名前の集合、`a&b` などは集合どうしの演算。
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
                else:
                    fresh = {}
                    self.state.strsymbols = {}
                    self.state.arrsymbols = {}
                continue
            if len(i) > 0 and i[0] == '.map':
                # `.map` のシンボルもこの前処理の表に積む。ここまでに積んだ
                # ものを公開してから展開するので、並びに書いた配列シンボルも、
                # 値の式に書いた `#記号` も解決できる。
                self.state.symbols = dict(fresh)
                self.directive_proc.map_apply(i, into=fresh, set_check=False)
                continue
            # `.free` はシンボルもこの前処理の表から外す（本体の走査でも同じ
            # ことをするが、ここで外しておかないと後続の `.setsym` の値の式から
            # 見えたままになる）。
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
                continue
            if len(i) > 0 and i[0] == '.bits':
                self.directive_proc.bits(i)
                continue
        self.state.patsymbols = fresh
        self.state.symbols = dict(fresh)

    def fileassemble(self, fn):

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

            # マクロ層の $/$$ は「展開後の何行目か」で決まる値なので、名前で
            # 引けるラベルと違って行番号でしか対応が取れない。この反復での
            # 行番号→アドレスを記録しておき、次の反復の展開時にそれを返す。
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
        af = ""
        while True:
            line = sys.stdin.readline()
            if line == '':
                break
            af += line.replace('\r', '')
        return af

    def imp_label(self, l):
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
                _mach_tbl_imp = ELF_MACHINES.get(self.state.elf_machine)
                reloc_type = _mach_tbl_imp['named'].get(rt_str.lower()) if _mach_tbl_imp else None
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
        print("%016x: " % pc, end='')

    def _section_word_ranges(self, name):
        ranges = [(rs, rl) for (rn, rs, rl) in self.state.section_ranges if rn == name]
        if ranges:
            return ranges
        entry = self.state.sections.get(name)
        if entry and entry[1] > 0:
            return [(entry[0], entry[1])]
        return []

    def _addr_to_word_offset(self, name, word_pc):
        if not self.state.sections:
            return word_pc
        cum = 0
        for rs, rl in self._section_word_ranges(name):
            if rs <= word_pc <= rs + rl:
                return cum + (word_pc - rs)
            cum += rl
        return None

    def _build_dwarf_sections(self, csecs, sec_name_to_idx, bpw, machine):
        line_map = self.state.line_map
        if not self.state.gen_debug or not line_map:
            return [], []

        _mach_tbl_dw = ELF_MACHINES.get(machine)
        _native_dw   = _mach_tbl_dw['elfclass'] if _mach_tbl_dw else 2
        _eff_class_dw = getattr(self.state, 'elf_class', None) or _native_dw
        if _mach_tbl_dw is None:
            self.state.diag(f" warning - DWARF debug info (-g) is not supported for "
                 f"unknown machine {machine}; skipping debug sections.", set_error=False)
            return [], []

        import struct as _struct
        _pk = '<' if self.state.endian != 'big' else '>'

        is_elf64_dw = (_eff_class_dw == 2)
        addr_sz = 8 if is_elf64_dw else 4
        is_rela_dw = _mach_tbl_dw.get('is_rela', True)

        def _pack_addr(v):
            v &= (1 << (addr_sz * 8)) - 1
            return _struct.pack(f'{_pk}I', v) if addr_sz == 4 else _struct.pack(f'{_pk}Q', v)

        # DWARF が書く絶対アドレス参照の欄幅は addr_sz（= -f で決まる ELF クラス）
        # だが、dwarf_abs はマシンごとの固定値。`-f` がそのマシンの慣習クラスと
        # 違うときは両者がずれ、4バイトの欄に 8バイト型（あるいはその逆）の
        # リロケーションを張ることになる。欄と同じ幅の型に取り替える。
        abs64 = _mach_tbl_dw['dwarf_abs']
        if _mach_tbl_dw['reloc_bytes'].get(abs64) != addr_sz:
            _want = 'abs64' if addr_sz == 8 else 'abs32'
            _alt = _mach_tbl_dw['named'].get(_want)
            if _alt is not None and _mach_tbl_dw['reloc_bytes'].get(_alt) == addr_sz:
                abs64 = _alt
            else:
                # 幅の合う絶対型を持たないマシン（32bit 機を -f 64 で出した場合）。
                # 幅の違う型を張れば黙って壊れたデバッグ情報になるので出さない。
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

        # 子 DIE になるラベルを先に集める。CU の DW_CHILDREN は「子があるか」を
        # 宣言するもので、ラベルを1つも持たないソース（命令だけのファイル）では
        # 子なしになる。宣言と中身が食い違うと DWARF の検証器が指摘するため、
        # 表を組む前に確定させる。
        _dbg_labels = []
        for _name, *_rest in sorted(self.state.labels.items()):
            _entry = _rest[0]
            if (len(_entry) > 2 and _entry[2]) or (len(_entry) > 3 and _entry[3]):
                continue                      # .equ と取り込みラベルは持たない
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
            # 子の連鎖を閉じる null DIE。DW_CHILDREN_no のときは連鎖自体が無いので
            # 置いてはいけない（読み手が余分な abbrev コード 0 を拾ってしまう）。
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
        import struct as _struct

        bpw = max(1, (self.state.bts + 7) // 8)
        buf = self.binary_writer._buffer

        _is_le    = (self.state.endian != 'big')
        _ei_data  = 1 if _is_le else 2
        _pk       = '<' if _is_le else '>'

        _native_elfclass = ELF_MACHINES.get(machine, {}).get('elfclass', 2)
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

        def _pack_ehdr(e_type, e_machine, e_shoff, e_shnum, e_shstrndx):
            ident = (b'\x7fELF'
                     + bytes([2 if _is_elf64 else 1, _ei_data, 1, self.state.osabi])
                     + b'\x00' * 8)
            if _is_elf64:
                return ident + _struct.pack(f'{_pk}HHIQQQIHHHHHH',
                    e_type, e_machine,
                    1,
                    0,
                    0,
                    e_shoff,
                    0,
                    _ehdr_size,
                    0, 0,
                    64,
                    e_shnum,
                    e_shstrndx)
            else:
                return ident + _struct.pack(f'{_pk}HHIIIIIHHHHHH',
                    e_type, e_machine,
                    1,
                    0,
                    0,
                    e_shoff,
                    0,
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
            __slots__ = ('name', 'byte_start', 'data', 'byte_size', 'flags')

            def __init__(self, name, byte_start, data, flags):
                self.name       = name
                self.byte_start = byte_start
                self.data       = data
                self.byte_size  = len(data)
                self.flags      = flags

        csecs = []
        max_w = max(buf.keys(), default=-1)

        if not self.state.sections:
            w_count = max_w + 1 if max_w >= 0 else 0
            csecs.append(_CSec('.text', 0, _extract(0, w_count), 0x2 | 0x4))
        else:
            sec_names = list(self.state.sections.keys())
            for i, sname in enumerate(sec_names):

                ranges = self._section_word_ranges(sname)
                w0 = ranges[0][0] if ranges else self.state.sections[sname][0]
                byte_start = w0 * bpw
                data = b''.join(_extract(rs, rl) for rs, rl in ranges)
                uname = sname.upper()
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
                csecs.append(_CSec(sname, byte_start, data, flags))

        ncs = len(csecs)

        sec_name_to_idx = {s.name: i + 1 for i, s in enumerate(csecs)}

        _mach_tbl_w = ELF_MACHINES.get(machine, {})
        _is_rela = _mach_tbl_w.get('is_rela', True)

        from collections import defaultdict as _defaultdict
        rela_entries = _defaultdict(list)
        for (sname, off, sym_name, rtype, addend, nbytes) in self.state.relocations:
            sidx = sec_name_to_idx.get(sname, 0)
            if sidx:
                rela_entries[sidx].append((off, sym_name, rtype, addend, nbytes))
            else:
                # 破綻点修正: セクション名が一致しないリロケーションを無警告で
                # 捨てていたため、修正が抜け落ちた「見た目は正常な」.oファイルが
                # 静かに生成されていた。診断を出す。
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
            name_off = len(strtab)
            strtab += name.encode() + b'\x00'
            syms.append(_pack_sym(name_off, 0x00, 0, shndx, sym_val, 0))

        first_global = len(syms)

        for name, *_lentry in sorted(self.state.labels.items()):
            is_imported = len(_lentry[0]) > 3 and _lentry[0][3]
            if not is_imported or name in export_keys:
                continue
            name_off = len(strtab)
            strtab += name.encode() + b'\x00'
            syms.append(_pack_sym(name_off, 0x10, 0, 0, 0, 0))

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
            name_off = len(strtab)
            strtab += name.encode() + b'\x00'
            syms.append(_pack_sym(name_off, 0x10, 0, shndx, sym_val, 0))

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
            return s.name.upper().startswith('.BSS')

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
                _sh_type_i = 8 if _is_nobits(s) else 1
                f.write(_pack_shdr(
                    sec_name_offs[i], _sh_type_i, s.flags, 0,
                    sec_offsets[i], s.byte_size, 0, 0, 16, 0))

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

        # 破綻点修正: 既定値が FreeBSD(9) 固定だったため、--osabi を指定しない
        # 通常の使い方では、標準的な Linux 環境の ld が OSABI ミスマッチで
        # 生成された .o を拒否し得た（axxelfbug 参照）。既定値を、実行環境として
        # 最も一般的な Linux(0) に変更する。
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
        ap.add_argument('-f', dest='elf_format', type=int, default=64,
                        choices=(32, 64), metavar='{32,64}',
                        help='ELF class for -o output: 64 for ELF64/ELFCLASS64, '
                             '32 for ELF32/ELFCLASS32 (default: 64). Independent '
                             'of -m/--machine; a value that does not match the '
                             'selected machine\'s conventional class (e.g. '
                             '-m 62 -f 32, the real x32 ABI\'s EM_X86_64-in-'
                             'ELFCLASS32 layout) is honored, with a warning. '
                             '-g/--gen-debug DWARF output supports both 32 and 64.')
        ap.add_argument('-m', dest='elf_machine', type=int, default=62,
                        metavar='MACHINE',
                        help='ELF e_machine value (default 62=EM_X86_64). '
                             'Must be one of the architectures axx has '
                             'relocation-numbering support for -- see '
                             'ELF_MACHINES near the top of this file for the '
                             'full list (currently: 3=i386, 4=M68K, '
                             '20=PowerPC, 21=PowerPC64, 22=s390x, 40=ARM, '
                             '42=SuperH, 43=SPARCV9, 62=x86-64, '
                             '183=AArch64, 243=RISC-V)')
        ap.add_argument('-v', '--verbose', dest='verbose', action='store_true',
                        default=False,
                        help='Verbose: print assembly listing to stdout (default: silent)')
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

    def _macro_expand_only(self, sourcefile, dest):
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
                    # An explicit "-" always names stdout. Consume it here so
                    # that argparse never sees it as a stray positional.
                    out += [a, '-']
                    i += 2
                elif (nxt is not None and not nxt.startswith('-')
                        and positional >= need):
                    out += [a, nxt]
                    i += 2
                elif nxt is not None and not nxt.startswith('-'):
                    # 破綻点修正: 位置引数が揃う前に `-P out.txt pat.axx src.s`
                    # と書かれた場合、この分岐は `-P` を引数なしと解釈し、
                    # out.txt を位置引数（＝パターンファイル）へ流していた。
                    # 「out.txt は -P の出力先」なのか「パターンファイル」なのか
                    # は原理的に決められないので、黙って一方に倒さず断る。
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

        if args.elf_machine not in ELF_MACHINES:
            _known = ', '.join(f"{m} ({ELF_MACHINES[m]['name']})" for m in sorted(ELF_MACHINES))
            self.state.diag(f" error - -m/--machine value {args.elf_machine} is not a supported "
                 f"ELF e_machine number. axx only knows correct relocation-type "
                 f"numbering for: {_known}. Refusing to guess/fall back to x86_64 "
                 f"numbering for an unrecognized machine, since that would silently "
                 f"mislabel every relocation in the output.", set_error=False, force=True)
            return False
        self.state.elf_machine  = args.elf_machine

        self.state.elf_class    = 2 if args.elf_format == 64 else 1

        _osabi_key = args.elf_osabi.lower()
        if _osabi_key not in osabitbl:
            print(f"warning: unknown --osabi value '{args.elf_osabi}'; "
                  f"valid choices are {list(osabitbl.keys())} (case-insensitive). Using 'Linux'.",
                  file=sys.stderr)
        self.state.osabi        = osabitbl.get(_osabi_key, 0)
        self.state.verbose      = args.verbose
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
            self.state.sub_defs = self.pattern_reader.subs
            self.state.func_defs = self.pattern_reader.funcs
            # 破綻点修正: パターンファイルが読めなかった場合、readpat() は
            # エラーを報告して空のパターン表を返すが、そのまま組み立てに進んで
            # いたため、全ソース行が「どのパターンにも一致しない」となり
            # 偽の "Syntax error" が行数ぶん並んで真の原因が埋もれていた。
            # （終了コードが 1 になっていたのはその偽エラーの副作用にすぎない。）
            if self.state.had_error:
                self.state.diag(" error - one or more errors were reported during assembly; "
                                "output would be incomplete or wrong.",
                                set_error=False, force=True)
                self.state.diag("         Aborting: no output file written.",
                                set_error=False, force=True)
                return False
            self.setpatsymbols(self.state.pat)
            # 破綻点修正: パターンファイル側のディレクティブ評価（.setsym / .bits 等）
            # で出たエラーを誰も拾っていなかったため、" error - ..." を表示しながら
            # 終了コード0で「出力ファイルだけ作られない」無言の失敗になっていた。
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

            # 破綻点修正: ここで既存の -b 出力を先に消すと、この後リラクゼーションが
            # 失敗して "no output written" と表示した場合でも、実際には直前の
            # 正常なビルド成果物が既に失われてしまう。書き込み側 (open(..,'wb'))
            # が成功時に上書き・切り詰めを行うので、ここでの事前削除は不要かつ有害。

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

                    # マクロ層に見せるスナップショット。次の反復の展開はこれを
                    # 使って評価される。名前の集合を値とは別に持つのは、値が
                    # まだ未確定なラベルを「綴り間違い」と誤判定しないため。
                    self.state._macro_label_values = dict(self.state._relax_prev_values)
                    self.state._macro_label_names = set(self.state.labels)
                    # dict() で複製するのは必須。同じ辞書を共有すると、次に
                    # fileassemble() が今回ぶんの記録を積み直すときに、まさに
                    # 展開中の式が読んでいるリストを空で上書きしてしまう
                    # （パス2で $ が 0 に化け、パス1と食い違う）。
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
                    # ラベル定義の誤りを既に報告している場合、ずれはその結果に
                    # すぎない（パス1では定義を拒否し、パス2では通ってしまう）。
                    # リラクゼーションの話を持ち出すと原因を見誤らせるので、
                    # そのときは上の報告を指す案内に差し替える。
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
                self.write_elf_obj(self.state.elf_objfile, self.state.elf_machine)
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
                                _mach_tbl_exp = ELF_MACHINES.get(self.state.elf_machine)
                                reloc_type_str = _mach_tbl_exp['reverse'].get(lentry[4], '') if _mach_tbl_exp else ''
                                if reloc_type_str:
                                    reloc_type_str = f'::{reloc_type_str}'

                        label_file.write(f"{i[0]}{reloc_type_str}\t{lbl_addr:#x}\n")

            if self.state.expfile:
                _write_export(self.state.expfile, elf=0)
            if self.state.expfile_elf:
                _write_export(self.state.expfile_elf, elf=1)

        finally:
            if self.state.stdin_tmp_path and os.path.exists(self.state.stdin_tmp_path):
                try:
                    os.remove(self.state.stdin_tmp_path)
                except OSError:
                    pass
                self.state.stdin_tmp_path = None

        return True


def main():
    assembler = Assembler()
    return assembler.run()


if __name__ == '__main__':
    ok = main()
    exit(0 if ok else 1)
