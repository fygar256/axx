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


from decimal import Decimal, localcontext
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
                 "heuristic may misclassify very large legitimate values as undefined.", set_error=False)
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
        pc_rel={2, 13, 21, 23},
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
        width_guess={4: 3, 2: 4, 1: 8},
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
        self.osabi: int = 9        # ELF ヘッダの OSABI（9=FreeBSD）
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

        # 直近の式評価で未定義ラベルを踏んだか。重要な約束として、この旗は
        # 「失敗したときに立てる」だけで、成功しても勝手に降ろさない。
        # 1つの式の途中で複数のラベルを引くため、途中で降ろすと先に立った
        # 失敗の情報が消えてしまう。降ろすのは、真新しく判定したい側
        # （.ORG/.RESB/.ZERO/.ALIGN/.EQU 等）が評価直前に自分で行う。
        self.error_undefined_label = False
        self.error_label_conflict = False

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
        self.vars = [VAR_UNDEF for i in range(26)]

        self.deb1 = ""           # 照合デバッグ用（ソース側の残り）
        self.deb2 = ""           # 同（パターン側の残り）

        self.exp_typ: str = 'i'  # 'i'=整数 / 'f'=浮動小数点

        self.relax = RelaxationState()

        self.verbose: bool = False

        # 標準入力から読んだソースを置く一時ファイル（全パスで再利用する）。
        self.stdin_tmp_path: str | None = None

        self.elf = ElfState()

        self.init_func: str | None = None
        self.fini_func: str | None = None

        # .check で登録された「この変数はこの条件を満たすこと」という制約。
        self.check_constraints: dict = {}

        # セクションは .section / .endsection の出入りで断片化しうる。
        # その断片ごとの (名前, 開始, ワード数) を順に記録する。
        self.section_ranges: list = []

        # .EQU の右辺が複数セクションのラベルにまたがっていないかの検査用。
        self._equ_sections_touched = None


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
    # 書き換えずに状態を整理できるようにしてある。実際の転送は下の
    # __getattr__ / __setattr__ が行う。
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
    def remove_comment(l):
        """パターンファイルのコメント `/* ...` を落とす（行単位・閉じ記号は不要）。"""
        idx = 0
        while idx < len(l):
            if l[idx:idx + 2] == '/*':
                return "" if idx == 0 else l[0:idx]
            idx += 1
        return l

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
            if idx >= len(s):
                self.state.diag(f" error - missing closing '}}' in expression: '{{{t}'", set_error=True)
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

    def get_label_word(self, s, idx):
        t = ""
        if idx < len(s) and (s[idx] == '.' or (s[idx] not in DIGIT and s[idx] in self.state.lwordchars)):
            t = s[idx]
            idx += 1
            while idx < len(s) and s[idx] in self.state.lwordchars:
                t += s[idx]
                idx += 1

            if idx < len(s) and s[idx] == ':' and (idx + 1 >= len(s) or s[idx + 1] != '='):
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
            sign = 0
            exponent = 0
            fraction = 0
        else:
            sign = 0 if d >= 0 else 1
            d = abs(d)

            two = Decimal(2)

            scaled = int(d * (two ** SIGNIFICAND_BITS))
            if scaled == 0:
                exp_unbiased = -(BIAS - 1)
            else:
                exp_unbiased = scaled.bit_length() - 1 - SIGNIFICAND_BITS

            scale = two ** exp_unbiased
            normalized = d / scale

            while normalized >= 2:
                exp_unbiased += 1
                normalized /= 2
            while normalized < 1:
                exp_unbiased -= 1
                normalized *= 2

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
                fraction = int(d / shift + Decimal('0.5'))
                if fraction >= (1 << SIGNIFICAND_BITS):
                    exponent = 1
                    fraction = 0
            else:
                exponent = biased_exp
                fraction = int((normalized - 1) * (two ** SIGNIFICAND_BITS) + Decimal('0.5'))
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
                    v = Decimal(int(v // t))
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
    """パターン変数 a〜z の束縛を管理する。
    
    `!x` や `!Fx` でソースから捕捉した値の置き場。状態は state.vars（26要素の配列）で、
    このクラスは添字計算と未定義判定を隠すだけの薄い層。
    """

    def __init__(self, state):
        self.state = state

    def get(self, s):
        c = ord(StringUtils.upper(s))
        return self.state.vars[c - ord('A')]

    def put(self, s, v):
        if StringUtils.upper(s) in CAPITAL:
            c = ord(StringUtils.upper(s))
            if isinstance(v, Decimal):
                if not v.is_finite():
                    self.state.vars[c - ord('A')] = float(v)
                elif v == v.to_integral_value():
                    self.state.vars[c - ord('A')] = int(v)
                else:
                    self.state.vars[c - ord('A')] = float(v)
            elif isinstance(v, float) and not v.is_integer():
                self.state.vars[c - ord('A')] = v
            else:
                try:
                    self.state.vars[c - ord('A')] = int(v)
                except (OverflowError, ValueError):
                    self.state.vars[c - ord('A')] = v


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
                self.state.diag(f" error - Label undefined: '{k}'"
                     f"  [{_fn}:{_ln}]", set_error=False)
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

    def put_value(self, k, v, s, is_equ=False, reloc_type=None):
        if self.state.pas == 1 or self.state.pas == 0:
            if k in self.state.labels:
                existing = self.state.labels[k]
                old_is_imported = len(existing) > 3 and existing[3]
                if not old_is_imported:
                    self.state.error_label_conflict = True
                    self.state.had_error = True
                    self.state.diag(" error - label already defined.", set_error=False)
                    return False
        elif self.state.pas == 2:
            if k not in self.state.labels:
                self.state.error_label_conflict = True
                self.state.had_error = True
                self.state.diag(f" error - label '{k}' not defined in pass 1.", set_error=False)
                return False

        if StringUtils.upper(k) in self.state.patsymbols:
            self.state.had_error = True
            self.state.diag(f" error - '{k}' is a pattern file symbol.", set_error=False)
            return False

        self.state.error_label_conflict = False

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
    
    レジスタ名などの「小文字1文字パターン」が照合時にここを参照する。
    名前は大小文字を区別せずに解決する。
    """

    def __init__(self, state):
        self.state = state

    def get(self, w):
        w = w.upper()
        return self.state.symbols.get(w, "")


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
        b = 0
        if isinstance(l, float) and not l == l:
            return 0
        if isinstance(l, float) and (l == float('inf') or l == float('-inf')):
            return 0
        try:
            r = int(abs(l))
        except (OverflowError, ValueError):
            return 0
        while r:
            r >>= 1
            b += 1
        return b

    def err(self, m):
        print(m, file=sys.stderr)
        return -1

    def factor(self, s, idx):
        idx = StringUtils.skipspc(s, idx)
        x = 0

        if idx + 4 <= len(s) and s[idx:idx + 4] == '!!!!' and self.state.expmode == EXP_PAT:
            x = self.state.vliwstop
            idx += 4
        elif idx + 3 <= len(s) and s[idx:idx + 3] == '!!!' and self.state.expmode == EXP_PAT:
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
                        try:
                            shift_amount = int(x2) * 8
                        except (OverflowError, ValueError):
                            self.state.diag(" error - non-finite byte-extract offset in *(expr, expr).", set_error=True)
                            x = 0
                        else:
                            if shift_amount < 0:
                                self.state.diag(" error - negative byte-extract offset in *(expr, expr).", set_error=True)
                                x = 0
                            else:
                                x = x >> shift_amount
                    else:
                        self.state.diag(" error - missing ')' in *(expr, expr) expression.", set_error=True)
                        x = 0
                else:
                    self.state.diag(" error - missing ',' in *(expr, expr) expression.", set_error=True)
                    x = 0
            else:
                self.state.diag(" error - expected '(' after '*' in *(expr,expr) expression.", set_error=True)
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
        elif self.state.exp_typ == 'i' and idx < len(s) and s[idx].isdigit():
                fs, idx = self.parser.get_intstr(s, idx)
                x = int(fs)
        elif self.state.exp_typ == 'f' and idx < len(s) and (self.parser.isfloatstr(s, idx)):
                fs, idx = self.parser.get_floatstr(s, idx)
                try:
                    x = float(fs) if fs else 0.0
                except ValueError:
                    x = 0.0
        elif (idx < len(s) and self.state.expmode == EXP_PAT and
              s[idx] in LOWER and (idx + 1 >= len(s) or s[idx + 1] not in self.state.lwordchars)):
            ch = s[idx]
            if idx + 3 <= len(s) and s[idx + 1:idx + 3] == ':=':
                x, idx = self.expression(s, idx + 3)
                self.var_manager.put(ch, x)
            else:
                x = self.var_manager.get(ch)
                idx += 1
                if (not self.state._in_match_attempt
                        and not self.state._pass1_size_mode
                        and (self.state.should_report_errors())
                        and _is_undef_derived(x)):
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
        elif idx < len(s) and s[idx] in self.state.lwordchars:
            w, idx_new = self.parser.get_label_word(s, idx)
            if idx != idx_new:
                idx = idx_new
                x = self.label_manager.get_value(w)

        idx = StringUtils.skipspc(s, idx)
        return x, idx

    def term0_0(self, s, idx):
        x, idx = self.factor(s, idx)
        while idx < len(s) and StringUtils.q(s, '**', idx):
            t, idx = self.factor(s, idx + 2)
            _EXP_MAX = 1024
            _EXP_RESULT_MAX_BITS = 1 << 20

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

            try:
                _base_bits = abs(x).bit_length() if isinstance(x, int) else 1024
            except (TypeError, ValueError, OverflowError):
                _base_bits = 1024
            if _base_bits * max(t_int, 1) > _EXP_RESULT_MAX_BITS:
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
        _SEXT_MAX_BITS = 128
        x, idx = self.term5(s, idx)
        while idx < len(s) and s[idx] == '\'':
            next_idx = idx + 1
            next_idx = StringUtils.skipspc(s, next_idx)
            if next_idx >= len(s) or (s[next_idx] not in DIGIT and s[next_idx] != '('):
                break
            t, idx = self.term5(s, idx + 1)
            try:
                x = int(x)
                t = int(t)
            except (ValueError, OverflowError):
                x = 0
                break
            if t <= 0:
                x = 0
            elif t > _SEXT_MAX_BITS:
                self.state.diag(f" warning - sign-extension bit width {t} exceeds maximum {_SEXT_MAX_BITS}, result set to 0.", set_error=False)
                x = 0
            else:
                x = (x & ~((~0) << t)) | ((~0) << t if (x >> (t - 1) & 1) else 0)
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

    def term11(self, s, idx):
        x, idx = self.term10(s, idx)
        if idx < len(s) and StringUtils.q(s, '?', idx):
            saved_vars              = self.state.vars[:]
            saved_err_undef         = self.state.error_undefined_label
            saved_err_conflict      = self.state.error_label_conflict
            saved_elf_refs_len      = len(self.state._elf_label_refs_seen)
            saved_elf_v2l           = dict(self.state._elf_var_to_label)

            t, idx = self.term11(s, idx + 1)
            vars_after_true         = self.state.vars[:]
            err_after_true          = self.state.error_undefined_label
            conflict_after_true     = self.state.error_label_conflict
            refs_after_true         = list(self.state._elf_label_refs_seen)
            v2l_after_true          = dict(self.state._elf_var_to_label)

            if idx < len(s) and StringUtils.q(s, ':', idx):
                self.state.vars                     = saved_vars[:]
                self.state.error_undefined_label    = saved_err_undef
                self.state.error_label_conflict     = saved_err_conflict
                del self.state._elf_label_refs_seen[saved_elf_refs_len:]
                self.state._elf_var_to_label        = dict(saved_elf_v2l)
                u, idx = self.term11(s, idx + 1)

                if x != 0:
                    self.state.vars                     = vars_after_true
                    self.state.error_undefined_label    = err_after_true
                    self.state.error_label_conflict     = conflict_after_true
                    self.state._elf_label_refs_seen     = refs_after_true
                    self.state._elf_var_to_label        = v2l_after_true
                    x = t
                else:
                    x = u
            else:
                if x != 0:
                    self.state.vars                     = vars_after_true
                    self.state.error_undefined_label    = err_after_true
                    self.state.error_label_conflict     = conflict_after_true
                    self.state._elf_label_refs_seen     = refs_after_true
                    self.state._elf_var_to_label        = v2l_after_true
                    x = t
                else:
                    self.state.vars                     = saved_vars
                    self.state.error_undefined_label    = saved_err_undef
                    self.state.error_label_conflict     = saved_err_conflict
                    del self.state._elf_label_refs_seen[saved_elf_refs_len:]
                    self.state._elf_var_to_label        = dict(saved_elf_v2l)
                    x = 0
        return x, idx

    def expression(self, s, idx):
        try:
            idx0 = StringUtils.skipspc(s, idx)
            x, idx0 = self.term11(s, idx0)
            return x, idx0
        except RecursionError:
            self.state.diag(" error - expression nesting too deep (RecursionError).", set_error=False)
            return 0, idx

    def _terminate(self, s):
        if not s or s[-1] != chr(0):
            return s + chr(0)
        return s

    def expression_pat(self, s, idx):
        prev = self.state.expmode
        self.state.expmode = EXP_PAT
        try:
            return self.expression(self._terminate(s), idx)
        finally:
            self.state.expmode = prev

    def expression_asm(self, s, idx):
        prev = self.state.expmode
        self.state.expmode = EXP_ASM
        try:
            return self.expression(self._terminate(s), idx)
        finally:
            self.state.expmode = prev

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
                if stack and OPEN_TO_CLOSE.get(stack[-1]) == ch:
                    stack.pop()
                    result.append(ch)
                else:
                    result.append(ch)
            else:
                result.append(ch)

        replaced = ''.join(result)
        return self.expression(self._terminate(replaced), idx)

    def expression_esc_float(self, s, idx, stopchar):
        prev_typ  = self.state.exp_typ
        prev_mode = self.state.expmode
        self.state.exp_typ = 'f'
        try:
            v, idx = self.expression_esc(s, idx, stopchar)
        finally:
            self.state.exp_typ  = prev_typ
            self.state.expmode  = prev_mode
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
        if not self.state.outfile or not self._buffer:
            return

        if self.state.bts <= 0:
            self.state.diag(f" warning - flush: bts={self.state.bts} is invalid (<=0); "
                 f"output file '{self.state.outfile}' will be empty.", set_error=False)
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
                self.state.diag(f" error - non-finite value {x!r} cannot be written as binary word.", set_error=False)

    def outbin(self, a, x):
        if self.state.should_report_errors():
            _prt = 1 if ((self.state.pas == 2 and self.state.verbose) or self.state.pas == 0) else 0
            try:
                self.fwrite(a, int(x), _prt)
            except (OverflowError, ValueError):
                self.state.diag(f" error - non-finite value {x!r} cannot be written as binary word.", set_error=False)

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
        else:
            self.state.symbols = {}

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

        if value_field:
            v, idx = self.expr_eval.expression_pat(value_field, 0)
        else:
            v = 0
        self.state.symbols[key] = v
        return True

    def bits(self, i):
        if len(i) == 0 or i[0] != '.bits':
            return False

        if len(i) >= 2:
            if i[1].lower() == 'big':
                self.state.endian = 'big'
            elif i[1].lower() == 'little':
                self.state.endian = 'little'

        v = None
        if len(i) >= 3:
            v, idx = self.expr_eval.expression_pat(i[2], 0)
        elif len(i) >= 2 and i[1].lower() not in ('big', 'little'):
            v, idx = self.expr_eval.expression_pat(i[1], 0)
        if v is not None:
            try:
                self.state.bts = int(v)
            except (OverflowError, ValueError):
                self.state.diag(" error - .bits: non-finite bit width value.", set_error=True)
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
            self.state.diag(f" error - .vliw directive requires 4 parameters (vliwbits, vliwinstbits, vliwtemplatebits, nop_value), got {len(i) - 1}", set_error=False)
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

            if (self.state.should_report_errors()) and u:
                try:
                    t_int = int(t)
                except (OverflowError, ValueError):
                    t_int = 0
                print(f"Line {self.state.ln} Error code {t_int} ", end="", file=sys.stderr)
                if 0 <= t_int < len(ERRORS):
                    print(f"{ERRORS[t_int]}", end='', file=sys.stderr)
                print(": ", file=sys.stderr)
                error_code = t_int
                triggered = True
                self.state.had_error = True

        return triggered, error_code

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
        var = var_field.strip().lower()
        if len(var) != 1 or var not in LOWER:
            self.state.diag(f" error - .check: variable should be a lower case letter ('{var_field}').", set_error=True)
            return True
        syms = []
        if syms_field:
            for s in syms_field.split(','):
                s = s.strip()
                if not s:
                    continue
                if s == '""' or s == "''":
                    # 空文字リテラルは「このオペランドは省略してよい」印。
                    # 省略時、変数には VAR_UNDEF(0) が入る。
                    if CHECK_OMIT not in syms:
                        syms.append(CHECK_OMIT)
                    continue
                syms.append(s.upper())
        self.state.check_constraints[var] = syms
        return True

    def clrcheck_processing(self, i):
        if len(i) == 0 or i[0] != '.clrcheck':
            return False
        var_field = i[2].strip() if len(i) >= 3 and i[2] else ''
        if var_field:
            var = var_field.lower()
            if len(var) == 1 and var in LOWER:
                self.state.check_constraints.pop(var, None)
            else:
                self.state.diag(f" error - .clrcheck: variable should be a lower case letter ('{var_field}').", set_error=True)
        else:
            self.state.check_constraints.clear()
        return True


_SYM_CORE = set(DIGIT + ALPHABET + '_')


def _expects_expr(t, idx):
    while idx < len(t) and t[idx] in ' \t':
        idx += 1
    return idx < len(t) and t[idx] == '!'


class PatternMatcher:
    r"""ソース行とパターンの照合を行う。
    
    字句解析をせず1文字ずつ突き合わせる。パターン側の文字の意味は:
      大文字        大小無視でリテラル一致（ニーモニック）
      小文字1文字   .setsym のシンボル（レジスタ名等）を取る
      `!x`          任意の式を読んで変数 x に束縛
      `!!x`         式ではなく factor 1個だけを束縛
      `!Fx`/`!Dx`/`!Qx`  浮動小数点式を IEEE754 の 32/64/128bit として束縛
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
                if idx_t < len(t) and t[idx_t] == b:
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
                    a = t[idx_t]
                    if a == chr(0) or a not in LOWER:
                        return False
                    idx_t = StringUtils.skipspc(t, idx_t + 1)
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
                    a = t[idx_t]
                    if a == chr(0) or a not in LOWER:
                        return False
                    idx_t = StringUtils.skipspc(t, idx_t + 1)
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
                    a = t[idx_t]
                    if a == chr(0) or a not in LOWER:
                        return False
                    idx_t = StringUtils.skipspc(t, idx_t + 1)
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
                elif a == '!':
                    if idx_t >= len(t):
                        return False
                    a = t[idx_t]
                    if a == chr(0) or a not in LOWER:
                        return False
                    idx_t += 1
                    self.state._elf_capturing_var = a
                    try:
                        v, idx_s = self.expr_eval.factor(s, idx_s)
                    finally:
                        self.state._elf_capturing_var = None
                    self.var_manager.put(a, v)
                    continue
                else:
                    if a == chr(0) or a not in LOWER:
                        return False
                    idx_t = StringUtils.skipspc(t, idx_t)
                    if idx_t < len(t) and t[idx_t] == '\\':
                        idx_t += 1
                        stopchar = t[idx_t] if idx_t < len(t) else chr(0)
                        idx_t += 1
                    else:
                        stopchar = chr(0)

                    self.state._elf_capturing_var = a
                    try:
                        v, idx_s = self.expr_eval.expression_esc(s, idx_s, stopchar)
                    finally:
                        self.state._elf_capturing_var = None
                    self.var_manager.put(a, v)
                    if stopchar != chr(0) and idx_s < len(s) and s[idx_s] == stopchar:
                        idx_s += 1
                    continue
            elif a in LOWER:
                prev_alnum = False
                idx_t += 1
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

    def match0(self, s, t):
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
                saved_vars = self.state.vars[:]
                saved_refs_len = len(self.state._elf_label_refs_seen)
                saved_v2l      = dict(self.state._elf_var_to_label)
                if self.match(s, lt):
                    self.last_match_score = self.last_score
                    return True
                self.state.vars = saved_vars
                del self.state._elf_label_refs_seen[saved_refs_len:]
                self.state._elf_var_to_label = saved_v2l
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

    def readpat(self, fn, base_dir=None, _depth=0, _chain=None):
        if fn == '':
            return []

        _MAX_PAT_DEPTH = 50
        if _depth > _MAX_PAT_DEPTH:
            diag(f" error - pattern .INCLUDE nesting exceeds {_MAX_PAT_DEPTH}: '{fn}'", set_error=False)
            return []

        if base_dir and not os.path.isabs(fn):
            fn = os.path.join(base_dir, fn)

        _real = os.path.realpath(fn)
        if _chain is None:
            _chain = frozenset()
        if _real in _chain:
            diag(f" error - circular pattern .INCLUDE detected: '{fn}' "
                 f"(already in include chain). Skipped.", set_error=False)
            return []
        _chain = _chain | {_real}

        this_dir = os.path.dirname(os.path.abspath(fn))

        p = []
        w = []

        if _depth == 0:
            self.macro_proc.reset_pass()

        try:
            with open(fn, "rt", encoding="utf-8") as f:
                raw_lines = f.readlines()
        except OSError as e:
            diag(f" error - cannot open pattern file '{fn}': {e}", set_error=True)
            return []

        for l, _mfile, _mln in self.macro_proc.expand(raw_lines, fn):

            l = StringUtils.remove_comment(l)
            l = l.replace('\t', ' ')
            l = l.replace(chr(13), '')
            l = l.replace('\n', '')
            l = StringUtils.reduce_spaces(l)

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

                if len(l) == 1:
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

        return w

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
                    diag(f" error - .INCLUDE directive has no filename: {l!r}", set_error=False)
                    return []
            else:
                diag(f" error - .INCLUDE directive has no filename: {l!r}", set_error=False)
                return []
        w = self.readpat(s, base_dir, _depth=_depth, _chain=_chain)
        return w


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

                    self.state.error_undefined_label = False
                    n, idx = self.expr_eval.expression_pat(expr, 0)
                    _N_MAX = 1 << 24
                    if self.state.error_undefined_label:
                        n = 0
                    try:
                        n_int = int(n)
                    except (ValueError, OverflowError):
                        n_int = 0
                    if n_int > _N_MAX:
                        self.state.diag(f" error - @@[n,...]: repeat count {n_int} exceeds maximum {_N_MAX}.", set_error=False)
                        n_int = 0
                    if n_int > 0:
                        n = n_int
                        has_content = True
                        for j in range(int(n)):
                            if j > 0:
                                result.append(',')
                            result.append(rep_pattern)

                    i += 1
                else:
                    self.state.diag(" error - @@[...]: missing ',' separating count and pattern.", set_error=True)
                    result.append('@@[')
                    has_content = True
            else:
                result.append(pattern[i])
                has_content = True
                i += 1

        return ''.join(result), not has_content

    def makeobj(self, s):
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
                if s[idx] == ';':
                    semicolon = True
                    idx += 1

                self.state._elf_current_word_idx = len(objl)

                if self.state.pas == 1:
                    self.state._pass1_size_mode = True
                x, idx = self.expr_eval.expression_pat(s, idx)
                if self.state.pas == 1:
                    self.state._pass1_size_mode = False
                    self.state.error_undefined_label = False

                if not semicolon or x != 0:
                    objl += [x]
                elif semicolon:
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

        return objl


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
                x, idx = self.expr_eval.expression_pat(k[1], 0)
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
                return ""
            else:
                ok = self.label_manager.put_value(label, self.state.pc, self.state.current_section, is_equ=False)
                if ok is False:
                    return ""
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
            if ch is not None:
                if ord(ch) > _word_mask:
                    _truncated = True
                self.binary_writer.outbin(self.state.pc, ord(ch))
                self.state.pc += 1
        if idx >= len(l2):
            self.state.diag(f" warning - unterminated string literal in .ASCII/.ASCIZ: {l2!r}", set_error=False)
        if _truncated and self.state.should_report_errors():
            self.state.diag(f" warning - .ASCII/.ASCIZ: one or more characters exceed the output word "
                 f"width ({self.state.bts} bit(s)) and were truncated (high bits discarded): "
                 f"{l2!r}", set_error=False)
        return True

    def export_processing(self, l1, l2):
        if not (self.state.should_report_errors()):
            return False
        _l1u = StringUtils.upper(l1)
        if _l1u != ".EXPORT" and _l1u != ".GLOBAL":
            return False

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

            if idx < len(l2) and l2[idx] == ':':
                idx += 1

            existing = self.state.labels.get(label_part)

            if existing is None:
                self.state.labels[label_part] = [0, '.text', False, True, reloc_type]
            elif len(existing) > 3 and existing[3]:

                if len(existing) >= 5 and reloc_type is not None:
                    existing[4] = reloc_type

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
        elif c in '"\'':
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
            a = self.ternary()
            self.expect(':')
            b = self.ternary()
            return a if _truth(c) else b
        return c

    def logic_or(self):
        v = self.logic_and()
        while self.eat('||'):
            r = self.logic_and()
            v = 1 if (_truth(v) or _truth(r)) else 0
        return v

    def logic_and(self):
        v = self.bit_or()
        while self.eat('&&'):
            r = self.bit_or()
            v = 1 if (_truth(v) and _truth(r)) else 0
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
            if self.s.startswith('<<', self.i) or self.s.startswith('>>', self.i):
                return v
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
                    self.err("shift count out of range")
                v = _as_int(self, v) << r
            elif self.eat('>>'):
                r = _as_int(self, self.additive())
                if r < 0 or r > 4096:
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
                    self.err("division by zero")
                v = _c_div(_as_int(self, v), r)
            elif self.s.startswith('%', self.i):
                self.i += 1
                r = _as_int(self, self.unary())
                if r == 0:
                    self.err("modulo by zero")
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
                return self.pp.call_value(name, args, self.pos)
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
        p.err(f"expected an integer, got the string {v!r}")
    return v


def _as_str(v):
    return v if isinstance(v, str) else str(v)


def _cmp_eq(a, b):
    if isinstance(a, str) != isinstance(b, str):
        return False
    return a == b


def _cmp_lt_eq(p, a, b, or_equal):
    if isinstance(a, str) != isinstance(b, str):
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


    def scope(self):
        return self.scopes[-1]

    def lookup(self, name, pos):
        for sc in reversed(self.scopes):
            if name in sc:
                return sc[name]
        if name in self.funcs:
            raise MacroError(f"{_fmt_pos(pos)}: macro '{name}' used as a variable "
                             f"(call it as '{name}(...)')")
        raise MacroError(f"{_fmt_pos(pos)}: undefined macro variable '{name}'")

    def is_defined(self, name):
        if name in self.funcs:
            return True
        return any(name in sc for sc in self.scopes)

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
        for k, pname in enumerate(fn.params):
            if k < len(args):
                local[pname] = args[k]
            else:
                local[pname] = self.eval(fn.defaults[k], pos)
        self.uid += 1
        local['__id__'] = self.uid
        local['__name__'] = fn.name

        self.scopes.append(local)
        self.depth += 1
        try:
            self.exec_block(fn.body)
        except _MacroReturn as r:
            return r.value
        finally:
            self.depth -= 1
            self.scopes.pop()
        return 0


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
        for k, c in enumerate(body):
            if quote:
                if c == '\\':
                    continue
                if c == quote:
                    quote = ''
                continue
            if c in '"\'':
                quote = c
            elif c in '([':
                par += 1
            elif c in ')]':
                par -= 1
            elif c == ':' and par == 0:
                if '?' in body[:k]:
                    continue
                spec = body[k + 1:].strip()
                body = body[:k]
                break
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
                print(_as_str(self.eval(expr, pos)), file=sys.stderr)
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
            with open(path, 'rt', encoding='utf-8') as f:
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
        if msg not in self._reported:
            self._reported.add(msg)
            self.state.diag(f" error - {msg}", set_error=False, force=True)
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
    neg = v < 0
    s = format(abs(v), 'x')
    if isinstance(width, int) and width > len(s):
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


def _bi_min(pp, a, pos):
    _bi_check(pp, a, pos, 'min', 1, 64)
    return min(a)


def _bi_max(pp, a, pos):
    _bi_check(pp, a, pos, 'max', 1, 64)
    return max(a)


def _bi_uid(pp, a, pos):
    _bi_check(pp, a, pos, 'uid', 0)
    pp.uid += 1
    return pp.uid


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
        if s:

            if s != "stdin" and not os.path.isabs(s):
                cur = self.state.current_file
                if cur and cur not in ("(stdin)", ""):
                    base = os.path.dirname(os.path.abspath(cur))
                    s = os.path.join(base, s)
            self.fileassemble(s)
        return True

    def lineassemble2(self, line, idx):
        l, idx = StringUtils.get_param_to_spc(line, idx)
        l2, idx = StringUtils.get_param_to_eon(line, idx)
        l = l.rstrip()
        l2 = l2.rstrip()
        l = l.replace(' ', '')

        if self.asm_directive_proc.section_processing(l, l2):
            return 0, [], True, idx
        if self.asm_directive_proc.endsection_processing(l, l2):
            return 0, [], True, idx
        if self.asm_directive_proc.resb_processing(l, l2):
            return 0, [], True, idx
        if self.asm_directive_proc.zero_processing(l, l2):
            return 0, [], True, idx
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
            return 0, [], True, idx
        if self.asm_directive_proc.align_processing(l, l2):
            return 0, [], True, idx
        if self.asm_directive_proc.org_processing(l, l2):
            return 0, [], True, idx
        if self.asm_directive_proc.labelc_processing(l, l2):
            return 0, [], True, idx
        if self.asm_directive_proc.extern_processing(l, l2):
            return 0, [], True, idx
        if self.asm_directive_proc.reloctype_processing(l, l2):
            return 0, [], True, idx
        if self.asm_directive_proc.export_processing(l, l2):
            return 0, [], True, idx

        if l == "":
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
            snap['vliwnop'] = list(self.state.vliwnop)
            snap['vliwset'] = list(self.state.vliwset)
            return snap

        def _restore_dirstate(snap):
            for f in _DIR_SCALAR_FIELDS:
                setattr(self.state, f, snap[f])
            self.state.symbols = dict(snap['symbols'])
            self.state.check_constraints = dict(snap['check_constraints'])
            self.state.vliwnop = list(snap['vliwnop'])
            self.state.vliwset = list(snap['vliwset'])


        for i in self.state.pat:
            pln += 1
            pl = i
            self.state.vars = [VAR_UNDEF] * 26

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

            saved_vars = self.state.vars[:]
            saved_refs_len = len(self.state._elf_label_refs_seen)
            saved_v2l = dict(self.state._elf_var_to_label)

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
                        'vars':  self.state.vars[:],
                        'refs':  self.state._elf_label_refs_seen[saved_refs_len:],
                        'v2l':   dict(self.state._elf_var_to_label),
                        'dir':   _snap_dirstate(),
                        'error_undefined_label': self.state.error_undefined_label,
                        'diags': _cand_diags,
                    }

                self.state.vars = saved_vars
                del self.state._elf_label_refs_seen[saved_refs_len:]
                self.state._elf_var_to_label = saved_v2l

                if score[0] == 0 and score[2] == 0:
                    break

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
            self.state.vars = best['vars'][:]
            self.state._elf_label_refs_seen.extend(best['refs'])
            self.state._elf_var_to_label = dict(best['v2l'])
            self.state.error_undefined_label = best.get('error_undefined_label', False)
            self.state.diag_replay(best.get('diags', ()))
            self.state.expmode = EXP_ASM

            try:
                self.state.pc_instr_start = self.state.pc
                self.state.pc_instr_end   = self.state.pc_instr_start
                _probe_sm_saved    = self.state._pass1_size_mode
                _probe_refs_len    = len(self.state._elf_label_refs_seen)
                _probe_widx_saved  = self.state._elf_current_word_idx
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
                self.state.diag(f" ; pat {pln} {pl} error - Illegal syntax in assemble line or pattern line.{_loc}", set_error=False)
                return 0, [], False, idx

        return idxs, objl, True, idx

    def lineassemble(self, line):
        line = line.replace('\t', ' ').replace('\n', '').replace('\r', '')
        line = StringUtils.reduce_spaces(line)
        line = StringUtils.remove_comment_asm(line)
        if line == '':
            return False
        line = StringUtils.resolve_vliw_escapes(line)

        self.state.check_constraints.clear()

        self.state.symbols = dict(self.state.patsymbols)

        line = self.asm_directive_proc.label_processing(line)

        _vparts = line.replace(VLIW_STOP, VLIW_SEP).split(VLIW_SEP)
        self.state.vcnt = sum(1 for _p in _vparts if _p != '')

        if self.state.elf_objfile and self.state.pas == 2:
            self.state._elf_tracking = True
            self.state._elf_label_refs_seen = []
            self.state._elf_current_word_idx = -1
            self.state._elf_var_to_label = {}
            self.state._elf_capturing_var = None

        try:
            idxs, objl, flag, idx = self.lineassemble2(line, 0)
        finally:
            self.state._elf_tracking = False

        if not flag:
            return False

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

                    rtype = 0
                    _rtype_is_default_guess = False
                    lentry = self.state.labels.get(lname)
                    _is_imported = lentry and len(lentry) > 3 and lentry[3]
                    if lentry and len(lentry) > 4 and lentry[4] is not None:
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

                    if rtype == 0 or first_widx >= len(objl):
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
            print(f"{self.state.current_file} {self.state.ln} {self.state.cl} ", end='')
        f = self.lineassemble(cleaned)
        if _show:
            print("")
        self.state.ln += 1
        return f

    def setpatsymbols(self, pat):
        fresh = {}
        for i in pat:
            if i is None:
                continue
            if len(i) > 0 and i[0] == '.setsym':
                if len(i) >= 2 and i[1]:
                    key = StringUtils.upper(i[1])
                    self.state.symbols = dict(fresh)
                    v, _ = self.expr_eval.expression_pat(i[2], 0)
                    fresh[key] = v
                elif len(i) >= 3 and i[2]:
                    key = StringUtils.upper(i[2])
                    fresh[key] = 0
                continue
            if len(i) > 0 and i[0] == '.clearsym':
                if len(i) >= 3 and i[2] != '':
                    key = StringUtils.upper(i[2])
                    fresh.pop(key, None)
                else:
                    fresh = {}
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
                    with open(self.state.stdin_tmp_path, "wt", encoding="utf-8") as stdintmp:
                        stdintmp.write(af)
                fn = self.state.stdin_tmp_path

            try:
                with open(fn, "rt", encoding="utf-8") as f:
                    af = f.readlines()
            except OSError as e:
                self.state.diag(f" error - cannot open source file '{fn}': {e}",
                                set_error=True)
                return

            for _mtext, _mfile, _mln in self.macro_proc.expand(af, self.state.current_file):
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

        abs64 = _mach_tbl_dw['dwarf_abs']

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

        abbrev = bytearray()
        abbrev += _uleb(1) + _uleb(DW_TAG_compile_unit) + bytes([DW_CHILDREN_yes])
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
        for name, *_rest in sorted(self.state.labels.items()):
            entry = _rest[0]
            val = entry[0]
            is_equ = len(entry) > 2 and entry[2]
            is_imported = len(entry) > 3 and entry[3]
            if is_equ or is_imported:
                continue
            try:
                byte_addr = int(val) * bpw
            except (TypeError, ValueError, OverflowError):
                continue
            sidx, off = _addr_to_sec(byte_addr, entry[1])
            if sidx is None:
                continue
            die += _uleb(2)
            die += name.encode() + b'\x00'
            info_relas.append((len(die), sidx, abs64, off))
            die += _pack_addr(0 if is_rela_dw else off)
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

        ap.add_argument('--osabi', dest='elf_osabi', type=str, default='FreeBSD',
                        help='ELF OSABI value (default: FreeBSD; FreeBSD/Linux, case-insensitive)')
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
            with open(sourcefile, "rt", encoding="utf-8") as f:
                raw = f.readlines()
        except OSError as e:
            self.state.diag(f" error - cannot open source file '{sourcefile}': {e}", set_error=False, force=True)
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
                with open(dest, "wt", encoding="utf-8") as f:
                    f.write(data)
            except OSError as e:
                self.state.diag(f" error - cannot write '{dest}': {e}", set_error=False, force=True)
                return False
        return True

    def _pat_macro_expand_only(self, patternfile, dest):
        self.pat_macro_proc.reset_pass()
        try:
            with open(patternfile, "rt", encoding="utf-8") as f:
                raw = f.readlines()
        except OSError as e:
            self.state.diag(f" error - cannot open pattern file '{patternfile}': {e}",
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
                with open(dest, "wt", encoding="utf-8") as f:
                    f.write(data)
            except OSError as e:
                self.state.diag(f" error - cannot write '{dest}': {e}",
                                set_error=False, force=True)
                return False
        return True

    @staticmethod
    def _normalise_macro_expand_argv(argv):
        _with_arg = {'--osabi', '-b', '-e', '-E', '-i', '-o', '-m'}
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

        osabitbl = {'Linux': 0, 'linux': 0, 'FreeBSD': 9, 'freebsd': 9}

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

        if args.elf_osabi not in osabitbl:
            print(f"warning: unknown --osabi value '{args.elf_osabi}'; "
                  f"valid choices are {list(osabitbl.keys())}. Using 'FreeBSD'.",
                  file=sys.stderr)
        self.state.osabi        = osabitbl.get(args.elf_osabi, 9)
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
            self.setpatsymbols(self.state.pat)

            if self.state.impfile:

                try:
                    with open(self.state.impfile, 'rt', encoding="utf-8") as label_file:
                        raw_lines = label_file.readlines()
                except OSError as e:
                    self.state.diag(f" error - cannot open import file "
                                    f"'{self.state.impfile}': {e}", set_error=True)
                    return False
                for l in raw_lines:
                    fields = l.rstrip('\r\n').split('\t')
                    if len(fields) >= 3:
                        self.imp_label(l)
                for l in raw_lines:
                    fields = l.rstrip('\r\n').split('\t')
                    if len(fields) == 2:
                        self.imp_label(l)

            if self.state.outfile:
                try:
                    os.remove(self.state.outfile)
                except OSError:
                    pass

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

                _initial_vars = list(self.state.vars)

                for relax_iter in range(MAX_RELAX):
                    self.state._relax_optimistic = (relax_iter == 0)
                    self.state.pc = 0
                    self.state.pas = 1
                    self.state.ln = 1
                    self.state.labels = dict(_imported_labels)
                    self.state.sections = {}
                    self.state.export_labels = {}
                    self.state.current_section = '.text'
                    self.state.symbols = dict(self.state.patsymbols)
                    self.state.vars = list(_initial_vars)
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
