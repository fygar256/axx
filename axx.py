#!/usr/bin/env python3

"""
axx general assembler designed and programmed by Taisuke Maekawa
Refactored with OOP design for improved maintainability

axxは特定のCPUに固定されたアセンブラではなく、命令のニーモニックと
バイナリエンコーディングの対応関係を「パターン定義ファイル(.axx)」に
テキストで記述することで、任意の命令セット(x86_64, ARM64, Z80, VLIW風の
独自ISA等)に対応できる汎用アセンブラである。

    axx.py <パターンファイル.axx> <ソースファイル.s> -o <出力.o>

全体の処理の流れは Assembler.run() を参照。詳しい設計の概説は
axx.abs.txt にまとめてある。
"""

from decimal import Decimal, getcontext, localcontext
try:
    import readline  # 対話モードの行編集用(Windows等では無くても動く)
except ImportError:
    pass
import ast
import subprocess
import itertools
import struct
import sys
import os
import math
import re
import tempfile

# run()を複数回呼んでもリラクゼーション収束判定が正しく動くよう、
# モジュールレベルで一度だけ生成する「未確定」を表す番兵オブジェクト。
_RELAXATION_SENTINEL = object()


# 式評価モード: パターンファイル中の式(EXP_PAT)かソース中の式(EXP_ASM)かを区別する。
EXP_PAT = 0
EXP_ASM = 1
exp_typ = 'i'  # 未使用(後方互換のためだけに残存)。実体はAssemblerState.exp_typ。

# [[ ... ]] オプショナルグループを表す内部専用の制御文字(通常の文字とは衝突しない)。
OB = chr(0x90)  # open  [[
CB = chr(0x91)  # close ]]

# 「未定義ラベル」を表す番兵値(2^256-1)。ラベル値は整数として扱われるため、
# 専用の型ではなくこの巨大な数値に重畳する設計になっている。
UNDEF = 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
VAR_UNDEF = 0

# UNDEFへの加減算(UNDEF-base, UNDEF+disp等)も2^256近傍の巨大値になるため、
# 「未定義由来」の値として検出する必要がある。axxが扱う最大値は256bit整数・
# 128bit浮動小数点(quad)なので、正当な定数は2^128未満に収まる。閾値を2^192に
# 取ることで、正当な大きい定数とUNDEF由来の値を確実に区別できる。
_UNDEF_DERIVED_THRESHOLD = 1 << 192

def _is_undef_derived(v):
    """v が UNDEF そのもの、または UNDEF 由来の巨大値かを判定する。"""
    if v == UNDEF:
        return True
    if isinstance(v, int):
        return abs(v) >= _UNDEF_DERIVED_THRESHOLD
    return False

CAPITAL = "ABCDEFGHIJKLMNOPQRSTUVWXYZ"
LOWER = "abcdefghijklmnopqrstuvwxyz"
DIGIT = '0123456789'
XDIGIT = "0123456789ABCDEF"
ALPHABET = LOWER + CAPITAL

# ERRORS[n] は .error::n::cond のようにパターンファイルからエラーコード番号
# 指定で参照される定型メッセージ。
ERRORS = [
    "",
    "Invalid syntax.",
    "Address out of range.",
    "Value out of range.",
    "",
    "Register out of range.",
    "Port number out of range."
]


class AssemblerState:
    """アセンブラ全体で共有される状態(PC・ラベル表・セクション・パス番号等)を
    1つにまとめたコンテナ。各種Manager/Processorクラスはこれを介して協調する。
    """

    def __init__(self):
        # コマンドラインオプションで指定される入出力ファイルパス
        self.outfile = ""
        self.expfile = ""
        self.expfile_elf = ""
        self.impfile = ""

        self.pc = 0             # 現在のプログラムカウンタ(次に書き込むアドレス)
        self.padding = 0
        # $$ / $. の評価に使う: makeobj()呼び出し前に命令の開始・終了アドレスを
        # 確定しておく。$$は_in_binary_list中のみpc_instr_startを返し、
        # それ以外の文脈(.equ等)ではself.pcを返す。
        self.pc_instr_start = 0
        self.pc_instr_end = 0
        self._in_binary_list = False  # makeobj()実行中かどうか

        # ラベル名・シンボル名として使える文字集合
        self.lwordchars = DIGIT + ALPHABET + "_."
        self.swordchars = DIGIT + ALPHABET + "_%$-~&|"

        self.current_section = ".text"
        self.current_file = ""

        self.labels = {}          # {ラベル名: [値, セクション, is_equ, is_imported, reloc_type?]}
        self.sections = {}        # {セクション名: [開始pc, サイズ, ...]}
        self.symbols = {}         # .setsymで登録された現在有効なシンボル
        self.patsymbols = {}      # パターンファイル読込み直後のシンボル(ソース側.setsymの復元用)
        self.export_labels = {}
        self.pat = []              # パターンファイルの全エントリ(PatternFileReaderが構築)

        # VLIW/EPICパケット設定(.vliw::vbits::instbits::templatebits::nopで設定)
        self.vliwinstbits = 41
        self.vliwnop = []
        self.vliwbits = 128
        self.vliwset = []
        self.vliwflag = False
        self.vliwtemplatebits = 0x00
        self.vliwstop = 0
        self.vcnt = 1

        self.expmode = EXP_PAT
        self.error_undefined_label = False
        self.error_label_conflict = False
        # match0()→match()→expression_esc()の経路でパターンマッチ試行中に
        # ラベル未定義エラーを出さないための抑制フラグ。マッチが不成立でも
        # 他の候補パターンを試すだけなので、この時点でのエラー表示は不要。
        self._in_match_attempt = False

        self.align = 16
        self.bts = 8
        self.endian = 'little'
        self.byte = 'yes'
        self.pas = 0             # 現在のパス番号: 0=対話モード, 1=Pass1, 2=Pass2
        self.debug = False

        self.cl = ""              # 現在処理中のソース行(デバッグ表示用)
        self.ln = 0               # 現在の行番号
        self.fnstack = []         # .INCLUDEのネスト用ファイル名スタック
        self.lnstack = []

        self.vars = [VAR_UNDEF for i in range(26)]  # パターンマッチで束縛される変数 a-z

        self.deb1 = ""            # デバッグ用: 直前のmatch()呼び出しの引数(ソース行/パターン)
        self.deb2 = ""

        self.exp_typ: str = 'i'   # 式評価の型モード('i'=整数, 'f'=浮動小数点)

        # True の間、未定義の前方参照ラベルはUNDEFではなく0を返す
        # (Pass1のサイズ見積もり専用モード)。
        self._pass1_size_mode = False

        # 直前のPass1反復で確定した「ラベル名→(pc,section)」。全ラベルが
        # 前回と一致すればリラクゼーション収束とみなす(run()参照)。
        self._pass1_prev_label_pcs = _RELAXATION_SENTINEL

        # 直前のPass1反復で確定した「ラベル名→値」。可変長命令アーキテクチャでは
        # 前方参照ラベルの値で命令サイズが変わるため、未確定の前方参照には
        # この推定値を返して反復ごとに真のレイアウトへ収束させる(get_value参照)。
        self._relax_prev_values = {}

        self.verbose: bool = False

        # stdin入力を保持する一時ファイルのパス(tempfileで生成、run()終了後に削除)。
        self.stdin_tmp_path: str | None = None

        # ELF出力設定
        self.osabi: int = 9       # 9=FreeBSD, 0=Linux
        self.elf_objfile: str = ""
        self.elf_machine: int = 62  # 既定はEM_X86_64

        # ELFリロケーション追跡用。_elf_tracking=Trueの間(Pass2のELF出力時)、
        # makeobj()内でラベルを参照するたびに_elf_label_refs_seen /
        # _elf_var_to_labelへ記録し、write_elf_obj()が.rela.*セクションを構築する。
        self.relocations = []
        self._elf_tracking = False
        self._elf_label_refs_seen = []       # [(label_name, abs_value, word_idx)]
        self._elf_current_word_idx: int = -1  # makeobj()が生成中のバイトインデックス(-1=範囲外)
        self._elf_var_to_label: dict = {}     # {変数名: (label_name, label_value)} (!x直接キャプチャ時)
        self._elf_capturing_var: str | None = None  # match()が!xを評価中の変数名

        self.init_func: str | None = None
        self.fini_func: str | None = None

        # DWARFデバッグ情報生成(-g)用。gen_debug=Trueかつ-o指定時、
        # write_elf_obj()が.debug_info/.debug_abbrev/.debug_lineを生成する。
        self.gen_debug: bool = False
        self.line_map: list = []  # Pass2で記録する (section, pc, file, line) のリスト

        # .check::x::sym1,sym2,... で登録される拘束条件。
        # {変数名: 許可シンボル名リスト}。マッチ成功後・makeobj前に検証し、
        # 変数の値がリスト外ならエラーにする。.clrcheckで解除する。
        self.check_constraints: dict = {}



class StringUtils:
    """パターンファイル・ソースファイルの行を扱う低レベル文字列ユーティリティ
    (空白スキップ、コメント除去、引用符/エスケープ処理等)。全メソッドがstatic。
    """
    
    @staticmethod
    def upper(s):
        """Convert string to uppercase"""
        return ''.join(c.upper() if c in LOWER else c for c in s)
    
    @staticmethod
    def q(s, t, idx):
        """Quick comparison of substring"""
        return StringUtils.upper(s[idx:idx+len(t)]) == StringUtils.upper(t)
    
    @staticmethod
    def skipspc(s, idx):
        """Skip spaces and tabs in string"""
        while idx < len(s) and s[idx] in ' \t':
            idx += 1
        return idx
    
    @staticmethod
    def skip_squote_literal(s, i):
        """シングルクォートリテラルを先読みで消費する共通ヘルパー。
        remove_comment_asm など複数箇所から呼ばれる一元化ロジック。

        消費できた場合は消費後の idx を返す。
        消費できなかった（孤立クォート）場合は i+1 を返す（クォート自体を読み飛ばす）。
        消費したかどうかは (戻り値 > i + 1) で判定できる。

        対応パターン:
          '\\xNN'  ← 16進エスケープ (0〜2桁)
          '\\x'    ← 4文字エスケープ (backslash + char + closeq)
          'x'      ← 通常3文字リテラル
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
    def reduce_spaces(text):
        """Reduce multiple spaces to single space"""
        return re.sub(r'\s{2,}', ' ', text)
    
    @staticmethod
    def remove_comment(l):
        """Remove /* style comments"""
        idx = 0
        while idx < len(l):
            if l[idx:idx+2] == '/*':
                return "" if idx == 0 else l[0:idx]
            idx += 1
        return l
    
    @staticmethod
    def remove_comment_asm(l):
        """Remove ; style comments, but preserve semicolons inside string literals.

        ダブルクォート文字列中の ";" はコメント開始とみなさない。エスケープされた
        引用符 \\" は文字列の開始・終了として数えない。シングルクォート文字
        リテラル('a', '\\x41'等)は skip_squote_literal() で丸ごと消費してから
        走査を続けるため、'a'b'c';comment のように文字リテラルが連続していても
        後続のセミコロンを正しくコメント開始として検出できる。
        """
        in_dquote = False
        i = 0
        while i < len(l):
            ch = l[i]

            if ch == '\\' and in_dquote:
                if i + 1 < len(l):
                    i += 2
                else:
                    i += 1
                continue

            if ch == '"':
                in_dquote = not in_dquote
            elif ch == '\'' and not in_dquote:
                i = StringUtils.skip_squote_literal(l, i)
                continue
            elif ch == ';' and not in_dquote:
                return l[:i].rstrip()

            i += 1
        if in_dquote:
            print(f" warning - unterminated string literal in line: {l!r}", file=sys.stderr)
        return l.rstrip()
    
    @staticmethod
    def get_param_to_spc(s, idx):
        """Get parameter up to space"""
        t = ""
        idx = StringUtils.skipspc(s, idx)
        while idx < len(s) and s[idx] != ' ':
            t += s[idx]
            idx += 1
        return t, idx
    
    @staticmethod
    def get_param_to_eon(s, idx):
        """Get parameter to end of line or !!"""
        t = ""
        idx = StringUtils.skipspc(s, idx)
        while idx < len(s) and s[idx:idx+2] != '!!':
            t += s[idx]
            idx += 1
        return t, idx
    
    @staticmethod
    def get_string(l2):
        """Get quoted string with proper escape sequence handling"""
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
                        print(f" warning - '\\x' escape takes at most 2 hex digits; "
                              f"extra digit(s) treated as literal characters in: {l2!r}", file=sys.stderr)
                    if hex_str:
                        s += chr(int(hex_str, 16))
                    else:
                        s += 'x'
                else:
                    s += next_char
                    idx += 2
            elif l2[idx] == '"':
                return s
            else:
                s += l2[idx]
                idx += 1
        print(f" warning - unterminated string literal: {l2!r}", file=sys.stderr)
        return s


class Parser:
    """アセンブリ行から数値・シンボル名・ラベル名・波括弧式などの
    トークンを切り出す。get_symbol_word()とget_label_word()の
    大文字小文字の扱いの違いに注意(下記docstring参照)。
    """

    def __init__(self, state):
        self.state = state
    
    def get_intstr(self, s, idx):
        """Get integer string from position"""
        fs = ''
        while idx < len(s) and s[idx] in DIGIT:
            fs += s[idx]
            idx += 1
        return fs, idx
    
    def get_floatstr(self, s, idx):
        """Get float string from position.

        単項マイナスは呼び出し元のfactor()が処理するため、ここで数値先頭の
        '-' を消費すると二重解釈になる。ただし '-inf' だけは1トークンとして
        特別扱いする(呼び出し箇所すべてがその前提で動く)。
        """
        if s[idx:idx+4] == '-inf':
            return '-inf', idx + 4
        elif s[idx:idx+3] == 'inf':
            return 'inf', idx + 3
        elif s[idx:idx+3] == 'nan':
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

    def isfloatstr(self,s,idx):
        sidx=idx
        v,idx = self.get_floatstr(s,idx)
        if idx==sidx:
            return False
        else:
            return True

    def get_curlb(self, s, idx):
        """Get curly bracket content.

        閉じブレース '}' が見つからないまま文字列末尾に達した場合は f=False を
        返してエラーを呼び出し元に知らせる(壊れた式をサイレントに評価しない)。
        """
        idx = StringUtils.skipspc(s, idx)
        f = False
        t = ''

        if idx < len(s) and s[idx] == '{':
            idx += 1
            idx = StringUtils.skipspc(s, idx)
            start_idx = idx
            while idx < len(s) and s[idx] != '}':
                t += s[idx]
                idx += 1
            if idx >= len(s):
                print(f" error - missing closing '}}' in expression: '{{{t}'", file=sys.stderr)
                return False, '', len(s)
            idx += 1
            f = True

        return f, t, idx

    def get_symbol_word(self, s, idx):
        """Get symbol word from position.

        戻り値は大文字に正規化する(.setsymシンボル/レジスタ名は大文字小文字を
        区別しないため)。ラベル名を大文字小文字区別で扱うget_label_word()とは
        対照的で、この違いがパターンマッチ時の具体度スコアの前提になっている。
        """
        t = ""
        if idx < len(s) and s[idx] not in DIGIT and s[idx] in self.state.swordchars:
            t = s[idx]
            idx += 1
            while idx < len(s) and s[idx] in self.state.swordchars:
                t += s[idx]
                idx += 1
        return StringUtils.upper(t), idx
    
    def get_label_word(self, s, idx):
        """Get label word from position.

        A trailing ':' is consumed as part of the label definition only when
        it is NOT immediately followed by '=' (which would form ':=' – an
        assignment operator rather than a label terminator).

        ラベル名は大文字・小文字を区別する（case-sensitive）。
        「foo:」と定義した場合、「FOO」では参照できない。
        """
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
        """Get parameters separated by ::"""
        idx = StringUtils.skipspc(l, idx)
        
        if idx >= len(l):
            return "", idx
        
        s = ""
        while idx < len(l):
            if l[idx:idx+2] == '::':
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
    """10進の数値/文字列をIEEE754の32/64/128bitビットパターン(16進文字列)に
    変換する。dbl{}/flt{}/qad{} リテラル記法から呼ばれる。128bit(quad)は
    Pythonのfloatが53bit精度しかないためDecimalで直接ビット演算する。
    """
    
    @staticmethod
    def decimal_to_ieee754_32bit_hex(a):
        """Convert decimal to IEEE 754 32-bit hex.

        Uses Python's struct module for the actual bit conversion so that
        the result is identical to what the hardware would produce.  The
        Decimal-based path was previously incorrect because Decimal.adjusted()
        returns a *decimal* (base-10) exponent, not a binary (base-2) one,
        which produced wrong bit patterns for most non-power-of-10 values.
        """
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
        """Convert decimal to IEEE 754 64-bit hex.

        Uses struct for correctness (same reason as the 32-bit variant).
        """
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
        """Convert decimal to IEEE 754 128-bit (binary128 / quad) hex.

        localcontext()でこの変換中だけDecimalの精度を60桁に上げる
        (プロセス全体の既定精度に副作用を残さないため)。
        """
        with localcontext() as _ctx:
            _ctx.prec = 60
            return IEEE754Converter._decimal_to_ieee754_128bit_hex_impl(a)

    @staticmethod
    def _decimal_to_ieee754_128bit_hex_impl(a):
        """decimal_to_ieee754_128bit_hex の本体（localcontext 内で呼ばれる）。"""
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
            else:
                exponent = biased_exp
                fraction = int((normalized - 1) * (two ** SIGNIFICAND_BITS) + Decimal('0.5'))

            fraction &= (1 << SIGNIFICAND_BITS) - 1

        bits = (sign << 127) | (exponent << SIGNIFICAND_BITS) | fraction
        return f"0x{bits:032X}"

    @staticmethod
    def decimal_eval_expr(text):
        """四則演算式を Decimal で評価して binary128 の整数ビットパターンを返す。

        対応文法:
            expr   = term   (('+' | '-') term)*
            term   = factor (('*' | '/') factor)*
            factor = '(' expr ')' | ['-'] number
            number = decimal リテラル (Decimal で解析)

        シンボル・ラベルを含む式（Decimal で解析できない場合）は
        ValueError を送出する。呼び出し側は except して
        float モードのフォールバックに切り替える。

        prec=60はlocalcontext()に閉じ込め、グローバル精度設定を汚染しない。
        """
        with localcontext() as _ctx:
            _ctx.prec = 60
            return IEEE754Converter._decimal_eval_expr_impl(text)

    @staticmethod
    def _decimal_eval_expr_impl(text):
        """decimal_eval_expr の本体（localcontext 内で呼ばれる）。"""
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
                if s[i:i+len(kw)] == kw:
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
                elif i + 1 < len(s) and s[i] == '/' and s[i+1] == '/':
                    t, i = parse_factor(s, i + 2)
                    if t == 0:
                        raise ZeroDivisionError("floor division by zero in qad{}")
                    v = Decimal(int(v // t))
                elif i < len(s) and s[i] == '/' and (i + 1 >= len(s) or s[i+1] != '/'):
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
    """パターンマッチで束縛される一時変数 a-z (state.vars、26要素の配列)を管理する。
    !e/!!e/d のようなパターンキャプチャがマッチ中にput()で書き込み、
    エンコーディング欄の式評価がget()で読み出す。
    """
    
    def __init__(self, state):
        self.state = state
    
    def get(self, s):
        """Get variable value by letter"""
        c = ord(StringUtils.upper(s))
        return self.state.vars[c - ord('A')]
    
    def put(self, s, v):
        """Set variable value by letter.

        !F/!D経由の値はmatch()側で既にIEEE754整数ビットパターンに変換済み
        なのでint()でよいが、exp_typ='f'モードで生のfloat/Decimalが渡された
        場合はint()で切り捨てず、小数部を持つ値・非有限値(inf/nan)は
        そのままfloatとして保持する。
        """
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
    """ソースコード中のラベル(アドレス・.equ定数)のアドレス・値・セクション
    帰属を管理する。state.labels の各エントリは
    [値, セクション, is_equ, is_imported, reloc_type?] のリスト。
    ラベル名は大文字小文字を区別する(SymbolManagerと対照的)。
    """

    def __init__(self, state):
        self.state = state

    def get_section(self, k):
        """Get label section"""
        self.state.error_undefined_label = False
        try:
            v = self.state.labels[k][1]
        except (KeyError, IndexError):
            v = UNDEF
            self.state.error_undefined_label = True
        return v

    def get_value(self, k):
        """Get label value.

        未定義(前方参照)の場合の扱いは3通り:
          1) pass1で前回反復の確定値があればそれを推定値として返す
             (可変長命令のサイズがリラクゼーションで真の値へ収束していく)。
          2) サイズ見積もり専用モード(_pass1_size_mode)中は0を返す。
          3) それ以外は真に未定義としてUNDEFを返し、エラーを報告する
             (ただしパターンマッチ試行中は後で別候補に置き換わるため抑制する)。
        """
        self.state.error_undefined_label = False
        try:
            v = self.state.labels[k][0]
        except (KeyError, IndexError):
            if self.state.pas == 1 and k in self.state._relax_prev_values:
                return self.state._relax_prev_values[k]
            if self.state._pass1_size_mode:
                return 0
            v = UNDEF
            self.state.error_undefined_label = True
            if not self.state._in_match_attempt and (self.state.pas == 2 or self.state.pas == 0):
                _fn = self.state.current_file or ""
                _ln = self.state.ln
                print(f" error - Label undefined: '{k}'"
                      f"  [{_fn}:{_ln}]", file=sys.stderr)
            return v
        # ELFリロケーション追跡: .equ定数(reloc_type指定なし)はリロケーション不要
        # なので除外し、それ以外のアドレスラベル参照だけを記録する。
        _is_equ = len(self.state.labels[k]) > 2 and self.state.labels[k][2]
        _equ_has_reloc = _is_equ and len(self.state.labels[k]) > 4 and self.state.labels[k][4] is not None
        if self.state._elf_tracking and not self.state.error_undefined_label and (not _is_equ or _equ_has_reloc):
            if self.state._elf_capturing_var is not None:
                # match()が!x式を評価中: 変数名→ラベルの対応を記録する。
                # 同じ変数への2回目以降の書き込みは複合式(label1+label2等)を
                # 意味するのでリロケーション不可としてNoneにする。
                cv = self.state._elf_capturing_var
                if cv not in self.state._elf_var_to_label:
                    self.state._elf_var_to_label[cv] = (k, v)
                else:
                    self.state._elf_var_to_label[cv] = None
            elif self.state._elf_current_word_idx >= 0:
                # makeobj()内でオブジェクトコード式が直接ラベルを参照している
                self.state._elf_label_refs_seen.append(
                    (k, v, self.state._elf_current_word_idx))
        return v
   
    def put_value(self, k, v, s, is_equ=False, reloc_type=None):
        """Set label value.

        is_equ=True  : .equ で定義された定数ラベル
        reloc_type   : ELFリロケーション型（.EQU ::reloctype 用）
        """
        if self.state.pas == 1 or self.state.pas == 0:
            if k in self.state.labels:
                existing = self.state.labels[k]
                old_is_imported = len(existing) > 3 and existing[3]
                if not old_is_imported:
                    self.state.error_label_conflict = True
                    print(f" error - label already defined.", file=sys.stderr)
                    return False
        elif self.state.pas == 2:
            if k not in self.state.labels:
                self.state.error_label_conflict = True
                print(f" error - label '{k}' not defined in pass 1.", file=sys.stderr)
                return False

        if k in self.state.patsymbols:
            print(f" error - '{k}' is a pattern file symbol.", file=sys.stderr)
            return False
        
        self.state.error_label_conflict = False
        existing = self.state.labels.get(k)
        is_imported = (existing is not None and len(existing) > 3 and existing[3])
        
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
    """.setsymで登録される固定シンボル(主にレジスタ名などのエンコーディング用
    定数)を管理する。get()は大文字小文字を無視して解決する
    (LabelManagerのラベル名は逆に大文字小文字を区別する)。
    """

    def __init__(self, state):
        self.state = state

    def get(self, w):
        """Get symbol value. 未登録なら空文字列を返す(呼び出し元で判定する)。"""
        w = w.upper()
        return self.state.symbols.get(w, "")


class ExpressionEvaluator:
    """パターンファイル・ソースファイル中の算術式を評価する再帰下降パーサ。

    優先順位の低い演算子から高い演算子へ、term0_0 -> term0 -> term1 -> ... ->
    term11 -> factor -> factor1 の順に1段ずつ処理を委譲する連鎖になっている
    (各termNメソッドが1つの優先順位レベルに対応する)。expression()が
    公開エントリポイントで、term11から始まる呼び出し連鎖全体をここで一括して
    RecursionError から保護している(深い再帰は"expression nesting too deep"
    エラーとして安全に打ち切る)。

    factor()/factor1()はリテラル・$$/$./#sym・0x.../文字リテラル・
    qad{}/dbl{}/flt{}等の浮動小数点記法・ラベル参照など「これ以上分解できない
    最小単位」を読み取る最下層。xeval()はqad{}等の中で使われる、eval()を
    一切呼ばない安全なミニ評価器(下記docstring参照)。
    """

    def __init__(self, state, var_manager, label_manager, symbol_manager, parser):
        self.state = state
        self.var_manager = var_manager
        self.label_manager = label_manager
        self.symbol_manager = symbol_manager
        self.parser = parser
    
    def nbit(self, l):
        """Count number of bits needed to represent value"""
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
        """Print error message"""
        print(m, file=sys.stderr)
        return -1
    
    def factor(self, s, idx):
        """Parse factor in expression: 単項演算子(-,~,@)・*(expr,expr)の
        バイト抽出・VLIWの!!!(スロット番号)/!!!!(ストップビット)を処理し、
        それ以外はfactor1()(リテラル・$$/$./ラベル等)に委譲する。
        """
        idx = StringUtils.skipspc(s, idx)
        x = 0

        if idx + 4 <= len(s) and s[idx:idx+4] == '!!!!' and self.state.expmode == EXP_PAT:
            x = self.state.vliwstop  # VLIWパケットのストップビット値
            idx += 4
        elif idx + 3 <= len(s) and s[idx:idx+3] == '!!!' and self.state.expmode == EXP_PAT:
            x = self.state.vcnt  # 現在のVLIWスロット番号(0起算)
            idx += 3
        elif idx < len(s) and s[idx] == '-':
            try:
                x, idx = self.factor(s, idx + 1)
            except RecursionError:
                if self.state.pas == 2 or self.state.pas == 0:
                    print(" error - expression nesting too deep (RecursionError) in unary '-'.", file=sys.stderr)
                return 0, idx
            x = -x
        elif idx < len(s) and s[idx] == '~':
            try:
                x, idx = self.factor(s, idx + 1)
            except RecursionError:
                if self.state.pas == 2 or self.state.pas == 0:
                    print(" error - expression nesting too deep (RecursionError) in unary '~'.", file=sys.stderr)
                return 0, idx
            try:
                x = ~int(x)
            except (OverflowError, ValueError):
                if self.state.pas == 2 or self.state.pas == 0:
                    print(f" error - cannot apply bitwise NOT (~) to non-finite float value.", file=sys.stderr)
                x = 0
        elif idx < len(s) and s[idx] == '@':
            try:
                x, idx = self.factor(s, idx + 1)
            except RecursionError:
                if self.state.pas == 2 or self.state.pas == 0:
                    print(" error - expression nesting too deep (RecursionError) in unary '@'.", file=sys.stderr)
                return 0, idx
            x = self.nbit(x)
        elif idx < len(s) and s[idx] == '*':
            if idx+1<len(s) and s[idx+1] == '(':
                x, idx = self.expression(s,idx+2)
                if idx<len(s) and s[idx] == ',':
                    x2,idx = self.expression(s,idx+1)
                    if idx<len(s) and s[idx] == ')':
                        idx+=1
                        try:
                            shift_amount = int(x2) * 8
                        except (OverflowError, ValueError):
                            if self.state.pas == 2 or self.state.pas == 0:
                                print(" error - non-finite byte-extract offset in *(expr, expr).", file=sys.stderr)
                            x = 0
                        else:
                            if shift_amount < 0:
                                if self.state.pas == 2 or self.state.pas == 0:
                                    print(" error - negative byte-extract offset in *(expr, expr).", file=sys.stderr)
                                x = 0
                            else:
                                x = x >> shift_amount
                    else:
                        print(" error - missing ')' in *(expr, expr) expression.", file=sys.stderr)
                        x=0
                else:
                    print(" error - missing ',' in *(expr, expr) expression.", file=sys.stderr)
                    x=0
            else:
                print(" error - expected '(' after '*' in *(expr,expr) expression.", file=sys.stderr)
        else:
            prev_idx = idx
            x, idx = self.factor1(s, idx)
            if (idx == prev_idx
                    and idx < len(s)
                    and s[idx] not in (chr(0), ',', ')', ']', CB, ' ', '\t')
                    and not self.state._in_match_attempt
                    and (self.state.pas == 2 or self.state.pas == 0)):
                print(f" warning - unrecognized token at position {idx} in expression: "
                      f"{s[idx:idx+8]!r} (treated as 0)", file=sys.stderr)
        idx = StringUtils.skipspc(s, idx)
        return x, idx

    def xeval(self, x, _=None):
        """qad{}/dbl{}/flt{}リテラル記法内の式を評価するミニ評価器。

        eval()は一切呼ばず、ASTを解析して許可されたノード種別だけを直接
        解釈する再帰インタプリタとして実装している(検証と評価を分離すると
        「検証漏れ=即コード実行」の脆さが残るため、両者を一体化してある)。
        演算の意味はPythonのeval()と同一('/'はfloat、'//'はfloor)。
        許可されていないノードに遭遇したらValueErrorを送出する。
        """
        def _cc_escape(chars):
            """文字クラス [...] の中で安全なエスケープ文字列を生成する。"""
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

        def replacer(match):
            label_name = match.group(1)
            try:
                val = self.state.labels[label_name][0]
            except (KeyError, IndexError):
                self.state.error_undefined_label = True
                val = 0
                return hex(0)
            if _is_undef_derived(val):
                self.state.error_undefined_label = True
                return hex(0)
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
                return hex(int(val))
            except (TypeError, ValueError, OverflowError):
                self.state.error_undefined_label = True
                return hex(0)

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
                if isinstance(op, ast.Add):      return l + r
                if isinstance(op, ast.Sub):      return l - r
                if isinstance(op, ast.Mult):     return l * r
                if isinstance(op, ast.Div):      return l / r
                if isinstance(op, ast.FloorDiv): return l // r
                if isinstance(op, ast.Mod):      return l % r
                if isinstance(op, ast.Pow):
                    if isinstance(r, int) and r > 1024:
                        raise ValueError("xeval: exponent exceeds 1024")
                    return l ** r
                if isinstance(op, ast.BitAnd):   return l & r
                if isinstance(op, ast.BitOr):    return l | r
                if isinstance(op, ast.BitXor):   return l ^ r
                if isinstance(op, ast.LShift):
                    if isinstance(r, int) and r > 65536:
                        raise ValueError("xeval: shift count exceeds 65536")
                    return l << r
                if isinstance(op, ast.RShift):   return l >> r
                raise ValueError(f"xeval: disallowed operator {type(op).__name__} in '{s}'")
            if isinstance(node, ast.UnaryOp):
                v = _ev(node.operand)
                op = node.op
                if isinstance(op, ast.UAdd):   return +v
                if isinstance(op, ast.USub):   return -v
                if isinstance(op, ast.Invert): return ~v
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
                    if   isinstance(cop, ast.Eq):    ok = left == right
                    elif isinstance(cop, ast.NotEq): ok = left != right
                    elif isinstance(cop, ast.Lt):    ok = left <  right
                    elif isinstance(cop, ast.LtE):   ok = left <= right
                    elif isinstance(cop, ast.Gt):    ok = left >  right
                    elif isinstance(cop, ast.GtE):   ok = left >= right
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
                raise ValueError(f"xeval: disallowed name '{node.id}' in '{s}'")
            raise ValueError(
                f"xeval: disallowed AST node {type(node).__name__} in '{s}'")

        result = _ev(tree)
        if not isinstance(result, (int, float, bool)):
            raise ValueError(f"xeval: unsafe result type {type(result)}")
        return result

    def factor1(self, s, idx):
        """Parse primary factor: '(' expr ')'、文字リテラル('A','\\n'等)、
        $$(命令先頭アドレス)、$.(命令の次のアドレス)、#sym(パターンシンボル値)、
        0x.../0b...、qad{}等の浮動小数点記法、それ以外はラベル参照、を判定する。
        """
        x = 0
        idx = StringUtils.skipspc(s, idx)
        
        if idx >= len(s):
            return x, idx
        
        if s[idx] == '(':
            x, idx = self.expression(s, idx + 1)
            if idx < len(s) and s[idx] == ')':
                idx += 1
            else:
                print(" error - missing closing ')' in expression.", file=sys.stderr)
        elif idx+4<=len(s) and s[idx:idx+4]=="'\\t'":
            x=0x09
            idx+=4
        elif idx+4<=len(s) and s[idx:idx+4]=="'\\''":
            x=ord("'")
            idx+=4
        elif idx+4<=len(s) and s[idx:idx+4]=="'\\\\'":
            x=ord("\\")
            idx+=4
        elif idx+4<=len(s) and s[idx:idx+4]=="'\\n'":
            x=0x0a
            idx+=4
        elif idx+4<=len(s) and s[idx:idx+4]=="'\\0'":
            x=0x00
            idx+=4
        elif idx+4<=len(s) and s[idx:idx+4]=="'\\r'":
            x=0x0d
            idx+=4
        elif idx+4<=len(s) and s[idx:idx+4]=="'\\a'":
            x=0x07
            idx+=4
        elif idx+4<=len(s) and s[idx:idx+4]=="'\\b'":
            x=0x08
            idx+=4
        elif idx+4<=len(s) and s[idx:idx+4]=="'\\f'":
            x=0x0c
            idx+=4
        elif idx+4<=len(s) and s[idx:idx+4]=="'\\v'":
            x=0x0b
            idx+=4
        elif idx+3<=len(s) and s[idx]=='\'' and s[idx+1] != '\\' and s[idx+2]=='\'':
            x=ord(s[idx+1])
            idx+=3
        elif StringUtils.q(s, '$$', idx):
            idx += 2
            x = self.state.pc_instr_start if self.state._in_binary_list else self.state.pc
        elif StringUtils.q(s, '$.', idx):
            idx += 2
            x = self.state.pc_instr_end
        elif StringUtils.q(s, '#', idx):
            idx += 1
            t, idx = self.parser.get_symbol_word(s, idx)
            _sym_val = self.symbol_manager.get(t)
            if _sym_val == "":
                if self.state.pas == 2 or self.state.pas == 0:
                    print(f" error - undefined symbol: '#{t}'", file=sys.stderr)
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
        elif (idx + 3 <= len(s) and s[idx:idx+3] == 'qad'
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
                        except (ValueError, TypeError):
                            if self.state.pas == 2 or self.state.pas == 0:
                                print(f" error - qad{{}}: cannot evaluate expression '{t}'; using 0.", file=sys.stderr)
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
        elif (idx + 3 <= len(s) and s[idx:idx+3] == 'dbl'
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
                    except (OverflowError, ValueError, TypeError, struct.error):
                        if self.state.pas == 2 or self.state.pas == 0:
                            print(f" error - dbl{{}}: cannot convert expression to float64; using 0.", file=sys.stderr)
                        x = 0
        elif (idx + 3 <= len(s) and s[idx:idx+3] == 'flt'
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
                    except (OverflowError, ValueError, TypeError, struct.error):
                        if self.state.pas == 2 or self.state.pas == 0:
                            print(f" error - flt{{}}: cannot convert expression to float32; using 0.", file=sys.stderr)
                        x = 0
        elif (idx + 5 <= len(s) and s[idx:idx+5] == 'enflt'
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
                    if self.state.pas == 2 or self.state.pas == 0:
                        print(" error - enflt{}: expression contains undefined label.", file=sys.stderr)
                    x = enflt(0)
                else:
                    try:
                        x = enflt(int(v) & 0xFFFFFFFF)
                    except (OverflowError, ValueError):
                        if self.state.pas == 2 or self.state.pas == 0:
                            print(" error - enflt{}: non-finite float value; using 0.", file=sys.stderr)
                        x = enflt(0)
        elif (idx + 5 <= len(s) and s[idx:idx+5] == 'endbl'
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
                    if self.state.pas == 2 or self.state.pas == 0:
                        print(" error - endbl{}: expression contains undefined label.", file=sys.stderr)
                    x = endbl(0)
                else:
                    try:
                        x = endbl(int(v) & 0xFFFFFFFFFFFFFFFF)
                    except (OverflowError, ValueError):
                        if self.state.pas == 2 or self.state.pas == 0:
                            print(" error - endbl{}: non-finite float value; using 0.", file=sys.stderr)
                        x = endbl(0)
        elif self.state.exp_typ=='i' and idx < len(s) and s[idx].isdigit():
                fs, idx = self.parser.get_intstr(s, idx)
                x = int(fs)
        elif self.state.exp_typ=='f' and idx < len(s) and (self.parser.isfloatstr(s,idx)):
                fs,idx = self.parser.get_floatstr(s,idx)
                try:
                    x = float(fs) if fs else 0.0
                except ValueError:
                    x = 0.0
        elif (idx < len(s) and
              s[idx] in LOWER and (idx + 1 >= len(s) or s[idx+1] not in self.state.lwordchars)):
            ch = s[idx]
            if idx + 3 <= len(s) and s[idx+1:idx+3] == ':=':
                x, idx = self.expression(s, idx + 3)
                self.var_manager.put(ch, x)
            else:
                x = self.var_manager.get(ch)
                idx += 1
                if (not self.state._in_match_attempt
                        and not self.state._pass1_size_mode
                        and (self.state.pas == 2 or self.state.pas == 0)
                        and _is_undef_derived(x)):
                    self.state.error_undefined_label = True
                    print(f" error - Label undefined: variable '{ch}' contains undefined value"
                          f"  [{self.state.current_file}:{self.state.ln}]", file=sys.stderr)
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
        """Handle exponentiation"""
        x, idx = self.factor(s, idx)
        while idx < len(s) and StringUtils.q(s, '**', idx):
            t, idx = self.factor(s, idx + 2)
            _EXP_MAX = 1024
            try:
                t_int = int(t)
            except (ValueError, OverflowError):
                t_int = 0
            if t_int < 0:
                self.err("Negative exponent in ** expression; result set to 0.")
                x = 0
                break
            if t_int > _EXP_MAX:
                self.err(f"Exponent {t_int} exceeds maximum {_EXP_MAX} in ** expression; result set to 0.")
                x = 0
                break
            x = x ** t_int
            if isinstance(x, float) and x.is_integer():
                x = int(x)
        return x, idx
    
    def term0(self, s, idx):
        """Handle multiplication, division, modulo"""
        x, idx = self.term0_0(s, idx)
        while idx < len(s):
            if s[idx] == '*' and (idx + 1 >= len(s) or s[idx+1] != '*'):
                t, idx = self.term0_0(s, idx + 1)
                x *= t
            elif StringUtils.q(s, '//', idx):
                t, idx = self.term0_0(s, idx + 2)
                if t == 0:
                    self.err("Division by 0 error.")
                    x = 0
                    break
                else:
                    x //= t
            elif s[idx] == '/':
                t, idx = self.term0_0(s, idx + 1)
                if t == 0:
                    self.err("Division by 0 error.")
                    x = 0
                    break
                else:
                    if isinstance(x, int) and isinstance(t, int):
                        q, r = divmod(x, t)
                        x = q if r == 0 else x / t
                    else:
                        x = x / t
            elif s[idx] == '%':
                t, idx = self.term0_0(s, idx + 1)
                if t == 0:
                    self.err("Division by 0 error.")
                    x = 0
                    break
                else:
                    x = x % t
            else:
                break
        return x, idx
    
    def term1(self, s, idx):
        """Handle addition, subtraction"""
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
        """Handle bit shifts"""
        x, idx = self.term1(s, idx)
        _SHIFT_MAX = 65536
        while idx < len(s):
            if StringUtils.q(s, '<<', idx):
                t, idx = self.term1(s, idx + 2)
                try:
                    x = int(x)
                    t = int(t)
                except (ValueError, OverflowError):
                    x = 0; break
                if t < 0:
                    if self.state.pas == 2 or self.state.pas == 0:
                        print(f" error - negative shift count ({t}) in << expression.", file=sys.stderr)
                    x = 0; break
                if t > _SHIFT_MAX:
                    if self.state.pas == 2 or self.state.pas == 0:
                        print(f" error - shift count {t} exceeds maximum {_SHIFT_MAX} in << expression.", file=sys.stderr)
                    x = 0; break
                x <<= t
            elif StringUtils.q(s, '>>', idx):
                t, idx = self.term1(s, idx + 2)
                try:
                    x = int(x)
                    t = int(t)
                except (ValueError, OverflowError):
                    x = 0; break
                if t < 0:
                    if self.state.pas == 2 or self.state.pas == 0:
                        print(f" error - negative shift count ({t}) in >> expression.", file=sys.stderr)
                    x = 0; break
                if t > _SHIFT_MAX:
                    x = 0; break
                x >>= t
            else:
                break
        return x, idx
    
    def _safe_int(self, v, op_name):
        """float/Decimal を安全に int に変換する。非有限値はエラーを出して 0 を返す。"""
        try:
            return int(v)
        except (OverflowError, ValueError):
            if self.state.pas == 2 or self.state.pas == 0:
                print(f" error - non-finite value {v!r} in bitwise '{op_name}' operation; treated as 0.", file=sys.stderr)
            return 0

    def term3(self, s, idx):
        """Handle bitwise AND"""
        x, idx = self.term2(s, idx)
        while idx < len(s) and s[idx] == '&' and (idx + 1 >= len(s) or s[idx+1] != '&'):
            t, idx = self.term2(s, idx + 1)
            x = self._safe_int(x, '&') & self._safe_int(t, '&')
        return x, idx
    
    def term4(self, s, idx):
        """Handle bitwise OR"""
        x, idx = self.term3(s, idx)
        while idx < len(s) and s[idx] == '|' and (idx + 1 >= len(s) or s[idx+1] != '|'):
            t, idx = self.term3(s, idx + 1)
            x = self._safe_int(x, '|') | self._safe_int(t, '|')
        return x, idx
    
    def term5(self, s, idx):
        """Handle bitwise XOR"""
        x, idx = self.term4(s, idx)
        while idx < len(s) and s[idx] == '^':
            t, idx = self.term4(s, idx + 1)
            x = self._safe_int(x, '^') ^ self._safe_int(t, '^')
        return x, idx
    
    def term6(self, s, idx):
        """Handle sign extension.

        修正⑨: t（ビット幅）が非常に大きい場合、`(~0) << t` が Python の
        任意精度整数で天文学的なサイズになり、後続の演算が極端に遅くなる。
        現実的なアセンブラでは符号拡張のビット幅が 128 を超えることはない
        ため、上限を設けてガードする。上限を超えた場合はゼロを返す
        （ビット幅 0 と同じ扱い）。

        Fix ②修正: term0 の '/' 演算が float を返すことがあり、その値が
        term6 まで伝播すると x >> (t-1) でビット演算できず TypeError になる。
        また term5 が float の t を返す場合も同様。演算前に明示的に int へ変換する。
        （term2〜term5 が int(x) を呼んでいるのと同じ方針）
        """
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
                print(f" warning - sign-extension bit width {t} exceeds maximum {_SEXT_MAX_BITS}, result set to 0.", file=sys.stderr)
                x = 0
            else:
                x = (x & ~((~0) << t)) | ((~0) << t if (x >> (t-1) & 1) else 0)
        return x, idx
    
    def term7(self, s, idx):
        """Handle comparisons"""
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
        """Handle logical NOT"""
        if idx + 4 <= len(s) and s[idx:idx+4] == 'not(':
            x, idx = self.expression(s, idx + 3)
            x = 0 if x else 1
        else:
            x, idx = self.term7(s, idx)
        return x, idx
    
    def term9(self, s, idx):
        """Handle logical AND"""
        x, idx = self.term8(s, idx)
        while idx < len(s) and StringUtils.q(s, '&&', idx):
            t, idx = self.term8(s, idx + 2)
            x = 1 if x and t else 0
        return x, idx
    
    def term10(self, s, idx):
        """Handle logical OR"""
        x, idx = self.term9(s, idx)
        while idx < len(s) and StringUtils.q(s, '||', idx):
            t, idx = self.term9(s, idx + 2)
            x = 1 if x or t else 0
        return x, idx
    
    def term11(self, s, idx):
        """Handle ternary operator (right-associative: a?b:c?d:e => a?b:(c?d:e))

        Fix ①: 旧実装は真ブランチ・偽ブランチを必ず両方評価してから
        条件に応じてどちらの値を返すかを選んでいた。
        変数代入（a:=expr）などの副作用を含むブランチでは、
        選ばれなかった側の副作用まで実行されてしまう問題があった。

        修正後: 評価前後で vars をスナップショット/リストアすることで、
        選ばれなかったブランチの変数変更を確実に取り消す。
        パーサーの性質上（終端位置を得るために両ブランチを評価する必要がある）
        式を評価しない訳にはいかないため、副作用のみロールバックする方式を採る。

        Fix ⑦: error_undefined_label フラグも選択されたブランチのものを
        採用するように修正する。旧実装は「最後に評価したブランチ」（偽ブランチ）
        のフラグが残るため、条件が真のとき偽ブランチに未定義ラベルがあると
        誤ってエラーとして報告されていた。

        Fix ⑫ (新規): ELF リロケーション追跡状態（_elf_label_refs_seen /
        _elf_var_to_label）も選ばれなかったブランチの副作用を取り消す。
        旧実装では両ブランチを評価するたびにこれらリストに追記されるため、
        使われない側のリロケーションエントリが混入し、ELF オブジェクトファイルに
        誤ったリロケーションが生成されていた。
        """
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
                err_after_false         = self.state.error_undefined_label
                conflict_after_false    = self.state.error_label_conflict

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
        """Main expression evaluator (internal, s must already be NUL-terminated)"""
        try:
            idx0 = StringUtils.skipspc(s, idx)
            x, idx0 = self.term11(s, idx0)
            return x, idx0
        except RecursionError:
            if self.state.pas == 2 or self.state.pas == 0:
                print(" error - expression nesting too deep (RecursionError).",
                      file=sys.stderr)
            return 0, idx

    def _terminate(self, s):
        """Return s with a single NUL sentinel appended (idempotent)."""
        if not s or s[-1] != chr(0):
            return s + chr(0)
        return s

    def expression_pat(self, s, idx):
        """Expression in pattern mode"""
        prev = self.state.expmode
        self.state.expmode = EXP_PAT
        try:
            return self.expression(self._terminate(s), idx)
        finally:
            self.state.expmode = prev

    def expression_asm(self, s, idx):
        """Expression in assembly mode"""
        prev = self.state.expmode
        self.state.expmode = EXP_ASM
        try:
            return self.expression(self._terminate(s), idx)
        finally:
            self.state.expmode = prev
    

    def expression_esc(self, s, idx, stopchar):
        """Expression with escaped stop character.

        stopchar は「どの括弧にも囲まれていない深さ0の位置」でのみ NUL に置換する。
        ( ) と [ ] を別カウンタで管理していた旧実装は、両者が混在した場合
        （例: `([)]` のような不正なネストや、stopcharが `)` のケース）に
        誤動作する可能性があった。

        修正後はスタック方式で開き括弧の種類を積み、対応する閉じ括弧が来たときだけ
        pop する。スタックが空のときに stopchar が現れた場合のみ NUL に置換する。
        これにより `([])`, `[(])` などの混在パターンも正確に処理できる。

        また、パターンファイルで [[/]] を変換した特殊文字 OB(0x90)/CB(0x91) も
        ブラケットペアとしてスタック追跡の対象に含める（旧実装では未対応だった）。
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
                if stack and OPEN_TO_CLOSE.get(stack[-1]) == ch:
                    stack.pop()
                    result.append(ch)
                else:
                    result.append(ch)
            else:
                result.append(ch)

        replaced = ''.join(result)
        return self.expression(self._terminate(replaced), idx)

    def expression_esc_float(self,s,idx,stopchar):
        prev_typ  = self.state.exp_typ
        prev_mode = self.state.expmode
        self.state.exp_typ = 'f'
        try:
            v,idx = self.expression_esc(s,idx,stopchar)
        finally:
            self.state.exp_typ  = prev_typ
            self.state.expmode  = prev_mode
        return (v,idx)


class BinaryWriter:
    """-b オプション用の素のバイナリファイル出力(ELFではなくワード単位の
    フラットバイナリ)。ワード位置→値の疎な辞書としてバッファし、flush()で
    まとめてバイト列に展開してファイルへ書く。ELFオブジェクト出力は
    Assembler.write_elf_obj() が別途担当する。
    """

    def __init__(self, state):
        self.state = state
        self._buffer = {}

    def _store(self, position, word_val):
        """ワード単位でバッファに格納"""
        if self.state.bts <= 0:
            return
        if position < 0:
            return
        mask = (1 << self.state.bts) - 1
        self._buffer[position] = word_val & mask
    
    def flush(self):
        """バッファをファイルに書き出す"""
        if not self.state.outfile or not self._buffer:
            return

        if self.state.bts <= 0:
            print(f" warning - flush: bts={self.state.bts} is invalid (<=0); "
                  f"output file '{self.state.outfile}' will be empty.", file=sys.stderr)
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
            print(f" error - output size {total_size} bytes exceeds maximum {_MAX_OUTPUT_BYTES}. "
                  f"Check for incorrect .ORG or address values.",
                  file=__import__('sys').stderr)
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

    def fwrite(self, position, x, prt):
        """1ワードをバッファへ書き込み"""
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
        """Output binary without printing"""
        if self.state.pas == 2 or self.state.pas == 0:
            try:
                self.fwrite(a, int(x), 0)
            except (OverflowError, ValueError):
                if self.state.pas == 2 or self.state.pas == 0:
                    print(f" error - non-finite value {x!r} cannot be written as binary word.", file=sys.stderr)

    def outbin(self, a, x):
        """Output binary with printing"""
        if self.state.pas == 2 or self.state.pas == 0:
            _prt = 1 if ((self.state.pas == 2 and self.state.verbose) or self.state.pas == 0) else 0
            try:
                self.fwrite(a, int(x), _prt)
            except (OverflowError, ValueError):
                if self.state.pas == 2 or self.state.pas == 0:
                    print(f" error - non-finite value {x!r} cannot be written as binary word.", file=sys.stderr)
    
    def align_(self, addr):
        """Align address"""
        if self.state.align <= 0:
            return addr
        a = addr % self.state.align
        if a == 0:
            return addr
        return addr + self.state.align - a


class DirectiveProcessor:
    """パターンファイル(.axx)内のディレクティブ(.setsym/.clearsym/.bits/
    .padding/.symbolc/.vliw/epic/.check/.clrcheck等)を処理する。

    各メソッドは「このディレクティブに該当するか」を i[0](パターンエントリの
    最初のフィールド)で判定し、該当しなければ何もせずFalseを返す。
    Assembler.lineassemble2()のパターン走査ループが全メソッドを順に試す
    ことで、ディレクティブ行を通常の命令パターンとして誤ってマッチさせない
    ようにしている。
    """

    def __init__(self, state, expr_eval, binary_writer, symbol_manager=None, parser=None):
        self.state = state
        self.expr_eval = expr_eval
        self.binary_writer = binary_writer
        self.symbol_manager = symbol_manager
        self.parser = parser
    
    def add_avoiding_dup(self, l, e):
        """Add element to list avoiding duplicates"""
        if e not in l:
            l.append(e)
        return l
    
    def clear_symbol(self, i):
        """Clear symbol directive"""
        if len(i) == 0 or i[0] != '.clearsym':
            return False
        
        if len(i) >= 3 and i[2] != '':
            key = StringUtils.upper(i[2])
            self.state.symbols.pop(key, None)
        else:
            self.state.symbols = {}
        
        return True
    
    def set_symbol(self, i):
        """Set symbol directive"""
        if len(i) == 0 or i[0] != '.setsym':
            return False
        
        if len(i) < 2:
            print(f" error - .setsym directive requires at least a symbol name", file=sys.stderr)
            return False
        
        key = StringUtils.upper(i[1])
        if len(i) > 2:
            v, idx = self.expr_eval.expression_pat(i[2], 0)
        else:
            v = 0
        self.state.symbols[key] = v
        return True
    
    def bits(self, i):
        """Bits directive"""
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
                print(f" error - .bits: non-finite bit width value.", file=sys.stderr)
        return True
    
    def paddingp(self, i):
        """Padding directive"""
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
            print(f" error - .padding: non-finite or invalid value; padding unchanged.", file=sys.stderr)
        return True
    
    def symbolc(self, i):
        """Symbol characters directive"""
        if len(i) == 0 or i[0] != '.symbolc':
            return False
        
        if len(i) > 2 and i[2] != '':
            self.state.swordchars = ALPHABET + DIGIT + i[2]
        return True
    
    def vliwp(self, i):
        """VLIW directive"""
        if len(i) == 0 or i[0] != ".vliw":
            return False
        
        if len(i) < 5:
            print(f" error - .vliw directive requires 4 parameters (vliwbits, vliwinstbits, vliwtemplatebits, nop_value), got {len(i)-1}", file=sys.stderr)
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
            print(f" error - .vliw: non-finite parameter value.", file=sys.stderr)
            return False
        self.state.vliwflag = True
        
        l = []
        for _byte_idx in range(self.state.vliwinstbits // 8 + (0 if self.state.vliwinstbits % 8 == 0 else 1)):
            l += [v4 & 0xff]
            v4 >>= 8
        self.state.vliwnop = l
        return True
    
    def epic(self, i):
        """EPIC directive"""
        if len(i) == 0 or StringUtils.upper(i[0]) != "EPIC":
            return False
        
        if len(i) <= 1 or i[1] == '':
            return False
        
        if len(i) < 3:
            print(f" error - EPIC directive requires 2 parameters (indices, pattern), got {len(i)-1}", file=sys.stderr)
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
        """パターンファイルのエラー条件欄(第2フィールド)を処理する。

        書式: cond1;code1, cond2;code2, ... の "cond;code" 組をカンマ区切りで
        並べる。condが真ならcodeをERRORSの索引としてエラーメッセージを
        表示する。戻り値は (triggered: bool, 最後に発火したerror_code)。

        expression_pat()がパース不能な文字で止まりidxが進まない場合は
        無限ループを避けるためそこで走査を打ち切る。
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

            if (self.state.pas == 2 or self.state.pas == 0) and u:
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

        return triggered, error_code

    def check_processing(self, i):
        """.check ディレクティブ (パターンファイル専用)。
        書式: .check::var::sym1,sym2,...
          var  : 小文字1文字の変数名（パターン中の !x などで捕捉される変数）。
          sym* : シンボルテーブルに登録済みのシンボル名（カンマ区切り）。
        """
        if len(i) == 0 or i[0] != '.check':
            return False
        if len(i) < 2 or not i[1].strip():
            print(" error - .check: variable name is not specified.", file=sys.stderr)
            return True
        var = i[1].strip().lower()
        if len(var) != 1 or var not in LOWER:
            print(f" error - .check: variable should be a lower case letter ('{i[1]}').",
                  file=sys.stderr)
            return True
        syms = []
        if len(i) >= 3 and i[2]:
            syms = [s.strip().upper() for s in i[2].split(',') if s.strip()]
        self.state.check_constraints[var] = syms
        return True

    def clrcheck_processing(self, i):
        """.clrcheck ディレクティブ (パターンファイル専用)。
        書式: .clrcheck::var
          var : 小文字1文字の変数名。省略時は全変数の拘束を解除する。
        対象変数の .check 拘束をテーブルから削除する。

        仕様: 変数名はフィールド2 (i[2]) を参照する。
        readpat のフィールドマッピングにより `.clrcheck::var` 形式
        （2フィールド）は i[1]='' / i[2]='var' となるため、
        .setsym 等と同様に引数はフィールド2 に格納される。
        i[2] が空の場合は引数省略とみなし全拘束を解除する。
        """
        if len(i) == 0 or i[0] != '.clrcheck':
            return False
        var_field = i[2].strip() if len(i) >= 3 and i[2] else ''
        if var_field:
            var = var_field.lower()
            if len(var) == 1 and var in LOWER:
                self.state.check_constraints.pop(var, None)
            else:
                print(f" error - .clrcheck: variable should be a lower case letter ('{var_field}').",
                      file=sys.stderr)
        else:
            self.state.check_constraints.clear()
        return True

class PatternMatcher:
    """パターン定義ファイルの1エントリ(マッチパターン文字列)とソース行を
    照合する。match()が実際の照合ロジック、match0()が[[ ]]オプショナル
    グループの全組合せを試す上位ラッパー。

    マッチパターン中の特殊トークン(matchの実装を参照):
        大文字リテラル   入力と大文字小文字を無視して完全一致
        \\x              次の1文字だけをリテラルとして扱う(エスケープ)
        小文字1文字      レジスタ名などの「シンボル」として.setsymの値を
                         大文字小文字無視で解決する(SymbolManager)
        !x               任意の算術式を読み取り変数xに束縛する
                         (ラベル参照は大文字小文字を区別する)
        !!x              factor()単体(式の最初の項のみ)を読み取り束縛する
        !Fx/!Dx/!Qx      浮動小数点式を読み取りIEEE754の32/64/128bit
                         ビットパターンとして整数化して束縛する
        [[ ... ]]        オプショナルグループ(match0が全組合せを試す)
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
        """Remove specified [[ ]] bracket-pair groups from pattern string s.

        OB(開き)が現れるたびに単調増加するシリアル番号を割り当て、スタックで
        対応するCB(閉じ)と紐付ける。これにより [[A]] [[B]] のような兄弟関係の
        グループも別々のシリアル番号を持ち、remove_brackets(t, [1,3]) のように
        「シリアル1番と3番のグループだけ除去する」という個別指定ができる
        (ネスト深度だけをIDにすると兄弟グループを区別できないため)。
        match0() が渡す l は1起算の連番 [1,2,...,cnt] になっている。
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
    
    def match(self, s, t):
        """Match assembly line against pattern.

        1つのソース行に複数のパターンが構文的にマッチしうる場合に備え、
        マッチ成功時は「具体度スコア」を self.last_score に格納する
        (呼び出し元がスコアの異なる複数の成功マッチを比較し、最も具体的な
        ものを採用する。順序非依存マッチングについては
        Assembler.lineassemble2() 参照)。

        スコアはタプル (式キャプチャ数, -リテラル一致文字数, シンボル
        キャプチャ数) で、値が小さいほど具体的(優先度が高い):
          - リテラルのみ  LD A,(HL)  → (0, -n, 0)   最優先
          - シンボル捕捉  LD A,r     → (0, -n, 1)
          - 式キャプチャ  LD A,!e    → (1, -n, 0)   最後

        第2キーにリテラル一致文字数(シンボル数ではなく)を採用しているのが
        重要な点: 式キャプチャ数が同点の2パターンでは、リテラル一致文字数が
        多い方を優先しないと、例えば `ld a,(iy+9)` において
        `LD A,(!n)`(iyまるごと式として飲み込む)が
        `LD s,(IY[[+!d]])`(IYをリテラルで一致させる、より具体的なパターン)
        より先に採用されてしまい、iyが未定義ラベルとしてエラーになる。
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
        
        # 直前に消費したパターン文字が英数字リテラルだったか(単語境界判定用)
        prev_alnum = False

        while True:
            # 単語境界ルール: アセンブリ行側の空白は「トークンの区切り」として
            # 扱う。以前はここで無条件に skipspc() を両側にかけていたため、
            # 空白がマッチに一切影響せず、例えば `jl exit_error` がパターン
            # `JLE !a` にマッチしてしまっていた(JLの後の空白を飛ばして
            # exit_errorの先頭'e'がパターンの'E'に食われ、!aが'xit_error'を
            # 捕捉して未定義エラーになる)。
            # ここでは空白スキップ自体は従来どおり行うが、「行側に空白が
            # あった」「パターン側に空白があった」を記録しておき、英数字
            # リテラル同士の連続(=1つの単語)の途中で行側だけに空白が
            # あった場合はマッチ失敗とする。カンマ・括弧など英数字以外の
            # 前後の空白は従来どおり自由(互換性維持)。
            s_sp = idx_s < len(s) and s[idx_s] in ' \t'
            t_sp = idx_t < len(t) and t[idx_t] in ' \t'
            idx_s = StringUtils.skipspc(s, idx_s)
            idx_t = StringUtils.skipspc(t, idx_t)
            # 行側だけに空白があった位置は単語境界。パターン側にも空白が
            # あればパターンもそこで単語が切れているので境界違反にならない。
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
                    # 英数字リテラルの連続途中に行側の空白は入れない
                    # (JLE が 'jl e...' にマッチするのを防ぐ)
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
                    idx_t = StringUtils.skipspc(t, idx_t+1)
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
                        if self.state.pas == 2 or self.state.pas == 0:
                            print(f" error - !F: cannot convert value to float32; using 0.", file=sys.stderr)
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
                    idx_t = StringUtils.skipspc(t, idx_t+1)
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
                        if self.state.pas == 2 or self.state.pas == 0:
                            print(f" error - !D: cannot convert value to float64; using 0.", file=sys.stderr)
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
                    idx_t = StringUtils.skipspc(t, idx_t+1)
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
                w, idx_s = self.parser.get_symbol_word(s, idx_s)
                v = self.symbol_manager.get(w)
                if v == "":
                    return False
                if a in self.state.check_constraints and w not in self.state.check_constraints[a]:
                    return False
                if idx_s == prev_idx_s:
                    return False
                self.var_manager.put(a, v)
                n_sym += 1
                continue
            elif a == b:
                # 数字リテラル等も英数字リテラル連続の一部として扱う
                # (パターン 'R1' が行 'r 1' にマッチしないように)
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
    
    def match0(self, s, t):
        """Match with optional bracket combinations.

        [[ ]]で囲まれた各グループを「含む/含まない」の全2^cnt通りの組合せで
        match()を試す。各試行の前にvarsをスナップショットし、失敗した試行の
        副作用(変数書き込み・ELF追跡記録)を必ずリストアしてから次の組合せを
        試すので、失敗した組み合わせの影響が後続の試行に漏れない。

        cntが大きいと2^cnt通りの全探索が非現実的な時間になるため、実用上
        20個を超えることはないという前提で_MAX_OPT_GROUPSを設け、超過分は
        「常に含む」扱いにして組合せ爆発を防ぐ。
        """
        t = t.replace('[[', OB).replace(']]', CB)
        cnt = t.count(OB)
        sl = [_ + 1 for _ in range(cnt)]

        _MAX_OPT_GROUPS = 20
        if cnt > _MAX_OPT_GROUPS:
            if self.state.pas == 2 or self.state.pas == 0:
                print(f" warning - pattern has {cnt} optional groups (max {_MAX_OPT_GROUPS}); "
                      f"first {_MAX_OPT_GROUPS} are treated as optional, "
                      f"remainder are always included.", file=sys.stderr)
            sl = sl[:_MAX_OPT_GROUPS]
            cnt = _MAX_OPT_GROUPS

        for i in range(len(sl) + 1):
            ll = list(itertools.combinations(sl, i))
            for j in ll:
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
    """パターン定義ファイル(.axx)を読み込み、"::"区切りで最大6フィールドの
    パターンエントリのリストに変換する。.INCLUDEディレクティブによる
    再帰的な読み込み(循環検出・深度上限つき)にも対応する。
    """

    def __init__(self, parser):
        self.parser = parser

    def readpat(self, fn, base_dir=None, _depth=0, _chain=None):
        """Read pattern file.

        base_dir: 呼び出し元パターンファイルのディレクトリ。
        None のときはプロセスの CWD を基準にする（トップレベル呼び出し）。
        相対パスの fn は base_dir（または CWD）を基準に解決する。

        _chain: 現在の .INCLUDE 連鎖中にある各ファイルの実パス(realpath)集合。
        A→B→A のような循環インクルードを検出するために使う(深度上限だけでは
        循環を検出できず、同じファイルを上限回数まで無駄に読み直してしまう)。

        戻り値: パターンエントリのリスト。ファイルが存在しない・読めない場合は例外を伝播する。
        """
        if fn == '':
            return []

        _MAX_PAT_DEPTH = 50
        if _depth > _MAX_PAT_DEPTH:
            print(f" error - pattern .INCLUDE nesting exceeds {_MAX_PAT_DEPTH}: '{fn}'", file=sys.stderr)
            return []
        
        if base_dir and not os.path.isabs(fn):
            fn = os.path.join(base_dir, fn)

        _real = os.path.realpath(fn)
        if _chain is None:
            _chain = frozenset()
        if _real in _chain:
            print(f" error - circular pattern .INCLUDE detected: '{fn}' "
                  f"(already in include chain). Skipped.", file=sys.stderr)
            return []
        _chain = _chain | {_real}
        
        this_dir = os.path.dirname(os.path.abspath(fn))
        
        p = []
        w = []
        with open(fn, "rt") as f:
            while True:
                l = f.readline()
                if not l:
                    break
                
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
                        print(f" warning - pattern line has more than 6 fields "
                              f"(extra fields ignored): {l[6:]!r}", file=sys.stderr)
                        p = [l[0], l[1], l[2], l[3], l[4], l[5]]
                    w.append(p)
        
        return w
    
    def include_pat(self, l, base_dir=None, _depth=0, _chain=None):
        """Include pattern directive.

        修正7: 旧実装は StringUtils.skipspc で先頭スペースをスキップして
        idx を求めておきながら、ファイル名の抽出に固定オフセット l[8:] を
        使っていた。インデントがある行（例: "  .INCLUDE foo.axx"）では
        l[8:] が .INCLUDE 文字列の途中から始まってしまいファイル名を
        正しく取り出せなかった。
        修正後: l[idx+8:] を使い、スキップ後の先頭位置から 8 文字
        (.INCLUDE) 分進んだ位置からファイル名を読み取る。

        修正5: ファイル名は base_dir を基準に解決する。

        修正⑥: get_string() がファイル名の取得に失敗した場合（クォート抜けなど）
        は空リストをサイレントに返さずエラーを表示する。

        Fix (new): 旧実装は戻り値が [] のとき「.INCLUDE 行でない」と「空ファイルを
        インクルード」の両方を区別できず、後者のとき .INCLUDE 行が通常パターンとして
        再解析される問題があった。
        修正: .INCLUDE にマッチしなかった場合は None を返し、呼び出し元で None と
        空リストを区別する。マッチして空ファイルだった場合は [] を返す。
        """
        idx = StringUtils.skipspc(l, 0)
        i = l[idx:idx+8]
        i = i.upper()
        if i != ".INCLUDE":
            return None
        s = StringUtils.get_string(l[idx+8:])
        if s == "":
            raw = l[idx+8:].strip()
            if raw:
                fallback, _ = StringUtils.get_param_to_spc(raw, 0)
                if fallback:
                    import sys as _sys
                    print(f" warning - .INCLUDE filename not quoted: {fallback!r}. "
                          "Please use double quotes.", file=_sys.stderr)
                    s = fallback
                else:
                    print(f" error - .INCLUDE directive has no filename: {l!r}", file=sys.stderr)
                    return []
            else:
                print(f" error - .INCLUDE directive has no filename: {l!r}", file=sys.stderr)
                return []
        w = self.readpat(s, base_dir, _depth=_depth, _chain=_chain)
        return w


class ObjectGenerator:
    """採用パターンのエンコーディング欄(第3フィールド)からオブジェクトコード
    (バイト値のリスト)を生成する。makeobj()が本体で、前処理として
    e_p()が@@[n,pattern]の繰り返し展開、replace_percent_with_index()が
    %%の連番置換を行う。
    """

    def __init__(self, state, expr_eval, binary_writer):
        self.state = state
        self.expr_eval = expr_eval
        self.binary_writer = binary_writer

    def replace_percent_with_index(self, s):
        """Replace %% with sequential numbers starting from 0.

        @@[4,*(e,%%)] の展開結果 *(e,0),*(e,1),*(e,2),*(e,3) のように、
        繰り返し生成されたコピーの各バイトが何バイト目かを埋め込むために使う。
        '%0' はカウンタを0にリセットする(複数の@@[]が並ぶ場合に使用)。
        """
        count = 0
        result = []
        i = 0
        while i < len(s):
            if i + 1 < len(s) and s[i:i+2] == '%%':
                result.append(str(count))
                count += 1
                i += 2
            elif i+1<len(s) and s[i:i+2] == "%0":
                count = 0
                i += 2
            else:
                result.append(s[i])
                i += 1
        return ''.join(result)

    def e_p(self, pattern):
        """Expand @@[n,pattern] syntax.

        @@[n,expr] は expr を n 回カンマ区切りで並べたものに展開する
        (nは式の中で%%を使い各コピーのバイト位置を参照できる)。例えば
        @@[4,*(e,%%)] は4バイトのリトルエンディアン整数展開に使われる。
        """
        result = []
        has_content = False
        i = 0
        while i < len(pattern):
            if i + 3 <= len(pattern) and pattern[i:i+3] == '@@[':
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
                    rep_pattern = pattern[comma_pos+1:i]
                    
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
                        if self.state.pas == 2 or self.state.pas == 0:
                            print(f" error - @@[n,...]: repeat count {n_int} exceeds maximum {_N_MAX}.", file=sys.stderr)
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
                    result.append('@@[')
                    has_content = True
            else:
                result.append(pattern[i])
                has_content = True
                i += 1
        
        return ''.join(result), not has_content

    def makeobj(self, s):
        """Make object code from expression string.

        エンコーディング欄はカンマ区切りの式の並びで、各式が1バイト(または
        1ワード)を生成する。先頭が ';' の要素は「値が0ならバイト自体を省略
        する」特殊扱いで、例えばx86_64のREXプレフィックスのように条件次第で
        存在したりしなかったりするバイトの表現に使われる
        (;((d&8)?0x41:0) は d&8 が真のときだけ0x41を出力し、偽のときは
        バイトを丸ごと省く)。
        """
        s,z = self.e_p(s)
        s = self.replace_percent_with_index(s)


        s += chr(0)
        idx = 0
        objl = []
        
        if z:
            return objl

        self.state._in_binary_list = True
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

        return objl


class VLIWProcessor:
    """VLIW(Very Long Instruction Word)パケットの組み立てを行う。
    .vliw::vbits::instbits::templatebits::nop で定義される固定ビット幅の
    パケットに、"!!"区切りの複数命令スロットとテンプレートビットを
    詰め込んで1つの固定長パケットにパックする。
    """

    def __init__(self, state, expr_eval, binary_writer):
        self.state = state
        self.expr_eval = expr_eval
        self.binary_writer = binary_writer

    def vliwprocess(self, line, idxs, objl, flag, idx, lineassemble2_func):
        """Process VLIW instruction.

        ソース行を"!!"で区切って各スロットを再帰的にlineassemble2_func()で
        アセンブルし(objs=各スロットのバイト列、idxlst=各スロットの
        パターンインデックス)、スロットの組合せに合うepicテンプレート
        (state.vliwset)を探して、テンプレートビット+各スロットのバイト列を
        vbitsビット幅のパケットに結合する。スロット不足分はvliwnop
        (NOPバイト列)で埋め、超過分は切り詰めて警告する。
        """
        objs = [objl]
        idxlst = [idxs]
        self.state.vliwstop = 0
        
        while True:
            idx = StringUtils.skipspc(line, idx)
            if idx + 4 <= len(line) and line[idx:idx+4] == '!!!!':
                idx += 4
                self.state.vliwstop = 1
                continue
            elif idx + 2 <= len(line) and line[idx:idx+2] == '!!':
                idx += 2
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
            if self.state.pas == 0 or self.state.pas == 2:
                print(" error - vliwinstbits is zero; cannot compute instruction slots.", file=sys.stderr)
            return False
        for k in self.state.vliwset:
            if list(k[0]) == list(idxlst) or self.state.vliwtemplatebits == 0:
                im = 2 ** self.state.vliwinstbits - 1
                tm = 2 ** abs(self.state.vliwtemplatebits) - 1
                pm = 2 ** vbits - 1
                x, idx = self.expr_eval.expression_pat(k[1], 0)
                templ = x & tm
                
                values = []
                nob = vbits // 8 + (0 if vbits % 8 == 0 else 1)
                ibyte = self.state.vliwinstbits // 8 + (0 if self.state.vliwinstbits % 8 == 0 else 1)
                noi = (vbits - abs(self.state.vliwtemplatebits)) // self.state.vliwinstbits
                
                for j in objs:
                    for m in j:
                        values += [m]
                
                target_len = ibyte * noi
                if len(values) > target_len:
                    if self.state.pas == 2 or self.state.pas == 0:
                        print(f"warning-VLIW:{len(values)} values exceed slot capacity {target_len},truncating.", file=sys.stderr)
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
            if self.state.pas == 0 or self.state.pas == 2:
                print(" error - No vliw instruction-set defined.", file=sys.stderr)
            return False
        return True


class AssemblyDirectiveProcessor:
    """ソースファイル(.s)側のディレクティブ(.section/.ascii/.align/.extern/
    .export・.global/.org/ラベル定義等)を処理する。DirectiveProcessorが
    パターンファイル側を担当するのと対になるクラス。各メソッドは
    「このディレクティブに該当するか」を判定し、該当しなければFalseを返す
    (Assembler.lineassemble2()が順に試す)。
    """

    def __init__(self, state, expr_eval, binary_writer, label_manager, parser):
        self.state = state
        self.expr_eval = expr_eval
        self.binary_writer = binary_writer
        self.label_manager = label_manager
        self.parser = parser

    def labelc_processing(self, l, ll):
        """Label characters directive"""
        if l.upper() != '.LABELC':
            return False
        if ll:
            self.state.lwordchars = ALPHABET + DIGIT + ll
        return True

    def label_processing(self, l):
        """Process label definitions: "label:" (アドレスラベル) と
        "label: .equ expr[::reloctype]" (定数ラベル、reloctypeでELF
        リロケーション型を明示指定可能)の両方をここで処理する。
        """
        if l == "":
            return ""
        
        label, idx = self.parser.get_label_word(l, 0)
        lidx = idx
        
        if label != "" and idx > 0 and l[idx-1] == ':':
            idx = StringUtils.skipspc(l, idx)
            e, idx = StringUtils.get_param_to_spc(l, idx)

            if e.upper() == '.EQU':
                reloc_type = None
                expr_part = l[idx:].strip()
                if '::' in expr_part:
                    parts = [p.strip() for p in expr_part.split('::', 1)]
                    expr_part = parts[0]
                    rt_str = parts[1].lower()
                    # x86_64 ELFリロケーション型名 → R_X86_64_* 数値コード
                    rtype_map = {
                        'abs64':1, 'abs32':10, 'abs32s':11, 'abs16':12, 'abs8':14,
                        'pc32':2, 'plt32':4, 'pc16':13, 'pc8':15,
                        'got32':3, 'gotpcrel':9, 'got64':27,
                    }
                    reloc_type = rtype_map.get(rt_str)
                    if reloc_type is None:
                        print(f" warning - unknown reloctype '{rt_str}' in .EQU", file=sys.stderr)

                self.state.error_undefined_label = False
                saved_mode = self.state._pass1_size_mode
                if self.state.pas == 1:
                    self.state._pass1_size_mode = True
                try:
                    u, _ = self.expr_eval.expression_asm(expr_part, 0)
                finally:
                    self.state._pass1_size_mode = saved_mode
                ok = self.label_manager.put_value(label, u, self.state.current_section, is_equ=True, reloc_type=reloc_type)
                return ""
            else:
                ok = self.label_manager.put_value(label, self.state.pc, self.state.current_section, is_equ=False)
                if ok is False:
                    return ""
                return l[lidx:]
        return l
    
    def asciistr(self, l2):
        """Process ASCII string"""
        idx = 0
        if l2 == '' or l2[idx] != '"':
            return False
        idx += 1
        
        while idx < len(l2) and not l2[idx]=='"':
            ch = None
            if l2[idx:idx+2] == '\\0':
                idx += 2
                ch = chr(0)
            elif l2[idx:idx+2] == '\\t':
                idx += 2
                ch = '\t'
            elif l2[idx:idx+2] == '\\n':
                idx += 2
                ch = '\n'
            elif l2[idx:idx+2] == '\\r':
                idx += 2
                ch = '\r'
            elif l2[idx:idx+2] == '\\\\':
                idx += 2
                ch = '\\'
            elif l2[idx:idx+2] == '\\"':
                idx += 2
                ch = '"'
            elif l2[idx:idx+2] in ('\\x', '\\X'):
                idx += 2
                hex_str = ''
                while idx < len(l2) and l2[idx] in '0123456789abcdefABCDEF' and len(hex_str) < 2:
                    hex_str += l2[idx]
                    idx += 1
                if hex_str:
                    ch = chr(int(hex_str, 16))
                else:
                    print(f" error - '\\x' escape requires at least one hex digit in string: {l2!r}", file=sys.stderr)
                    return False
            else:
                ch = l2[idx]
                idx += 1
            if ch is not None:
                self.binary_writer.outbin(self.state.pc, ord(ch))
                self.state.pc += 1
        if idx >= len(l2):
            print(f" warning - unterminated string literal in .ASCII/.ASCIZ: {l2!r}", file=sys.stderr)
        return True
    
    def export_processing(self, l1, l2):
        """Export / Global directive.
        .EXPORT label  -- mark label(s) as globally visible (ELF STB_GLOBAL)
        .GLOBAL label  -- alias for .EXPORT (GAS/NASM compatible syntax)
        Both directives are only active during pass2 and interactive mode.
        """
        if not (self.state.pas == 2 or self.state.pas == 0):
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
    
    def resb_processing(self, l1, l2):
        """Reserve directive - advance PC by N without writing bytes to output buffer.

        .RESB N は N ワード分だけ PC を前進させるが、出力バッファへは何も書き込まない。
        .bss セクションのような未初期化データ領域の確保に使用する。
        出力ファイル上の対応するバイトは flush() 時に padding 値（デフォルト0）で埋められる。

        Fix ①: .ZERO と同様に未定義ラベルと負値をガードする。
        """
        if StringUtils.upper(l1) != '.RESB':
            return False
        x, idx = self.expr_eval.expression_asm(l2, 0)
        if self.state.error_undefined_label:
            if self.state.pas == 2 or self.state.pas == 0:
                print(f" error - .RESB argument contains undefined label.", file=sys.stderr)
            return True
        try:
            x = int(x)
        except (OverflowError, ValueError):
            if self.state.pas == 2 or self.state.pas == 0:
                print(f" error - .RESB argument is non-finite or invalid.", file=sys.stderr)
            return True
        if x < 0:
            print(f" error - .RESB requires a non-negative count, got {x}.", file=sys.stderr)
            return True
        _RESB_MAX = 1 << 28
        if x > _RESB_MAX:
            if self.state.pas == 2 or self.state.pas == 0:
                print(f" error - .RESB count {x} exceeds maximum {_RESB_MAX}.", file=sys.stderr)
            return True
        self.state.pc += x
        return True

    def zero_processing(self, l1, l2):
        """Zero directive

        Fix ②: pass1 でディレクティブの引数に未定義ラベルが含まれると
        expression_asm() が UNDEF (約10^77) を返す。
        このまま range(UNDEF) を実行するとプロセスが事実上フリーズする。
        zero_processing はパターンスキャンの try/except ブロック外で
        直接呼ばれるため、_pass1_size_mode フォールバックも効かない。

        修正: error_undefined_label フラグを確認して UNDEF を早期検出する。
        また負値もガードしてエラーを出す。
        """
        if StringUtils.upper(l1) != ".ZERO":
            return False
        x, idx = self.expr_eval.expression_asm(l2, 0)
        if self.state.error_undefined_label:
            if self.state.pas == 2 or self.state.pas == 0:
                print(f" error - .ZERO argument contains undefined label.", file=sys.stderr)
            return True
        try:
            x = int(x)
        except (OverflowError, ValueError):
            if self.state.pas == 2 or self.state.pas == 0:
                print(f" error - .ZERO argument is non-finite or invalid.", file=sys.stderr)
            return True
        if x < 0:
            print(f" error - .ZERO requires a non-negative count, got {x}.", file=sys.stderr)
            return True
        _ZERO_MAX = 1 << 28
        if x > _ZERO_MAX:
            if self.state.pas == 2 or self.state.pas == 0:
                print(f" error - .ZERO count {x} exceeds maximum {_ZERO_MAX}.", file=sys.stderr)
            return True
        for i in range(x):
            self.binary_writer.outbin2(self.state.pc, 0x00)
            self.state.pc += 1
        return True
    
    def ascii_processing(self, l1, l2):
        """ASCII directive"""
        if StringUtils.upper(l1) != ".ASCII":
            return False
        return self.asciistr(l2)
    
    def asciiz_processing(self, l1, l2):
        """ASCIZ directive"""
        if StringUtils.upper(l1) != ".ASCIZ":
            return False
        if not self.asciistr(l2):
            if self.state.pas == 2 or self.state.pas == 0:
                print(f" error - .ASCIZ requires a quoted string.", file=sys.stderr)
            return False
        self.binary_writer.outbin(self.state.pc, 0x00)
        self.state.pc += 1
        return True
    
    def section_processing(self, l1, l2):
        """Section directive.

        state.sections[名前] は [開始pc, 確定済みサイズ, 直近の再入pc, confirmed]
        のリスト。同じセクションに複数回出入りできるため(.text→.data→.text等)、
        セクションを離れるたびに「今回の滞在分」を確定済みサイズへ加算し、
        再入時のpcを記録しておく。confirmedはENDSECTIONで最終確定したことを示す。
        """
        if StringUtils.upper(l1) != ".SECTION" and StringUtils.upper(l1) != ".SEGMENT":
            return False
        
        if l2 != '':
            old_sec = self.state.current_section
            if old_sec not in self.state.sections:
                self.state.sections[old_sec] = [0, 0, 0, False]
            old_entry = self.state.sections[old_sec]
            _confirmed = len(old_entry) > 3 and old_entry[3]
            if not _confirmed:
                _entry_pc = old_entry[2] if len(old_entry) > 2 else old_entry[0]
                tentative = self.state.pc - _entry_pc
                if tentative > 0:
                    old_entry[1] += tentative

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
                self.state.sections[l2] = [new_start, existing_size, self.state.pc, existing_confirmed]
        return True
    
    def align_processing(self, l1, l2):
        """Align directive"""
        if StringUtils.upper(l1) != ".ALIGN":
            return False
        
        if l2 != '':
            u, idx = self.expr_eval.expression_asm(l2, 0)
            try:
                u_int = int(u)
            except (OverflowError, ValueError):
                print(f" error - .ALIGN argument is non-finite or invalid.", file=sys.stderr)
                return True
            if u_int <= 0:
                print(f" error - .ALIGN requires a positive value, got {u_int}.", file=sys.stderr)
                return True
            self.state.align = u_int
        
        self.state.pc = self.binary_writer.align_(self.state.pc)
        return True
    
    def endsection_processing(self, l1, l2):
        """End section directive"""
        if StringUtils.upper(l1) != ".ENDSECTION" and StringUtils.upper(l1) != ".ENDSEGMENT":
            return False
        if self.state.current_section not in self.state.sections:
            print(f" error - .ENDSECTION without matching .SECTION for '{self.state.current_section}'.", file=sys.stderr)
            return True
        entry = self.state.sections[self.state.current_section]
        start = entry[0]
        entry_pc = entry[2] if len(entry) > 2 else start
        block_size = self.state.pc - entry_pc
        if block_size < 0:
            print(f" warning - ENDSECTION: computed block size {block_size} < 0 for "
                  f"'{self.state.current_section}'; keeping previous size.", file=sys.stderr)
            return True
        new_size = entry[1] + block_size
        self.state.sections[self.state.current_section] = [start, new_size, self.state.pc, True]
        return True
    
    def extern_processing(self, l1, l2):
        """Extern directive with optional reloc type override.
        .EXTERN label::plt32 [, label2::gotpcrel, ...]
        """
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
            if _em_ext == 3:
                reloc_type = 2
            elif _em_ext == 40:
                reloc_type = 3
            elif _em_ext == 183:
                reloc_type = 261
            elif _em_ext == 243:
                reloc_type = 1
            elif _em_ext == 20:
                reloc_type = 26
            else:
                reloc_type = 2
            if idx < len(l2) and l2[idx:idx+2] == '::':
                idx += 2
                rt_start = idx
                while idx < len(l2) and l2[idx] not in ' \t,:' + chr(0):
                    idx += 1
                rt_str = l2[rt_start:idx].strip().lower()

                if rt_str:
                    rtype_map = {
                        'abs64':  1,
                        'abs32':  10,
                        'abs32s': 11,
                        'abs16':  12,
                        'abs8':   14,
                        'pc32':   2,
                        'rel32':  2,
                        'plt32':  4,
                        'pc16':   13,
                        'pc8':    15,
                        'pc64':   24,
                        'got32':    3,
                        'gotpcrel': 9,
                        'got64':   27,
                    }
                    reloc_type = rtype_map.get(rt_str)
                    if reloc_type is None:
                        print(f" warning - unknown reloc type '{rt_str}' in .EXTERN", file=sys.stderr)

            if idx < len(l2) and l2[idx] == ':':
                idx += 1

            existing = self.state.labels.get(label_part)
            if existing is None or not (len(existing) > 3 and existing[3]):
                self.state.labels[label_part] = [0, '.text', False, True, reloc_type]
            elif len(existing) >= 5:
                if reloc_type is not None:
                    existing[4] = reloc_type

            idx = StringUtils.skipspc(l2, idx)
            if idx < len(l2) and l2[idx] == ',':
                idx += 1

        return True

    def org_processing(self, l1, l2):
        """ORG directive"""
        if StringUtils.upper(l1) != ".ORG":
            return False
        u, idx = self.expr_eval.expression_asm(l2, 0)
        if self.state.error_undefined_label:
            if self.state.pas == 2 or self.state.pas == 0:
                print(f" error - .ORG argument contains undefined label.", file=sys.stderr)
            return True
        try:
            u = int(u)
        except (OverflowError, ValueError):
            if self.state.pas == 2 or self.state.pas == 0:
                print(f" error - .ORG argument is non-finite or invalid.", file=sys.stderr)
            return True
        if u < 0:
            if self.state.pas == 2 or self.state.pas == 0:
                print(f" error - .ORG address must be non-negative, got {u}.", file=sys.stderr)
            return True
        if idx + 2 <= len(l2) and l2[idx:idx+2].upper() == ',P':
            if u > self.state.pc:
                _ORG_FILL_MAX = 1 << 28
                fill_count = u - self.state.pc
                if fill_count > _ORG_FILL_MAX:
                    if self.state.pas == 2 or self.state.pas == 0:
                        print(f" error - .ORG ,P fill count {fill_count} exceeds maximum {_ORG_FILL_MAX}.", file=sys.stderr)
                    return True
                for i in range(fill_count):
                    self.binary_writer.outbin2(i + self.state.pc, self.state.padding)
        self.state.pc = u
        return True


class Assembler:
    """アセンブラ全体の制御クラス。他の全Manager/Processorクラスを束ね、
    run()がコマンドライン引数の解釈から2パス+リラクゼーション方式の
    アセンブル、ELF/バイナリ出力までを統括する。

    ソース1行の処理は lineassemble2()(パターン選択+オブジェクト生成) ->
    lineassemble()(ラベル定義・アドレス確定) -> lineassemble0()(1行全体の
    エントリポイント、undo可能な形で状態を確定) という3層構造になっている。
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
        self.pattern_reader = PatternFileReader(self.parser)
        self.obj_gen = ObjectGenerator(self.state, self.expr_eval, self.binary_writer)
        self.vliw_proc = VLIWProcessor(self.state, self.expr_eval, self.binary_writer)
        self.asm_directive_proc = AssemblyDirectiveProcessor(self.state, self.expr_eval, 
                                                             self.binary_writer, self.label_manager, self.parser)
        self._imp_sections: dict = {}
    
    def include_asm(self, l1, l2):
        """Include directive.

        相対パスの.INCLUDEは、現在アセンブル中のファイルのディレクトリを
        基準に解決する(プロセスのCWDではなく)。stdin/対話モードの場合は
        基準ディレクトリが定まらないためCWD基準のままになる。
        """
        if StringUtils.upper(l1) != ".INCLUDE":
            return False
        s = StringUtils.get_string(l2)
        if s:
            if not os.path.isabs(s):
                cur = self.state.current_file
                if cur and cur not in ("(stdin)", ""):
                    base = os.path.dirname(os.path.abspath(cur))
                    s = os.path.join(base, s)
            self.fileassemble(s)
        return True
    
    def lineassemble2(self, line, idx):
        """Assemble line (phase 2).

        1行の処理は大きく2段階:
          (1) ディレクティブ判定 — .section/.ascii/.align/.setsym等の
              各処理メソッドを順に試し、該当すればそこで処理して返る。
          (2) 命令パターンの選択 — どのディレクティブにも該当しなければ、
              パターンファイルの全エントリを走査して最も具体的にマッチする
              パターンを選び、そのエンコーディングでオブジェクトコードを
              生成する(詳細は下の走査ループのコメント参照)。
        """
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
            if not _ok and (self.state.pas == 2 or self.state.pas == 0):
                print(f" error - .ASCII: failed to process string argument: {l2!r}", file=sys.stderr)
            return 0, [], True, idx
        if _l_upper == '.ASCIZ':
            _ok = self.asm_directive_proc.asciiz_processing(l, l2)
            if not _ok and (self.state.pas == 2 or self.state.pas == 0):
                print(f" error - .ASCIZ: failed to process string argument: {l2!r}", file=sys.stderr)
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
        if self.asm_directive_proc.export_processing(l, l2):
            return 0, [], True, idx

        _l_upper = l.upper()
        if _l_upper in ('.SETSYM', '.CLEARSYM'):
            _l2_key, _l2_key_end = StringUtils.get_param_to_spc(l2, 0)
            _l2_val = l2[_l2_key_end:].strip()
            if _l_upper == '.SETSYM':
                _i_src = [l.lower(), _l2_key, _l2_val, '', '', '']
            else:
                _i_src = [l.lower(), '', _l2_key, '', '', '']
        else:
            _i_src = [l, '', l2, '', '', '']
        if self.directive_proc.set_symbol(_i_src):
            self.state.patsymbols = dict(self.state.symbols)
            return 0, [], True, idx
        if self.directive_proc.clear_symbol(_i_src):
            self.state.patsymbols = dict(self.state.symbols)
            return 0, [], True, idx
        if l == "":
            return 0, [], False, idx
        
        of = 0
        se = False
        oerr = False
        pln = 0
        pl = ""
        idxs = 0
        objl = []
        loopflag = True

        # ---- 順序非依存パターン選択 ----
        # 1つのソース行に複数のパターンが構文的にマッチしうる場合(例:
        # "CALL rax" は "CALL !e"(式キャプチャ)にも "CALL d"(レジスタ)にも
        # 一致しうる)、パターンファイル中の全エントリを走査し、マッチした
        # ものの中から PatternMatcher.match() が返す具体度スコアが最小
        # (=最も具体的)なものを採用する。同点ならファイル内で先に出現した
        # ものを採用する。
        #
        # ディレクティブ(.setsym等)はパターン走査中も出現順に副作用を適用
        # し続ける必要があるため、マッチ成功時点のディレクティブ状態を
        # _snap_dirstate() でスナップショットしておき、最終的に採用された
        # パターンのオブジェクト生成時にそのスナップショットを復元する
        # (「そのパターン位置までのディレクティブが適用された状態で生成する」
        # というセマンティクスを保つため)。
        best = None              # 現時点の最良マッチ(スナップショットdict)
        hit_sentinel = False     # 番兵エントリ(i[0]=='')に到達したか
        first_match_exc = None   # 診断用: 走査中に最初に例外を出したパターン

        _DIR_SCALAR_FIELDS = ('endian', 'bts', 'padding', 'swordchars',
                              'vliwbits', 'vliwinstbits', 'vliwtemplatebits',
                              'vliwflag')

        def _snap_dirstate():
            """ディレクティブが変更し得る状態のスナップショットを取る。"""
            snap = {f: getattr(self.state, f) for f in _DIR_SCALAR_FIELDS}
            snap['symbols'] = dict(self.state.symbols)
            snap['check_constraints'] = dict(self.state.check_constraints)
            snap['vliwnop'] = list(self.state.vliwnop)
            snap['vliwset'] = list(self.state.vliwset)
            return snap

        def _restore_dirstate(snap):
            """_snap_dirstate() のスナップショットを復元する。"""
            for f in _DIR_SCALAR_FIELDS:
                setattr(self.state, f, snap[f])
            self.state.symbols = dict(snap['symbols'])
            self.state.check_constraints = dict(snap['check_constraints'])
            self.state.vliwnop = list(snap['vliwnop'])
            self.state.vliwset = list(snap['vliwset'])

        def _lead_caps(pat_text):
            """パターン先頭のリテラル大文字列（ニーモニック部）を空白抜きで返す。

            match() の CAPITAL 分岐は「パターンの大文字は入力と大文字小文字を
            無視して完全一致、空白は両側で読み飛ばし」なので、この前置部分が
            入力行と一致しないパターンは match0() を呼ぶまでもなく不成立と
            判定できる（結果を変えない純粋な高速化）。
            大文字・空白以外の文字（!, 小文字, 記号, [[ 等）が現れた時点で打ち切る。
            """
            p = []
            for ch in pat_text:
                if ch in CAPITAL:
                    p.append(ch)
                elif ch == ' ':
                    continue
                else:
                    break
            return ''.join(p)

        for i in self.state.pat:
            pln += 1
            pl = i
            self.state.vars = [VAR_UNDEF] * 26
            
            if i is None: continue
            if self.directive_proc.set_symbol(i): continue
            if self.directive_proc.clear_symbol(i): continue
            if self.directive_proc.paddingp(i): continue
            if self.directive_proc.bits(i): continue
            if self.directive_proc.symbolc(i): continue
            if self.directive_proc.epic(i): continue
            if self.directive_proc.vliwp(i): continue
            if self.directive_proc.check_processing(i): continue
            if self.directive_proc.clrcheck_processing(i): continue
            
            lw = len([_ for _ in i if _])
            if lw == 0: continue
            
            # Fix: l2(オペランド部)が空のとき l + ' ' + l2 は末尾に余分な
            # 空白を残してしまい、空白の有無を厳密に見るようになった
            # match() で「NOP」のようなオペランド無しパターンが不一致に
            # なってしまう。l2が空の場合は区切りの空白を入れない。
            lin = (l + ' ' + l2) if l2 else l
            lin = StringUtils.reduce_spaces(lin)
            
            if i[0] == '':
                hit_sentinel = True
                if best is None:
                    idxs, _ = self.expr_eval.expression_pat(i[3], 0)
                break
            
            _pfx = _lead_caps(i[0])
            if _pfx:
                _k = 0
                _ok = True
                for _ch in lin:
                    if _ch == ' ':
                        continue
                    if _ch.upper() != _pfx[_k]:
                        _ok = False
                        break
                    _k += 1
                    if _k == len(_pfx):
                        break
                if _k < len(_pfx):
                    _ok = False
                if not _ok:
                    continue

            self.state.error_undefined_label = False
            
            self.state.expmode=EXP_ASM

            saved_vars = self.state.vars[:]
            saved_refs_len = len(self.state._elf_label_refs_seen)
            saved_v2l = dict(self.state._elf_var_to_label)

            try:
                self.state._in_match_attempt = True
                _match_result = self.pattern_matcher.match0(lin, i[0])
            except (ArithmeticError, KeyError, IndexError, ValueError,
                    TypeError, AttributeError, OverflowError,
                    struct.error):
                # 順序非依存化の一環: マッチ試行中の例外は「このパターンは
                # 不成立」として扱い、他パターンの走査を継続する。
                # RecursionError等ここに列挙されない例外は再送出される。
                _match_result = False
                if first_match_exc is None:
                    first_match_exc = (pln, pl)
            finally:
                self.state._in_match_attempt = False

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
                    }
                # 副作用を巻き戻して走査を続ける(より具体的なパターンが
                # ファイル内の後方にあるかもしれないため)。
                self.state.vars = saved_vars
                del self.state._elf_label_refs_seen[saved_refs_len:]
                self.state._elf_var_to_label = saved_v2l

                # リテラル・シンボルキャプチャのみ(式キャプチャ0個)のマッチは
                # これ以上具体的なパターンがあり得ないため走査を打ち切る高速化。
                if score[0] == 0 and score[2] == 0:
                    break

            self.state.error_undefined_label = False

        if best is not None:
            i = best['pat']
            pln = best['pln']
            pl = i
            loopflag = False

            _restore_dirstate(best['dir'])
            self.state.vars = best['vars'][:]
            self.state._elf_label_refs_seen.extend(best['refs'])
            self.state._elf_var_to_label = dict(best['v2l'])
            self.state.error_undefined_label = False
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
                    self.state.error_undefined_label = False
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
        
        if self.state.pas == 2 or self.state.pas == 0:
            _loc = f"  [{self.state.current_file}:{self.state.ln}]"
            if self.state.error_undefined_label:
                print(f" error - Undefined label in expression.{_loc}", file=sys.stderr)
                return 0, [], False, idx
            if se:
                print(f" error - Syntax error.{_loc}", file=sys.stderr)
                return 0, [], False, idx
            if oerr:
                print(f" ; pat {pln} {pl} error - Illegal syntax in assemble line or pattern line.{_loc}", file=sys.stderr)
                return 0, [], False, idx
        
        return idxs, objl, True, idx
    
    def lineassemble(self, line):
        """Assemble single line.

        1行分の前処理をしてlineassemble2()を呼び、結果をVLIWパケットの
        1スロットとしてvliw_proc.vliwprocess()へ渡すか、通常の単一命令として
        バイナリへ書き出すかを振り分ける。前処理には: コメント除去、
        ラベル定義の消費(label_processing)、"!!"区切りでのVLIWスロット数
        (vcnt)の事前カウント、ELFリロケーション追跡の開始/終了が含まれる。
        """
        line = line.replace('\t', ' ').replace('\n', '').replace('\r', '')
        line = StringUtils.reduce_spaces(line)
        line = StringUtils.remove_comment_asm(line)
        if line == '':
            return False

        self.state.check_constraints.clear()

        self.state.symbols = dict(self.state.patsymbols)

        line = self.asm_directive_proc.label_processing(line)

        # "!!"(VLIWスロット区切り)で行を分割し、空でないスロット数を数える
        # (!!!が参照するstate.vcntを、実際のマッチ前に確定させておく必要がある)。
        # ダブルクォート文字列中や'a'のような文字リテラル中の"!!"は
        # 区切りとして扱わない。
        _vparts = []
        _vpart_buf = []
        _in_dq_v = False
        _vi = 0
        while _vi < len(line):
            _vc = line[_vi]
            if _vc == '\\' and _in_dq_v:
                _vpart_buf.append(_vc)
                if _vi + 1 < len(line):
                    _vpart_buf.append(line[_vi + 1])
                _vi += 2
                continue
            if _vc == '"':
                _in_dq_v = not _in_dq_v
                _vpart_buf.append(_vc)
            elif _vc == "'" and not _in_dq_v:
                _new_vi = StringUtils.skip_squote_literal(line, _vi)
                _vpart_buf.extend(list(line[_vi:_new_vi]))
                _vi = _new_vi
                continue
            elif not _in_dq_v and line[_vi:_vi+2] == '!!':
                _vparts.append(''.join(_vpart_buf))
                _vpart_buf = []
                _vi += 2
                continue
            else:
                _vpart_buf.append(_vc)
            _vi += 1
        _vparts.append(''.join(_vpart_buf))
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

        if not self.state.vliwflag or (idx >= len(line) or line[idx:idx+2] != '!!'):
            of = len(objl)
            if self.state.elf_objfile and self.state.pas == 2 and objl and self.state._elf_label_refs_seen:
                bpw_r = max(1, (self.state.bts + 7) // 8)
                sec_name_r = self.state.current_section
                sec_start_w = 0
                if sec_name_r in self.state.sections:
                    sec_start_w = self.state.sections[sec_name_r][0]

                valid_refs = [(ln, aw, wi) for (ln, aw, wi) in self.state._elf_label_refs_seen if wi >= 0]
                valid_refs.sort(key=lambda r: r[2])

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

                _em = self.state.elf_machine
                if _em == 3:
                    _rmap = {4: 2, 2: 20, 1: 22}
                elif _em == 20:
                    _rmap = {4: 26, 2: 4}
                elif _em == 40:
                    _rmap = {4: 3, 2: 4, 1: 8}
                elif _em == 183:
                    _rmap = {8: 257, 4: 261, 2: 262}
                elif _em == 243:
                    _rmap = {8: 2, 4: 1, 2: 34, 1: 33}
                else:
                    _rmap = {8: 1, 4: 2, 2: 12, 1: 14}

                _em_r = self.state.elf_machine
                if _em_r == 3:
                    _pc_rel_types_all = {2, 13, 23}
                elif _em_r == 40:
                    _pc_rel_types_all = {1, 3}
                elif _em_r == 183:
                    _pc_rel_types_all = {260, 261, 262}
                elif _em_r == 20:
                    _pc_rel_types_all = {10, 26}
                elif _em_r == 243:
                    _pc_rel_types_all = set()
                else:
                    _pc_rel_types_all = {2, 4, 9, 13, 15, 24}

                for lname, abs_w, first_widx, num_words in groups:
                    num_bytes = num_words * bpw_r

                    rtype = 0
                    lentry = self.state.labels.get(lname)
                    _is_imported = lentry and len(lentry) > 3 and lentry[3]
                    if lentry and len(lentry) > 4 and lentry[4] is not None:
                        rtype_override = lentry[4]
                        _rtype_field_bytes = {
                            1: 8, 24: 8, 27: 8,
                            10: 4, 11: 4, 2: 4, 4: 4,
                            3: 4, 9: 4,
                            12: 2, 13: 2,
                            14: 1, 15: 1,
                        }
                        expected = _rtype_field_bytes.get(rtype_override)
                        if _is_imported or expected is None or expected == num_bytes:
                            rtype = rtype_override
                        else:
                            rtype = _rmap.get(num_bytes, 0)
                    else:
                        rtype = _rmap.get(num_bytes, 0)

                    if rtype == 0 or first_widx >= len(objl):
                        continue

                    sec_rel = (self.state.pc + first_widx - sec_start_w) * bpw_r

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

                    _field_bits = num_bytes * 8
                    if 0 < _field_bits < 64 and raw_val >= (1 << (_field_bits - 1)):
                        raw_val -= (1 << _field_bits)

                    abs_w_bytes = int(abs_w) * bpw_r

                    if rtype in _pc_rel_types_all:

                        P_asm_bytes = (self.state.pc + first_widx) * bpw_r

                        addend = raw_val - abs_w_bytes + P_asm_bytes

                    else:

                        addend = raw_val - abs_w_bytes

                    self.state.relocations.append((sec_name_r, sec_rel, lname, rtype, addend))

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
            except Exception:
                if self.state.pas == 0 or self.state.pas == 2:
                    print(" error - Some error(s) in vliw definition.", file=sys.stderr)
            return vflag
        
        return True
    
    def lineassemble0(self, line):
        """Assemble line with output"""
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
        """Set pattern symbols.

        パターンファイル中の.setsym/.clearsymを出現順に空の辞書へ適用して
        state.patsymbolsを確定する(ソースファイル側で.setsym/.clearsymが
        現れるとstate.symbolsは一時的に変化するが、次の行の先頭で必ず
        patsymbolsから復元されるので、パターンファイル由来のシンボルだけが
        永続する)。
        """
        fresh = {}
        for i in pat:
            if i is None:
                continue
            if len(i) > 0 and i[0] == '.setsym':
                if len(i) >= 2:
                    key = StringUtils.upper(i[1])
                    if len(i) > 2:
                        self.state.symbols = dict(fresh)
                        v, _ = self.expr_eval.expression_pat(i[2], 0)
                    else:
                        v = 0
                    fresh[key] = v
                continue
            if len(i) > 0 and i[0] == '.clearsym':
                if len(i) >= 3 and i[2] != '':
                    key = StringUtils.upper(i[2])
                    fresh.pop(key, None)
                else:
                    fresh = {}
                continue
        self.state.patsymbols = fresh
        self.state.symbols = dict(fresh)
    
    def fileassemble(self, fn):
        """Assemble file.

        fn == "stdin" になるのは、ソース内で .INCLUDE "stdin" と書かれ、
        include_asm() 経由でこの文字列リテラルがそのまま渡ってきた場合のみ
        (run() のインタラクティブモードではfileassemble()自体を呼ばず、
        stdin入力はlineassemble0()で直接処理する)。この場合はstdin全体を
        一時ファイル(stdin_tmp_path、run()終了時に削除)に書き出してから
        読み直し、リラクゼーション2回目以降は同じ一時ファイルを再利用する。
        """

        _MAX_INCLUDE_DEPTH = 100
        if len(self.state.fnstack) >= _MAX_INCLUDE_DEPTH:
            print(f" error - .INCLUDE nesting depth exceeds {_MAX_INCLUDE_DEPTH}: '{fn}'", file=sys.stderr)
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
                print(f" error - circular .INCLUDE detected: '{fn}' is already being assembled.", file=sys.stderr)
                return

        self.state.fnstack.append(self.state.current_file)
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
                    with open(self.state.stdin_tmp_path, "wt") as stdintmp:
                        stdintmp.write(af)
                fn = self.state.stdin_tmp_path
            
            with open(fn, "rt") as f:
                af = f.readlines()
            
            for i in af:
                self.lineassemble0(i)
        finally:
            self.state.current_file = self.state.fnstack.pop()
            self.state.ln = self.state.lnstack.pop()
    
    def file_input_from_stdin(self):
        """Read input from stdin until EOF (Ctrl+D / piped end).
        Empty lines within the input are preserved correctly."""
        af = ""
        while True:
            line = sys.stdin.readline()
            if line == '':
                break
            af += line.replace('\r', '')
        return af
    
    def imp_label(self, l):
        """Import label from exported TSV format (produced by _write_export).

        Line formats (tab-separated):
          section_name  start_hex  size_hex  [flag]   <- section line (≥3 fields)
          label_name    value_hex                     <- label line (2 fields)

        フィールド数で行種別を判定する。セクション行はself._imp_sectionsに
        記録し、後続のラベル行がアドレス値からセクション名を逆引きできる
        ようにする(呼び出し元のrun()はセクション行を先に全て読み込んでから
        ラベル行を処理する2パス方式で、この逆引き表を確実に完成させる)。
        """
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
            self._imp_sections[sname] = (start, size)
            return True

        if len(fields) == 2:
            label = fields[0]
            if not label:
                return False
            try:
                v = int(fields[1], 16)
            except ValueError:
                return False
            section = '.text'
            for sname, (start, size) in self._imp_sections.items():
                if size > 0 and start <= v < start + size:
                    section = sname
                    break
                if size == 0 and v == start:
                    section = sname
                    break
            self.state.labels[label] = [v, section, False, True]
            return True

        return False
    
    def printaddr(self, pc):
        """Print address"""
        print("%016x: " % pc, end='')

    def _build_dwarf_sections(self, csecs, sec_name_to_idx, bpw, machine):
        """Build DWARF v4 debug sections for an ELF64 relocatable object.

        Returns (prog_sections, rela_list):
          prog_sections : list of (name, data) for SHT_PROGBITS debug sections,
                          in this fixed order:
                              .debug_abbrev, .debug_info, .debug_line
          rela_list     : list of (rela_name, target_name, rela_data) for the
                          .rela.debug_info / .rela.debug_line relocation sections.

        Returns ([], []) when debug generation is disabled or there is nothing
        to describe (no emitted lines).

        Design notes / limitations (intentionally kept simple but valid):
          * One compilation unit (CU) only. DW_AT_stmt_list and the CU's
            debug_abbrev_offset are therefore 0 and need no relocation.
          * Addresses are 8 bytes (the container is always ELFCLASS64 here).
            Each DW_AT_low_pc / DW_LNE_set_address operand is relocated against
            the *section symbol* (STT_SECTION) of the content section it lives
            in, with the in-section byte offset carried in r_addend. Section
            symbols occupy symtab indices 1..ncs in csecs order, so the symbol
            index of a content section equals its 1-based section index.
          * All strings are stored inline (DW_FORM_string), so no .debug_str
            section / relocations are required.
          * The line program emits one sequence per content section that
            contains code, each bounded by DW_LNE_end_sequence at the section
            end. Rows are sorted by address.
        """
        line_map = self.state.line_map
        if not self.state.gen_debug or not line_map:
            return [], []

        import struct as _struct
        _pk = '<' if self.state.endian != 'big' else '>'

        _abs64_map = {
            62:  1,
            183: 257,
            243: 2,
        }
        abs64 = _abs64_map.get(machine, 1)

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

        csec_by_name = {s.name: s for s in csecs}

        def _addr_to_sec(byte_addr):
            """Return (content_idx_1based, in_section_byte_offset) or (None, 0)."""
            for i, s in enumerate(csecs):
                if s.byte_size > 0 and s.byte_start <= byte_addr < s.byte_start + s.byte_size:
                    return i + 1, byte_addr - s.byte_start
            for i, s in enumerate(csecs):
                if s.byte_size == 0 and byte_addr == s.byte_start:
                    return i + 1, 0
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
        die += b'\x00' * 8
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
            sidx, off = _addr_to_sec(byte_addr)
            if sidx is None:
                continue
            die += _uleb(2)
            die += name.encode() + b'\x00'
            info_relas.append((len(die), sidx, abs64, off))
            die += b'\x00' * 8
        die += _uleb(0)

        info_body = (_struct.pack(f'{_pk}H', 4)
                     + _struct.pack(f'{_pk}I', 0)
                     + bytes([8])
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
            w0 = csec.byte_start // bpw if bpw else 0
            first_off = (rows[0][0] - w0) * bpw
            prog += b'\x00' + _uleb(1 + 8) + b'\x02'
            line_relas.append((prog_base + len(prog), sidx, abs64, first_off))
            prog += b'\x00' * 8
            cur_off = first_off
            cur_line = 1
            cur_file = 1
            for (wpc, fidx, ln) in rows:
                byte_off = (wpc - w0) * bpw
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

        def _pack_relas(entries):
            out = bytearray()
            _S64_MAX, _S64_MIN = (1 << 63) - 1, -(1 << 63)
            for (off, sym, rtype, addend) in entries:
                r_info = (sym << 32) | (rtype & 0xffffffff)
                a = addend
                if a > _S64_MAX:
                    a = _S64_MAX
                elif a < _S64_MIN:
                    a = _S64_MIN
                out += _struct.pack(f'{_pk}QQq', off, r_info, a)
            return bytes(out)

        prog_sections = [
            ('.debug_abbrev', abbrev),
            ('.debug_info',   debug_info),
            ('.debug_line',   debug_line),
        ]
        rela_list = []
        if info_relas:
            rela_list.append(('.rela.debug_info', '.debug_info', _pack_relas(info_relas)))
        if line_relas:
            rela_list.append(('.rela.debug_line', '.debug_line', _pack_relas(line_relas)))

        return prog_sections, rela_list

    def write_elf_obj(self, path: str, machine: int = 62) -> None:
        """Write a FreeBSD ELF64 relocatable object file (.o).

        File layout:
          ELF header (64 bytes)
          Content section data  (16-byte aligned each)
          .symtab               (8-byte aligned, 24 bytes/entry)
          .strtab
          .shstrtab
          Section header table  (8-byte aligned, 64 bytes/entry)

        Section header indices:
          0          NULL
          1 … N      Content sections in SECTION-directive order
          N+1        .symtab
          N+2        .strtab
          N+3        .shstrtab  (e_shstrndx)
        """
        import struct as _struct

        bpw = max(1, (self.state.bts + 7) // 8)
        buf = self.binary_writer._buffer

        _is_le    = (self.state.endian != 'big')
        _ei_data  = 1 if _is_le else 2
        _pk       = '<' if _is_le else '>'

        def _pack_ehdr(e_type, e_machine, e_shoff, e_shnum, e_shstrndx):
            ident = (b'\x7fELF'
                     + bytes([2, _ei_data, 1, self.state.osabi])
                     + b'\x00' * 8)
            return ident + _struct.pack(f'{_pk}HHIQQQIHHHHHH',
                e_type, e_machine,
                1,
                0,
                0,
                e_shoff,
                0,
                64,
                0, 0,
                64,
                e_shnum,
                e_shstrndx)

        def _pack_shdr(sh_name, sh_type, sh_flags, sh_addr, sh_offset,
                       sh_size, sh_link, sh_info, sh_addralign, sh_entsize):
            return _struct.pack(f'{_pk}IIQQQQIIQQ',
                sh_name, sh_type, sh_flags, sh_addr, sh_offset,
                sh_size, sh_link, sh_info, sh_addralign, sh_entsize)

        def _pack_sym(st_name, st_info, st_other, st_shndx, st_value, st_size):
            return _struct.pack(f'{_pk}IBBHQQ',
                st_name, st_info, st_other, st_shndx, st_value, st_size)

        def _align_up(x, a):
            return (x + a - 1) & ~(a - 1)

        def _extract(w_start, w_count):
            """Return bytes for word range [w_start, w_start+w_count)."""
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
                        if off + j < n: data[off + j] = tmp & 0xff
                        tmp >>= 8
                else:
                    for j in range(bpw - 1, -1, -1):
                        if off + j < n: data[off + j] = tmp & 0xff
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
                w0 = self.state.sections[sname][0]
                wn = self.state.sections[sname][1]
                if wn == 0:
                    if i + 1 < len(sec_names):
                        w1 = self.state.sections[sec_names[i + 1]][0]
                        wn = max(0, w1 - w0)
                    else:
                        wn = max(0, max_w + 1 - w0) if max_w >= w0 else 0
                byte_start = w0 * bpw
                data = _extract(w0, wn)
                uname = sname.upper()
                if   uname.startswith('.TEXT'):   flags = 0x2 | 0x4
                elif uname.startswith('.DATA'):   flags = 0x2 | 0x1
                elif uname.startswith('.RODATA'): flags = 0x2
                elif uname.startswith('.BSS'):    flags = 0x2 | 0x1
                else:                             flags = 0x2
                csecs.append(_CSec(sname, byte_start, data, flags))

        ncs = len(csecs)

        sec_name_to_idx = {s.name: i + 1 for i, s in enumerate(csecs)}

        from collections import defaultdict as _defaultdict
        rela_entries = _defaultdict(list)
        for (sname, off, sym_name, rtype, addend) in self.state.relocations:
            sidx = sec_name_to_idx.get(sname, 0)
            if sidx:
                rela_entries[sidx].append((off, sym_name, rtype, addend))

        rela_sec_order = [i + 1 for i, s in enumerate(csecs) if (i + 1) in rela_entries]
        nrela = len(rela_sec_order)

        dbg_prog, dbg_rela = self._build_dwarf_sections(
            csecs, sec_name_to_idx, bpw, machine)

        shstrtab = bytearray(b'\x00')
        sec_name_offs = []
        for s in csecs:
            sec_name_offs.append(len(shstrtab))
            shstrtab += s.name.encode() + b'\x00'
        rela_name_offs = []
        for sidx in rela_sec_order:
            rela_name_offs.append(len(shstrtab))
            shstrtab += ('.rela' + csecs[sidx - 1].name).encode() + b'\x00'
        symtab_name_off   = len(shstrtab); shstrtab += b'.symtab\x00'
        strtab_name_off   = len(shstrtab); shstrtab += b'.strtab\x00'
        shstrtab_name_off = len(shstrtab); shstrtab += b'.shstrtab\x00'
        dbg_prog_name_offs = []
        for (dname, _ddata) in dbg_prog:
            dbg_prog_name_offs.append(len(shstrtab))
            shstrtab += dname.encode() + b'\x00'
        dbg_rela_name_offs = []
        for (rname, _tname, _rdata) in dbg_rela:
            dbg_rela_name_offs.append(len(shstrtab))
            shstrtab += rname.encode() + b'\x00'
        shstrtab = bytes(shstrtab)


        def _find_shndx(byte_addr):
            """Return (elf_section_1based, value_within_section).

            Fix 7 (new): byte_addr == 0 のとき、すべてのセクションが
            byte_start > 0 であると範囲外になり SHN_ABS(0xfff1) が返っていた。
            アドレス 0 のラベルは先頭セクションの先頭に属するとみなすのが正しい。
            また byte_size == 0 のセクションが複数あるケースでも
            byte_addr == byte_start の最初の一致を返す。
            """
            for i, s in enumerate(csecs):
                if s.byte_size > 0 and s.byte_start <= byte_addr < s.byte_start + s.byte_size:
                    return i + 1, byte_addr - s.byte_start
            for i, s in enumerate(csecs):
                if s.byte_size == 0 and byte_addr == s.byte_start:
                    return i + 1, 0
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
            is_equ      = len(_lentry[0]) > 2 and _lentry[0][2]
            is_imported = len(_lentry[0]) > 3 and _lentry[0][3]
            if name in export_keys or is_imported:
                continue
            _equ_has_reloc = is_equ and len(_lentry[0]) > 4 and _lentry[0][4] is not None
            if is_equ and not _equ_has_reloc:
                shndx, sym_val = 0xfff1, val
            else:
                byte_addr = val * bpw
                shndx, sym_val = _find_shndx(byte_addr)
            sym_val = int(sym_val) & 0xFFFFFFFFFFFFFFFF
            name_off = len(strtab); strtab += name.encode() + b'\x00'
            syms.append(_pack_sym(name_off, 0x00, 0, shndx, sym_val, 0))

        first_global = len(syms)

        for name, *_lentry in sorted(self.state.labels.items()):
            is_imported = len(_lentry[0]) > 3 and _lentry[0][3]
            if not is_imported or name in export_keys:
                continue
            name_off = len(strtab); strtab += name.encode() + b'\x00'
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
                shndx, sym_val = _find_shndx(byte_addr)
            sym_val = int(sym_val) & 0xFFFFFFFFFFFFFFFF
            name_off = len(strtab); strtab += name.encode() + b'\x00'
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

        def _pack_rela(r_offset, r_sym, r_type, r_addend):
            r_info = (r_sym << 32) | (r_type & 0xffffffff)
            _S64_MAX =  (1 << 63) - 1
            _S64_MIN = -(1 << 63)
            if r_addend > _S64_MAX:
                r_addend = _S64_MAX
            elif r_addend < _S64_MIN:
                r_addend = _S64_MIN
            return _struct.pack(f'{_pk}QQq', r_offset, r_info, r_addend)

        rela_datas = []
        for sidx in rela_sec_order:
            entries = rela_entries[sidx]
            data = b''.join(
                _pack_rela(off, sym_name_to_idx.get(sn, 0), rtype, addend)
                for (off, sn, rtype, addend) in entries
            )
            rela_datas.append(data)

        offset = 64
        sec_offsets = []
        for s in csecs:
            offset = _align_up(offset, 16)
            sec_offsets.append(offset)
            offset += s.byte_size

        rela_offsets = []
        for rd in rela_datas:
            offset = _align_up(offset, 8)
            rela_offsets.append(offset)
            offset += len(rd)

        symtab_off  = _align_up(offset, 8); offset = symtab_off + len(symtab)
        strtab_off  = offset;               offset += len(strtab)
        shstrtab_off = offset;              offset += len(shstrtab)

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
            print(f" error - cannot create ELF output file '{path}': {_e}", file=sys.stderr)
            return
        with _elf_file as f:
            f.write(_pack_ehdr(1, machine, shdr_off, total_shdrs, shstrndx))

            for i, s in enumerate(csecs):
                cur = f.tell()
                f.write(b'\x00' * (sec_offsets[i] - cur))
                f.write(s.data)

            for i, rd in enumerate(rela_datas):
                cur = f.tell()
                f.write(b'\x00' * (rela_offsets[i] - cur))
                f.write(rd)

            cur = f.tell(); f.write(b'\x00' * (symtab_off - cur))
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

            cur = f.tell(); f.write(b'\x00' * (shdr_off - cur))

            f.write(_pack_shdr(0, 0, 0, 0, 0, 0, 0, 0, 0, 0))

            for i, s in enumerate(csecs):
                _sh_type_i = 8 if s.name.upper().startswith('.BSS') else 1
                f.write(_pack_shdr(
                    sec_name_offs[i], _sh_type_i, s.flags, 0,
                    sec_offsets[i], s.byte_size, 0, 0, 16, 0))

            for ri, sidx in enumerate(rela_sec_order):
                f.write(_pack_shdr(
                    rela_name_offs[ri], 4, 0x40, 0,
                    rela_offsets[ri], len(rela_datas[ri]),
                    symtab_shidx, sidx, 8, 24))

            f.write(_pack_shdr(
                symtab_name_off, 2, 0, 0,
                symtab_off, len(symtab),
                symtab_link, first_global, 8, 24))

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
                    dbg_rela_name_offs[i], 4, 0x40, 0,
                    dbg_rela_offsets[i], len(rdata),
                    symtab_shidx, dbg_prog_shndx.get(tname, 0), 8, 24))

        _dbg_msg = f", {len(dbg_prog)} debug section(s)" if dbg_prog else ""
        print(f"elf: wrote {path} ({ncs} section(s), {nrela} rela section(s), "
              f"{len(syms)} symbol(s){_dbg_msg})",
              file=sys.stderr)

    def _build_arg_parser(self):
        """Build and return the argparse.ArgumentParser for axx."""
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
                        choices=['FreeBSD', 'Linux'],
                        help='ELF OSABI value (default: FreeBSD)')
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
                        help='Write ELF64 relocatable object file (.o)')
        ap.add_argument('-m', dest='elf_machine', type=int, default=62,
                        metavar='MACHINE',
                        help='ELF e_machine value (default 62=EM_X86_64; '
                             '183=AArch64, 243=RISC-V, 3=i386, 20=PPC, 40=ARM)')
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
        return ap

    def run(self):
        """Main assembly process.

        全体の流れ: (1)パターンファイル読込み (2)-iラベルインポート
        (3-a)ソースファイル省略時は対話モード(1パス) (3-b)指定時は
        Pass1をリラクゼーション収束するまで繰り返してからPass2を1回実行する
        2パス方式 (4)ELF/バイナリ出力。可変長命令アーキテクチャでは前方参照
        ラベルの値で命令サイズが変わるため、単純な2パスでは不十分であり、
        Pass1を繰り返して真のレイアウトへ収束させる必要がある(詳細は
        下のリラクゼーションループのコメント参照)。
        """
        ap = self._build_arg_parser()

        if len(sys.argv) == 1:
            ap.print_help()
            return True

        args = ap.parse_args()

        osabitbl = {'Linux':0,'linux':0,'FreeBSD':9,'freebsd':9}

        self.state.outfile      = args.outfile
        self.state.expfile      = args.expfile
        self.state.expfile_elf  = args.expfile_elf
        self.state.impfile      = args.impfile
        self.state.elf_objfile  = args.elf_objfile
        self.state.elf_machine  = args.elf_machine

        if args.elf_osabi not in osabitbl:
            print(f"warning: unknown --osabi value '{args.elf_osabi}'; "
                  f"valid choices are {list(osabitbl.keys())}. Using 'FreeBSD'.",
                  file=sys.stderr)
        self.state.osabi        = osabitbl.get(args.elf_osabi, 9)
        self.state.verbose      = args.verbose
        self.state.debug        = args.debug
        self.state.gen_debug    = args.gen_debug

        try:
            self.state.pat = self.pattern_reader.readpat(args.patternfile)
            self.setpatsymbols(self.state.pat)

            if self.state.impfile:
                # 2パス読込み: セクション行(≥3フィールド)を先に全て処理して
                # self._imp_sectionsを完成させてから、ラベル行(2フィールド)を
                # 処理する。順序を混在させるとラベルのセクション逆引きが
                # まだ登録されていないセクションを参照してしまう。
                with open(self.state.impfile, 'rt') as label_file:
                    raw_lines = label_file.readlines()
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
                        line = line.replace("\\\\", "\\")
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
                # ---- リラクゼーション法によるPass1の反復 ----
                # 可変長命令アーキテクチャでは、前方参照ラベルの値によって
                # 命令の符号化サイズ(短形式/長形式)が変わりうる。単純に
                # 前方参照を0と仮定してPass1を1回やるだけでは、Pass2で
                # アドレスがずれる可能性がある。そこでPass1を最大MAX_RELAX回
                # 繰り返し、全ラベルのPC・所属セクションが前回反復と一致
                # したら収束とみなしてPass2に進む。前回反復の確定値は
                # state._relax_prev_valuesに保持し、まだ未確定な前方参照の
                # 推定値としてLabelManager.get_value()が返す。
                MAX_RELAX = 16
                self.state._pass1_prev_label_pcs = _RELAXATION_SENTINEL
                self.state._relax_prev_values = {}

                _imported_labels = dict(self.state.labels)

                _initial_vars = list(self.state.vars)

                for relax_iter in range(MAX_RELAX):
                    self.state.pc = 0
                    self.state.pas = 1
                    self.state.ln = 1
                    self.state.labels = dict(_imported_labels)
                    self.state.sections = {}
                    self.state.export_labels = {}
                    self.state.current_section = '.text'
                    self.state.symbols = dict(self.state.patsymbols)
                    self.state.vars = list(_initial_vars)
                    self.fileassemble(args.sourcefile)

                    _last_sec1 = self.state.current_section
                    if _last_sec1 in self.state.sections:
                        _e1 = self.state.sections[_last_sec1]
                        if not (len(_e1) > 3 and _e1[3]):
                            _ep1 = _e1[2] if len(_e1) > 2 else _e1[0]
                            _blk1 = self.state.pc - _ep1
                            if _blk1 > 0:
                                _e1[1] += _blk1

                    # 収束判定: 全ラベルの(pc, セクション)が前回反復と完全一致すれば
                    # 収束とみなす。UNDEF由来の値が混ざっている間は収束とみなさない
                    # (前後の反復でたまたま同じUNDEFが並ぶ誤判定を避けるため)。
                    current_pcs = {k: (v[0], v[1]) for k, v in self.state.labels.items()}
                    has_undef = any(
                        _is_undef_derived(pc)
                        for k, (pc, _sec) in current_pcs.items()
                        if not (len(self.state.labels[k]) > 2 and self.state.labels[k][2])
                    )
                    # 次反復の前方参照推定に使う値を保存する(UNDEF由来は保存しない、
                    # 前方参照はその分0または前々回値にフォールバックする)。
                    self.state._relax_prev_values = {
                        k: v[0] for k, v in self.state.labels.items()
                        if not _is_undef_derived(v[0])
                    }
                    if (not has_undef
                            and self.state._pass1_prev_label_pcs is not _RELAXATION_SENTINEL
                            and current_pcs == self.state._pass1_prev_label_pcs):
                        if self.state.debug:
                            print(f"Pass1 relaxation converged after {relax_iter + 1} iteration(s)", file=sys.stderr)
                        break
                    self.state._pass1_prev_label_pcs = current_pcs
                else:
                    # Fix: 収束しなかった場合は単なる警告ではなく致命的エラーとする。
                    # 収束前提のPass2アドレスは信頼できないため、以降のPass2実行・
                    # 出力書き込みを行わずここで打ち切る(誤ったバイナリを黙って
                    # 出力しないため)。
                    print(" error - Pass1 relaxation did not converge after {0} iterations.".format(MAX_RELAX),
                          file=sys.stderr)
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

                # Pass1↔Pass2整合チェックの安全網用に、Pass1で確定したラベル
                # アドレス(is_equ=Falseのもの、つまり定数ではなくアドレス)を
                # スナップショットしておく。Pass2完了後にこれと突き合わせ、
                # ずれがあれば「リラクゼーション未収束のためアドレスが確定
                # していない」ことを明示的なエラーとして報告する
                # (検査なしで誤ったバイナリを黙って出力しないため)。
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
                self.fileassemble(args.sourcefile)

                _last_sec = self.state.current_section
                if _last_sec in self.state.sections:
                    _e = self.state.sections[_last_sec]
                    _confirmed = len(_e) > 3 and _e[3]
                    if not _confirmed:
                        _entry_pc = _e[2] if len(_e) > 2 else _e[0]
                        _block = self.state.pc - _entry_pc
                        if _block > 0:
                            _e[1] += _block

                _drift = []
                for k, p2 in ((kk, vv[0]) for kk, vv in self.state.labels.items()
                              if not (len(vv) > 2 and vv[2])):
                    p1 = _pass1_final_addrs.get(k)
                    if p1 is not None and p1 != p2 and not _is_undef_derived(p2):
                        _drift.append((k, p1, p2))
                if _drift:
                    print(" error - address mismatch between pass1 and pass2 "
                          f"({len(_drift)} label(s)); output addresses are UNRELIABLE.",
                          file=sys.stderr)
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

            self.binary_writer.flush()

            if self.state.elf_objfile:
                self.write_elf_obj(self.state.elf_objfile, self.state.elf_machine)

            if self.state.expfile_elf and self.state.expfile:
                print(f"warning: both -e '{self.state.expfile}' and -E '{self.state.expfile_elf}' specified; "
                      f"exporting plain format to -e and ELF format to -E separately.",
                      file=sys.stderr)

            def _write_export(path, elf):
                h   = list(self.state.export_labels.items())
                key = list(self.state.sections.keys())
                _bpw_export = max(1, (self.state.bts + 7) // 8)
                with open(path, 'wt') as label_file:
                    for i in key:
                        if i == '.text' and elf == 1:
                            flag = 'AX'
                        elif i == '.data' and elf == 1:
                            flag = 'WA'
                        else:
                            flag = ''
                        w_start = self.state.sections[i][0]
                        w_count = self.state.sections[i][1]
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
                                _RTYPE_REVERSE = {
                                    1:  'abs64',
                                    10: 'abs32',
                                    11: 'abs32s',
                                    12: 'abs16',
                                    14: 'abs8',
                                    2:  'pc32',
                                    4:  'plt32',
                                    13: 'pc16',
                                    15: 'pc8',
                                    24: 'pc64',
                                    3:  'got32',
                                    9:  'gotpcrel',
                                    27: 'got64',
                                }
                                reloc_type_str = _RTYPE_REVERSE.get(lentry[4], '')
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
    """Main entry point"""
    assembler = Assembler()
    return assembler.run()


if __name__ == '__main__':
    ok = main()
    exit(0 if ok else 1)
