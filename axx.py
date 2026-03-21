#!/usr/bin/env python3
# cython: language_level=3

"""
axx general assembler designed and programmed by Taisuke Maekawa
Refactored with OOP design for improved maintainability
"""

from decimal import Decimal, getcontext
import readline
import string
import subprocess
import itertools
import struct
import sys
import os
import math
import re
import tempfile

# Expression mode constants
EXP_PAT = 0
EXP_ASM = 1
# exp_typ は後方互換のため残存するが、実際には AssemblerState.exp_typ を使用する。
# このグローバルは参照されなくなった（修正1対応）。
exp_typ = 'i'  # deprecated – do not use directly

# Special bracket characters
OB = chr(0x90)  # open double bracket
CB = chr(0x91)  # close double bracket

# Constants
UNDEF = 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
VAR_UNDEF = 0

# Character sets
CAPITAL = "ABCDEFGHIJKLMNOPQRSTUVWXYZ"
LOWER = "abcdefghijklmnopqrstuvwxyz"
DIGIT = '0123456789'
XDIGIT = "0123456789ABCDEF"
ALPHABET = LOWER + CAPITAL

# Error messages
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
    """Global state container for the assembler"""
    
    def __init__(self):
        # File paths
        self.outfile = ""
        self.expfile = ""
        self.expfile_elf = ""
        self.impfile = ""
        
        # Program counter and padding
        self.pc = 0
        self.padding = 0
        
        # Character sets for parsing
        self.lwordchars = DIGIT + ALPHABET + "_."
        self.swordchars = DIGIT + ALPHABET + "_%$-~&|"
        
        # Current context
        self.current_section = ".text"
        self.current_file = ""
        
        # Data structures
        self.labels = {}
        self.sections = {}
        self.symbols = {}
        self.patsymbols = {}
        self.export_labels = {}
        self.pat = []
        
        # VLIW configuration
        self.vliwinstbits = 41
        self.vliwnop = []
        self.vliwbits = 128
        self.vliwset = []
        self.vliwflag = False
        self.vliwtemplatebits = 0x00
        self.vliwstop = 0
        self.vcnt = 1
        
        # Expression mode and errors
        self.expmode = EXP_PAT
        self.error_undefined_label = False
        self.error_label_conflict = False
        
        # Assembly configuration
        self.align = 16
        self.bts = 8
        self.endian = 'little'
        self.byte = 'yes'
        self.pas = 0
        self.debug = False
        
        # Current line info
        self.cl = ""
        self.ln = 0
        self.fnstack = []
        self.lnstack = []
        
        # Variables (a-z)
        self.vars = [VAR_UNDEF for i in range(26)]
        
        # Debug strings
        self.deb1 = ""
        self.deb2 = ""
        
        # Expression type mode: 'i' = integer, 'f' = float.
        # スレッドセーフかつ再入安全にするため、モジュールレベルのグローバルではなく
        # インスタンス変数として保持する。変更箇所では必ず try/finally で元に戻す。
        self.exp_typ: str = 'i'

        # Pass 1 size-estimation mode:
        # True の間は未定義ラベルを UNDEF ではなく 0 として返す。
        # forward参照があっても makeobj がサイズを正しく計算できるようにするため。
        self._pass1_size_mode = False

        # リラクゼーション用: 直前のpass1でのラベルアドレス記録
        # {label_name: pc_value} の辞書。収束判定に使う。
        self._pass1_prev_label_pcs = None

        # stdin 入力を保持する一時ファイルパス。
        # 固定名 "axx.tmp" の代わりに tempfile で生成したパスを使うことで
        # 複数インスタンスの同時実行時の競合を防ぐ。
        # None のとき未生成。run() 終了後に cleanup される。
        self.stdin_tmp_path: str | None = None

        # ELF OSABI (FreeBSD==9,Linux==0)
        self.osabi: int = 9 # default OSABI==9(FreeBSD)
        # ELF relocatable object file output (-r / -m options)
        self.elf_objfile: str = ""
        self.elf_machine: int = 62   # default EM_X86_64

        # ELF relocation tracking
        # relocations: list of (section_name, sec_rel_byte_offset, sym_name, reloc_type, addend)
        self.relocations = []
        # _elf_tracking: True while assembling an instruction during pass2 ELF output
        self._elf_tracking = False

        # _elf_label_refs_seen: リロケーション候補。各エントリ: (label_name, abs_value, word_idx)
        # word_idx は makeobj() 内で参照が発生した objl インデックス（0 以上）。
        self._elf_label_refs_seen = []  # [(label_name, abs_word_value, word_idx)]

        # makeobj() が現在生成中のワードインデックス（objl への追加前の len(objl)）。
        # -1 は makeobj() の外（センチネル値）。
        self._elf_current_word_idx: int = -1

        # _elf_var_to_label: match() で !x がラベルを直接キャプチャしたとき
        # 変数名 → (label_name, label_value) を記録する辞書。
        # makeobj() 内で変数を読む際にリロケーション情報の生成に使う。
        # ラベル値そのものではなく式（label+offset等）でキャプチャした場合は
        # この辞書には登録しない（_elf_capturing_var が None に戻る前に複数の
        # get_value() 呼び出しが起きたケースは登録を取り消す）。
        self._elf_var_to_label: dict = {}  # {var_letter: (label_name, label_value)}

        # _elf_capturing_var: match() が !x 式を評価している最中にセットされる変数名。
        # get_value() はこれを見て _elf_var_to_label を更新する。
        # None のとき「キャプチャ中でない」。
        self._elf_capturing_var: str | None = None


class StringUtils:
    """Utility functions for string manipulation"""
    
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
        """Skip spaces in string"""
        while idx < len(s) and s[idx] == ' ':
            idx += 1
        return idx
    
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

        エスケープされた引用符 \\" は文字列の開始・終了とみなさない。
        これにより "hello \\"world\\"; not a comment" のような入力で
        誤ってコメント開始位置がずれる問題を修正。
        """
        in_string = False
        i = 0
        while i < len(l):
            ch = l[i]
            if ch == '\\' and in_string:
                # エスケープシーケンス: 次の文字をスキップ
                # 境界チェックを追加
                if i + 1 < len(l):
                    i += 2
                else:
                    i += 1  # 末尾の孤立したバックスラッシュ
                continue
            if ch == '"':
                in_string = not in_string
            elif ch == ';' and not in_string:
                return l[:i].rstrip()
            i += 1
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
                # エスケープシーケンスを処理
                next_char = l2[idx + 1]
                if next_char == '"':
                    s += '"'
                elif next_char == '\\':
                    s += '\\'
                elif next_char == 'n':
                    s += '\n'
                elif next_char == 't':
                    s += '\t'
                elif next_char == 'r':
                    s += '\r'
                else:
                    # その他のエスケープはそのまま保持
                    s += next_char
                idx += 2
            elif l2[idx] == '"':
                return s
            else:
                s += l2[idx]
                idx += 1
        return s


class Parser:
    """Parser for extracting tokens and strings from assembly code"""
    
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
        """Get float string from position"""
        if s[idx:idx+4] == '-inf':
            return '-inf', idx + 4
        elif s[idx:idx+3] == 'inf':
            return 'inf', idx + 3
        elif s[idx:idx+3] == 'nan':
            return 'nan', idx + 3
        else:
            fs = ''
            # Accept leading minus sign only at the start
            if idx < len(s) and s[idx] == '-':
                fs += '-'
                idx += 1
            while idx < len(s) and s[idx] in "0123456789.":
                fs += s[idx]
                idx += 1
            # Accept exponent part: e/E followed by optional sign and digits
            if idx < len(s) and s[idx] in "eE":
                fs += s[idx]
                idx += 1
                if idx < len(s) and s[idx] in "+-":
                    fs += s[idx]
                    idx += 1
                while idx < len(s) and s[idx] in "0123456789":
                    fs += s[idx]
                    idx += 1
            return fs, idx

    def isfloatstr(self,s,idx):
        sidx=idx
        v,idx = self.get_floatstr(s,idx)
        if idx==sidx:
            return False
        else:
            return True

    def get_curlb(self, s, idx):
        """Get curly bracket content"""
        idx = StringUtils.skipspc(s, idx)
        f = False
        t = ''
        
        if idx < len(s) and s[idx] == '{':
            idx += 1
            f = True
            idx = StringUtils.skipspc(s, idx)
            while idx < len(s) and s[idx] != '}':
                t += s[idx]
                idx += 1
            idx = StringUtils.skipspc(s, idx)
            if idx < len(s) and s[idx] == '}':
                idx += 1
        
        return f, t, idx

    def get_symbol_word(self, s, idx):
        """Get symbol word from position"""
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
        """
        t = ""
        if idx < len(s) and (s[idx] == '.' or (s[idx] not in DIGIT and s[idx] in self.state.lwordchars)):
            t = s[idx]
            idx += 1
            while idx < len(s) and s[idx] in self.state.lwordchars:
                t += s[idx]
                idx += 1

            # Consume ':' only when it is a label terminator, not part of ':='
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
    float_value = struct.unpack('f', struct.pack('I', a))[0]
    return float_value

def endouble(a):
    double_value = struct.unpack('d', struct.pack('Q', a))[0]
    return double_value

# enflt / endbl は enfloat / endouble の別名。
# factor1() および xeval() の safe_env から参照されるが、
# これまで定義が存在せず NameError でクラッシュしていた。
enflt = enfloat
endbl = endouble

class IEEE754Converter:
    """IEEE 754 floating point conversion utilities"""
    
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

        fval = float(Decimal(a))
        bits = struct.unpack('I', struct.pack('f', fval))[0]
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

        fval = float(Decimal(a))
        bits = struct.unpack('Q', struct.pack('d', fval))[0]
        return f"0x{bits:016X}"
    
    @staticmethod
    def decimal_to_ieee754_128bit_hex(a):
        """Convert decimal to IEEE 754 128-bit (binary128 / quad) hex.

        Python's struct does not support binary128, so we implement the
        conversion with the Decimal module at high precision.
        The binary exponent is found by integer bit-length of the scaled
        integer approximation, which avoids any float-precision loss.
        Precision is set to 60 digits to cover the 112-bit significand
        (~34 significant decimal digits) with rounding headroom.
        """
        BIAS = 16383
        SIGNIFICAND_BITS = 112
        EXPONENT_BITS = 15

        getcontext().prec = 60  # 112ビット仮数部(約34桁)を十分カバー

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

            # 2進指数を純粋なDecimal演算で求める:
            #   d に 2^SIGNIFICAND_BITS を掛けて整数化し、
            #   そのbit長から指数を逆算する。float変換は一切使わない。
            scaled = int(d * (two ** SIGNIFICAND_BITS))
            if scaled == 0:
                exp_unbiased = -(BIAS - 1)
            else:
                # bit_length() - 1 = floor(log2(scaled))
                exp_unbiased = scaled.bit_length() - 1 - SIGNIFICAND_BITS

            scale = two ** exp_unbiased
            normalized = d / scale

            # 念のため境界を確認・微調整
            while normalized >= 2:
                exp_unbiased += 1
                normalized /= 2
            while normalized < 1:
                exp_unbiased -= 1
                normalized *= 2

            biased_exp = exp_unbiased + BIAS

            if biased_exp <= 0:
                # サブノーマル数
                exponent = 0
                shift = two ** (1 - BIAS - SIGNIFICAND_BITS)
                fraction = int(d / shift + Decimal('0.5'))
            else:
                exponent = biased_exp
                # 仮数部ビット（最近接丸め）
                fraction = int((normalized - 1) * (two ** SIGNIFICAND_BITS) + Decimal('0.5'))

            fraction &= (1 << SIGNIFICAND_BITS) - 1

        bits = (sign << 127) | (exponent << SIGNIFICAND_BITS) | fraction
        return f"0x{bits:032X}"


class VariableManager:
    """Manages assembler variables (a-z)"""
    
    def __init__(self, state):
        self.state = state
    
    def get(self, s):
        """Get variable value by letter"""
        c = ord(StringUtils.upper(s))
        return self.state.vars[c - ord('A')]
    
    def put(self, s, v):
        """Set variable value by letter"""
        if StringUtils.upper(s) in CAPITAL:
            c = ord(StringUtils.upper(s))
            self.state.vars[c - ord('A')] = int(v)

class LabelManager:
    """Manages assembly labels"""
    
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
        """Get label value"""
        self.state.error_undefined_label = False
        try:
            v = self.state.labels[k][0]
        except (KeyError, IndexError):
            # Pass1 サイズ推定モード中は 0 を返す（値は不正だがリスト長=命令サイズは正しく求まる）
            v = 0 if self.state._pass1_size_mode else UNDEF
            self.state.error_undefined_label = True
            return v
        # ELF リロケーション追跡
        # is_equ=True の定数ラベルはリロケーション不要なので追跡しない
        _is_equ = len(self.state.labels[k]) > 2 and self.state.labels[k][2]
        if self.state._elf_tracking and not self.state.error_undefined_label and not _is_equ:
            if self.state._elf_capturing_var is not None:
                # match() が !var 式を評価中: 変数→ラベル名の対応を記録。
                # 1 回の変数キャプチャで get_value() が 2 回以上呼ばれた場合
                # （複合式: label1 + label2 など）は信頼できないので登録を取り消す。
                cv = self.state._elf_capturing_var
                if cv not in self.state._elf_var_to_label:
                    self.state._elf_var_to_label[cv] = (k, v)
                else:
                    # 2 回目以降 → 複合式なのでリロケーション不可としてマーク
                    self.state._elf_var_to_label[cv] = None
            elif self.state._elf_current_word_idx >= 0:
                # makeobj() 内でオブジェクト式がラベルを直接参照
                self.state._elf_label_refs_seen.append(
                    (k, v, self.state._elf_current_word_idx))
        return v
    
    def put_value(self, k, v, s, is_equ=False):
        """Set label value.

        is_equ=True  : .equ で定義された定数ラベル（リロケーション不要）
        is_equ=False : アドレスラベル（リロケーション対象になり得る）
        """
        if self.state.pas == 1 or self.state.pas == 0:
            # パス1/インタラクティブ: 同名ラベルの二重定義はエラー
            if k in self.state.labels:
                self.state.error_label_conflict = True
                print(f" error - label already defined.")
                return False
        elif self.state.pas == 2:
            # パス2: パス1で登録されていないラベルが新出現した場合はエラー
            if k not in self.state.labels:
                self.state.error_label_conflict = True
                print(f" error - label '{k}' not defined in pass 1.")
                return False

        if StringUtils.upper(k) in self.state.patsymbols:
            print(f" error - '{k}' is a pattern file symbol.")
            return False
        
        self.state.error_label_conflict = False
        self.state.labels[k] = [v, s, is_equ]
        return True

    def printlabels(self):
        result = {}
        for key, value in self.state.labels.items():
            num = value[0]
            section = value[1]
            result[key] = [hex(num), section]
        print(result)
        
class SymbolManager:
    """Manages assembler symbols"""
    
    def __init__(self, state):
        self.state = state
    
    def get(self, w):
        """Get symbol value"""
        w = w.upper()
        return self.state.symbols.get(w, "")


class ExpressionEvaluator:
    """Evaluates mathematical expressions"""
    
    def __init__(self, state, var_manager, label_manager, symbol_manager, parser):
        self.state = state
        self.var_manager = var_manager
        self.label_manager = label_manager
        self.symbol_manager = symbol_manager
        self.parser = parser
    
    def nbit(self, l):
        """Count number of bits needed to represent value"""
        b = 0
        r = abs(l)  # negative values would loop forever with arithmetic right shift
        while r:
            r >>= 1
            b += 1
        return b
    
    def err(self, m):
        """Print error message"""
        print(m)
        return -1
    
    def factor(self, s, idx):
        """Parse factor in expression"""
        idx = StringUtils.skipspc(s, idx)
        x = 0
        
        if idx + 4 <= len(s) and s[idx:idx+4] == '!!!!' and self.state.expmode == EXP_PAT:
            x = self.state.vliwstop
            idx += 4
        elif idx + 3 <= len(s) and s[idx:idx+3] == '!!!' and self.state.expmode == EXP_PAT:
            x = self.state.vcnt
            idx += 3
        elif idx < len(s) and s[idx] == '-':
            x, idx = self.factor(s, idx + 1)
            x = -x
        elif idx < len(s) and s[idx] == '~':
            x, idx = self.factor(s, idx + 1)
            x = ~int(x)
        elif idx < len(s) and s[idx] == '@':
            x, idx = self.factor(s, idx + 1)
            x = self.nbit(x)
        elif idx < len(s) and s[idx] == '*':
            if idx+1<len(s) and s[idx+1] == '(':
                x, idx = self.expression(s,idx+2)
                if idx<len(s) and s[idx] == ',':
                    x2,idx = self.expression(s,idx+1)
                    if idx<len(s) and s[idx] == ')':
                        idx+=1
                        x=x>>(x2*8)
                    else:
                        x=0
                else:
                    x=0
            else:
                x=0
        else:
            x, idx = self.factor1(s, idx)
        
        idx = StringUtils.skipspc(s, idx)
        return x, idx

    def xeval(self, x, _=None):
        escaped = re.escape(self.state.lwordchars)
        pattern = rf":([{escaped}]+)(?=[^{escaped}]|$)"

        def replacer(match):
            label_name = match.group(1)
            try:
                val = self.state.labels[label_name][0]
            except (KeyError, IndexError):
                self.state.error_undefined_label = True
                val = 0
                return hex(0)
            # ELF追跡: get_value() と同じ分岐方針で記録する。
            # .equ 定義ラベルはリロケーション不要なので除外する。
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
            return hex(val)

        s = re.sub(pattern, replacer, x)
        safe_env = {
            "__builtins__": {},
            "enfloat": enfloat,
            "endouble": endouble,
            "enflt": enflt,
            "endbl": endbl,
        }
        # eval の第3引数にも空辞書を渡すことでローカルスコープも封鎖する。
        # クラス継承チェーン経由のエスケープを防ぐため、
        # 評価結果が数値型であることを確認する。
        result = eval(s, safe_env, {})
        if not isinstance(result, (int, float, bool)):
            raise ValueError(f"xeval: unsafe result type {type(result)}")
        return result

    def factor1(self, s, idx):
        """Parse primary factor"""
        x = 0
        idx = StringUtils.skipspc(s, idx)
        
        if idx >= len(s):
            return x, idx
        
        if s[idx] == '(':
            x, idx = self.expression(s, idx + 1)
            if idx < len(s) and s[idx] == ')':
                idx += 1
        elif idx+4<len(s) and s[idx:idx+4]=="'\\t'":
            x=0x09
            idx+=4
        elif idx+4<len(s) and s[idx:idx+4]=="'\\''":
            x=ord("'")
            idx+=4
        elif idx+4<len(s) and s[idx:idx+4]=="'\\\\'":
            x=ord("\\")
            idx+=4
        elif idx+4<len(s) and s[idx:idx+4]=="'\\n'":
            x=0x0a
            idx+=4
        elif idx+3<len(s) and s[idx]=='\'' and s[idx+2]=='\'':
            x=ord(s[idx+1])
            idx+=3
        elif StringUtils.q(s, '$$', idx):
            idx += 2
            x = self.state.pc
        elif StringUtils.q(s, '#', idx):
            idx += 1
            t, idx = self.parser.get_symbol_word(s, idx)
            x = self.symbol_manager.get(t)
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
        elif idx + 3 <= len(s) and s[idx:idx+3] == 'qad':
            idx += 3
            idx = StringUtils.skipspc(s, idx)
            if idx < len(s) and s[idx] == '{':
                fs, idx = self.parser.get_floatstr(s, idx + 1)
                h = IEEE754Converter.decimal_to_ieee754_128bit_hex(fs)
                x = int(h, 16)
                if idx < len(s) and s[idx] == '}':
                    idx += 1
        elif idx + 3 <= len(s) and s[idx:idx+3] == 'dbl':
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
                    v = float(self.xeval(t, None))
                    x = int.from_bytes(struct.pack('>d', v), "big")
        elif idx + 3 <= len(s) and s[idx:idx+3] == 'flt':
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
                    v = float(self.xeval(t, None))
                    x = int.from_bytes(struct.pack('>f', v), "big")
        elif idx + 5 <= len(s) and s[idx:idx+5] == 'enflt':
            idx += 5
            f, t, idx = self.parser.get_curlb(s, idx)
            if f:
                v, _ = self.expression(t + chr(0), 0)
                x = enflt(int(v))
        elif idx + 5 <= len(s) and s[idx:idx+5] == 'endbl':
            idx += 5
            f, t, idx = self.parser.get_curlb(s, idx)
            if f:
                v, _ = self.expression(t + chr(0), 0)
                x = endbl(int(v))
        elif self.state.exp_typ=='i' and idx < len(s) and s[idx].isdigit():
                fs, idx = self.parser.get_intstr(s, idx)
                x = int(fs)  # int(float(fs)) would lose precision for large integers
        elif self.state.exp_typ=='f' and idx < len(s) and (self.parser.isfloatstr(s,idx)):
                fs,idx = self.parser.get_floatstr(s,idx)
                x = float(fs)
        elif (idx < len(s) and self.state.expmode == EXP_PAT and 
              s[idx] in LOWER and idx + 1 < len(s) and s[idx+1] not in LOWER):
            ch = s[idx]
            if idx + 3 <= len(s) and s[idx+1:idx+3] == ':=':
                x, idx = self.expression(s, idx + 3)
                self.var_manager.put(ch, x)
            else:
                x = self.var_manager.get(ch)
                idx += 1
                # ELF追跡: makeobj() 内で変数を読んだとき、その変数が
                # match() でラベルを直接キャプチャしたものであれば
                # リロケーション候補として記録する。
                if (self.state._elf_tracking
                        and self.state._elf_current_word_idx >= 0
                        and ch in self.state._elf_var_to_label
                        and self.state._elf_var_to_label[ch] is not None):
                    lname, lval = self.state._elf_var_to_label[ch]
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
            x = x ** t
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
                else:
                    x //= t
            elif s[idx] == '/':
                t, idx = self.term0_0(s, idx + 1)
                if t == 0:
                    self.err("Division by 0 error.")
                else:
                    x = x / t
            elif s[idx] == '%':
                t, idx = self.term0_0(s, idx + 1)
                if t == 0:
                    self.err("Division by 0 error.")
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
        while idx < len(s):
            if StringUtils.q(s, '<<', idx):
                t, idx = self.term1(s, idx + 2)
                x=int(x)
                t=int(t)
                x <<= t
            elif StringUtils.q(s, '>>', idx):
                t, idx = self.term1(s, idx + 2)
                x=int(x)
                t=int(t)
                x >>= t
            else:
                break
        return x, idx
    
    def term3(self, s, idx):
        """Handle bitwise AND"""
        x, idx = self.term2(s, idx)
        while idx < len(s) and s[idx] == '&' and (idx + 1 >= len(s) or s[idx+1] != '&'):
            t, idx = self.term2(s, idx + 1)
            x = int(x) & int(t)
        return x, idx
    
    def term4(self, s, idx):
        """Handle bitwise OR"""
        x, idx = self.term3(s, idx)
        while idx < len(s) and s[idx] == '|' and (idx + 1 >= len(s) or s[idx+1] != '|'):
            t, idx = self.term3(s, idx + 1)
            x = int(x) | int(t)
        return x, idx
    
    def term5(self, s, idx):
        """Handle bitwise XOR"""
        x, idx = self.term4(s, idx)
        while idx < len(s) and s[idx] == '^':
            t, idx = self.term4(s, idx + 1)
            x = int(x) ^ int(t)
        return x, idx
    
    def term6(self, s, idx):
        """Handle sign extension"""
        x, idx = self.term5(s, idx)
        # Use '\'' as sign-extension operator only when followed by a digit or '('
        # to avoid ambiguity with character literal closing quotes.
        while idx < len(s) and s[idx] == '\'':
            next_idx = idx + 1
            next_idx = StringUtils.skipspc(s, next_idx)
            if next_idx >= len(s) or (s[next_idx] not in DIGIT and s[next_idx] != '('):
                break
            t, idx = self.term5(s, idx + 1)
            if t <= 0:
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
        """Handle ternary operator (right-associative: a?b:c?d:e => a?b:(c?d:e))"""
        x, idx = self.term10(s, idx)
        if idx < len(s) and StringUtils.q(s, '?', idx):
            t, idx = self.term11(s, idx + 1)   # 右辺を再帰でterm11に委譲 → 右結合
            if idx < len(s) and StringUtils.q(s, ':', idx):
                u, idx = self.term11(s, idx + 1)
                x = t if x != 0 else u
        return x, idx
    
    def expression(self, s, idx):
        """Main expression evaluator (internal, s must already be NUL-terminated)"""
        idx = StringUtils.skipspc(s, idx)
        x, idx = self.term11(s, idx)
        return x, idx

    def _terminate(self, s):
        """Return s with a single NUL sentinel appended (idempotent)."""
        if not s or s[-1] != chr(0):
            return s + chr(0)
        return s

    def expression_pat(self, s, idx):
        """Expression in pattern mode"""
        self.state.expmode = EXP_PAT
        return self.expression(self._terminate(s), idx)
    
    def expression_asm(self, s, idx):
        """Expression in assembly mode"""
        self.state.expmode = EXP_ASM
        return self.expression(self._terminate(s), idx)
    

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
        # prefix (s[:idx]) はそのままコピー
        result = list(s[:idx])

        # 開き括弧 → 対応する閉じ括弧（OB/CB を追加）
        OPEN_TO_CLOSE = {'(': ')', '[': ']', OB: CB}
        CLOSE_CHARS   = set(OPEN_TO_CLOSE.values())

        stack = []   # 開き括弧を積むスタック

        for ch in s[idx:]:
            if ch in OPEN_TO_CLOSE:
                # 開き括弧: スタックに積んで出力
                stack.append(ch)
                result.append(ch)
            elif ch in CLOSE_CHARS:
                if stack and OPEN_TO_CLOSE.get(stack[-1]) == ch:
                    # 対応する開き括弧と一致 → ネストを1段抜ける
                    stack.pop()
                    result.append(ch)
                elif not stack and ch == stopchar:
                    # 深さ0 かつ stopchar → ここで式を終端
                    result.append(chr(0))
                else:
                    # 対応不一致の閉じ括弧（不正な入力）はそのまま出力
                    result.append(ch)
            else:
                if not stack and ch == stopchar:
                    result.append(chr(0))
                else:
                    result.append(ch)

        replaced = ''.join(result)
        return self.expression(self._terminate(replaced), idx)

    def expression_esc_float(self,s,idx,stopchar):
        prev = self.state.exp_typ
        self.state.exp_typ = 'f'
        try:
            v,idx = self.expression_esc(s,idx,stopchar)
        finally:
            self.state.exp_typ = prev
        return (v,idx)


class BinaryWriter:
    """Handles binary output to files"""
    
    def __init__(self, state):
        self.state = state
        self._buffer = {}   # {position: byte_value} のランダムアクセスバッファ
    
    def _store(self, position, word_val):
        """ワード単位でバッファに格納"""
        # 11ビットなら 0x7ff でマスクして格納
        mask = (1 << self.state.bts) - 1
        self._buffer[position] = word_val & mask
    
    def flush(self):
        """バッファをファイルに書き出す"""
        if not self.state.outfile or not self._buffer:
            return

        max_word_pos = max(self._buffer.keys())
        
        # 1ワードあたりに必要なバイト数を計算 (例: 11bit -> 2bytes)
        word_bits = self.state.bts
        bytes_per_word = (word_bits + 7) // 8
        
        total_size = (max_word_pos + 1) * bytes_per_word

        # 修正8: .padding で設定した state.padding 値で全ワードを初期化してから
        # 実際に書き込まれたワードで上書きする。
        # 旧実装は bytearray(total_size) でゼロ初期化のみ行い padding を無視していた。
        # ROM の未使用領域を 0xFF で埋める用途などで誤った出力が生成されていた。
        data = bytearray(total_size)
        pad_val = int(self.state.padding) & ((1 << word_bits) - 1)
        if pad_val != 0:
            for pos in range(max_word_pos + 1):
                base_idx = pos * bytes_per_word
                tmp = pad_val
                if self.state.endian == 'little':
                    for i in range(bytes_per_word):
                        if base_idx + i < total_size:
                            data[base_idx + i] = tmp & 0xff
                        tmp >>= 8
                else:
                    for i in range(bytes_per_word - 1, -1, -1):
                        if base_idx + i < total_size:
                            data[base_idx + i] = tmp & 0xff
                        tmp >>= 8

        for pos, val in self._buffer.items():
            # 書き込み先のバイト位置を特定
            base_idx = pos * bytes_per_word
            
            # エンディアンに基づいてバイト列に変換
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
        # デバッグ表示用のマスク
        mask = (1 << self.state.bts) - 1
        val = x & mask
        
        if prt:
            b = self.state.bts
            colm = (b + 3) // 4  # bビットを16進表示するのに必要な桁数（切り上げ）
            print(f" 0x{val:0{colm}x}", end='')

        self._store(position, val)
        return 1 # 1ワード書き込んだことを返す

    def outbin2(self, a, x):
        """Output binary without printing"""
        if self.state.pas == 2 or self.state.pas == 0:
            self.fwrite(a, int(x), 0)

    
    def outbin(self, a, x):
        """Output binary with printing"""
        if self.state.pas == 2 or self.state.pas == 0:
            self.fwrite(a, int(x), 1)
    
    def align_(self, addr):
        """Align address"""
        a = addr % self.state.align
        if a == 0:
            return addr
        return addr + self.state.align - a


class DirectiveProcessor:
    """Processes assembler directives"""
    
    def __init__(self, state, expr_eval, binary_writer):
        self.state = state
        self.expr_eval = expr_eval
        self.binary_writer = binary_writer
    
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
            key = StringUtils.upper(i[2]) # This is an abbreviation for field 1, so this is OK.
            self.state.symbols.pop(key, None)
        else:
            self.state.symbols = {}
        
        return True
    
    def set_symbol(self, i):
        """Set symbol directive"""
        if len(i) == 0 or i[0] != '.setsym':
            return False
        
        # 引数チェック: 少なくとも .setsym KEY が必要
        if len(i) < 2:
            print(f" error - .setsym directive requires at least a symbol name")
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
        
        if len(i) >= 2 and i[1] == 'big':
            self.state.endian = 'big'
        else:
            self.state.endian = 'little'
        
        if len(i) >= 3:
            v, idx = self.expr_eval.expression_pat(i[2], 0)
        else:
            v = 8
        self.state.bts = int(v)
        return True
    
    def paddingp(self, i):
        """Padding directive"""
        if len(i) == 0 or i[0] != '.padding':
            return False
        
        if len(i) >= 3:
            v, idx = self.expr_eval.expression_pat(i[2], 0)
        else:
            v = 0
        self.state.padding = int(v)
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
        
        # 引数チェック: .vliw には5つのパラメータが必要
        if len(i) < 5:
            print(f" error - .vliw directive requires 4 parameters (vliwbits, vliwinstbits, vliwtemplatebits, nop_value), got {len(i)-1}")
            return False
        
        v1, idx = self.expr_eval.expression_pat(i[1], 0)
        v2, idx = self.expr_eval.expression_pat(i[2], 0)
        v3, idx = self.expr_eval.expression_pat(i[3], 0)
        v4, idx = self.expr_eval.expression_pat(i[4], 0)
        
        self.state.vliwbits = int(v1)
        self.state.vliwinstbits = int(v2)
        self.state.vliwtemplatebits = int(v3)
        self.state.vliwflag = True
        
        l = []
        for i in range(self.state.vliwinstbits // 8 + (0 if self.state.vliwinstbits % 8 == 0 else 1)):
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
        
        # 引数チェック: EPIC には少なくとも2つのパラメータが必要
        if len(i) < 3:
            print(f" error - EPIC directive requires 2 parameters (indices, pattern), got {len(i)-1}")
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
        """Process error directive"""
        ss = s.replace(' ', '')
        if ss == "":
            return
        
        s += chr(0)
        idx = 0
        error_code = 0
        
        while True:
            ch = s[idx] if idx < len(s) else chr(0)
            if ch == chr(0):
                break
            if ch == ',':
                idx += 1
                continue
            
            prev_typ = self.expr_eval.state.exp_typ
            self.expr_eval.state.exp_typ = 'f'
            try:
                u, idxn = self.expr_eval.expression_pat(s, idx)
            finally:
                self.expr_eval.state.exp_typ = prev_typ
            idx = idxn
            if idx < len(s) and s[idx] == ';':
                idx += 1
            t, idx = self.expr_eval.expression_pat(s, idx)
            
            if (self.state.pas == 2 or self.state.pas == 0) and u:
                print(f"Line {self.state.ln} Error code {t} ", end="")
                if t >= 0 and t < len(ERRORS):
                    print(f"{ERRORS[t]}", end='')
                print(": ")
                error_code = t


class PatternMatcher:
    """Handles pattern matching for assembly instructions"""
    
    def __init__(self, state, expr_eval, var_manager, symbol_manager, parser):
        self.state = state
        self.expr_eval = expr_eval
        self.var_manager = var_manager
        self.symbol_manager = symbol_manager
        self.parser = parser
    
    def remove_brackets(self, s, l):
        """Remove specified bracket pairs.

        修正3: 旧実装はネスト深度 (open_count) をグループIDとして使っていた。
        これだと兄弟関係にある [[A]] [[B]] は両方 open_count==1 になり、
        個別に指定できなかった。

        修正後: OB を見るたびに単調増加するシリアル番号を割り当て、
        スタックで対応する CB と紐付ける。
        remove_brackets(t, [1,3]) は「シリアル1番と3番のグループを除去せよ」
        という意味になり、どの兄弟でも正しく個別指定できる。
        match0 が渡す l のシリアルは 1-origin の連番 (sl = [1,2,...,cnt]) なので
        この変更と完全に対応している。
        """
        # --- シリアル番号と文字位置の対応表を構築 ---
        serial = 0          # 次に割り当てるシリアル
        stack = []          # (serial, open_pos) のスタック
        bracket_pairs = {}  # serial -> (open_pos, close_pos)

        for i, char in enumerate(s):
            if char == OB:
                serial += 1
                stack.append((serial, i))
            elif char == CB:
                if stack:
                    ser, open_pos = stack.pop()
                    bracket_pairs[ser] = (open_pos, i)

        # --- l に含まれるシリアルのグループを除去 ---
        result = list(s)
        for index in l:
            if index in bracket_pairs:
                start_pos, end_pos = bracket_pairs[index]
                for j in range(start_pos, end_pos + 1):
                    result[j] = ''

        return ''.join(result)
    
    def match(self, s, t):
        """Match assembly line against pattern"""
        self.state.deb1 = s
        self.state.deb2 = t
        
        t = t.replace(OB, '').replace(CB, '')
        idx_s = 0
        idx_t = 0
        idx_s = StringUtils.skipspc(s, idx_s)
        idx_t = StringUtils.skipspc(t, idx_t)
        s += chr(0)
        t += chr(0)
        
        while True:
            idx_s = StringUtils.skipspc(s, idx_s)
            idx_t = StringUtils.skipspc(t, idx_t)
            b = s[idx_s]
            a = t[idx_t]
            
            if a == chr(0) and b == chr(0):
                return True
            
            if a == '\\':
                idx_t += 1
                if idx_t < len(t) and t[idx_t] == b:
                    idx_t += 1
                    idx_s += 1
                    continue
                else:
                    return False
            elif a.isupper():
                if a == b.upper():
                    idx_s += 1
                    idx_t += 1
                    continue
                else:
                    return False
            elif a == '!':
                idx_t += 1
                a = t[idx_t]
                idx_t += 1
                if a == 'F':
                    a = t[idx_t]
                    idx_t = StringUtils.skipspc(t, idx_t+1)
                    if idx_t < len(t) and t[idx_t] == '\\':
                        idx_t = StringUtils.skipspc(t, idx_t+1)
                        stopchar = t[idx_t] if idx_t < len(t) else chr(0)
                        idx_t += 1                                    # skip stopchar in pattern
                    else:
                        stopchar = chr(0)

                    v, idx_s = self.expr_eval.expression_esc_float(s, idx_s, stopchar)
                    v = float(v)
                    v = int.from_bytes(struct.pack('>f', v), "big")
                    self.var_manager.put(a, v)
                    # consume stopchar from source as well
                    if stopchar != chr(0) and idx_s < len(s) and s[idx_s] == stopchar:
                        idx_s += 1
                    continue
                elif a == 'D':
                    a = t[idx_t]
                    idx_t = StringUtils.skipspc(t, idx_t+1)
                    if idx_t < len(t) and t[idx_t] == '\\':
                        idx_t = StringUtils.skipspc(t, idx_t+1)
                        stopchar = t[idx_t] if idx_t < len(t) else chr(0)
                        idx_t += 1                                    # skip stopchar in pattern
                    else:
                        stopchar = chr(0)

                    v, idx_s = self.expr_eval.expression_esc_float(s, idx_s, stopchar)
                    v = float(v)
                    v = int.from_bytes(struct.pack('>d', v), "big")
                    self.var_manager.put(a, v)
                    # consume stopchar from source as well
                    if stopchar != chr(0) and idx_s < len(s) and s[idx_s] == stopchar:
                        idx_s += 1
                    continue
                elif a == 'Q':
                    # !Q<var> : ソースから浮動小数点式を読み取り、
                    # IEEE754 128ビット(quad)整数ビットパターンとして変数に格納する
                    a = t[idx_t]
                    idx_t = StringUtils.skipspc(t, idx_t+1)
                    if idx_t < len(t) and t[idx_t] == '\\':
                        idx_t = StringUtils.skipspc(t, idx_t+1)
                        stopchar = t[idx_t] if idx_t < len(t) else chr(0)
                        idx_t += 1                                    # skip stopchar in pattern
                    else:
                        stopchar = chr(0)

                    v, idx_s = self.expr_eval.expression_esc_float(s, idx_s, stopchar)
                    h = IEEE754Converter.decimal_to_ieee754_128bit_hex(str(float(v)))
                    x = int(h, 16)
                    self.var_manager.put(a, x)
                    # consume stopchar from source as well
                    if stopchar != chr(0) and idx_s < len(s) and s[idx_s] == stopchar:
                        idx_s += 1
                    continue
                elif a == '!':
                    a = t[idx_t]
                    idx_t += 1
                    # ELF追跡: !!a（factor キャプチャ）
                    self.state._elf_capturing_var = a
                    v, idx_s = self.expr_eval.factor(s, idx_s)
                    self.state._elf_capturing_var = None
                    self.var_manager.put(a, v)
                    continue
                else:
                    idx_t = StringUtils.skipspc(t, idx_t)
                    if idx_t < len(t) and t[idx_t] == '\\':
                        idx_t += 1                                    # skip '\'
                        idx_t = StringUtils.skipspc(t, idx_t)
                        stopchar = t[idx_t] if idx_t < len(t) else chr(0)
                        idx_t += 1                                    # skip stopchar in pattern
                    else:
                        stopchar = chr(0)

                    # ELF追跡: !a（expression キャプチャ）
                    self.state._elf_capturing_var = a
                    v, idx_s = self.expr_eval.expression_esc(s, idx_s, stopchar)
                    self.state._elf_capturing_var = None
                    self.var_manager.put(a, v)
                    # consume stopchar from source as well
                    if stopchar != chr(0) and idx_s < len(s) and s[idx_s] == stopchar:
                        idx_s += 1
                    continue
            elif a in LOWER:
                idx_t += 1
                w, idx_s = self.parser.get_symbol_word(s, idx_s)
                v = self.symbol_manager.get(w)
                if v == "":
                    return False
                self.var_manager.put(a, v)
                continue
            elif a == b:
                idx_t += 1
                idx_s += 1
                continue
            else:
                return False
    
    def match0(self, s, t):
        """Match with optional bracket combinations.

        各 match() 試行の前に vars をスナップショットし、
        マッチ失敗した試行で書き込まれた変数値を必ずリストアする。
        これにより、失敗した組み合わせの副作用が次の試行に持ち越されない。
        """
        t = t.replace('[[', OB).replace(']]', CB)
        cnt = t.count(OB)
        sl = [_ + 1 for _ in range(cnt)]

        for i in range(len(sl) + 1):
            ll = list(itertools.combinations(sl, i))
            for j in ll:
                lt = self.remove_brackets(t, list(j))
                # マッチ前の vars を保存
                saved_vars = self.state.vars[:]
                if self.match(s, lt):
                    return True
                # 失敗 → vars をリストア
                self.state.vars = saved_vars
        return False


class PatternFileReader:
    """Reads and processes pattern files"""
    
    def __init__(self, parser):
        self.parser = parser
    
    def readpat(self, fn, base_dir=None):
        """Read pattern file.

        base_dir: 呼び出し元パターンファイルのディレクトリ。
        None のときはプロセスの CWD を基準にする（トップレベル呼び出し）。
        相対パスの fn は base_dir（または CWD）を基準に解決する。
        """
        if fn == '':
            return []
        
        # 相対パスを解決する
        if base_dir and not os.path.isabs(fn):
            fn = os.path.join(base_dir, fn)
        
        # このファイルと同じディレクトリを、再帰的な .INCLUDE の基準にする
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
                
                ww = self.include_pat(l, this_dir)
                if ww:
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
                        p = [l[0], l[1], l[2], l[3], l[4], l[5]]
                    w.append(p)
        
        return w
    
    def include_pat(self, l, base_dir=None):
        """Include pattern directive.

        修正7: 旧実装は StringUtils.skipspc で先頭スペースをスキップして
        idx を求めておきながら、ファイル名の抽出に固定オフセット l[8:] を
        使っていた。インデントがある行（例: "  .INCLUDE foo.axx"）では
        l[8:] が .INCLUDE 文字列の途中から始まってしまいファイル名を
        正しく取り出せなかった。
        修正後: l[idx+8:] を使い、スキップ後の先頭位置から 8 文字
        (.INCLUDE) 分進んだ位置からファイル名を読み取る。

        修正5: ファイル名は base_dir を基準に解決する。
        """
        idx = StringUtils.skipspc(l, 0)
        i = l[idx:idx+8]
        i = i.upper()
        if i != ".INCLUDE":
            return []
        s = StringUtils.get_string(l[idx+8:])
        w = self.readpat(s, base_dir)
        return w


class ObjectGenerator:
    """Generates object code from expressions"""
    
    def __init__(self, state, expr_eval, binary_writer):
        self.state = state
        self.expr_eval = expr_eval
        self.binary_writer = binary_writer
    
    def replace_percent_with_index(self, s):
        """Replace %% with sequential numbers starting from 0"""
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
        """Expand @@[n,pattern] syntax"""
        result = []
        has_content = False
        i = 0
        while i < len(pattern):
            if i + 3 <= len(pattern) and pattern[i:i+3] == '@@[':
                # @@[ found
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
                
                if comma_pos > 0:
                    expr = pattern[expr_start:comma_pos]
                    rep_pattern = pattern[comma_pos+1:i]
                    
                    # Evaluate expression
                    n, idx = self.expr_eval.expression_pat(expr, 0)
                    # Expand pattern n times
                    if int(n) > 0:
                        has_content = True
                        for j in range(int(n)):
                            if j > 0:
                                result.append(',')
                            result.append(rep_pattern)
                    
                    i += 1  # Skip closing ]
                else:
                    result.append('@@[')
                    has_content = True
            else:
                result.append(pattern[i])
                has_content = True
                i += 1
        
        return ''.join(result), not has_content

    def makeobj(self, s):
        """Make object code from expression string"""
        # Expand @@[] and replace %%
        s,z = self.e_p(s)
        s = self.replace_percent_with_index(s)
        
        s += chr(0)
        idx = 0
        objl = []
        
        if z:
            return objl

        try:
            while True:
                if idx >= len(s) or s[idx] == chr(0):
                    break

                if s[idx] == ',':
                    idx += 1
                    p = self.state.pc + len(objl)
                    n = self.binary_writer.align_(p)
                    for i in range(p, n):
                        objl += [self.state.padding]
                    continue

                semicolon = False
                if s[idx] == ';':
                    semicolon = True
                    idx += 1

                # ELF リロケーション追跡: このワードを生成する式評価の開始時点で
                # 現在のワードインデックス（objl への追加前の長さ）を記録する。
                # get_value() がこの値を参照して (label, value, word_idx) を記録する。
                self.state._elf_current_word_idx = len(objl)

                x, idx = self.expr_eval.expression_pat(s, idx)

                if (semicolon == True and x != 0) or (semicolon == False):
                    objl += [x]

                if idx < len(s) and s[idx] == ',':
                    idx += 1
                    continue
                break
        finally:
            # makeobj() を抜けたら必ずセンチネルに戻す（例外安全）
            self.state._elf_current_word_idx = -1

        return objl


class VLIWProcessor:
    """Handles VLIW instruction processing"""
    
    def __init__(self, state, expr_eval, binary_writer):
        self.state = state
        self.expr_eval = expr_eval
        self.binary_writer = binary_writer
    
    def vliwprocess(self, line, idxs, objl, flag, idx, lineassemble2_func):
        """Process VLIW instruction"""
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
                objs += [objl]
                idxlst += [idxs]
                continue
            else:
                break
        
        if self.state.vliwtemplatebits == 0:
            self.state.vliwset = [[[0], "0"]]
        
        vbits = abs(self.state.vliwbits)
        for k in self.state.vliwset:
            if sorted(k[0]) == sorted(idxlst) or self.state.vliwtemplatebits == 0:
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
                
                # values がスロット数より多い場合は末尾を切り捨て、
                # 少ない場合は NOP で埋める。
                target_len = ibyte * noi
                if len(values) > target_len:
                    if self.state.pas == 2 or self.state.pas == 0:
                        print(f"warning-VLIW:{len(values)} values exceed slot capacity {target_len},truncating.")
                    values = values[:target_len]
                else:
                    for i in range(target_len - len(values)):
                        values += self.state.vliwnop
                
                v1 = []
                cnt = 0
                
                for j in range(noi):
                    vv = 0
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
                if self.state.vliwbits > 0:
                    bc = vbits - 8
                    vm = 0xff << bc
                    for cnt in range(vbits // 8):
                        self.binary_writer.outbin(self.state.pc + cnt, ((res & vm) >> bc) & 0xff)
                        bc = bc - 8
                        vm >>= 8
                        q += 1
                else:
                    for cnt in range(vbits // 8):
                        self.binary_writer.outbin(self.state.pc + cnt, res & 0xff)
                        res >>= 8
                        q += 1
                
                self.state.pc += q
                break
        else:
            if self.state.pas == 0 or self.state.pas == 2:
                print(" error - No vliw instruction-set defined.")
                return False
        return True


class AssemblyDirectiveProcessor:
    """Processes assembly-level directives"""
    
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
        """Process label definitions"""
        if l == "":
            return ""
        
        label, idx = self.parser.get_label_word(l, 0)
        lidx = idx
        
        if label != "" and idx > 0 and l[idx-1] == ':':
            idx = StringUtils.skipspc(l, idx)
            e, idx = StringUtils.get_param_to_spc(l, idx)
            if e.upper() == '.EQU':
                u, idx = self.expr_eval.expression_asm(l, idx)
                # is_equ=True: 定数ラベル（.equ 式の結果）はリロケーション対象外
                self.label_manager.put_value(label, u, self.state.current_section, is_equ=True)
                return ""
            else:
                # is_equ=False: アドレスラベル（リロケーション対象になり得る）
                self.label_manager.put_value(label, self.state.pc, self.state.current_section, is_equ=False)
                return l[lidx:]
        return l
    
    def asciistr(self, l2):
        """Process ASCII string"""
        idx = 0
        if l2 == '' or l2[idx] != '"':
            return False
        idx += 1
        
        while idx < len(l2) and not l2[idx]=='"':
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
            elif l2[idx:idx+2] == '\\\\'  :
                idx += 2
                ch = '\\'
            elif l2[idx:idx+2] == '\\"':
                idx += 2
                ch = '"'
            else:
                ch = l2[idx]
                idx += 1
            self.binary_writer.outbin(self.state.pc, ord(ch))
            self.state.pc += 1
        return True
    
    def export_processing(self, l1, l2):
        """Export directive"""
        if not (self.state.pas == 2 or self.state.pas == 0):
            return False
        if StringUtils.upper(l1) != ".EXPORT":
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
            self.state.export_labels[s] = [v, sec]
            if idx < len(l2) and l2[idx] == ',':
                idx += 1
        return True
    
    def zero_processing(self, l1, l2):
        """Zero directive"""
        if StringUtils.upper(l1) != ".ZERO":
            return False
        x, idx = self.expr_eval.expression_asm(l2, 0)
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
        """ASCIIZ directive"""
        if StringUtils.upper(l1) != ".ASCIIZ":
            return False
        f = self.asciistr(l2)
        if not f:
            if self.state.pas == 2 or self.state.pas == 0:
                print(f" error - .ASCIIZ requires a quoted string.")
            return False
        self.binary_writer.outbin(self.state.pc, 0x00)
        self.state.pc += 1
        return True
    
    def section_processing(self, l1, l2):
        """Section directive"""
        if StringUtils.upper(l1) != "SECTION" and StringUtils.upper(l1) != "SEGMENT":
            return False
        
        if l2 != '':
            self.state.current_section = l2
            # 同名セクションが再宣言された場合（.text→.data→.text など）は
            # 最初に記録した開始アドレスを保護する。
            # 旧実装は毎回 [self.state.pc, 0] で上書きしていたため、
            # ELF セクション開始アドレスや endsection のサイズ計算が狂っていた。
            if l2 not in self.state.sections:
                self.state.sections[l2] = [self.state.pc, 0]
        return True
    
    def align_processing(self, l1, l2):
        """Align directive"""
        if StringUtils.upper(l1) != ".ALIGN":
            return False
        
        if l2 != '':
            u, idx = self.expr_eval.expression_asm(l2, 0)
            self.state.align = int(u)
        
        self.state.pc = self.binary_writer.align_(self.state.pc)
        return True
    
    def endsection_processing(self, l1, l2):
        """End section directive"""
        if StringUtils.upper(l1) != "ENDSECTION" and StringUtils.upper(l1) != "ENDSEGMENT":
            return False
        if self.state.current_section not in self.state.sections:
            print(f" error - ENDSECTION without matching SECTION for '{self.state.current_section}'.")
            return True
        start = self.state.sections[self.state.current_section][0]
        self.state.sections[self.state.current_section] = [start, self.state.pc - start]
        return True
    
    def org_processing(self, l1, l2):
        """ORG directive"""
        if StringUtils.upper(l1) != ".ORG":
            return False
        u, idx = self.expr_eval.expression_asm(l2, 0)
        if idx + 2 <= len(l2) and l2[idx:idx+2].upper() == ',P':
            if u > self.state.pc:
                for i in range(u - self.state.pc):
                    self.binary_writer.outbin2(i + self.state.pc, self.state.padding)
        self.state.pc = u
        return True


class Assembler:
    """Main assembler class"""
    
    def __init__(self):
        self.state = AssemblerState()
        self.parser = Parser(self.state)
        self.var_manager = VariableManager(self.state)
        self.label_manager = LabelManager(self.state)
        self.symbol_manager = SymbolManager(self.state)
        self.expr_eval = ExpressionEvaluator(self.state, self.var_manager, 
                                            self.label_manager, self.symbol_manager, self.parser)
        self.binary_writer = BinaryWriter(self.state)
        self.directive_proc = DirectiveProcessor(self.state, self.expr_eval, self.binary_writer)
        self.pattern_matcher = PatternMatcher(self.state, self.expr_eval, self.var_manager, 
                                             self.symbol_manager, self.parser)
        self.pattern_reader = PatternFileReader(self.parser)
        self.obj_gen = ObjectGenerator(self.state, self.expr_eval, self.binary_writer)
        self.vliw_proc = VLIWProcessor(self.state, self.expr_eval, self.binary_writer)
        self.asm_directive_proc = AssemblyDirectiveProcessor(self.state, self.expr_eval, 
                                                             self.binary_writer, self.label_manager, self.parser)
        # セクション情報の一時記録テーブル（imp_label が使用）。
        # アセンブリ中に構築される state.sections とは独立した辞書で、
        # import ファイルの解析中のみ参照される。
        self._imp_sections: dict = {}  # {sname: (start, size)}
    
    def include_asm(self, l1, l2):
        """Include directive.

        修正5: インクルードパスを現在アセンブル中のファイルのディレクトリを基準に解決する。
        旧実装はパスをそのまま open() に渡すため、プロセスの CWD と異なる場所にある
        ソースファイル内の相対パス .INCLUDE が常に失敗していた。
        stdin や対話モードの場合は解決不能なので CWD 基準のままとする。
        """
        if StringUtils.upper(l1) != ".INCLUDE":
            return False
        s = StringUtils.get_string(l2)
        if s:
            # 相対パスを現在ファイルのディレクトリ基準に解決する
            if not os.path.isabs(s):
                cur = self.state.current_file
                if cur and cur not in ("(stdin)", ""):
                    base = os.path.dirname(os.path.abspath(cur))
                    s = os.path.join(base, s)
            self.fileassemble(s)
        return True
    
    def lineassemble2(self, line, idx):
        """Assemble line (phase 2)"""
        l, idx = StringUtils.get_param_to_spc(line, idx)
        l2, idx = StringUtils.get_param_to_eon(line, idx)
        l = l.rstrip()
        l2 = l2.rstrip()
        l = l.replace(' ', '')
        
        if self.asm_directive_proc.section_processing(l, l2):
            return [], [], True, idx
        if self.asm_directive_proc.endsection_processing(l, l2):
            return [], [], True, idx
        if self.asm_directive_proc.zero_processing(l, l2):
            return [], [], True, idx
        if self.asm_directive_proc.ascii_processing(l, l2):
            return [], [], True, idx
        if self.asm_directive_proc.asciiz_processing(l, l2):
            return [], [], True, idx
        if self.include_asm(l, l2):
            return [], [], True, idx
        if self.asm_directive_proc.align_processing(l, l2):
            return [], [], True, idx
        if self.asm_directive_proc.org_processing(l, l2):
            return [], [], True, idx
        if self.asm_directive_proc.labelc_processing(l, l2):
            return [], [], True, idx
        if self.asm_directive_proc.export_processing(l, l2):
            return [], [], True, idx
        if l == "":
            return [], [], False, idx
        
        of = 0
        se = False
        oerr = False
        pln = 0
        pl = ""
        idxs = 0
        objl = []
        loopflag = True
        
        for i in self.state.pat:
            pln += 1
            pl = i
            for a in LOWER:
                self.var_manager.put(a, VAR_UNDEF)
            
            if i is None: continue
            if self.directive_proc.set_symbol(i): continue
            if self.directive_proc.clear_symbol(i): continue
            if self.directive_proc.paddingp(i): continue
            if self.directive_proc.bits(i): continue
            if self.directive_proc.symbolc(i): continue
            if self.directive_proc.epic(i): continue
            if self.directive_proc.vliwp(i): continue
            
            lw = len([_ for _ in i if _])
            if lw == 0: continue
            
            lin = l + ' ' + l2
            lin = StringUtils.reduce_spaces(lin)
            
            if i[0] == '':
                # 番兵エントリ: マッチせずにループ終端に達したとみなす。
                # i[3] にはVLIWスロットインデックス式が入っているため、
                # 評価せずに break すると idxs が初期値 0 のまま返り
                # VLIWスロット配置が狂う。ここで必ず評価する。
                idxs, _ = self.expr_eval.expression_pat(i[3], 0)
                loopflag = False
                break
            
            self.state.error_undefined_label = False
            
            self.state.expmode=EXP_ASM
            if not self.state.debug:
                try:
                    if self.pattern_matcher.match0(lin, i[0]) == True:
                        self.directive_proc.error(i[1])
                        objl = self.obj_gen.makeobj(i[2])
                        # makeobj() の finally が _elf_current_word_idx を -1 に
                        # リセット済み。以降のサイズ式 expression_pat(i[3]) で発生する
                        # ラベル参照は word_idx=-1 となりリロケーション対象外になる。
                        idxs, _ = self.expr_eval.expression_pat(i[3], 0)
                        loopflag = False
                        break
                except Exception:
                    if self.state.pas == 1:
                        # Pass1: パターンはマッチしたが forward参照で makeobj が失敗した。
                        # ラベルを 0 と仮定してサイズだけ確定させ、PC を正しく進める。
                        # makeobj() の finally が _elf_current_word_idx を -1 にリセット
                        # するため、ここで追加リセットは不要。
                        try:
                            self.state._pass1_size_mode = True
                            objl = self.obj_gen.makeobj(i[2])
                            idxs, _ = self.expr_eval.expression_pat(i[3], 0)
                        except Exception:
                            objl = []  # それでも失敗した場合はサイズ0のまま
                        finally:
                            self.state._pass1_size_mode = False
                        loopflag = False
                    else:
                        oerr = True
                        loopflag = False
                    break
            else:
                if self.pattern_matcher.match0(lin, i[0]) == True:
                    self.directive_proc.error(i[1])
                    objl = self.obj_gen.makeobj(i[2])
                    # makeobj() の finally が _elf_current_word_idx を -1 にリセット済み
                    idxs, _ = self.expr_eval.expression_pat(i[3], 0)
                    loopflag = False
                    break
        
        if loopflag == True:
            se = True
            pln = 0
            pl = ""
        
        if self.state.pas == 2 or self.state.pas == 0:
            if self.state.error_undefined_label:
                print(f" error - undefined label error.")
                return [], [], False, idx
            if se:
                print(f" error - Syntax error.")
                return [], [], False, idx
            if oerr:
                print(f" ; pat {pln} {pl} error - Illegal syntax in assemble line or pattern line.")
                return [], [], False, idx
        
        return idxs, objl, True, idx
    
    def lineassemble(self, line):
        """Assemble single line"""
        line = line.replace('\t', ' ').replace('\n', '')
        line = StringUtils.reduce_spaces(line)
        line = StringUtils.remove_comment_asm(line)
        if line == '':
            return False

        # 修正4a: .EQU 式はパターンファイル由来のシンボル（レジスタ名など）を
        # 参照できるべきだが、前行のパターンスキャンで蓄積された
        # 位置依存 .setsym の残留値には依存すべきでない。
        # そのため label_processing (= .EQU 評価) の前に symbols を
        # patsymbols ベースラインにリセットしてから評価する。
        self.state.symbols = dict(self.state.patsymbols)

        line = self.asm_directive_proc.label_processing(line)

        # 修正4b: 旧実装は clear_symbol([".clearsym","",...]) で symbols={} に
        # 空クリアしていた。これでは patsymbols に定義されたシンボルまで
        # 消えてしまい、lineassemble2 内のパターンスキャンが再構築する前の
        # .setsym 参照が失敗する。
        # 修正後: lineassemble2 の先頭でパターンスキャンが .setsym を
        # 順次適用するため、ここでの明示的クリアは不要。
        # patsymbols ベースラインは上記 4a で設定済み。
        
        parts = line.split("!!")
        self.state.vcnt = sum(1 for p in parts if p != "")

        # ELF リロケーション追跡: pass2 かつ ELF 出力時のみ有効
        if self.state.elf_objfile and self.state.pas == 2:
            self.state._elf_tracking = True
            self.state._elf_label_refs_seen = []
            self.state._elf_current_word_idx = -1    # makeobj 外はセンチネル
            self.state._elf_var_to_label = {}        # 命令ごとにリセット
            self.state._elf_capturing_var = None

        idxs, objl, flag, idx = self.lineassemble2(line, 0)

        self.state._elf_tracking = False

        if flag == False:
            return False
        
        if self.state.vliwflag == False or (idx >= len(line) or line[idx:idx+2] != '!!'):
            of = len(objl)

            # ------------------------------------------------------------------ #
            # ELF リロケーション検出（トラッキング方式）                            #
            #                                                                       #
            # makeobj() 内で get_value() が呼ばれたとき、(lname, val, word_idx)    #
            # として _elf_label_refs_seen に記録済み。                              #
            # word_idx は objl への追加前の len(objl)（=ワード位置）。              #
            # makeobj() 外（パターンマッチ・サイズ式）の参照は word_idx=-1 のため  #
            # 無視される。                                                          #
            # 同一ラベルが連続ワードを占める場合（例: bts=8 で 64bit アドレスを    #
            # 8 バイトに分割して格納）は連続グループとして1エントリにまとめる。     #
            # ------------------------------------------------------------------ #
            if self.state.elf_objfile and self.state.pas == 2 and objl and self.state._elf_label_refs_seen:
                bpw_r = max(1, (self.state.bts + 7) // 8)
                sec_name_r = self.state.current_section
                sec_start_w = 0
                if sec_name_r in self.state.sections:
                    sec_start_w = self.state.sections[sec_name_r][0]

                # word_idx >= 0（makeobj 内の参照）のみを対象とし、ワード順にソート
                valid_refs = [
                    (ln, aw, wi)
                    for (ln, aw, wi) in self.state._elf_label_refs_seen
                    if wi >= 0
                ]
                valid_refs.sort(key=lambda r: r[2])

                # 同一ラベルの連続ワード参照をひとつのリロケーショングループにまとめる
                # 例: bts=8 で 64bit アドレスを 8 バイトに分割 → 8 連続エントリ → 1 グループ
                groups = []  # [(lname, abs_w, first_word_idx, num_words)]
                gi = 0
                while gi < len(valid_refs):
                    lname, abs_w, widx = valid_refs[gi]
                    gj = gi + 1
                    while (gj < len(valid_refs)
                           and valid_refs[gj][0] == lname
                           and valid_refs[gj][2] == widx + (gj - gi)):
                        gj += 1
                    groups.append((lname, abs_w, widx, gj - gi))
                    gi = gj

                # アーキテクチャごとのリロケーションタイプ表
                # {machine: {num_bytes: rtype}}
                # 未定義サイズは 0 → スキップ
                _RTYPE_MAP = {
                    62:  {8: 1,  4: 10, 2: 12, 1: 14},  # EM_X86_64
                    3:   {4: 1,  2: 2,  1: 7},           # EM_386   (R_386_32/16/8)
                    40:  {4: 2,  2: 250},                 # EM_ARM   (R_ARM_ABS32/16)
                    183: {8: 257, 4: 258},                # EM_AARCH64 (R_AARCH64_ABS64/32)
                    243: {8: 2,  4: 3},                   # EM_RISCV (R_RISCV_64/32)
                    20:  {4: 1},                          # EM_PPC   (R_PPC_ADDR32)
                }
                _rmap = _RTYPE_MAP.get(self.state.elf_machine, {8: 1, 4: 2, 2: 3, 1: 4})

                for lname, abs_w, first_widx, num_words in groups:
                    num_bytes = num_words * bpw_r
                    rtype = _rmap.get(num_bytes, 0)
                    if rtype == 0:
                        continue  # このサイズのリロケーションタイプが未定義 → スキップ
                    if first_widx >= len(objl):
                        continue  # 安全ガード
                    # セクション相対バイトオフセット
                    sec_rel = (self.state.pc + first_widx - sec_start_w) * bpw_r

                    # RELA addend の計算:
                    #   RELA 形式では r_addend がシンボル参照の定数オフセットを保持する。
                    #   リンカは "S + A"（S=シンボル最終アドレス, A=addend）でフィールドを
                    #   上書きするため、addend = (objl に書き込まれた値) - (ラベルの絶対値)
                    #   とすることで label+N のような式の N が失われなくなる。
                    #
                    #   旧実装は addend を常に 0 に固定していたため、label+N の N が
                    #   リンク後に消え、誤ったアドレスが生成される問題があった。
                    #
                    #   複数ワードで1つのアドレスを表す場合（bts=8 で 64bit を 8 バイトに
                    #   分割するケース等）は、ワード列を結合してスカラ値を復元する。
                    word_mask = (1 << self.state.bts) - 1
                    if self.state.endian == 'little':
                        raw_val = 0
                        for k in range(num_words):
                            widx_k = first_widx + k
                            if widx_k < len(objl):
                                raw_val |= (int(objl[widx_k]) & word_mask) << (self.state.bts * k)
                    else:
                        raw_val = 0
                        for k in range(num_words):
                            widx_k = first_widx + k
                            if widx_k < len(objl):
                                raw_val = (raw_val << self.state.bts) | (int(objl[widx_k]) & word_mask)
                    addend = raw_val - abs_w
                    self.state.relocations.append((sec_name_r, sec_rel, lname, rtype, addend))

            for cnt in range(of):
                self.binary_writer.outbin(self.state.pc + cnt, objl[cnt])
            self.state.pc += of
        else:
            vflag = False
            try:
                vflag = self.vliw_proc.vliwprocess(line, idxs, objl, flag, idx, self.lineassemble2)
            except Exception:
                if self.state.pas == 0 or self.state.pas == 2:
                    print(" error - Some error(s) in vliw definition.")
            return vflag
        
        return True
    
    def lineassemble0(self, line):
        """Assemble line with output"""
        self.state.cl = line.replace('\n', '')
        if self.state.pas == 2 or self.state.pas == 0:
            print("%016x " % self.state.pc, end='')
            print(f"{self.state.current_file} {self.state.ln} {self.state.cl} ", end='')
        f = self.lineassemble(self.state.cl)
        if self.state.pas == 2 or self.state.pas == 0:
            print("")
        self.state.ln += 1
        return f
    
    def setpatsymbols(self, pat):
        """Set pattern symbols"""
        for i in pat:
            if self.directive_proc.set_symbol(i):
                continue
        self.state.patsymbols.update(self.state.symbols)
    
    def fileassemble(self, fn):
        """Assemble file"""
        # fnstack と lnstack を必ずペアで push してから try に入る。
        # これにより finally での pop が常に対称になる。
        self.state.fnstack.append(self.state.current_file)
        self.state.lnstack.append(self.state.ln)
        self.state.current_file = fn
        self.state.ln = 1

        try:
            if fn == "stdin":
                # Pass 1 (pas==1): read stdin and write to a per-instance temp file.
                # Pass 2 (pas==2) and relaxation iterations: re-use the same temp file.
                # Using tempfile instead of the fixed name "axx.tmp" prevents races
                # when multiple axx instances run concurrently.
                if self.state.stdin_tmp_path is None:
                    # 初回のみ: 一時ファイルを作成し stdin を読み込む。
                    # リラクゼーション2回目以降は stdin が EOF なので読み直さない。
                    # pas == 1 の条件で毎回読んでいた旧実装のバグを修正。
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
            # push は try の前で必ず成功しているので、無条件で pop する。
            self.state.current_file = self.state.fnstack.pop()
            self.state.ln = self.state.lnstack.pop()
    
    def file_input_from_stdin(self):
        """Read input from stdin until EOF (Ctrl+D / piped end).
        Empty lines within the input are preserved correctly."""
        af = ""
        while True:
            line = sys.stdin.readline()
            if line == '':   # EOF: readline() returns '' only at EOF
                break
            # Normalize line endings but keep the newline so line numbers match
            af += line.replace('\r', '')
        return af
    
    def imp_label(self, l):
        """Import label from exported TSV format (produced by _write_export).

        Line formats (tab-separated):
          section_name  start_hex  size_hex  [flag]   <- section line (≥3 fields, skip)
          label_name    value_hex                     <- label line (2 fields, import)

        旧実装は "section label value" の空白区切り3トークンを仮定していたが、
        _write_export が出力するのはタブ区切り TSV であり、フォーマットが
        根本的に食い違っていた。さらに skipspc() はタブをスキップしないため
        タブ区切りの先頭フィールド解析も常に失敗していた。
        修正後は str.split('\\t') で TSV を正しく分割し、フィールド数で行種別を
        判定する。セクション行は self._imp_sections に記録し、後続のラベル行が
        セクション名を逆引きできるようにする。
        """
        l = l.rstrip('\r\n')
        if not l:
            return False

        fields = l.split('\t')

        if len(fields) >= 3:
            # Section line: record for later label→section mapping.
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
            # Determine section by range lookup in previously parsed section table.
            section = '.text'
            for sname, (start, size) in self._imp_sections.items():
                if size > 0 and start <= v < start + size:
                    section = sname
                    break
                if size == 0 and v == start:
                    section = sname
                    break
            self.label_manager.put_value(label, v, section)
            return True

        return False
    
    def printaddr(self, pc):
        """Print address"""
        print("%016x: " % pc, end='')

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
        buf = self.binary_writer._buffer   # {word_pos: word_val}

        # ------------------------------------------------------------------ #
        # Helper: pack ELF structures                                          #
        # エンディアンは state.endian から決定する。                           #
        #   little → EI_DATA=1 (ELFDATA2LSB), struct prefix '<'              #
        #   big    → EI_DATA=2 (ELFDATA2MSB), struct prefix '>'              #
        # ------------------------------------------------------------------ #
        _is_le    = (self.state.endian != 'big')
        _ei_data  = 1 if _is_le else 2          # EI_DATA byte in e_ident
        _pk       = '<' if _is_le else '>'      # struct.pack prefix

        def _pack_ehdr(e_type, e_machine, e_shoff, e_shnum, e_shstrndx):
            ident = (b'\x7fELF'
                     + bytes([2, _ei_data, 1, self.state.osabi])  # class64, EI_DATA, ver1, ELFOSABI
                     + b'\x00' * 8)
            return ident + _struct.pack(f'{_pk}HHIQQQIHHHHHH',
                e_type, e_machine,
                1,       # e_version
                0,       # e_entry
                0,       # e_phoff
                e_shoff,
                0,       # e_flags
                64,      # e_ehsize
                0, 0,    # phentsize, phnum
                64,      # e_shentsize
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

        # ------------------------------------------------------------------ #
        # 1. Collect content sections                                          #
        # ------------------------------------------------------------------ #
        def _extract(w_start, w_count):
            """Return bytes for word range [w_start, w_start+w_count)."""
            n = w_count * bpw
            if n == 0:
                return b''
            data = bytearray(n)
            pad = int(self.state.padding) & ((1 << self.state.bts) - 1)
            if pad:
                for p in range(w_count):
                    base = p * bpw
                    tmp = pad
                    if self.state.endian == 'little':
                        for j in range(bpw):
                            data[base + j] = tmp & 0xff; tmp >>= 8
                    else:
                        for j in range(bpw - 1, -1, -1):
                            data[base + j] = tmp & 0xff; tmp >>= 8
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
            # No SECTION directives → everything into .text
            w_count = max_w + 1 if max_w >= 0 else 0
            csecs.append(_CSec('.text', 0, _extract(0, w_count), 0x2 | 0x4))
        else:
            sec_names = list(self.state.sections.keys())
            for i, sname in enumerate(sec_names):
                w0, wn = self.state.sections[sname]
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

        # ------------------------------------------------------------------ #
        # 2. Collect relocations per content section                           #
        # ------------------------------------------------------------------ #
        # Build section-name → section-index (1-based) map
        sec_name_to_idx = {s.name: i + 1 for i, s in enumerate(csecs)}

        # Group relocations: {content_sec_index(1-based): [(offset, sym_name, type, addend)]}
        from collections import defaultdict as _defaultdict
        rela_entries = _defaultdict(list)   # sec_idx → list of (off, sym_name, rtype, addend)
        for (sname, off, sym_name, rtype, addend) in self.state.relocations:
            sidx = sec_name_to_idx.get(sname, 0)
            if sidx:
                rela_entries[sidx].append((off, sym_name, rtype, addend))

        # Content sections that have at least one relocation → need .rela.X section
        rela_sec_order = [i + 1 for i, s in enumerate(csecs) if (i + 1) in rela_entries]
        nrela = len(rela_sec_order)


        shstrtab = bytearray(b'\x00')
        sec_name_offs = []
        for s in csecs:
            sec_name_offs.append(len(shstrtab))
            shstrtab += s.name.encode() + b'\x00'
        # .rela.X セクション名を追加
        rela_name_offs = []
        for sidx in rela_sec_order:
            rela_name_offs.append(len(shstrtab))
            shstrtab += ('.rela' + csecs[sidx - 1].name).encode() + b'\x00'
        symtab_name_off   = len(shstrtab); shstrtab += b'.symtab\x00'
        strtab_name_off   = len(shstrtab); shstrtab += b'.strtab\x00'
        shstrtab_name_off = len(shstrtab); shstrtab += b'.shstrtab\x00'
        shstrtab = bytes(shstrtab)

        # ------------------------------------------------------------------ #
        # 3. Build symbol table (.symtab) and string table (.strtab)          #
        # ------------------------------------------------------------------ #
        def _find_shndx(byte_addr):
            """Return (elf_section_1based, offset_from_section_start)."""
            for i, s in enumerate(csecs):
                if s.byte_start <= byte_addr < s.byte_start + s.byte_size:
                    return i + 1, byte_addr - s.byte_start
                # label exactly at section start when size==0
                if s.byte_size == 0 and byte_addr == s.byte_start:
                    return i + 1, 0
            return 0xfff1, byte_addr   # SHN_ABS

        strtab = bytearray(b'\x00')
        syms   = []

        # null symbol
        syms.append(_pack_sym(0, 0, 0, 0, 0, 0))

        # section symbols (STB_LOCAL | STT_SECTION = 0x03)
        for i in range(ncs):
            syms.append(_pack_sym(0, 0x03, 0, i + 1, 0, 0))

        # local symbols (not in export_labels)
        export_keys = set(self.state.export_labels.keys())
        for name, *_lentry in sorted(self.state.labels.items()):
            val, _sec = _lentry[0][0], _lentry[0][1]
            is_equ = len(_lentry[0]) > 2 and _lentry[0][2]
            if name in export_keys:
                continue
            if is_equ:
                # .equ 定義ラベルは絶対値シンボル (SHN_ABS=0xfff1)
                shndx, sym_val = 0xfff1, val
            else:
                byte_addr = val * bpw
                shndx, sym_val = _find_shndx(byte_addr)
            name_off = len(strtab); strtab += name.encode() + b'\x00'
            syms.append(_pack_sym(name_off, 0x00, 0, shndx, sym_val, 0))

        first_global = len(syms)

        # global symbols (export_labels, STB_GLOBAL | STT_NOTYPE = 0x10)
        for name, *_eentry in sorted(self.state.export_labels.items()):
            val, _sec = _eentry[0][0], _eentry[0][1]
            is_equ = len(_eentry[0]) > 2 and _eentry[0][2]
            if is_equ:
                shndx, sym_val = 0xfff1, val
            else:
                byte_addr = val * bpw
                shndx, sym_val = _find_shndx(byte_addr)
            name_off = len(strtab); strtab += name.encode() + b'\x00'
            syms.append(_pack_sym(name_off, 0x10, 0, shndx, sym_val, 0))

        symtab = b''.join(syms)
        strtab = bytes(strtab)

        # ------------------------------------------------------------------ #
        # シンボル名 → シンボルテーブルインデックス のマッピングを構築        #
        # (リロケーションエントリの r_info に使う)                            #
        # ------------------------------------------------------------------ #
        sym_name_to_idx = {}
        _si = 1 + ncs   # null(0) + section syms(1..ncs) を飛ばした位置
        for name, *_lentry in sorted(self.state.labels.items()):
            val, _sec = _lentry[0][0], _lentry[0][1]
            if name in export_keys:
                continue
            sym_name_to_idx[name] = _si
            _si += 1
        for name, *_eentry in sorted(self.state.export_labels.items()):
            val, _sec = _eentry[0][0], _eentry[0][1]
            sym_name_to_idx[name] = _si
            _si += 1

        # ------------------------------------------------------------------ #
        # .rela セクションデータを構築 (Elf64_Rela: offset/info/addend 各8B)  #
        # ------------------------------------------------------------------ #
        def _pack_rela(r_offset, r_sym, r_type, r_addend):
            r_info = (r_sym << 32) | (r_type & 0xffffffff)
            return _struct.pack(f'{_pk}QQq', r_offset, r_info, r_addend)

        rela_datas = []   # rela_sec_order と同順
        for sidx in rela_sec_order:
            entries = rela_entries[sidx]
            data = b''.join(
                _pack_rela(off, sym_name_to_idx.get(sn, 0), rtype, addend)
                for (off, sn, rtype, addend) in entries
            )
            rela_datas.append(data)

        # ------------------------------------------------------------------ #
        # 4. Compute file offsets                                              #
        # ------------------------------------------------------------------ #
        offset = 64   # after ELF header
        sec_offsets = []
        for s in csecs:
            offset = _align_up(offset, 16)
            sec_offsets.append(offset)
            offset += s.byte_size

        # .rela セクションのファイルオフセット
        rela_offsets = []
        for rd in rela_datas:
            offset = _align_up(offset, 8)
            rela_offsets.append(offset)
            offset += len(rd)

        symtab_off  = _align_up(offset, 8); offset = symtab_off + len(symtab)
        strtab_off  = offset;               offset += len(strtab)
        shstrtab_off = offset;              offset += len(shstrtab)
        shdr_off    = _align_up(offset, 8)

        # セクションヘッダ数: null + content + rela + symtab + strtab + shstrtab
        total_shdrs = 1 + ncs + nrela + 3
        shstrndx    = ncs + nrela + 3
        symtab_shidx = ncs + nrela + 1     # .symtab section index
        strtab_shidx = ncs + nrela + 2     # .strtab section index (= symtab_link)
        symtab_link = strtab_shidx

        # ------------------------------------------------------------------ #
        # 5. Write ELF file                                                    #
        # ------------------------------------------------------------------ #
        with open(path, 'wb') as f:
            # ELF header
            f.write(_pack_ehdr(1, machine, shdr_off, total_shdrs, shstrndx))

            # Content section data
            for i, s in enumerate(csecs):
                cur = f.tell()
                f.write(b'\x00' * (sec_offsets[i] - cur))
                f.write(s.data)

            # .rela.X セクションデータ
            for i, rd in enumerate(rela_datas):
                cur = f.tell()
                f.write(b'\x00' * (rela_offsets[i] - cur))
                f.write(rd)

            # .symtab
            cur = f.tell(); f.write(b'\x00' * (symtab_off - cur))
            f.write(symtab)

            # .strtab
            f.write(strtab)

            # .shstrtab
            f.write(shstrtab)

            # Section header table
            cur = f.tell(); f.write(b'\x00' * (shdr_off - cur))

            f.write(_pack_shdr(0, 0, 0, 0, 0, 0, 0, 0, 0, 0))  # [0] NULL

            for i, s in enumerate(csecs):                        # [1..ncs] content
                f.write(_pack_shdr(
                    sec_name_offs[i], 1, s.flags, 0,
                    sec_offsets[i], s.byte_size, 0, 0, 16, 0))

            for ri, sidx in enumerate(rela_sec_order):           # .rela.X
                # sh_flags: SHF_INFO_LINK=0x40
                f.write(_pack_shdr(
                    rela_name_offs[ri], 4, 0x40, 0,
                    rela_offsets[ri], len(rela_datas[ri]),
                    symtab_shidx, sidx, 8, 24))

            f.write(_pack_shdr(                                   # .symtab
                symtab_name_off, 2, 0, 0,
                symtab_off, len(symtab),
                symtab_link, first_global, 8, 24))

            f.write(_pack_shdr(                                   # .strtab
                strtab_name_off, 3, 0, 0,
                strtab_off, len(strtab), 0, 0, 1, 0))

            f.write(_pack_shdr(                                   # .shstrtab
                shstrtab_name_off, 3, 0, 0,
                shstrtab_off, len(shstrtab), 0, 0, 1, 0))

        import sys as _sys
        print(f"elf: wrote {path} ({ncs} section(s), {nrela} rela section(s), {len(syms)} symbol(s))",
              file=_sys.stderr)

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
        return ap

    def run(self):
        """Main assembly process"""
        ap = self._build_arg_parser()

        # argparse prints help and exits when no arguments are given,
        # but we want a custom usage message and a clean return instead.
        if len(sys.argv) == 1:
            ap.print_help()
            return

        args = ap.parse_args()

        # make osabi table
        osabitbl = {'Linux':0,'FreeBSD':9}

        # --- Apply parsed options to assembler state ---
        self.state.outfile      = args.outfile
        self.state.expfile      = args.expfile
        self.state.expfile_elf  = args.expfile_elf
        self.state.impfile      = args.impfile
        self.state.elf_objfile  = args.elf_objfile
        self.state.elf_machine  = args.elf_machine
        self.state.osabi        = osabitbl[args.elf_osabi]

        # Load pattern file
        self.state.pat = self.pattern_reader.readpat(args.patternfile)
        self.setpatsymbols(self.state.pat)

        # Import labels
        if self.state.impfile:
            with open(self.state.impfile, 'rt') as label_file:
                for l in label_file:
                    self.imp_label(l)

        # Remove stale output file before writing
        if self.state.outfile:
            try:
                os.remove(self.state.outfile)
            except OSError:
                pass

        # --- Assemble ---
        if args.sourcefile is None:
            # Interactive / stdin mode (single pass)
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
            # Two-pass file assembly with pass1 relaxation.
            #
            # 可変長命令アーキテクチャでは、forward参照ラベルを 0 と仮定した
            # pass1 のサイズ推定が間違い、pass2 でアドレスがずれることがある。
            # 対策: pass1 を最大 MAX_RELAX 回繰り返し、全ラベルの PC が
            # 前回と一致したら収束とみなして pass2 に進む（リラクゼーション法）。
            MAX_RELAX = 8
            self.state._pass1_prev_label_pcs = None

            for relax_iter in range(MAX_RELAX):
                self.state.pc = 0
                self.state.pas = 1
                self.state.ln = 1
                self.state.labels = {}
                self.state.sections = {}
                self.state.export_labels = {}
                # ソース内の .setsym / .clearsym が前回イテレーションで
                # symbols を変化させている可能性があるため、
                # パターンファイル読み込み直後の状態（patsymbols）に毎回リセットする。
                self.state.symbols = dict(self.state.patsymbols)
                self.fileassemble(args.sourcefile)

                current_pcs = {k: v[0] for k, v in self.state.labels.items()}
                if current_pcs == self.state._pass1_prev_label_pcs:
                    if self.state.debug:
                        print(f"Pass1 relaxation converged after {relax_iter + 1} iteration(s)", file=sys.stderr)
                    break   # 収束
                self.state._pass1_prev_label_pcs = current_pcs
            else:
                # 収束しなかった場合の詳細情報
                import sys as _sys
                print("WARNING: Pass1 relaxation did not converge after {0} iterations.".format(MAX_RELAX), 
                      file=_sys.stderr)
                print("         Generated code may have incorrect addresses for", file=_sys.stderr)
                print("         variable-length instructions with forward references.", file=_sys.stderr)
                if self.state.debug and self.state._pass1_prev_label_pcs:
                    # デバッグモードでは変化したラベルを表示
                    changed = []
                    for k in current_pcs:
                        if k in self.state._pass1_prev_label_pcs:
                            if current_pcs[k] != self.state._pass1_prev_label_pcs[k]:
                                changed.append(k)
                    if changed:
                        print(f"         Labels still changing: {', '.join(changed[:10])}", file=_sys.stderr)

            self.state.pc = 0
            self.state.pas = 2
            self.state.ln = 1
            self.state.relocations = []   # pass2 でリロケーションを新規収集
            self.fileassemble(args.sourcefile)

        self.binary_writer.flush()

        # --- ELF relocatable object file ---
        if self.state.elf_objfile:
            self.write_elf_obj(self.state.elf_objfile, self.state.elf_machine)

        # --- Export labels ---
        # -e と -E が同時に指定された場合は警告を出し、両方を別々に出力する。
        # 以前は -E が -e をサイレントに上書きしていた。
        if self.state.expfile_elf and self.state.expfile:
            print(f"warning: both -e '{self.state.expfile}' and -E '{self.state.expfile_elf}' specified; "
                  f"exporting plain format to -e and ELF format to -E separately.")

        def _write_export(path, elf):
            h   = list(self.state.export_labels.items())
            key = list(self.state.sections.keys())
            with open(path, 'wt') as label_file:
                for i in key:
                    if i == '.text' and elf == 1:
                        flag = 'AX'
                    elif i == '.data' and elf == 1:
                        flag = 'WA'
                    else:
                        flag = ''
                    start = self.state.sections[i][0]
                    label_file.write(
                        f"{i}\t{start:#x}\t{self.state.sections[i][1]:#x}\t{flag}\n"
                    )
                for i in h:
                    label_file.write(f"{i[0]}\t{i[1][0]:#x}\n")

        if self.state.expfile:
            _write_export(self.state.expfile, elf=0)
        if self.state.expfile_elf:
            _write_export(self.state.expfile_elf, elf=1)

        # stdin 用一時ファイルをクリーンアップ
        if self.state.stdin_tmp_path and os.path.exists(self.state.stdin_tmp_path):
            try:
                os.remove(self.state.stdin_tmp_path)
            except OSError:
                pass
            self.state.stdin_tmp_path = None


def main():
    """Main entry point"""
    assembler = Assembler()
    assembler.run()


if __name__ == '__main__':
    main()
    exit(0)
