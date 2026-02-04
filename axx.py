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
import numpy as np
import sys
import os
import math
import re

# Expression mode constants
EXP_PAT = 0
EXP_ASM = 1

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
    "Value out of range.",
    "Invalid syntax.",
    "Address out of range.",
    "",
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
        self.sections = {}
        self.symbols = {}
        self.patsymbols = {}
        self.labels = {}
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
        self.error_already_defined = False
        
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
                return "" if idx == 0 else l[0:idx-1]
            idx += 1
        return l
    
    @staticmethod
    def remove_comment_asm(l):
        """Remove ; style comments"""
        if ';' in l:
            s = l[0:l.index(';')]
        else:
            s = l
        return s.rstrip()
    
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
        """Get quoted string"""
        idx = 0
        idx = StringUtils.skipspc(l2, idx)
        if l2 == '' or idx >= len(l2) or l2[idx] != '"':
            return ""
        idx += 1
        s = ""
        while idx < len(l2):
            if l2[idx] == '"':
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
        if s[idx:idx+3] == 'inf':
            return 'inf', idx + 3
        elif s[idx:idx+4] == '-inf':
            return '-inf', idx + 4
        elif s[idx:idx+3] == 'nan':
            return 'nan', idx + 3
        else:
            fs = ''
            while idx < len(s) and s[idx] in "0123456789-.eE":
                fs += s[idx]
                idx += 1
            return fs, idx
    
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
        """Get label word from position"""
        t = ""
        if idx < len(s) and (s[idx] == '.' or (s[idx] not in DIGIT and s[idx] in self.state.lwordchars)):
            t = s[idx]
            idx += 1
            while idx < len(s) and s[idx] in self.state.lwordchars:
                t += s[idx]
                idx += 1
            
            if idx < len(s) and s[idx] == ':':
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


class IEEE754Converter:
    """IEEE 754 floating point conversion utilities"""
    
    @staticmethod
    def decimal_to_ieee754_32bit_hex(a):
        """Convert decimal to IEEE 754 32-bit hex"""
        BIAS = 127
        SIGNIFICAND_BITS = 23
        EXPONENT_BITS = 8
        
        getcontext().prec = 34
        
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
        elif d == Decimal(0):
            sign = 0 if d >= 0 else 1
            exponent = 0
            fraction = 0
        else:
            sign = 0 if d >= 0 else 1
            d = abs(d)
            
            exponent_value = d.adjusted() + BIAS
            
            if exponent_value <= 0:
                exponent = 0
                fraction = int(d.scaleb(BIAS - SIGNIFICAND_BITS).normalize() * (2**SIGNIFICAND_BITS))
            else:
                exponent = exponent_value
                normalized_value = d / (Decimal(2) ** d.adjusted())
                fraction = int((normalized_value - 1) * (2**SIGNIFICAND_BITS))
            
            fraction &= (1 << SIGNIFICAND_BITS) - 1
        
        bits = (sign << 31) | (exponent << SIGNIFICAND_BITS) | fraction
        return f"0x{bits:08X}"
    
    @staticmethod
    def decimal_to_ieee754_64bit_hex(a):
        """Convert decimal to IEEE 754 64-bit hex"""
        BIAS = 1023
        SIGNIFICAND_BITS = 52
        EXPONENT_BITS = 11
        
        getcontext().prec = 34
        
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
        elif d == Decimal(0):
            sign = 0 if d >= 0 else 1
            exponent = 0
            fraction = 0
        else:
            sign = 0 if d >= 0 else 1
            d = abs(d)
            
            exponent_value = d.adjusted() + BIAS
            
            if exponent_value <= 0:
                exponent = 0
                fraction = int(d.scaleb(BIAS - SIGNIFICAND_BITS).normalize() * (2**SIGNIFICAND_BITS))
            else:
                exponent = exponent_value
                normalized_value = d / (Decimal(2) ** d.adjusted())
                fraction = int((normalized_value - 1) * (2**SIGNIFICAND_BITS))
            
            fraction &= (1 << SIGNIFICAND_BITS) - 1
        
        bits = (sign << 63) | (exponent << SIGNIFICAND_BITS) | fraction
        return f"0x{bits:016X}"
    
    @staticmethod
    def decimal_to_ieee754_128bit_hex(a):
        """Convert decimal to IEEE 754 128-bit hex"""
        BIAS = 16383
        SIGNIFICAND_BITS = 112
        EXPONENT_BITS = 15
        
        getcontext().prec = 34
        
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
        elif d == Decimal(0):
            sign = 0 if d >= 0 else 1
            exponent = 0
            fraction = 0
        else:
            sign = 0 if d >= 0 else 1
            d = abs(d)
            
            exponent_value = d.adjusted() + BIAS
            
            if exponent_value <= 0:
                exponent = 0
                fraction = int(d.scaleb(BIAS - SIGNIFICAND_BITS).normalize() * (2**SIGNIFICAND_BITS))
            else:
                exponent = exponent_value
                normalized_value = d / (Decimal(2) ** d.adjusted())
                fraction = int((normalized_value - 1) * (2**SIGNIFICAND_BITS))
            
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
        except:
            v = UNDEF
            self.state.error_undefined_label = True
        return v
    
    def get_value(self, k):
        """Get label value"""
        self.state.error_undefined_label = False
        try:
            v = self.state.labels[k][0]
        except:
            v = UNDEF
            self.state.error_undefined_label = True
        return v
    
    def put_value(self, k, v, s):
        """Set label value"""
        if self.state.pas == 1 or self.state.pas == 0:
            if k in self.state.labels:
                self.state.error_already_defined = True
                print(f" error - label already defined.")
                return False
        
        if StringUtils.upper(k) in self.state.patsymbols:
            print(f" error - '{k}' is a pattern file symbol.")
            return False
        
        self.state.error_already_defined = False
        self.state.labels[k] = [v, s]
        return True

    def printlabels(self):
        result = {}
        for key, value in self.state.labels.items():
            num, section = value
            result[key] = [hex(num), section]
        print(result)
        return
        
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
        r = l
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
            x = ~x
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
                    v = float(eval(t))
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
                    v = float(eval(t))
                    x = int.from_bytes(struct.pack('>f', v), "big")
        elif idx < len(s) and s[idx].isdigit():
            fs, idx = self.parser.get_intstr(s, idx)
            x = int(float(fs))
        elif (idx < len(s) and self.state.expmode == EXP_PAT and 
              s[idx] in LOWER and idx + 1 < len(s) and s[idx+1] not in LOWER):
            ch = s[idx]
            if idx + 3 <= len(s) and s[idx+1:idx+3] == ':=':
                x, idx = self.expression(s, idx + 3)
                self.var_manager.put(ch, x)
            else:
                x = self.var_manager.get(ch)
                idx += 1
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
            if s[idx] == '*':
                t, idx = self.term0_0(s, idx + 1)
                x *= t
            elif StringUtils.q(s, '//', idx):
                t, idx = self.term0_0(s, idx + 2)
                if t == 0:
                    self.err("Division by 0 error.")
                else:
                    x //= t
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
                x <<= t
            elif StringUtils.q(s, '>>', idx):
                t, idx = self.term1(s, idx + 2)
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
        while idx < len(s) and s[idx] == '\'':
            t, idx = self.term5(s, idx + 1)
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
        """Handle ternary operator"""
        x, idx = self.term10(s, idx)
        while idx < len(s) and StringUtils.q(s, '?', idx):
            t, idx = self.term10(s, idx + 1)
            if idx < len(s) and StringUtils.q(s, ':', idx):
                u, idx = self.term10(s, idx + 1)
                x = t if x != 0 else u
        return x, idx
    
    def expression(self, s, idx):
        """Main expression evaluator"""
        s += chr(0)
        idx = StringUtils.skipspc(s, idx)
        x, idx = self.term11(s, idx)
        return x, idx
    
    def expression_pat(self, s, idx):
        """Expression in pattern mode"""
        self.state.expmode = EXP_PAT
        return self.expression(s, idx)
    
    def expression_asm(self, s, idx):
        """Expression in assembly mode"""
        self.state.expmode = EXP_ASM
        return self.expression(s, idx)
    
    def expression_esc(self, s, idx, stopchar):
        """Expression with escaped stop character"""
        self.state.expmode = EXP_PAT
        result = []
        depth = 0
        
        for ch in s:
            if ch == '(':
                depth += 1
                result.append(ch)
            elif ch == ')':
                if depth > 0:
                    depth -= 1
                result.append(ch)
            else:
                if depth == 0 and ch == stopchar:
                    result.append(chr(0))
                else:
                    result.append(ch)
        
        replaced = ''.join(result)
        return self.expression(replaced, idx)


class BinaryWriter:
    """Handles binary output to files"""
    
    def __init__(self, state):
        self.state = state
    
    def fwrite(self, file_path, position, x, prt):
        """Write binary data to file"""
        b = 8 if self.state.bts <= 8 else self.state.bts
        byts = b // 8 + (0 if b / 8 == b // 8 else 1)
        
        if file_path != "":
            file = open(file_path, 'a+b')
            file.seek(position * byts)
        
        cnt = 0
        if self.state.endian == 'little':
            p = (2 ** self.state.bts) - 1
            v = x & p
            for i in range(byts):
                vv = v & 0xff
                if file_path != "":
                    file.write(struct.pack('B', vv))
                if prt:
                    print(" 0x%02x" % vv, end='')
                v = v >> 8
                cnt += 1
        else:
            bp = (2 ** self.state.bts) - 1
            x = x & bp
            p = 0xff << (byts * 8 - 8)
            for i in range(byts - 1, -1, -1):
                v = ((x & p) >> (i * 8)) & 0xff
                if file_path != "":
                    file.write(struct.pack('B', v))
                if prt:
                    print(" 0x%02x" % v, end='')
                p = p >> 8
                cnt += 1
        
        if file_path != "":
            file.close()
        return cnt
    
    def outbin2(self, a, x):
        """Output binary without printing"""
        if self.state.pas == 2 or self.state.pas == 0:
            x = int(x)
            self.fwrite(self.state.outfile, a, x, 0)
    
    def outbin(self, a, x):
        """Output binary with printing"""
        if self.state.pas == 2 or self.state.pas == 0:
            x = int(x)
            self.fwrite(self.state.outfile, a, x, 1)
    
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
        
        if len(i) > 2:
            key = StringUtils.upper(i[2])
            self.state.symbols.pop(key, None)
        elif len(i) == 1:
            self.state.symbols = {}
        
        return True
    
    def set_symbol(self, i):
        """Set symbol directive"""
        if len(i) == 0 or i[0] != '.setsym':
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
        if len(i) == 0 or (len(i) > 1 and i[0] != '.bits'):
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
        if len(i) == 0 or (len(i) > 1 and i[0] != '.padding'):
            return False
        
        if len(i) >= 3:
            v, idx = self.expr_eval.expression_pat(i[2], 0)
        else:
            v = 0
        self.state.padding = int(v)
        return True
    
    def symbolc(self, i):
        """Symbol characters directive"""
        if len(i) == 0 or (len(i) > 1 and i[0] != '.symbolc'):
            return False
        
        if len(i) > 3:
            self.state.swordchars = ALPHABET + DIGIT + i[2]
        return True
    
    def vliwp(self, i):
        """VLIW directive"""
        if len(i) == 0 or i[0] != ".vliw":
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
            
            u, idxn = self.expr_eval.expression_pat(s, idx)
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
        """Remove specified bracket pairs"""
        open_count = 0
        result = list(s)
        bracket_positions = []
        
        for i, char in enumerate(s):
            if char == OB:
                open_count += 1
                bracket_positions.append((open_count, i, 'open'))
            elif char == CB:
                bracket_positions.append((open_count, i, 'close'))
        
        for index in sorted(l, reverse=True):
            start_index = None
            end_index = None
            for count, pos, type in bracket_positions:
                if count == index and type == 'open':
                    start_index = pos
                elif count == index and type == 'close':
                    end_index = pos
                    break
            
            if start_index is not None and end_index is not None:
                for j in range(start_index, end_index + 1):
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
                if a == '!':
                    a = t[idx_t]
                    idx_t += 1
                    v, idx_s = self.expr_eval.factor(s, idx_s)
                    self.var_manager.put(a, v)
                    continue
                else:
                    idx_t = StringUtils.skipspc(t, idx_t)
                    if idx_t < len(t) and t[idx_t] == '\\':
                        idx_t = StringUtils.skipspc(t, idx_t + 1)
                        b = t[idx_t] if idx_t < len(t) else chr(0)
                        stopchar = b
                    else:
                        stopchar = chr(0)
                    
                    v, idx_s = self.expr_eval.expression_esc(s, idx_s, stopchar)
                    self.var_manager.put(a, v)
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
        """Match with optional bracket combinations"""
        t = t.replace('[[', OB).replace(']]', CB)
        cnt = t.count(OB)
        sl = [_ + 1 for _ in range(cnt)]
        
        for i in range(len(sl) + 1):
            ll = list(itertools.combinations(sl, i))
            for j in ll:
                lt = self.remove_brackets(t, list(j))
                if self.match(s, lt):
                    return True
        return False


class PatternFileReader:
    """Reads and processes pattern files"""
    
    def __init__(self, parser):
        self.parser = parser
    
    def readpat(self, fn):
        """Read pattern file"""
        if fn == '':
            return []
        
        f = open(fn, "rt")
        p = []
        w = []
        
        while True:
            l = f.readline()
            if not l:
                break
            
            l = StringUtils.remove_comment(l)
            l = l.replace('\t', ' ')
            l = l.replace(chr(13), '')
            l = l.replace('\n', '')
            l = StringUtils.reduce_spaces(l)
            
            ww = self.include_pat(l)
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
                    p = ["", "", "", "", "", "", ""]
                w.append(p)
        
        f.close()
        return w
    
    def include_pat(self, l):
        """Include pattern directive"""
        idx = StringUtils.skipspc(l, 0)
        i = l[idx:idx+8]
        i = i.upper()
        if i != ".INCLUDE":
            return []
        s = StringUtils.get_string(l[8:])
        w = self.readpat(s)
        return w


class ObjectGenerator:
    """Generates object code from expressions"""
    
    def __init__(self, state, expr_eval, binary_writer):
        self.state = state
        self.expr_eval = expr_eval
        self.binary_writer = binary_writer
    
    def replace_percent_with_index(self, s):
        """Replace %% with sequential numbers starting from 1"""
        count = 0
        result = []
        i = 0
        while i < len(s):
            if i + 1 < len(s) and s[i:i+2] == '%%':
                result.append(str(count))
                count += 1
                i += 2
            else:
                result.append(s[i])
                i += 1
        return ''.join(result)

    def e_p(self, pattern):
        """Expand rep[expr,pattern] syntax"""
        result = []
        i = 0
        while i < len(pattern):
            if i + 4 <= len(pattern) and pattern[i:i+4] == 'rep[':
                # Find matching ]
                i += 4
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
                    for j in range(int(n)):
                        if j > 0:
                            result.append(',')
                        result.append(rep_pattern)
                    
                    i += 1  # Skip closing ]
                else:
                    result.append('rep[')
            else:
                result.append(pattern[i])
                i += 1
        
        return ''.join(result)

    def makeobj(self, s):
        """Make object code from expression string"""
        # Expand rep[] and replace %%
        s = self.e_p(s)
        s = self.replace_percent_with_index(s)
        
        s += chr(0)
        idx = 0
        objl = []
        
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
            
            x, idx = self.expr_eval.expression_pat(s, idx)
            
            if (semicolon == True and x != 0) or (semicolon == False):
                objl += [x]
            
            if idx < len(s) and s[idx] == ',':
                idx += 1
                continue
            break
        
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
            if list(set(k[0])) == list(set(idxlst)) or self.state.vliwtemplatebits == 0:
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
                
                for i in range(ibyte * noi - len(values)):
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
                self.label_manager.put_value(label, u, self.state.current_section)
                return ""
            else:
                self.label_manager.put_value(label, self.state.pc, self.state.current_section)
                return l[lidx:]
        return l
    
    def asciistr(self, l2):
        """Process ASCII string"""
        idx = 0
        if l2 == '' or l2[idx] != '"':
            return False
        idx += 1
        
        while idx < len(l2):
            if l2[idx] == '"':
                return True
            if l2[idx:idx+2] == '\\0':
                idx += 2
                ch = chr(0)
            elif l2[idx:idx+2] == '\\t':
                idx += 2
                ch = '\t'
            elif l2[idx:idx+2] == '\\n':
                idx += 2
                ch = '\n'
            else:
                ch = l2[idx]
                idx += 1
            self.binary_writer.outbin(self.state.pc, ord(ch))
            self.state.pc += 1
    
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
        for i in range(x + 1):
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
        if f:
            self.binary_writer.outbin(self.state.pc, 0x00)
            self.state.pc += 1
        return True
    
    def section_processing(self, l1, l2):
        """Section directive"""
        if StringUtils.upper(l1) != "SECTION" and StringUtils.upper(l1) != "SEGMENT":
            return False
        
        if l2 != '':
            self.state.current_section = l2
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
    
    def include_asm(self, l1, l2):
        """Include directive"""
        if StringUtils.upper(l1) != ".INCLUDE":
            return False
        s = StringUtils.get_string(l2)
        if s:
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
            
            lw = len([_ for _ in i if _])
            if lw == 0:
                continue
            
            lin = l + ' ' + l2
            lin = StringUtils.reduce_spaces(lin)
            
            if i[0] == '':
                loopflag = False
                break
            
            self.state.error_undefined_label = False
            
            if not self.state.debug:
                try:
                    if self.pattern_matcher.match0(lin, i[0]) == True:
                        self.directive_proc.error(i[1])
                        objl = self.obj_gen.makeobj(i[2])
                        idxs, _ = self.expr_eval.expression_pat(i[3], 0)
                        loopflag = False
                        break
                except:
                    oerr = True
                    loopflag = False
                    break
            else:
                if self.pattern_matcher.match0(lin, i[0]) == True:
                    self.directive_proc.error(i[1])
                    objl = self.obj_gen.makeobj(i[2])
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
        
        line = self.asm_directive_proc.label_processing(line)
        self.directive_proc.clear_symbol([".clearsym", "", ""])
        
        parts = line.split("!!")
        self.state.vcnt = sum(1 for p in parts if p != "")
        
        idxs, objl, flag, idx = self.lineassemble2(line, 0)
        
        if flag == False:
            return False
        
        if self.state.vliwflag == False or (idx >= len(line) or line[idx:idx+2] != '!!'):
            of = len(objl)
            for cnt in range(of):
                self.binary_writer.outbin(self.state.pc + cnt, objl[cnt])
            self.state.pc += of
        else:
            vflag = False
            try:
                vflag = self.vliw_proc.vliwprocess(line, idxs, objl, flag, idx, self.lineassemble2)
            except:
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
        self.state.fnstack += [self.state.current_file]
        self.state.lnstack += [self.state.ln]
        self.state.current_file = fn
        self.state.ln = 1
        
        if fn == "stdin":
            if self.state.pas != 2 and self.state.pas != 0:
                af = self.file_input_from_stdin()
                with open("axx.tmp", "wt") as stdintmp:
                    stdintmp.write(af)
            fn = "axx.tmp"
        
        f = open(fn, "rt")
        af = f.readlines()
        f.close()
        
        for i in af:
            self.lineassemble0(i)
        
        if self.state.fnstack:
            self.state.current_file = self.state.fnstack.pop()
            self.state.ln = self.state.lnstack.pop()
    
    def file_input_from_stdin(self):
        """Read input from stdin"""
        af = ""
        while True:
            line = sys.stdin.readline().strip()
            if line == '':
                break
            af += line + '\n'
        return af
    
    def imp_label(self, l):
        """Import label"""
        idx = StringUtils.skipspc(l, 0)
        section, idx = self.parser.get_label_word(l, idx)
        idx = StringUtils.skipspc(l, idx)
        label, idx = self.parser.get_label_word(l, idx)
        if label == '':
            return False
        idx = StringUtils.skipspc(l, idx)
        v, new_idx = self.expr_eval.expression(l, idx)
        if new_idx == idx:
            return False
        idx = new_idx
        self.label_manager.put_value(label, v, section)
        return True
    
    def option(self, l, o):
        """Parse command line option"""
        if o in l:
            idx = l.index(o)
            if idx + 1 < len(l):
                if idx + 2 < len(l):
                    return l[0:idx] + l[idx+2:], l[idx+1]
                else:
                    return l[0:idx], l[idx+1]
            else:
                return l[0:idx], ''
        return l, ''
    
    def printaddr(self, pc):
        """Print address"""
        print("%016x: " % pc, end='')
    
    def run(self):
        """Main assembly process"""
        if len(sys.argv) == 1:
            print("axx general assembler programmed and designed by Taisuke Maekawa")
            print("Usage: python axx.py patternfile.axx [sourcefile.s] [-o outfile.bin] [-e export_labels.tsv] [-i import_labels.tsv]")
            return
        
        sys_argv = sys.argv
        
        if len(sys_argv) >= 2:
            self.state.pat = self.pattern_reader.readpat(sys_argv[1])
            self.setpatsymbols(self.state.pat)
        
        sys_argv, self.state.expfile = self.option(sys_argv, "-e")
        sys_argv, expefile = self.option(sys_argv, "-E")
        sys_argv, self.state.outfile = self.option(sys_argv, '-o')
        sys_argv, self.state.impfile = self.option(sys_argv, "-i")
        
        if self.state.impfile != "":
            with open(self.state.impfile, "rt") as label_file:
                while True:
                    l = label_file.readline()
                    if not l:
                        break
                    self.imp_label(l)
        
        try:
            os.remove(self.state.outfile)
        except:
            pass
        
        if self.state.outfile:
            f = open(self.state.outfile, "wb")
            f.close()
        
        if len(sys_argv) == 2:
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
        
        elif len(sys_argv) >= 3:
            self.state.pc = 0
            self.state.pas = 1
            self.state.ln = 1
            self.fileassemble(sys.argv[2])
            self.state.pc = 0
            self.state.pas = 2
            self.state.ln = 1
            self.fileassemble(sys.argv[2])
        
        if expefile != "":
            self.state.expfile = expefile
            elf = 1
        else:
            elf = 0
        
        if self.state.expfile != "":
            h = list(self.state.export_labels.items())
            key = list(self.state.sections.keys())
            with open(self.state.expfile, "wt") as label_file:
                for i in key:
                    if i == '.text' and elf == 1:
                        flag = 'AX'
                    elif i == '.data' and elf == 1:
                        flag = 'WA'
                    else:
                        flag = ''
                    start = self.state.sections[i][0]
                    label_file.write(f"{i}\t{start:#x}\t{self.state.sections[i][1]:#x}\t{flag}\n")
                for i in h:
                    label_file.write(f"{i[0]}\t{i[1][0]:#x}\n")


def main():
    """Main entry point"""
    assembler = Assembler()
    assembler.run()


if __name__ == '__main__':
    main()
    exit(0)
