#!/usr/bin/env python3
# cython: language_level=3

"""
axx general assembler designed and programmed by Taisuke Maekawa
Refactored for improved readability and maintainability
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


# Global state instance
state = AssemblerState()


# Utility functions
def add_avoiding_dup(l, e):
    """Add element to list avoiding duplicates"""
    if e not in l:
        l.append(e)
    return l


def upper(s):
    """Convert string to uppercase"""
    return ''.join(c.upper() if c in LOWER else c for c in s)


def q(s, t, idx):
    """Quick comparison of substring"""
    return upper(s[idx:idx+len(t)]) == upper(t)


def err(m):
    """Print error message"""
    print(m)
    return -1


def nbit(l):
    """Count number of bits needed to represent value"""
    b = 0
    r = l
    while r:
        r >>= 1
        b += 1
    return b


def skipspc(s, idx):
    """Skip spaces in string"""
    while idx < len(s) and s[idx] == ' ':
        idx += 1
    return idx


def get_param_to_spc(s, idx):
    """Get parameter up to space"""
    t = ""
    idx = skipspc(s, idx)
    while idx < len(s) and s[idx] != ' ':
        t += s[idx]
        idx += 1
    return t, idx


def get_param_to_eon(s, idx):
    """Get parameter to end of line or !!"""
    t = ""
    idx = skipspc(s, idx)
    while idx < len(s) and s[idx:idx+2] != '!!':
        t += s[idx]
        idx += 1
    return t, idx


def reduce_spaces(text):
    """Reduce multiple spaces to single space"""
    return re.sub(r'\s{2,}', ' ', text)


def remove_comment(l):
    """Remove /* style comments"""
    idx = 0
    while idx < len(l):
        if l[idx:idx+2] == '/*':
            return "" if idx == 0 else l[0:idx-1]
        idx += 1
    return l


def remove_comment_asm(l):
    """Remove ; style comments"""
    if ';' in l:
        s = l[0:l.index(';')]
    else:
        s = l
    return s.rstrip()


# Variable management
def get_vars(s):
    """Get variable value by letter"""
    c = ord(upper(s))
    return state.vars[c - ord('A')]


def put_vars(s, v):
    """Set variable value by letter"""
    if upper(s) in CAPITAL:
        c = ord(upper(s))
        state.vars[c - ord('A')] = int(v)


# Label management
def get_label_section(k):
    """Get label section"""
    state.error_undefined_label = False
    try:
        v = state.labels[k][1]
    except:
        v = UNDEF
        state.error_undefined_label = True
    return v


def get_label_value(k):
    """Get label value"""
    state.error_undefined_label = False
    try:
        v = state.labels[k][0]
    except:
        v = UNDEF
        state.error_undefined_label = True
    return v


def put_label_value(k, v, s):
    """Set label value"""
    if state.pas == 1 or state.pas == 0:
        if k in state.labels:
            state.error_already_defined = True
            print(f" error - label already defined.")
            return False
    
    if upper(k) in state.patsymbols:
        print(f" error - '{k}' is a pattern file symbol.")
        return False
    
    state.error_already_defined = False
    state.labels[k] = [v, s]
    return True


# IEEE 754 conversion functions
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


# String parsing helpers
def get_intstr(s, idx):
    """Get integer string from position"""
    fs = ''
    while idx < len(s) and s[idx] in DIGIT:
        fs += s[idx]
        idx += 1
    return fs, idx


def get_floatstr(s, idx):
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


def get_curlb(s, idx):
    """Get curly bracket content"""
    idx = skipspc(s, idx)
    f = False
    t = ''
    
    if idx < len(s) and s[idx] == '{':
        idx += 1
        f = True
        idx = skipspc(s, idx)
        while idx < len(s) and s[idx] != '}':
            t += s[idx]
            idx += 1
        idx = skipspc(s, idx)
        if idx < len(s) and s[idx] == '}':
            idx += 1
    
    return f, t, idx


def get_symbol_word(s, idx):
    """Get symbol word from position"""
    t = ""
    if idx < len(s) and s[idx] not in DIGIT and s[idx] in state.swordchars:
        t = s[idx]
        idx += 1
        while idx < len(s) and s[idx] in state.swordchars:
            t += s[idx]
            idx += 1
    return upper(t), idx


def get_label_word(s, idx):
    """Get label word from position"""
    t = ""
    if idx < len(s) and (s[idx] == '.' or (s[idx] not in DIGIT and s[idx] in state.lwordchars)):
        t = s[idx]
        idx += 1
        while idx < len(s) and s[idx] in state.lwordchars:
            t += s[idx]
            idx += 1
        
        if idx < len(s) and s[idx] == ':':
            idx += 1
    
    return t, idx


def getsymval(w):
    """Get symbol value"""
    w = w.upper()
    return state.symbols.get(w, "")


# Expression evaluation
def factor(s, idx):
    """Parse factor in expression"""
    idx = skipspc(s, idx)
    x = 0
    
    if idx + 4 <= len(s) and s[idx:idx+4] == '!!!!' and state.expmode == EXP_PAT:
        x = state.vliwstop
        idx += 4
    elif idx + 3 <= len(s) and s[idx:idx+3] == '!!!' and state.expmode == EXP_PAT:
        x = state.vcnt
        idx += 3
    elif idx < len(s) and s[idx] == '-':
        x, idx = factor(s, idx + 1)
        x = -x
    elif idx < len(s) and s[idx] == '~':
        x, idx = factor(s, idx + 1)
        x = ~x
    elif idx < len(s) and s[idx] == '@':
        x, idx = factor(s, idx + 1)
        x = nbit(x)
    else:
        x, idx = factor1(s, idx)
    
    idx = skipspc(s, idx)
    return x, idx


def factor1(s, idx):
    """Parse primary factor"""
    x = 0
    idx = skipspc(s, idx)
    
    if idx >= len(s):
        return x, idx
    
    if s[idx] == '(':
        x, idx = expression(s, idx + 1)
        if idx < len(s) and s[idx] == ')':
            idx += 1
    elif q(s, '$$', idx):
        idx += 2
        x = state.pc
    elif q(s, '#', idx):
        idx += 1
        t, idx = get_symbol_word(s, idx)
        x = getsymval(t)
    elif q(s, '0b', idx):
        idx += 2
        while idx < len(s) and s[idx] in "01":
            x = 2 * x + int(s[idx], 2)
            idx += 1
    elif q(s, '0x', idx):
        idx += 2
        while idx < len(s) and upper(s[idx]) in XDIGIT:
            x = 16 * x + int(s[idx].lower(), 16)
            idx += 1
    elif idx + 3 <= len(s) and s[idx:idx+3] == 'qad':
        idx += 3
        idx = skipspc(s, idx)
        if idx < len(s) and s[idx] == '{':
            fs, idx = get_floatstr(s, idx + 1)
            h = decimal_to_ieee754_128bit_hex(fs)
            x = int(h, 16)
        if idx < len(s) and s[idx] == '}':
            idx += 1
    elif idx + 3 <= len(s) and s[idx:idx+3] == 'dbl':
        idx += 3
        f, t, idx = get_curlb(s, idx)
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
        f, t, idx = get_curlb(s, idx)
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
        fs, idx = get_intstr(s, idx)
        x = int(float(fs))
    elif (idx < len(s) and state.expmode == EXP_PAT and 
          s[idx] in LOWER and idx + 1 < len(s) and s[idx+1] not in LOWER):
        ch = s[idx]
        if idx + 3 <= len(s) and s[idx+1:idx+3] == ':=':
            x, idx = expression(s, idx + 3)
            put_vars(ch, x)
        else:
            x = get_vars(ch)
            idx += 1
    elif idx < len(s) and s[idx] in state.lwordchars:
        w, idx_new = get_label_word(s, idx)
        if idx != idx_new:
            idx = idx_new
            x = get_label_value(w)
    
    idx = skipspc(s, idx)
    return x, idx


def term0_0(s, idx):
    """Handle exponentiation"""
    x, idx = factor(s, idx)
    while idx < len(s) and q(s, '**', idx):
        t, idx = factor(s, idx + 2)
        x = x ** t
    return x, idx


def term0(s, idx):
    """Handle multiplication, division, modulo"""
    x, idx = term0_0(s, idx)
    while idx < len(s):
        if s[idx] == '*':
            t, idx = term0_0(s, idx + 1)
            x *= t
        elif q(s, '//', idx):
            t, idx = term0_0(s, idx + 2)
            if t == 0:
                err("Division by 0 error.")
            else:
                x //= t
        elif s[idx] == '%':
            t, idx = term0_0(s, idx + 1)
            if t == 0:
                err("Division by 0 error.")
            else:
                x = x % t
        else:
            break
    return x, idx


def term1(s, idx):
    """Handle addition, subtraction"""
    x, idx = term0(s, idx)
    while idx < len(s):
        if s[idx] == '+':
            t, idx = term0(s, idx + 1)
            x += t
        elif s[idx] == '-':
            t, idx = term0(s, idx + 1)
            x -= t
        else:
            break
    return x, idx


def term2(s, idx):
    """Handle bit shifts"""
    x, idx = term1(s, idx)
    while idx < len(s):
        if q(s, '<<', idx):
            t, idx = term1(s, idx + 2)
            x <<= t
        elif q(s, '>>', idx):
            t, idx = term1(s, idx + 2)
            x >>= t
        else:
            break
    return x, idx


def term3(s, idx):
    """Handle bitwise AND"""
    x, idx = term2(s, idx)
    while idx < len(s) and s[idx] == '&' and (idx + 1 >= len(s) or s[idx+1] != '&'):
        t, idx = term2(s, idx + 1)
        x = int(x) & int(t)
    return x, idx


def term4(s, idx):
    """Handle bitwise OR"""
    x, idx = term3(s, idx)
    while idx < len(s) and s[idx] == '|' and (idx + 1 >= len(s) or s[idx+1] != '|'):
        t, idx = term3(s, idx + 1)
        x = int(x) | int(t)
    return x, idx


def term5(s, idx):
    """Handle bitwise XOR"""
    x, idx = term4(s, idx)
    while idx < len(s) and s[idx] == '^':
        t, idx = term4(s, idx + 1)
        x = int(x) ^ int(t)
    return x, idx


def term6(s, idx):
    """Handle sign extension"""
    x, idx = term5(s, idx)
    while idx < len(s) and s[idx] == '\'':
        t, idx = term5(s, idx + 1)
        x = (x & ~((~0) << t)) | ((~0) << t if (x >> (t-1) & 1) else 0)
    return x, idx


def term7(s, idx):
    """Handle comparisons"""
    x, idx = term6(s, idx)
    while idx < len(s):
        if q(s, '<=', idx):
            t, idx = term6(s, idx + 2)
            x = 1 if x <= t else 0
        elif s[idx] == '<':
            t, idx = term6(s, idx + 1)
            x = 1 if x < t else 0
        elif q(s, '>=', idx):
            t, idx = term6(s, idx + 2)
            x = 1 if x >= t else 0
        elif s[idx] == '>':
            t, idx = term6(s, idx + 1)
            x = 1 if x > t else 0
        elif q(s, '==', idx):
            t, idx = term6(s, idx + 2)
            x = 1 if x == t else 0
        elif q(s, '!=', idx):
            t, idx = term6(s, idx + 2)
            x = 1 if x != t else 0
        else:
            break
    return x, idx


def term8(s, idx):
    """Handle logical NOT"""
    if idx + 4 <= len(s) and s[idx:idx+4] == 'not(':
        x, idx = expression(s, idx + 3)
        x = 0 if x else 1
    else:
        x, idx = term7(s, idx)
    return x, idx


def term9(s, idx):
    """Handle logical AND"""
    x, idx = term8(s, idx)
    while idx < len(s) and q(s, '&&', idx):
        t, idx = term8(s, idx + 2)
        x = 1 if x and t else 0
    return x, idx


def term10(s, idx):
    """Handle logical OR"""
    x, idx = term9(s, idx)
    while idx < len(s) and q(s, '||', idx):
        t, idx = term9(s, idx + 2)
        x = 1 if x or t else 0
    return x, idx


def term11(s, idx):
    """Handle ternary operator"""
    x, idx = term10(s, idx)
    while idx < len(s) and q(s, '?', idx):
        t, idx = term10(s, idx + 1)
        if idx < len(s) and q(s, ':', idx):
            u, idx = term10(s, idx + 1)
            x = t if x != 0 else u
    return x, idx


def expression(s, idx):
    """Main expression evaluator"""
    s += chr(0)
    idx = skipspc(s, idx)
    x, idx = term11(s, idx)
    return x, idx


def expression0(s, idx):
    """Expression in pattern mode"""
    state.expmode = EXP_PAT
    return expression(s, idx)


def expression1(s, idx):
    """Expression in assembly mode"""
    state.expmode = EXP_ASM
    return expression(s, idx)


def expression_esc(s, idx, stopchar):
    """Expression with escaped stop character"""
    state.expmode = EXP_PAT
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
    return expression(replaced, idx)


# Symbol and directive processing
def clear_symbol(i):
    """Clear symbol directive"""
    if len(i) == 0 or i[0] != '.clearsym':
        return False
    
    if len(i) > 2:
        key = upper(i[2])
        state.symbols.pop(key, None)
    elif len(i) == 1:
        state.symbols = {}
    
    return True


def set_symbol(i):
    """Set symbol directive"""
    if len(i) == 0 or i[0] != '.setsym':
        return False
    
    key = upper(i[1])
    if len(i) > 2:
        v, idx = expression0(i[2], 0)
    else:
        v = 0
    state.symbols[key] = v
    return True


def bits(i):
    """Bits directive"""
    if len(i) == 0 or (len(i) > 1 and i[0] != '.bits'):
        return False
    
    if len(i) >= 2 and i[1] == 'big':
        state.endian = 'big'
    else:
        state.endian = 'little'
    
    if len(i) >= 3:
        v, idx = expression0(i[2], 0)
    else:
        v = 8
    state.bts = int(v)
    return True


def paddingp(i):
    """Padding directive"""
    if len(i) == 0 or (len(i) > 1 and i[0] != '.padding'):
        return False
    
    if len(i) >= 3:
        v, idx = expression0(i[2], 0)
    else:
        v = 0
    state.padding = int(v)
    return True


def symbolc(i):
    """Symbol characters directive"""
    if len(i) == 0 or (len(i) > 1 and i[0] != '.symbolc'):
        return False
    
    if len(i) > 3:
        state.swordchars = ALPHABET + DIGIT + i[2]
    return True


def vliwp(i):
    """VLIW directive"""
    if len(i) == 0 or i[0] != ".vliw":
        return False
    
    v1, idx = expression0(i[1], 0)
    v2, idx = expression0(i[2], 0)
    v3, idx = expression0(i[3], 0)
    v4, idx = expression0(i[4], 0)
    
    state.vliwbits = int(v1)
    state.vliwinstbits = int(v2)
    state.vliwtemplatebits = int(v3)
    state.vliwflag = True
    
    l = []
    for i in range(state.vliwinstbits // 8 + (0 if state.vliwinstbits % 8 == 0 else 1)):
        l += [v4 & 0xff]
        v4 >>= 8
    state.vliwnop = l
    return True


def epic(i):
    """EPIC directive"""
    if len(i) == 0 or upper(i[0]) != "EPIC":
        return False
    
    if len(i) <= 1 or i[1] == '':
        return False
    
    s = i[1]
    idxs = []
    idx = 0
    while True:
        v, idx = expression0(s, idx)
        idxs += [v]
        if idx < len(s) and s[idx] == ',':
            idx += 1
            continue
        break
    
    s2 = i[2]
    state.vliwset = add_avoiding_dup(state.vliwset, [idxs, s2])
    return True


# File I/O functions
def fwrite(file_path, position, x, prt):
    """Write binary data to file"""
    b = 8 if state.bts <= 8 else state.bts
    byts = b // 8 + (0 if b / 8 == b // 8 else 1)
    
    if file_path != "":
        file = open(file_path, 'a+b')
        file.seek(position * byts)
    
    cnt = 0
    if state.endian == 'little':
        p = (2 ** state.bts) - 1
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
        bp = (2 ** state.bts) - 1
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


def outbin2(a, x):
    """Output binary without printing"""
    if state.pas == 2 or state.pas == 0:
        x = int(x)
        fwrite(state.outfile, a, x, 0)


def outbin(a, x):
    """Output binary with printing"""
    if state.pas == 2 or state.pas == 0:
        x = int(x)
        fwrite(state.outfile, a, x, 1)


def align_(addr):
    """Align address"""
    a = addr % state.align
    if a == 0:
        return addr
    return addr + state.align - a


# Pattern file processing
def get_params1(l, idx):
    """Get parameters separated by ::"""
    idx = skipspc(l, idx)
    
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


def readpat(fn):
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
        
        l = remove_comment(l)
        l = l.replace('\t', ' ')
        l = l.replace(chr(13), '')
        l = l.replace('\n', '')
        l = reduce_spaces(l)
        
        ww = include_pat(l)
        if ww:
            w = w + ww
            continue
        else:
            r = []
            idx = 0
            while True:
                s, idx = get_params1(l, idx)
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


def include_pat(l):
    """Include pattern directive"""
    idx = skipspc(l, 0)
    i = l[idx:idx+8]
    i = i.upper()
    if i != ".INCLUDE":
        return []
    s = get_string(l[8:])
    w = readpat(s)
    return w


# Assembly object generation
def makeobj(s):
    """Make object code from expression string"""
    s += chr(0)
    idx = 0
    objl = []
    
    while True:
        if idx >= len(s) or s[idx] == chr(0):
            break
        
        if s[idx] == ',':
            idx += 1
            p = state.pc + len(objl)
            n = align_(p)
            for i in range(p, n):
                objl += [state.padding]
            continue
        
        semicolon = False
        if s[idx] == ';':
            semicolon = True
            idx += 1
        
        x, idx = expression0(s, idx)
        
        if (semicolon == True and x != 0) or (semicolon == False):
            objl += [x]
        
        if idx < len(s) and s[idx] == ',':
            idx += 1
            continue
        break
    
    return objl


# Pattern matching
def remove_brackets(s, l):
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


def match(s, t):
    """Match assembly line against pattern"""
    state.deb1 = s
    state.deb2 = t
    
    t = t.replace(OB, '').replace(CB, '')
    idx_s = 0
    idx_t = 0
    idx_s = skipspc(s, idx_s)
    idx_t = skipspc(t, idx_t)
    s += chr(0)
    t += chr(0)
    
    while True:
        idx_s = skipspc(s, idx_s)
        idx_t = skipspc(t, idx_t)
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
                v, idx_s = factor(s, idx_s)
                put_vars(a, v)
                continue
            else:
                idx_t = skipspc(t, idx_t)
                if idx_t < len(t) and t[idx_t] == '\\':
                    idx_t = skipspc(t, idx_t + 1)
                    b = t[idx_t] if idx_t < len(t) else chr(0)
                    stopchar = b
                else:
                    stopchar = chr(0)
                
                v, idx_s = expression_esc(s, idx_s, stopchar)
                put_vars(a, v)
                continue
        elif a in LOWER:
            idx_t += 1
            w, idx_s = get_symbol_word(s, idx_s)
            v = getsymval(w)
            if v == "":
                return False
            put_vars(a, v)
            continue
        elif a == b:
            idx_t += 1
            idx_s += 1
            continue
        else:
            return False


def match0(s, t):
    """Match with optional bracket combinations"""
    t = t.replace('[[', OB).replace(']]', CB)
    cnt = t.count(OB)
    sl = [_ + 1 for _ in range(cnt)]
    
    for i in range(len(sl) + 1):
        ll = list(itertools.combinations(sl, i))
        for j in ll:
            lt = remove_brackets(t, list(j))
            if match(s, lt):
                return True
    return False


# Error handling
def error(s):
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
        
        u, idxn = expression0(s, idx)
        idx = idxn
        if idx < len(s) and s[idx] == ';':
            idx += 1
        t, idx = expression0(s, idx)
        
        if (state.pas == 2 or state.pas == 0) and u:
            print(f"Line {state.ln} Error code {t} ", end="")
            if t >= 0 and t < len(ERRORS):
                print(f"{ERRORS[t]}", end='')
            print(": ")
            error_code = t


# Label processing
def labelc_processing(l, ll):
    """Label characters directive"""
    if l.upper() != '.LABELC':
        return False
    if ll:
        state.lwordchars = ALPHABET + DIGIT + ll
    return True


def label_processing(l):
    """Process label definitions"""
    if l == "":
        return ""
    
    label, idx = get_label_word(l, 0)
    lidx = idx
    
    if label != "" and idx > 0 and l[idx-1] == ':':
        idx = skipspc(l, idx)
        e, idx = get_param_to_spc(l, idx)
        if e.upper() == '.EQU':
            u, idx = expression1(l, idx)
            put_label_value(label, u, state.current_section)
            return ""
        else:
            put_label_value(label, state.pc, state.current_section)
            return l[lidx:]
    return l


def get_string(l2):
    """Get quoted string"""
    idx = 0
    idx = skipspc(l2, idx)
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


# Directive processors
def asciistr(l2):
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
        outbin(state.pc, ord(ch))
        state.pc += 1


def export_processing(l1, l2):
    """Export directive"""
    if not (state.pas == 2 or state.pas == 0):
        return False
    if upper(l1) != ".EXPORT":
        return False
    
    idx = 0
    l2 += chr(0)
    while idx < len(l2) and l2[idx] != chr(0):
        idx = skipspc(l2, idx)
        s, idx = get_label_word(l2, idx)
        if s == "":
            break
        if idx < len(l2) and l2[idx] == ':':
            idx += 1
        v = get_label_value(s)
        sec = get_label_section(s)
        state.export_labels[s] = [v, sec]
        if idx < len(l2) and l2[idx] == ',':
            idx += 1
    return True


def zero_processing(l1, l2):
    """Zero directive"""
    if upper(l1) != ".ZERO":
        return False
    x, idx = expression1(l2, 0)
    for i in range(x + 1):
        outbin2(state.pc, 0x00)
        state.pc += 1
    return True


def ascii_processing(l1, l2):
    """ASCII directive"""
    if upper(l1) != ".ASCII":
        return False
    return asciistr(l2)


def asciiz_processing(l1, l2):
    """ASCIIZ directive"""
    if upper(l1) != ".ASCIIZ":
        return False
    f = asciistr(l2)
    if f:
        outbin(state.pc, 0x00)
        state.pc += 1
    return True


def include_asm(l1, l2):
    """Include directive"""
    if upper(l1) != ".INCLUDE":
        return False
    s = get_string(l2)
    if s:
        fileassemble(s)
    return True


def section_processing(l1, l2):
    """Section directive"""
    if upper(l1) != "SECTION" and upper(l1) != "SEGMENT":
        return False
    
    if l2 != '':
        state.current_section = l2
        state.sections[l2] = [state.pc, 0]
    return True


def align_processing(l1, l2):
    """Align directive"""
    if upper(l1) != ".ALIGN":
        return False
    
    if l2 != '':
        u, idx = expression1(l2, 0)
        state.align = int(u)
    
    state.pc = align_(state.pc)
    return True


def endsection_processing(l1, l2):
    """End section directive"""
    if upper(l1) != "ENDSECTION" and upper(l1) != "ENDSEGMENT":
        return False
    start = state.sections[state.current_section][0]
    state.sections[state.current_section] = [start, state.pc - start]
    return True


def org_processing(l1, l2):
    """ORG directive"""
    if upper(l1) != ".ORG":
        return False
    u, idx = expression1(l2, 0)
    if idx + 2 <= len(l2) and l2[idx:idx+2].upper() == ',P':
        if u > state.pc:
            for i in range(u - state.pc):
                outbin2(i + state.pc, state.padding)
    state.pc = u
    return True


def printaddr(pc):
    """Print address"""
    print("%016x: " % pc, end='')


# VLIW processing
def vliwprocess(line, idxs, objl, flag, idx):
    """Process VLIW instruction"""
    objs = [objl]
    idxlst = [idxs]
    state.vliwstop = 0
    
    while True:
        idx = skipspc(line, idx)
        if idx + 4 <= len(line) and line[idx:idx+4] == '!!!!':
            idx += 4
            state.vliwstop = 1
            continue
        elif idx + 2 <= len(line) and line[idx:idx+2] == '!!':
            idx += 2
            idxs, objl, flag, idx = lineassemble2(line, idx)
            objs += [objl]
            idxlst += [idxs]
            continue
        else:
            break
    
    if state.vliwtemplatebits == 0:
        state.vliwset = [[[0], "0"]]
    
    vbits = abs(state.vliwbits)
    for k in state.vliwset:
        if list(set(k[0])) == list(set(idxlst)) or state.vliwtemplatebits == 0:
            im = 2 ** state.vliwinstbits - 1
            tm = 2 ** abs(state.vliwtemplatebits) - 1
            pm = 2 ** vbits - 1
            x, idx = expression0(k[1], 0)
            templ = x & tm
            
            values = []
            nob = vbits // 8 + (0 if vbits % 8 == 0 else 1)
            ibyte = state.vliwinstbits // 8 + (0 if state.vliwinstbits % 8 == 0 else 1)
            noi = (vbits - abs(state.vliwtemplatebits)) // state.vliwinstbits
            
            for j in objs:
                for m in j:
                    values += [m]
            
            for i in range(ibyte * noi - len(values)):
                values += state.vliwnop
            
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
                r = (r << state.vliwinstbits) | v
            r = r & pm
            
            if state.vliwtemplatebits < 0:
                res = r | (templ << (vbits - abs(state.vliwtemplatebits)))
            else:
                res = (r << state.vliwtemplatebits) | templ
            
            q = 0
            if state.vliwbits > 0:
                bc = vbits - 8
                vm = 0xff << bc
                for cnt in range(vbits // 8):
                    outbin(state.pc + cnt, ((res & vm) >> bc) & 0xff)
                    bc = bc - 8
                    vm >>= 8
                    q += 1
            else:
                for cnt in range(vbits // 8):
                    outbin(state.pc + cnt, res & 0xff)
                    res >>= 8
                    q += 1
            
            state.pc += q
            break
    else:
        if state.pas == 0 or state.pas == 2:
            print(" error - No vliw instruction-set defined.")
            return False
    return True


# Main assembly functions
def lineassemble2(line, idx):
    """Assemble line (phase 2)"""
    l, idx = get_param_to_spc(line, idx)
    l2, idx = get_param_to_eon(line, idx)
    l = l.rstrip()
    l2 = l2.rstrip()
    l = l.replace(' ', '')
    
    if section_processing(l, l2):
        return [], [], True, idx
    if endsection_processing(l, l2):
        return [], [], True, idx
    if zero_processing(l, l2):
        return [], [], True, idx
    if ascii_processing(l, l2):
        return [], [], True, idx
    if asciiz_processing(l, l2):
        return [], [], True, idx
    if include_asm(l, l2):
        return [], [], True, idx
    if align_processing(l, l2):
        return [], [], True, idx
    if org_processing(l, l2):
        return [], [], True, idx
    if labelc_processing(l, l2):
        return [], [], True, idx
    if export_processing(l, l2):
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
    
    for i in state.pat:
        pln += 1
        pl = i
        for a in LOWER:
            put_vars(a, VAR_UNDEF)
        
        if i is None:
            continue
        if set_symbol(i):
            continue
        if clear_symbol(i):
            continue
        if paddingp(i):
            continue
        if bits(i):
            continue
        if symbolc(i):
            continue
        if epic(i):
            continue
        if vliwp(i):
            continue
        
        lw = len([_ for _ in i if _])
        if lw == 0:
            continue
        
        lin = l + ' ' + l2
        lin = reduce_spaces(lin)
        
        if i[0] == '':
            loopflag = False
            break
        
        state.error_undefined_label = False
        
        if not state.debug:
            try:
                if match0(lin, i[0]) == True:
                    error(i[1])
                    objl = makeobj(i[2])
                    idxs, _ = expression0(i[3], 0)
                    loopflag = False
                    break
            except:
                oerr = True
                loopflag = False
                break
        else:
            if match0(lin, i[0]) == True:
                error(i[1])
                objl = makeobj(i[2])
                idxs, _ = expression0(i[3], 0)
                loopflag = False
                break
    
    if loopflag == True:
        se = True
        pln = 0
        pl = ""
    
    if state.pas == 2 or state.pas == 0:
        if state.error_undefined_label:
            print(f" error - undefined label error.")
            return [], [], False, idx
        if se:
            print(f" error - Syntax error.")
            return [], [], False, idx
        if oerr:
            print(f" ; pat {pln} {pl} error - Illegal syntax in assemble line or pattern line.")
            return [], [], False, idx
    
    return idxs, objl, True, idx


def lineassemble(line):
    """Assemble single line"""
    line = line.replace('\t', ' ').replace('\n', '')
    line = reduce_spaces(line)
    line = remove_comment_asm(line)
    if line == '':
        return False
    
    line = label_processing(line)
    clear_symbol([".clearsym", "", ""])
    
    parts = line.split("!!")
    state.vcnt = sum(1 for p in parts if p != "")
    
    idxs, objl, flag, idx = lineassemble2(line, 0)
    
    if flag == False:
        return False
    
    if state.vliwflag == False or (idx >= len(line) or line[idx:idx+2] != '!!'):
        of = len(objl)
        for cnt in range(of):
            outbin(state.pc + cnt, objl[cnt])
        state.pc += of
    else:
        vflag = False
        try:
            vflag = vliwprocess(line, idxs, objl, flag, idx)
        except:
            if state.pas == 0 or state.pas == 2:
                print(" error - Some error(s) in vliw definition.")
        return vflag
    
    return True


def lineassemble0(line):
    """Assemble line with output"""
    state.cl = line.replace('\n', '')
    if state.pas == 2 or state.pas == 0:
        print("%016x " % state.pc, end='')
        print(f"{state.current_file} {state.ln} {state.cl} ", end='')
    f = lineassemble(state.cl)
    if state.pas == 2 or state.pas == 0:
        print("")
    state.ln += 1
    return f


# File assembly
def option(l, o):
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


def file_input_from_stdin():
    """Read input from stdin"""
    af = ""
    while True:
        line = sys.stdin.readline().strip()
        if line == '':
            break
        af += line + '\n'
    return af


def setpatsymbols(pat):
    """Set pattern symbols"""
    for i in pat:
        if set_symbol(i):
            continue
    state.patsymbols.update(state.symbols)


def fileassemble(fn):
    """Assemble file"""
    state.fnstack += [state.current_file]
    state.lnstack += [state.ln]
    state.current_file = fn
    state.ln = 1
    
    if fn == "stdin":
        if state.pas != 2 and state.pas != 0:
            af = file_input_from_stdin()
            with open("axx.tmp", "wt") as stdintmp:
                stdintmp.write(af)
        fn = "axx.tmp"
    
    f = open(fn, "rt")
    af = f.readlines()
    f.close()
    
    for i in af:
        lineassemble0(i)
    
    if state.fnstack:
        state.current_file = state.fnstack.pop()
        state.ln = state.lnstack.pop()


def imp_label(l):
    """Import label"""
    idx = skipspc(l, 0)
    section, idx = get_label_word(l, idx)
    idx = skipspc(l, 0)
    label, idx = get_label_word(l, idx)
    if label == '':
        return False
    idx = skipspc(l, idx)
    v, new_idx = expression(l, idx)
    if new_idx == idx:
        return False
    idx = new_idx
    put_label_value(label, v, section)
    return True


# Main entry point
def main():
    """Main function"""
    global state
    
    if len(sys.argv) == 1:
        print("axx general assembler programmed and designed by Taisuke Maekawa")
        print("Usage: python axx.py patternfile.axx [sourcefile.s] [-o outfile.bin] [-e export_labels.tsv] [-i import_labels.tsv]")
        return
    
    sys_argv = sys.argv
    
    if len(sys_argv) >= 2:
        state.pat = readpat(sys_argv[1])
        setpatsymbols(state.pat)
    
    sys_argv, state.expfile = option(sys_argv, "-e")
    sys_argv, expefile = option(sys_argv, "-E")
    sys_argv, state.outfile = option(sys_argv, '-o')
    sys_argv, state.impfile = option(sys_argv, "-i")
    
    if state.impfile != "":
        with open(state.impfile, "rt") as label_file:
            while True:
                l = label_file.readline()
                if not l:
                    break
                imp_label(l)
    
    try:
        os.remove(state.outfile)
    except:
        pass
    
    if state.outfile:
        f = open(state.outfile, "wb")
        f.close()
    
    if len(sys_argv) == 2:
        state.pc = 0
        state.pas = 0
        state.ln = 1
        state.current_file = "(stdin)"
        while True:
            printaddr(state.pc)
            try:
                line = input(">> ")
                line = line.replace("\\\\", "\\")
            except EOFError:
                break
            line = line.strip()
            if line == "":
                continue
            lineassemble0(line)
    
    elif len(sys_argv) >= 3:
        state.pc = 0
        state.pas = 1
        state.ln = 1
        fileassemble(sys.argv[2])
        state.pc = 0
        state.pas = 2
        state.ln = 1
        fileassemble(sys.argv[2])
    
    if expefile != "":
        state.expfile = expefile
        elf = 1
    else:
        elf = 0
    
    if state.expfile != "":
        h = list(state.export_labels.items())
        key = list(state.sections.keys())
        with open(state.expfile, "wt") as label_file:
            for i in key:
                if i == '.text' and elf == 1:
                    flag = 'AX'
                elif i == '.data' and elf == 1:
                    flag = 'WA'
                else:
                    flag = ''
                start = state.sections[i][0]
                label_file.write(f"{i}\t{start:#x}\t{state.sections[i][1]:#x}\t{flag}\n")
            for i in h:
                label_file.write(f"{i[0]}\t{i[1][0]:#x}\n")


if __name__ == '__main__':
    main()
    exit(0)
