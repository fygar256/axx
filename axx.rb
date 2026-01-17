#!/usr/bin/env ruby
#
# axx general assembler
# Full Ruby translation of axx.py (Taisuke Maekawa)
#
# Notes:
# - Uses python3 (via Open3) to evaluate expressions for dbl/flt to match Python's eval semantics.
#   If python3 is not available, falls back to Ruby eval.
# - The translation aims to preserve the original behavior; test with your .axx pattern files.
#

require 'bigdecimal'
require 'readline'
require 'set'
require 'fileutils'
require 'open3'

# -- globals and constants ---------------------------------------------------
EXP_PAT = 0
EXP_ASM = 1
OB = 0x90.chr
CB = 0x91.chr
UNDEF = (1 << 256) - 1
VAR_UNDEF = 0

$capital = "ABCDEFGHIJKLMNOPQRSTUVWXYZ"
$lower   = "abcdefghijklmnopqrstuvwxyz"
$digit   = '0123456789'
$xdigit  = "0123456789ABCDEF"
$errors  = ["Value out of range.","Invalid syntax.","Address out of range.","","","Register out of range.","Port number out of range."]
$outfile = ""
$expfile = ""
$impfile = ""
$pc = 0
$padding = 0
$alphabet = $lower + $capital
$lwordchars = $digit + $alphabet + "_."
$swordchars = $digit + $alphabet + "_%$-~&|"
$current_section = ".text"
$current_file = ""
$sections = {}
$symbols = {}
$patsymbols = {}
$labels = {}
$export_labels = {}
$pat = []

$vliwinstbits = 41
$vliwnop = []
$vliwbits = 128
$vliwset = []
$vliwflag = false
$vliwtemplatebits = 0x00
$vliwstop = 0
$vcnt = 1

$expmode = EXP_PAT
$error_undefined_label = false
$error_already_defined = false
$align = 16
$bts = 8
$endian = 'little'
$byte = 'yes'
$pas = 0
$debug = false
$cl = ""
$ln = 0
$fnstack = []
$lnstack = []
$vars = Array.new(26, VAR_UNDEF)
$deb1 = ""
$deb2 = ""

# -----------------------
# Helpers & utilities
# -----------------------

def add_avoiding_dup(l, e)
  l << e unless l.include?(e)
  l
end

def upper(s)
  s.to_s.upcase
end

def safe_char(s, idx)
  return "\0" if idx.nil?
  return "\0" if idx < 0
  return "\0" if idx >= s.length
  s[idx]
end

def outbin2(a, x)
  if $pas == 2 || $pas == 0
    fwrite($outfile, a, x.to_i, 0)
  end
end

def outbin(a, x)
  if $pas == 2 || $pas == 0
    fwrite($outfile, a, x.to_i, 1)
  end
end

def get_vars(s)
  c = upper(s)[0].ord
  $vars[c - 'A'.ord]
end

def put_vars(s, v)
  k = upper(s).to_s
  if k =~ /\A[A-Z]\z/
    $vars[k[0].ord - 'A'.ord] = v.to_i
  end
  nil
end

def q(s, t, idx)
  upper(s[idx, t.length].to_s) == upper(t)
end

def err(m)
  puts m
  -1
end

def nbit(l)
  b = 0
  r = l
  while r != 0
    r >>= 1
    b += 1
  end
  b
end

def skipspc(s, idx)
  idx ||= 0
  while idx < s.length && s[idx] == ' '
    idx += 1
  end
  idx
end

def get_param_to_spc(s, idx)
  idx = skipspc(s, idx)
  t = ""
  while idx < s.length && s[idx] != ' '
    t << s[idx]
    idx += 1
  end
  [t, idx]
end

def get_param_to_eon(s, idx)
  idx = skipspc(s, idx)
  t = ""
  while idx < s.length && s[idx,2] != '!!'
    t << s[idx]
    idx += 1
  end
  [t, idx]
end

# -----------------------
# Expression evaluation helpers
# -----------------------

# Evaluate expression using system python3 to match Python eval semantics.
# Fallback to Ruby eval on error.
def py_eval(expr)
  begin
    out, err, st = Open3.capture3("python3", "-c", "import sys\ns=sys.stdin.read()\ntry:\n v=eval(s)\n print(repr(v))\nexcept Exception:\n sys.exit(1)\n", :stdin_data => expr)
    if st.success?
      s = out.strip
      begin
        Integer(s)
      rescue
        begin
          Float(s)
        rescue
          s # return raw string if neither numeric
        end
      end
    else
      # fallback to Ruby eval
      begin
        eval(expr)
      rescue
        0
      end
    end
  rescue Errno::ENOENT
    # python3 not found, fallback to Ruby eval
    begin
      eval(expr)
    rescue
      0
    end
  end
end

# Decimal -> IEEE helpers (approximate using BigDecimal/Float)
def decimal_to_ieee754_32bit_hex(a)
  bias = 127
  sbits = 23
  ebits = 8
  s = a.to_s
  s = 'Infinity' if s == 'inf'
  s = '-Infinity' if s == '-inf'
  s = 'NaN' if s == 'nan'
  d = begin BigDecimal(s) rescue BigDecimal('0') end
  if d.respond_to?(:nan?) && d.nan?
    sign = 0
    exponent = (1 << ebits) - 1
    fraction = 1 << (sbits - 1)
  elsif %w[Infinity -Infinity].include?(s)
    sign = s.start_with?('-') ? 1 : 0
    exponent = (1 << ebits) - 1
    fraction = 0
  elsif d == 0
    sign = d >= 0 ? 0 : 1
    exponent = 0
    fraction = 0
  else
    sign = d >= 0 ? 0 : 1
    d = d.abs
    adj = (Math.log(d.to_f, 2).floor rescue 0)
    exponent_value = adj + bias
    if exponent_value <= 0
      exponent = 0
      fraction = (d * (2 ** (bias - sbits))).to_i
    else
      exponent = exponent_value
      normalized = d.to_f / (2 ** adj)
      fraction = ((normalized - 1.0) * (2 ** sbits)).to_i
    end
    fraction &= (1 << sbits) - 1
  end
  bits = (sign << 31) | (exponent << sbits) | fraction
  "0x%08X" % bits
end

def decimal_to_ieee754_64bit_hex(a)
  bias = 1023
  sbits = 52
  ebits = 11
  s = a.to_s
  s = 'Infinity' if s == 'inf'
  s = '-Infinity' if s == '-inf'
  s = 'NaN' if s == 'nan'
  d = begin BigDecimal(s) rescue BigDecimal('0') end
  if d.respond_to?(:nan?) && d.nan?
    sign = 0
    exponent = (1 << ebits) - 1
    fraction = 1 << (sbits - 1)
  elsif %w[Infinity -Infinity].include?(s)
    sign = s.start_with?('-') ? 1 : 0
    exponent = (1 << ebits) - 1
    fraction = 0
  elsif d == 0
    sign = d >= 0 ? 0 : 1
    exponent = 0
    fraction = 0
  else
    sign = d >= 0 ? 0 : 1
    d = d.abs
    adj = (Math.log(d.to_f, 2).floor rescue 0)
    exponent_value = adj + bias
    if exponent_value <= 0
      exponent = 0
      fraction = (d * (2 ** (bias - sbits))).to_i
    else
      exponent = exponent_value
      normalized = d.to_f / (2 ** adj)
      fraction = ((normalized - 1.0) * (2 ** sbits)).to_i
    end
    fraction &= (1 << sbits) - 1
  end
  bits = (sign << 63) | (exponent << sbits) | fraction
  "0x%016X" % bits
end

def decimal_to_ieee754_128bit_hex(a)
  bias = 16383
  sbits = 112
  ebits = 15
  s = a.to_s
  s = 'Infinity' if s == 'inf'
  s = '-Infinity' if s == '-inf'
  s = 'NaN' if s == 'nan'
  d = begin BigDecimal(s) rescue BigDecimal('0') end
  if d.respond_to?(:nan?) && d.nan?
    sign = 0
    exponent = (1 << ebits) - 1
    fraction = 1 << (sbits - 1)
  elsif %w[Infinity -Infinity].include?(s)
    sign = s.start_with?('-') ? 1 : 0
    exponent = (1 << ebits) - 1
    fraction = 0
  elsif d == 0
    sign = d >= 0 ? 0 : 1
    exponent = 0
    fraction = 0
  else
    sign = d >= 0 ? 0 : 1
    d = d.abs
    approx = (Math.log(d.to_f, 2) rescue (d.to_f > 0 ? Math.log(d.to_f) / Math.log(2) : 0))
    exponent_value = approx.floor + bias
    if exponent_value <= 0
      exponent = 0
      fraction = (d * (2 ** (bias - sbits))).to_i
    else
      exponent = exponent_value
      normalized = d.to_f / (2 ** approx.floor)
      fraction = ((normalized - 1.0) * (2 ** sbits)).to_i
    end
    fraction &= (1 << sbits) - 1
  end
  bits = (sign << 127) | (exponent << sbits) | fraction
  "0x%032X" % bits
end

# -----------------------
# Token parsers
# -----------------------

def get_intstr(s, idx)
  fs = ""
  while idx < s.length && s[idx] =~ /[0-9]/
    fs << s[idx]; idx += 1
  end
  [fs, idx]
end

def get_floatstr(s, idx)
  if s[idx,3] == 'inf'
    ['inf', idx + 3]
  elsif s[idx,4] == '-inf'
    ['-inf', idx + 4]
  elsif s[idx,3] == 'nan'
    ['nan', idx + 3]
  else
    fs = ""
    while idx < s.length && s[idx] =~ /[0-9\-.eE]/
      fs << s[idx]; idx += 1
    end
    [fs, idx]
  end
end

def get_curlb(s, idx)
  idx = skipspc(s, idx)
  return [false, "", idx] unless safe_char(s, idx) == '{'
  idx += 1
  idx = skipspc(s, idx)
  t = ""
  while safe_char(s, idx) != '}'
    t << s[idx]; idx += 1
  end
  idx += 1 if safe_char(s, idx) == '}'
  [true, t, idx]
end

# -----------------------
# Expression parser (term functions)
# -----------------------

def factor(s, idx)
  idx = skipspc(s, idx)
  x = 0
  if idx + 4 <= s.length && s[idx,4] == '!!!!' && $expmode == EXP_PAT
    x = $vliwstop
    idx += 4
  elsif idx + 3 <= s.length && s[idx,3] == '!!!' && $expmode == EXP_PAT
    x = $vcnt
    idx += 3
  elsif safe_char(s, idx) == '-'
    (x, idx) = factor(s, idx + 1)
    x = -x
  elsif safe_char(s, idx) == '~'
    (x, idx) = factor(s, idx + 1)
    x = ~x
  elsif safe_char(s, idx) == '@'
    (x, idx) = factor(s, idx + 1)
    x = nbit(x)
  else
    (x, idx) = factor1(s, idx)
  end
  idx = skipspc(s, idx)
  [x, idx]
end

def factor1(s, idx)
  x = 0
  idx = skipspc(s, idx)
  c = safe_char(s, idx)
  if c == '('
    (x, idx) = expression(s, idx + 1)
    idx += 1 if safe_char(s, idx) == ')'
  elsif q(s, '$$', idx)
    idx += 2
    x = $pc
  elsif q(s, '#', idx)
    idx += 1
    (t, idx) = get_symbol_word(s, idx)
    x = getsymval(t)
  elsif q(s, '0b', idx)
    idx += 2
    while safe_char(s, idx) =~ /[01]/
      x = 2 * x + s[idx].to_i(2); idx += 1
    end
  elsif q(s, '0x', idx)
    idx += 2
    while idx < s.length && $xdigit.include?(s[idx].upcase)
      x = 16 * x + s[idx].to_i(16); idx += 1
    end
  elsif s[idx,3] == 'qad'
    idx += 3
    idx = skipspc(s, idx)
    if safe_char(s, idx) == '{'
      (fs, idx) = get_floatstr(s, idx + 1)
      h = decimal_to_ieee754_128bit_hex(fs)
      x = h.to_i(16)
    end
    idx += 1 if safe_char(s, idx) == '}'
  elsif s[idx,3] == 'dbl'
    idx += 3
    (f, t, idx) = get_curlb(s, idx)
    if f
      if t == 'nan'
        x = 0x7ff8000000000000
      elsif t == 'inf'
        x = 0x7ff0000000000000
      elsif t == '-inf'
        x = 0xfff0000000000000
      else
        v = py_eval(t)
        bs = [v.to_f].pack('G') rescue ("\0" * 8)
        hex = bs.unpack1('H*') rescue "0"
        x = hex.to_i(16)
      end
    end
  elsif s[idx,3] == 'flt'
    idx += 3
    (f, t, idx) = get_curlb(s, idx)
    if f
      if t == 'nan'
        x = 0x7fc00000
      elsif t == 'inf'
        x = 0x7f800000
      elsif t == '-inf'
        x = 0xff800000
      else
        v = py_eval(t)
        bs = [v.to_f].pack('g') rescue ("\0" * 4)
        hex = bs.unpack1('H*') rescue "0"
        x = hex.to_i(16)
      end
    end
  elsif safe_char(s, idx) =~ /\d/
    (fs, idx) = get_intstr(s, idx)
    x = fs.to_i
  elsif $expmode == EXP_PAT && safe_char(s, idx) && $lower.include?(safe_char(s, idx)) && !(safe_char(s, idx + 1) && $lower.include?(safe_char(s, idx + 1)))
    ch = s[idx]
    if s[idx+1,2] == ':='
      (x, idx) = expression(s, idx + 3)
      put_vars(ch, x)
    else
      x = get_vars(ch)
      idx += 1
    end
  elsif safe_char(s, idx) != "\0" && ($lwordchars.include?(safe_char(s, idx)) || safe_char(s, idx) == '.')
    (w, idx_new) = get_label_word(s, idx)
    if idx != idx_new
      idx = idx_new
      x = get_label_value(w)
    else
      x = 0
    end
  else
    x = 0
  end
  idx = skipspc(s, idx)
  [x, idx]
end

def term0_0(s, idx)
  (x, idx) = factor(s, idx)
  while true
    if q(s, '**', idx)
      (t, idx) = factor(s, idx + 2)
      x = x ** t
    else
      break
    end
  end
  [x, idx]
end

def term0(s, idx)
  (x, idx) = term0_0(s, idx)
  while true
    if safe_char(s, idx) == '*'
      (t, idx) = term0_0(s, idx + 1)
      x *= t
    elsif q(s, '//', idx)
      (t, idx) = term0_0(s, idx + 2)
      if t == 0
        err("Division by 0 error.")
      else
        x = x.to_i / t.to_i
      end
    elsif safe_char(s, idx) == '%'
      (t, idx) = term0_0(s, idx + 1)
      if t == 0
        err("Division by 0 error.")
      else
        x = x % t
      end
    else
      break
    end
  end
  [x, idx]
end

def term1(s, idx)
  (x, idx) = term0(s, idx)
  while true
    if safe_char(s, idx) == '+'
      (t, idx) = term0(s, idx + 1)
      x += t
    elsif safe_char(s, idx) == '-'
      (t, idx) = term0(s, idx + 1)
      x -= t
    else
      break
    end
  end
  [x, idx]
end

def term2(s, idx)
  (x, idx) = term1(s, idx)
  while true
    if q(s, '<<', idx)
      (t, idx) = term1(s, idx + 2)
      x <<= t
    elsif q(s, '>>', idx)
      (t, idx) = term1(s, idx + 2)
      x >>= t
    else
      break
    end
  end
  [x, idx]
end

def term3(s, idx)
  (x, idx) = term2(s, idx)
  while true
    if safe_char(s, idx) == '&' && safe_char(s, idx + 1) != '&'
      (t, idx) = term2(s, idx + 1)
      x = x.to_i & t.to_i
    else
      break
    end
  end
  [x, idx]
end

def term4(s, idx)
  (x, idx) = term3(s, idx)
  while true
    if safe_char(s, idx) == '|' && safe_char(s, idx + 1) != '|'
      (t, idx) = term3(s, idx + 1)
      x = x.to_i | t.to_i
    else
      break
    end
  end
  [x, idx]
end

def term5(s, idx)
  (x, idx) = term4(s, idx)
  while true
    if safe_char(s, idx) == '^'
      (t, idx) = term4(s, idx + 1)
      x = x.to_i ^ t.to_i
    else
      break
    end
  end
  [x, idx]
end

def term6(s, idx)
  (x, idx) = term5(s, idx)
  while true
    if safe_char(s, idx) == "'"
      (t, idx) = term5(s, idx + 1)
      x = (x & ~((~0) << t)) | ((~0) << t if (x >> (t - 1) & 1) rescue 0)
    else
      break
    end
  end
  [x, idx]
end

def term7(s, idx)
  (x, idx) = term6(s, idx)
  while true
    if q(s, '<=', idx)
      (t, idx) = term6(s, idx + 2)
      x = x <= t ? 1 : 0
    elsif safe_char(s, idx) == '<'
      (t, idx) = term6(s, idx + 1)
      x = x < t ? 1 : 0
    elsif q(s, '>=', idx)
      (t, idx) = term6(s, idx + 2)
      x = x >= t ? 1 : 0
    elsif safe_char(s, idx) == '>'
      (t, idx) = term6(s, idx + 1)
      x = x > t ? 1 : 0
    elsif q(s, '==', idx)
      (t, idx) = term6(s, idx + 2)
      x = x == t ? 1 : 0
    elsif q(s, '!=', idx)
      (t, idx) = term6(s, idx + 2)
      x = x != t ? 1 : 0
    else
      break
    end
  end
  [x, idx]
end

def term8(s, idx)
  if s[idx,4] == 'not('
    (x, idx) = expression(s, idx + 3)
    x = x == 0 ? 1 : 0
  else
    (x, idx) = term7(s, idx)
  end
  [x, idx]
end

def term9(s, idx)
  (x, idx) = term8(s, idx)
  while true
    if q(s, '&&', idx)
      (t, idx) = term8(s, idx + 2)
      x = (x != 0 && t != 0) ? 1 : 0
    else
      break
    end
  end
  [x, idx]
end

def term10(s, idx)
  (x, idx) = term9(s, idx)
  while true
    if q(s, '||', idx)
      (t, idx) = term9(s, idx + 2)
      x = (x != 0 || t != 0) ? 1 : 0
    else
      break
    end
  end
  [x, idx]
end

def term11(s, idx)
  (x, idx) = term10(s, idx)
  while true
    if q(s, '?', idx)
      (t, idx) = term10(s, idx + 1)
      if q(s, ':', idx)
        (u, idx) = term10(s, idx + 1)
        x = x == 0 ? u : t
      end
    else
      break
    end
  end
  [x, idx]
end

def expression(s, idx)
  s2 = s + "\0"
  idx = skipspc(s2, idx)
  term11(s2, idx)
end

def expression0(s, idx)
  $expmode = EXP_PAT
  expression(s, idx)
end

def expression1(s, idx)
  $expmode = EXP_ASM
  expression(s, idx)
end

def expression_esc(s, idx, stopchar)
  $expmode = EXP_PAT
  result = []
  depth = 0
  s.each_char do |ch|
    if ch == '('
      depth += 1; result << ch
    elsif ch == ')'
      depth -= 1 if depth > 0; result << ch
    else
      if depth == 0 && ch == stopchar
        result << "\0"
      else
        result << ch
      end
    end
  end
  replaced = result.join
  expression(replaced, idx)
end

# -----------------------
# Symbol helpers & directives
# -----------------------

def getsymval(w)
  w = w.upcase
  $symbols[w] || ""
end

def clear_symbol(i)
  return false if i.nil? || i.empty?
  return false unless i[0] == '.clearsym'
  key = upper(i[2].to_s)
  if $symbols.key?(key)
    $symbols.delete(key)
    return true
  end
  if i.length == 1
    $symbols = {}
  end
  true
end

def set_symbol(i)
  return false if i.nil? || i.empty?
  return false unless i[0] == '.setsym'
  key = upper(i[1].to_s)
  if i.length > 2
    v, _ = expression0(i[2], 0)
  else
    v = 0
  end
  $symbols[key] = v
  true
end

def bits(i)
  return false if i.nil? || i.empty?
  return false unless i[0] == '.bits'
  $endian = (i.length >= 2 && i[1] == 'big') ? 'big' : 'little'
  if i.length >= 3
    v, _ = expression0(i[2], 0)
  else
    v = 8
  end
  $bts = v.to_i
  true
end

def paddingp(i)
  return false if i.nil? || i.empty?
  return false unless i[0] == '.padding'
  if i.length >= 3
    v, _ = expression0(i[2], 0)
  else
    v = 0
  end
  $padding = v.to_i
  true
end

def symbolc(i)
  return false if i.nil? || i.empty?
  return false unless i[0] == '.symbolc'
  if i.length > 3
    $swordchars = $alphabet + $digit + i[2]
  end
  true
end

def remove_comment(line)
  idx = 0
  while idx < line.length
    if line[idx,2] == '/*'
      return "" if idx == 0
      return line[0, idx - 1]
    end
    idx += 1
  end
  line
end

def remove_comment_asm(l)
  pos = l.index(';')
  pos ? l[0, pos].rstrip : l.rstrip
end

def get_params1(l, idx)
  idx = skipspc(l, idx)
  return ["", idx] if idx >= l.length
  s = ""
  while idx < l.length
    if l[idx,2] == '::'
      idx += 2
      break
    else
      s << l[idx]; idx += 1
    end
  end
  [s.rstrip, idx]
end

def reduce_spaces(text)
  text.gsub(/\s{2,}/, ' ')
end

def readpat(fn)
  return [] if fn == ''
  w = []
  File.open(fn, "rt") do |f|
    f.each_line do |line|
      l = remove_comment(line)
      l = l.gsub("\t", ' ').gsub("\r",'').gsub("\n",'')
      l = reduce_spaces(l)
      ww = include_pat(l) rescue []
      if ww && !ww.empty?
        w += ww
        next
      else
        r = []
        idx = 0
        loop do
          s, idx = get_params1(l, idx)
          r << s
          break if idx >= l.length
        end
        p =
          case r.length
          when 1 then [r[0],'','','','','']
          when 2 then [r[0],'',r[1],'','','']
          when 3 then [r[0],r[1],r[2],'','','']
          when 4 then [r[0],r[1],r[2],r[3],'','']
          when 5 then [r[0],r[1],r[2],r[3],r[4],'']
          when 6 then r[0,6]
          else ["","","","","","",""]
          end
        w << p
      end
    end
  end
  w
end

def fwrite(file_path, position, x, prt)
  b = $bts <= 8 ? 8 : $bts
  byts = (b / 8.0).ceil
  cnt = 0
  if file_path && file_path != ""
    File.open(file_path, "a+b") do |file|
      file.seek(position * byts)
      if $endian == 'little'
        mask = (2 ** $bts) - 1
        v = x & mask
        byts.times do
          vv = v & 0xff
          file.write([vv].pack('C'))
          print(" 0x%02x" % vv) if prt == 1
          v >>= 8
          cnt += 1
        end
      else
        mask = (2 ** $bts) - 1
        x_masked = x & mask
        p = 0xff << (byts * 8 - 8)
        (byts - 1).downto(0) do |i|
          v = ((x_masked & p) >> (i * 8)) & 0xff
          file.write([v].pack('C'))
          print(" 0x%02x" % v) if prt == 1
          p >>= 8
          cnt += 1
        end
      end
    end
  else
    if $endian == 'little'
      mask = (2 ** $bts) - 1
      v = x & mask
      byts.times do
        vv = v & 0xff
        ptint(" 0x%02x" % vv) if prt == 1
        v >>= 8
        cnt += 1
      end
    else
      mask = (2 ** $bts) - 1
      x_masked = x & mask
      p = 0xff << (byts * 8 - 8)
      (byts - 1).downto(0) do |i|
        v = ((x_masked & p) >> (i * 8)) & 0xff
        print(" 0x%02x" % v) if prt == 1
        p >>= 8
        cnt += 1
      end
    end
  end
  cnt
end

def align_(addr)
  a = addr % $align
  a == 0 ? addr : (addr + ($align - a))
end

def makeobj(s)
  s2 = s + "\0"
  idx = 0
  objl = []
  while safe_char(s2, idx) != "\0"
    if s2[idx] == ','
      idx += 1
      p = $pc + objl.length
      n = align_(p)
      (p...n).each { objl << $padding }
      next
    end
    semicolon = false
    if s2[idx] == ';'
      semicolon = true
      idx += 1
    end
    x, idx = expression0(s2, idx)
    objl << x if (semicolon == false) || (semicolon == true && x != 0)
    idx += 1 if s2[idx] == ','
  end
  objl
end

def get_symbol_word(s, idx)
  t = ""
  if idx < s.length && (!$digit.include?(s[idx]) && $swordchars.include?(s[idx]))
    t << s[idx]; idx += 1
    while idx < s.length && $swordchars.include?(s[idx])
      t << s[idx]; idx += 1
    end
  end
  [t.upcase, idx]
end

def get_label_word(s, idx)
  t = ""
  if idx < s.length && (s[idx] == '.' || (!$digit.include?(s[idx]) && $lwordchars.include?(s[idx])))
    t << s[idx]; idx += 1
    while idx < s.length && $lwordchars.include?(s[idx])
      t << s[idx]; idx += 1
    end
    idx += 1 if idx < s.length && s[idx] == ':'
  end
  [t, idx]
end

def match(s, t)
  t2 = t.gsub(OB, '').gsub(CB, '')
  idx_s = skipspc(s, 0)
  idx_t = skipspc(t2, 0)
  s2 = s + "\0"
  t2 += "\0"
  $deb1 = s2; $deb2 = t2
  loop do
    idx_s = skipspc(s2, idx_s)
    idx_t = skipspc(t2, idx_t)
    b = safe_char(s2, idx_s)
    a = safe_char(t2, idx_t)
    return true if a == "\0" && b == "\0"
    if a == '\\'
      idx_t += 1
      if safe_char(t2, idx_t) == b
        idx_t += 1; idx_s += 1; next
      else
        return false
      end
    elsif a =~ /[A-Z]/
      if a == b.upcase
        idx_s += 1; idx_t += 1; next
      else
        return false
      end
    elsif a == '!'
      idx_t += 1
      a = safe_char(t2, idx_t); idx_t += 1
      if a == '!'
        a = safe_char(t2, idx_t); idx_t += 1
        v, idx_s = factor(s2, idx_s)
        put_vars(a, v)
        next
      else
        idx_t = skipspc(t2, idx_t)
        if safe_char(t2, idx_t) == '\\'
          idx_t = skipspc(t2, idx_t + 1)
          b = safe_char(t2, idx_t)
          stopchar = b
        else
          stopchar = "\0"
        end
        v, idx_s = expression_esc(s2, idx_s, stopchar)
        put_vars(a, v)
        next
      end
    elsif a =~ /[a-z]/
      idx_t += 1
      w, idx_s = get_symbol_word(s2, idx_s)
      v = getsymval(w)
      return false if v == ""
      put_vars(a, v)
      next
    elsif a == b
      idx_t += 1; idx_s += 1; next
    else
      return false
    end
  end
end

def remove_brackets(s, l)
  open_count = 0
  result = s.chars
  bracket_positions = []
  s.chars.each_with_index do |ch, i|
    if ch == OB
      open_count += 1
      bracket_positions << [open_count, i, 'open']
    elsif ch == CB
      bracket_positions << [open_count, i, 'close']
    end
  end
  l.sort.reverse.each do |index|
    start_index = nil; end_index = nil
    bracket_positions.each do |count, pos, type|
      if count == index && type == 'open'
        start_index = pos
      elsif count == index && type == 'close'
        end_index = pos; break
      end
    end
    if start_index && end_index
      (start_index..end_index).each { |j| result[j] = '' }
    end
  end
  result.join
end

def match0(s, t)
  t2 = t.gsub('[[', OB).gsub(']]', CB)
  cnt = t2.count(OB)
  sl = (1..cnt).to_a
  (0..sl.length).each do |i|
    ll = sl.combination(i).to_a
    ll.each do |j|
      lt = remove_brackets(t2, j)
      return true if match(s, lt)
    end
  end
  false
end

def error(s)
  ss = s.gsub(' ','')
  return if ss == ""
  s2 = s + "\0"
  idx = 0
  error_code = 0
  while safe_char(s2, idx) != "\0"
    ch = safe_char(s2, idx)
    if ch == ','
      idx += 1; next
    end
    u, idxn = expression0(s2, idx)
    idx = idxn
    idx += 1 if safe_char(s2, idx) == ';'
    t, idx = expression0(s2, idx)
    if ($pas == 2 || $pas == 0) && u != 0
      print "Line #{$ln} Error code #{t} "
      if t >= 0 && t < $errors.length
        print $errors[t]
      end
      puts ": "
      error_code = t
    end
  end
  nil
end

# -----------------------
# Remaining directives etc.
# -----------------------

def labelc_processing(l, ll)
  return false unless l.upcase == '.LABELC'
  $lwordchars = $alphabet + $digit + ll if ll
  true
end

def label_processing(l)
  return "" if l == ""
  label, idx = get_label_word(l, 0)
  lidx = idx
  if label != "" && safe_char(l, idx - 1) == ':'
    idx = skipspc(l, idx)
    e, idx = get_param_to_spc(l, idx)
    if e.upcase == '.EQU'
      u, idx = expression1(l, idx)
      put_label_value(label, u, $current_section)
      return ""
    else
      put_label_value(label, $pc, $current_section)
      return l[lidx..-1].to_s
    end
  end
  l
end

def get_string(l2)
  idx = skipspc(l2, 0)
  return "" if l2 == '' || safe_char(l2, idx) != '"'
  idx += 1
  s = ""
  while idx < l2.length
    return s if l2[idx] == '"'
    s << l2[idx]; idx += 1
  end
  ""
end

def asciistr(l2)
  idx = skipspc(l2, 0)
  return false if l2 == '' || safe_char(l2, idx) != '"'
  idx += 1
  while idx < l2.length
    return true if l2[idx] == '"'
    if l2[idx,2] == '\\0'
      idx += 2; ch = "\0"
    elsif l2[idx,2] == '\\t'
      idx += 2; ch = "\t"
    elsif l2[idx,2] == '\\n'
      idx += 2; ch = "\n"
    else
      ch = l2[idx]; idx += 1
    end
    outbin($pc, ch.ord)
    $pc += 1
  end
end

def export_processing(l1, l2)
  return false unless ($pas == 2 || $pas == 0)
  return false unless l1.upcase == ".EXPORT"
  idx = 0
  l2 = l2 + "\0"
  while safe_char(l2, idx) != "\0"
    idx = skipspc(l2, idx)
    s, idx = get_label_word(l2, idx)
    break if s == ""
    idx += 1 if safe_char(l2, idx) == ':'
    v = get_label_value(s)
    sec = get_label_section(s)
    $export_labels[s] = [v, sec]
    idx += 1 if safe_char(l2, idx) == ','
  end
  true
end

def zero_processing(l1, l2)
  return false unless l1.upcase == ".ZERO"
  x, _ = expression1(l2, 0)
  (0..x).each do
    outbin2($pc, 0x00)
    $pc += 1
  end
  true
end

def ascii_processing(l1, l2)
  return false unless l1.upcase == ".ASCII"
  asciistr(l2)
end

def asciiz_processing(l1, l2)
  return false unless l1.upcase == ".ASCIIZ"
  f = asciistr(l2)
  if f
    outbin($pc, 0x00)
    $pc += 1
  end
  f
end

def include_pat(l)
  idx = skipspc(l, 0)
  i = l[idx,8].to_s.upcase
  return [] unless i == ".INCLUDE"
  s = get_string(l[8..-1].to_s)
  readpat(s)
end

def vliwp(i)
  return false unless i[0] == ".vliw"
  v1, _ = expression0(i[1], 0)
  v2, _ = expression0(i[2], 0)
  v3, _ = expression0(i[3], 0)
  v4, _ = expression0(i[4], 0)
  $vliwbits = v1.to_i
  $vliwinstbits = v2.to_i
  $vliwtemplatebits = v3.to_i
  $vliwflag = true
  l = []
  (( $vliwinstbits / 8.0 ).ceil).times do
    l << (v4 & 0xff)
    v4 >>= 8
  end
  $vliwnop = l
  true
end

def include_asm(l1, l2)
  return false unless l1.upcase == ".INCLUDE"
  s = get_string(l2)
  fileassemble(s) if s && s != ""
  true
end

def section_processing(l1, l2)
  return false unless ["SECTION", "SEGMENT"].include?(l1.upcase)
  if l2 && l2 != ''
    $current_section = l2
    $sections[l2] = [$pc, 0]
  end
  true
end

def align_processing(l1, l2)
  return false unless l1.upcase == ".ALIGN"
  if l2 && l2 != ''
    u, _ = expression1(l2, 0)
    $align = u.to_i
  end
  $pc = align_($pc)
  true
end

def printaddr(pc)
  print "%016x: " % pc
end

def endsection_processing(l1, l2)
  return false unless ["ENDSECTION", "ENDSEGMENT"].include?(l1.upcase)
  start = $sections[$current_section][0]
  $sections[$current_section] = [start, $pc - start]
  true
end

def org_processing(l1, l2)
  return false unless l1.upcase == ".ORG"
  u, idx = expression1(l2, 0)
  if l2[idx,2].upcase == ',P'
    if u > $pc
      (u - $pc).times { |i| outbin2(i + $pc, $padding) }
    end
  end
  $pc = u
  true
end

def epic(i)
  return false unless i[0].upcase == "EPIC"
  return false unless i.length > 1 && i[1] != ''
  s = i[1]
  idxs = []
  idx = 0
  loop do
    v, idx = expression0(s, idx)
    idxs << v
    break unless idx < s.length && s[idx] == ','
    idx += 1
  end
  s2 = i[2]
  $vliwset = add_avoiding_dup($vliwset, [idxs, s2])
  true
end

# -----------------------
# Assemble flow
# -----------------------

def lineassemble2(line, idx)
  (l, idx) = get_param_to_spc(line, idx)
  (l2, idx) = get_param_to_eon(line, idx)
  l = l.rstrip; l2 = l2.rstrip
  l = l.gsub(' ', '')
  return [[], [], true, idx] if section_processing(l, l2)
  return [[], [], true, idx] if endsection_processing(l, l2)
  return [[], [], true, idx] if zero_processing(l, l2)
  return [[], [], true, idx] if ascii_processing(l, l2)
  return [[], [], true, idx] if asciiz_processing(l, l2)
  return [[], [], true, idx] if include_asm(l, l2)
  return [[], [], true, idx] if align_processing(l, l2)
  return [[], [], true, idx] if org_processing(l, l2)
  return [[], [], true, idx] if labelc_processing(l, l2)
  return [[], [], true, idx] if export_processing(l, l2)
  return [[], [], false, idx] if l == ''

  of = 0; se = false; oerr = false; pln = 0; pl = ""; idxs = 0; objl = []; loopflag = true

  $pat.each do |i|
    pln += 1; pl = i
    $lower.each_char { |a| put_vars(a, VAR_UNDEF) }
    next if i.nil?
    next if set_symbol(i)
    next if clear_symbol(i)
    next if paddingp(i)
    next if bits(i)
    next if symbolc(i)
    next if epic(i)
    next if vliwp(i)
    lw = i.count { |x| x && x != '' }
    next if lw == 0
    lin = reduce_spaces((l + ' ' + l2).strip)
    if i[0] == ''
      loopflag = false; break
    end
    $error_undefined_label = false
    begin
      if !$debug
        if match0(lin, i[0]) == true
          error(i[1])
          objl = makeobj(i[2])
          idxs, _ = expression0(i[3], 0)
          loopflag = false
          break
        end
      else
        if match0(lin, i[0]) == true
          error(i[1])
          objl = makeobj(i[2])
          idxs, _ = expression0(i[3], 0)
          loopflag = false
          break
        end
      end
    rescue
      oerr = true
      loopflag = false
      break
    end
  end

  if loopflag
    se = true; pln = 0; pl = ""
  end

  if ($pas == 2 || $pas == 0)
    if $error_undefined_label
      puts " error - undefined label error."; return [[], [], false, idx]
    end
    if se
      puts " error - Syntax error."; return [[], [], false, idx]
    end
    if oerr
      puts " ; pat #{pln} #{pl} error - Illegal syntax in assemble line or pattern line."; return [[], [], false, idx]
    end
  end

  [idxs, objl, true, idx]
end

def vliwprocess(line, idxs, objl, flag, idx)
  objs = [objl]; idxlst = [idxs]; $vliwstop = 0
  loop do
    idx = skipspc(line, idx)
    if idx + 4 <= line.length && line[idx,4] == '!!!!'
      idx += 4; $vliwstop = 1; next
    elsif idx + 2 <= line.length && line[idx,2] == '!!'
      idx += 2
      idxs, objl, flag, idx = lineassemble2(line, idx)
      objs << objl; idxlst << idxs
      next
    else
      break
    end
  end

  $vliwset = [[[0], "0"]] if $vliwtemplatebits == 0
  vbits = $vliwbits.abs
  $vliwset.each do |k|
    if k[0].to_set == idxlst.to_set || $vliwtemplatebits == 0
      im = 2 ** $vliwinstbits - 1
      tm = 2 ** $vliwtemplatebits.abs - 1
      pm = 2 ** vbits - 1
      x, _ = expression0(k[1], 0)
      templ = x & tm
      values = []
      nob = (vbits / 8.0).ceil
      ibyte = ($vliwinstbits / 8.0).ceil
      noi = (vbits - $vliwtemplatebits.abs) / $vliwinstbits
      objs.each { |j| j.each { |m| values << m } }
      (ibyte * noi - values.length).times { values += $vliwnop } if ibyte * noi > values.length
      v1 = []; cnt = 0
      noi.to_i.times do
        vv = 0
        ibyte.to_i.times do
          vv <<= 8
          vv |= (values[cnt] & 0xff) if values.length > cnt
          cnt += 1
        end
        v1 << (vv & im)
      end
      r = 0
      v1.each { |v| r = (r << $vliwinstbits) | v }
      r &= pm
      res = ($vliwtemplatebits < 0) ? (r | (templ << (vbits - $vliwtemplatebits.abs))) : ((r << $vliwtemplatebits) | templ)
      q = 0
      if $vliwbits > 0
        bc = vbits - 8; vm = 0xff << bc
        (vbits / 8).to_i.times do |cnt|
          outbin($pc + cnt, ((res & vm) >> bc) & 0xff)
          bc -= 8; vm >>= 8; q += 1
        end
      else
        (vbits / 8).to_i.times do |cnt|
          outbin($pc + cnt, res & 0xff)
          res >>= 8; q += 1
        end
      end
      $pc += q
      return true
    end
  end
  if $pas == 0 || $pas == 2
    puts " error - No vliw instruction-set defined."
    return false
  end
  false
end

def lineassemble(line)
  line = line.gsub("\t", ' ').gsub("\n", '')
  line = reduce_spaces(line)
  line = remove_comment_asm(line)
  return false if line == ''
  line = label_processing(line)
  clear_symbol([".clearsym","",""])
  parts = line.split("!!")
  $vcnt = parts.count { |p| p != "" }
  idxs, objl, flag, idx = lineassemble2(line, 0)
  return false unless flag
  if !$vliwflag || line[idx,2] != '!!'
    of = objl.length
    of.times { |cnt| outbin($pc + cnt, objl[cnt]) }
    $pc += of
  else
    begin
      vflag = vliwprocess(line, idxs, objl, flag, idx)
      return vflag
    rescue
      puts " error - Some error(s) in vliw definition." if $pas == 0 || $pas == 2
      return false
    end
  end
  true
end

def lineassemble0(line)
  $cl = line.gsub("\n", '')
  if $pas == 2 || $pas == 0
    printf("%016x ", $pc); print "#{$current_file} #{$ln} #{$cl} "
  end
  f = lineassemble($cl)
  puts "" if $pas == 2 || $pas == 0
  $ln += 1
  f
end

def option(argv, o)
  idx = argv.index(o) || -1
  return [argv, ''] if idx == -1
  if idx + 1 < argv.length
    val = argv[idx + 1]
    new_argv = argv[0...idx] + (idx + 2 < argv.length ? argv[(idx+2)..-1] : [])
    [new_argv, val]
  else
    [argv[0...idx], '']
  end
end

def file_input_from_stdin
  af = ""
  while (line = STDIN.gets)
    line2 = line.strip
    break if line2 == ''
    af += line2 + "\n"
  end
  af
end

def setpatsymbols(pat)
  pat.each { |i| set_symbol(i) rescue nil }
  $patsymbols.merge!($symbols)
end

def fileassemble(fn)
  $fnstack << $current_file
  $lnstack << $ln
  $current_file = fn
  $ln = 1
  if fn == "stdin"
    if $pas != 2 && $pas != 0
      af = file_input_from_stdin
      File.open("axx.tmp", "wt") { |f| f.write(af) }
      fn = "axx.tmp"
    end
  end
  File.open(fn, "rt") { |f| f.each_line { |i| lineassemble0(i) } }
  if $fnstack.any?
    $current_file = $fnstack.pop
    $ln = $lnstack.pop
  end
end

def imp_label(l)
  idx = skipspc(l, 0)
  section, idx = get_label_word(l, idx)
  idx = skipspc(l, idx)
  label, idx = get_label_word(l, idx)
  return false if label == ''
  idx = skipspc(l, idx)
  v, new_idx = expression(l, idx)
  return false if new_idx == idx
  put_label_value(label, v, section)
  true
end

def put_label_value(k, v, s)
  if $pas == 1 || $pas == 0
    if $labels.key?(k)
      $error_already_defined = true
      puts " error - label already defined."
      return false
    end
  end

  $patsymbols.each_key do |key|
    if key == upper(k)
      puts " error - '#{k}' is a pattern file symbol."
      return false
    end
  end

  $error_already_defined = false
  $labels[k] = [v, s]
  true
end

def get_label_section(k)
  begin
    $labels[k][1]
  rescue
    $error_undefined_label = true
    UNDEF
  end
end

def get_label_value(k)
  begin
    $labels[k][0]
  rescue
    $error_undefined_label = true
    UNDEF
  end
end

# -- main -------------------------------------------------------------------

def main
  if ARGV.length == 0
    puts "axx general assembler programmed and designed by Taisuke Maekawa"
    puts "Usage: ruby axx.rb patternfile.axx [sourcefile.s] [-o outfile.bin] [-e export_labels.tsv] [-i import_labels.tsv]"
    return
  end
  sys_argv = ARGV.dup
  if sys_argv.length >= 1
    $pat.replace(readpat(sys_argv[0]))
    setpatsymbols($pat)
  end
  sys_argv, $expfile = option(sys_argv, "-e")
  sys_argv, expefile = option(sys_argv, "-E")
  sys_argv, $outfile = option(sys_argv, "-o")
  sys_argv, $impfile = option(sys_argv, "-i")
  if $impfile && $impfile != ""
    File.open($impfile, "rt") do |label_file|
      label_file.each_line { |l| imp_label(l) }
    end
  end
  File.delete($outfile) if $outfile && $outfile != "" rescue nil
  File.open($outfile, "wb") { |f| } if $outfile && $outfile != ""
  if sys_argv.length == 1
    $pc = 0; $pas = 0; $ln = 1; $current_file = "(stdin)"
    loop do
      begin
        line = Readline.readline( ("%016x: " % $pc)+ ">> ", true)
        break if line.nil?
        line = line.gsub('\\\\', '\\')
      rescue EOFError
        break
      end
      line = line.strip
      next if line == ""
      lineassemble0(line)
    end
  elsif sys_argv.length >= 2
    $pc = 0; $pas = 1; $ln = 1
    fileassemble(sys_argv[1])
    $pc = 0; $pas = 2; $ln = 1
    fileassemble(sys_argv[1])
  end
  if expefile && expefile != ""
    $expfile = expefile; elf = 1
  else
    elf = 0
  end
  if $expfile && $expfile != ""
    File.open($expfile, "wt") do |label_file|
      $sections.keys.each do |i|
        flag = ''
        flag = 'AX' if i == '.text' && elf == 1
        flag = 'WA' if i == '.data' && elf == 1
        start = $sections[i][0]
        label_file.write("#{i}\t#{format('%#x', start)}\t#{format('%#x', $sections[i][1])}\t#{flag}\n")
      end
      $export_labels.each { |k,v| label_file.write("#{k}\t#{format('%#x', v[0])}\n") }
    end
  end
end

if __FILE__ == $0
  main
  exit 0
end
