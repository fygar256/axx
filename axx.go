// axx general assembler
// Go translation of axx (Taisuke Maekawa)
//

package main

import (
    "math/big"
    "unsafe"
    "bufio"
    "fmt"
    "io"
    "math"
    "os"
    "os/exec"
    "strconv"
    "strings"
    "unicode"
)

const (
    EXP_PAT = 0
    EXP_ASM = 1
)

var (
    OB   = string([]byte{0x90})
    CB   = string([]byte{0x91})
    UNDEF int64 = -1

    Capital = "ABCDEFGHIJKLMNOPQRSTUVWXYZ"
    Lower   = "abcdefghijklmnopqrstuvwxyz"
    Digit   = "0123456789"
    Xdigit  = "0123456789ABCDEF"

    Errors = []string{
        "Value out of range.",
        "Invalid syntax.",
        "Address out of range.",
        "",
        "",
        "Register out of range.",
        "Port number out of range.",
    }

    Outfile string
    Expfile string
    Impfile string

    Pc       int64
    Padding  int64
    Alphabet = Lower + Capital
    Lwordchars = Digit + Alphabet + "_."
    Swordchars = Digit + Alphabet + "_%$-~&|"

    CurrentSection = ".text"
    CurrentFile    = ""
    Sections       = map[string][2]int64{} // section -> [start, size]

    Symbols    = map[string]int64{}
    Patsymbols = map[string]int64{}

    typeLabel = struct {
        Value   int64
        Section string
    }{}
    Labels       = map[string]struct{ Value, Dummy int64; Section string }{}
    ExportLabels = map[string]struct {
        Value   int64
        Section string
    }{}

    Pat [][]string

    VliwInstBits     = 41
    VliwNop          []int64
    VliwBits         = 128
    VliwSet          []VliwEntry
    VliwFlag         = false
    VliwTemplateBits = int64(0x00)
    VliwStop         int64
    Vcnt             int64 = 1

    ExpMode             = EXP_PAT
    ErrorUndefinedLabel = false
    ErrorAlreadyDefined = false
    AlignVal            int64 = 16
    Bts                 int64 = 8
    Endian              = "little"
    ByteFlag            = "yes"
    Pas                 = 0
    Debug               = false
    Cl                  = ""
    Ln                  = 0
    FnStack             []string
    LnStack             []int
    Vars                = make([]int64, 26)
    Deb1                = ""
    Deb2                = ""
)

type VliwEntry struct {
    Idxs []int64
    Expr string
}

func upper(s string) string {
    return strings.ToUpper(s)
}

func safeChar(s string, idx int) byte {
    if idx < 0 || idx >= len(s) {
        return 0
    }
    return s[idx]
}

func addAvoidingDup[T comparable](l []T, e T) []T {
    for _, v := range l {
        if v == e {
            return l
        }
    }
    return append(l, e)
}

func outbin2(a int64, x int64) {
    if Pas == 2 || Pas == 0 {
        fwrite(Outfile, a, x, 0)
    }
}

func outbin(a int64, x int64) {
    if Pas == 2 || Pas == 0 {
        fwrite(Outfile, a, x, 1)
    }
}

func getVars(s string) int64 {
    c := upper(s)
    if len(c) == 0 {
        return 0
    }
    idx := int(c[0] - 'A')
    if idx < 0 || idx >= len(Vars) {
        return 0
    }
    return Vars[idx]
}

func putVars(s string, v int64) {
    k := upper(s)
    if len(k) == 1 && k[0] >= 'A' && k[0] <= 'Z' {
        Vars[int(k[0]-'A')] = v
    }
}

func q(s string, t string, idx int) bool {
    if idx+len(t) > len(s) {
        return false
    }
    return strings.ToUpper(s[idx:idx+len(t)]) == strings.ToUpper(t)
}

func nbit(l int64) int64 {
    b := int64(0)
    r := l
    for r != 0 {
        r >>= 1
        b++
    }
    return b
}

func skipspc(s string, idx int) int {
    for idx < len(s) && s[idx] == ' ' {
        idx++
    }
    return idx
}

func getParamToSpc(s string, idx int) (string, int) {
    idx = skipspc(s, idx)
    var t strings.Builder
    for idx < len(s) && s[idx] != ' ' {
        t.WriteByte(s[idx])
        idx++
    }
    return t.String(), idx
}

func getParamToEon(s string, idx int) (string, int) {
    idx = skipspc(s, idx)
    var t strings.Builder
    for idx < len(s) && !(idx+2 <= len(s) && s[idx:idx+2] == "!!") {
        t.WriteByte(s[idx])
        idx++
    }
    return t.String(), idx
}

// pyEval: try python3 eval, fallback to ParseFloat
func pyEval(expr string) float64 {
    cmd := exec.Command("python3", "-c", "import sys\ns=sys.stdin.read()\ntry:\n v=eval(s)\n print(repr(v))\nexcept Exception:\n sys.exit(1)\n")
    cmd.Stdin = strings.NewReader(expr)
    out, err := cmd.Output()
    if err == nil {
        s := strings.TrimSpace(string(out))
        if f, e := strconv.ParseFloat(s, 64); e == nil {
            return f
        }
    }
    f, _ := strconv.ParseFloat(expr, 64)
    return f
}

func getIntStr(s string, idx int) (string, int) {
    var fs strings.Builder
    for idx < len(s) && s[idx] >= '0' && s[idx] <= '9' {
        fs.WriteByte(s[idx])
        idx++
    }
    return fs.String(), idx
}

func getFloatStr(s string, idx int) (string, int) {
    if idx+3 <= len(s) && s[idx:idx+3] == "inf" {
        return "inf", idx + 3
    }
    if idx+4 <= len(s) && s[idx:idx+4] == "-inf" {
        return "-inf", idx + 4
    }
    if idx+3 <= len(s) && s[idx:idx+3] == "nan" {
        return "nan", idx + 3
    }
    var fs strings.Builder
    for idx < len(s) {
        ch := s[idx]
        if (ch >= '0' && ch <= '9') || ch == '-' || ch == '.' || ch == 'e' || ch == 'E' {
            fs.WriteByte(ch)
            idx++
        } else {
            break
        }
    }
    return fs.String(), idx
}

func getCurlb(s string, idx int) (bool, string, int) {
    idx = skipspc(s, idx)
    if safeChar(s, idx) != '{' {
        return false, "", idx
    }
    idx++
    idx = skipspc(s, idx)
    var t strings.Builder
    for safeChar(s, idx) != '}' && safeChar(s, idx) != 0 {
        t.WriteByte(s[idx])
        idx++
    }
    if safeChar(s, idx) == '}' {
        idx++
    }
    return true, t.String(), idx
}

func factor(s string, idx int) (int64, int) {
    idx = skipspc(s, idx)
    var x int64
    if idx+4<=len(s) && s[idx:idx+4] == "'\\n'" {
        idx+=4
        x=0x0a
    } else if idx+4<=len(s) && s[idx:idx+4] == "'\\t'" {
        idx+=4
        x=0x09
    } else if idx+3<=len(s) && s[idx:idx+3] == "'\\'" {
        idx+=3
        x=int64('\\')
    } else if idx+4<=len(s) && s[idx:idx+4] == "'\\''" {
        idx+=4
        x=int64('\'')
    } else if idx+3<=len(s) && s[idx] == '\'' && s[idx+2]=='\'' {
        x=int64(s[idx+1])
        idx+=3
    } else if idx+4 <= len(s) && s[idx:idx+4] == "!!!!" && ExpMode == EXP_PAT {
        x = VliwStop
        idx += 4
    } else if idx+3 <= len(s) && s[idx:idx+3] == "!!!" && ExpMode == EXP_PAT {
        x = Vcnt
        idx += 3
    } else if safeChar(s, idx) == '-' {
        var t int
        x, t = factor(s, idx+1)
        idx = t
        x = -x
    } else if safeChar(s, idx) == '~' {
        var t int
        x, t = factor(s, idx+1)
        idx = t
        x = ^x
    } else if safeChar(s, idx) == '@' {
        var t int
        x, t = factor(s, idx+1)
        idx = t
        x = nbit(x)
    } else if safeChar(s, idx) == '*' {
        idx+=1
        if safeChar(s, idx) == '(' {
            var t int
            x,t = expression(s, idx+1)
            idx=t
            if safeChar(s, idx)==',' {
                var tt int
                var x2 int64
                x2, tt = expression(s,idx+1)
                idx=tt
                if safeChar(s, idx)==')' {
                    idx+=1
                    x=x>>(x2*8)
                }
            } else {
                x = 0
            }
        } else {
            x = 0
        }
    } else {
        var t int
        x, t = factor1(s, idx)
        idx = t
    }
    idx = skipspc(s, idx)
    return x, idx
}

func factor1(s string, idx int) (int64, int) {
    var x int64
    idx = skipspc(s, idx)
    c := safeChar(s, idx)
    if c == '(' {
        var t int
        x, t = expression(s, idx+1)
        idx = t
        if safeChar(s, idx) == ')' {
            idx++
        }
    } else if q(s, "$$", idx) {
        idx += 2
        x = Pc
    } else if q(s, "#", idx) {
        idx++
        var t string
        var tIdx int
        t, tIdx = getSymbolWord(s, idx)
        idx = tIdx
        x = getSymVal(t)
    } else if q(s, "0b", idx) {
        idx += 2
        for idx < len(s) && (s[idx] == '0' || s[idx] == '1') {
            x = 2*x + int64(s[idx]-'0')
            idx++
        }
    } else if q(s, "0x", idx) {
        idx += 2
        for idx < len(s) && strings.ContainsRune(Xdigit, rune(unicode.ToUpper(rune(s[idx])))) {
            v, _ := strconv.ParseInt(string(s[idx]), 16, 64)
            x = 16*x + v
            idx++
        }
    /*
    } else if idx+3 <= len(s) && s[idx:idx+3] == "qad" {
        idx += 3
        idx = skipspc(s, idx)
        if safeChar(s, idx) == '{' {
            fs, tIdx := getFloatStr(s, idx+1)
            idx = tIdx
            hex := decimalToIEEE754_128bit_hex(fs)
            v, _ := strconv.ParseInt(hex[2:], 16, 64)
            x = v
        }
        if safeChar(s, idx) == '}' {
            idx++
        }
    */
    } else if idx+3 <= len(s) && s[idx:idx+3] == "dbl" {
        idx += 3
        f, t, tIdx := getCurlb(s, idx)
        idx = tIdx
        if f {
            switch t {
            case "nan":
                x = 0x7ff8000000000000
            case "inf":
                x = 0x7ff0000000000000
            case "-inf":
                var u uint64 = 0xfff0000000000000
                x = *(*int64)(unsafe.Pointer(&u))
            default:
                v := pyEval(t)
                u := math.Float64bits(v)
                bs := make([]byte, 8)
                for i := 0; i < 8; i++ {
                    bs[7-i] = byte(u & 0xff)
                    u >>= 8
                }
                hex := fmt.Sprintf("%x", bs)
                val, _ := strconv.ParseInt(hex, 16, 64)
                x = val
            }
        }
    } else if idx+3 <= len(s) && s[idx:idx+3] == "flt" {
        idx += 3
        f, t, tIdx := getCurlb(s, idx)
        idx = tIdx
        if f {
            switch t {
            case "nan":
                x = 0x7fc00000
            case "inf":
                x = 0x7f800000
            case "-inf":
                x = 0xff800000
            default:
                v := pyEval(t)
                u := math.Float32bits(float32(v))
                bs := make([]byte, 4)
                for i := 0; i < 4; i++ {
                    bs[3-i] = byte(u & 0xff)
                    u >>= 8
                }
                hex := fmt.Sprintf("%x", bs)
                val, _ := strconv.ParseInt(hex, 16, 64)
                x = val
            }
        }
    } else if idx < len(s) && s[idx] >= '0' && s[idx] <= '9' {
        fs, tIdx := getIntStr(s, idx)
        idx = tIdx
        val, _ := strconv.ParseInt(fs, 10, 64)
        x = val
    } else if ExpMode == EXP_PAT && idx < len(s) && strings.ContainsRune(Lower, rune(s[idx])) &&
        !(idx+1 < len(s) && strings.ContainsRune(Lower, rune(s[idx+1]))) {
        ch := string(s[idx])
        if idx+3 <= len(s) && s[idx+1:idx+3] == ":=" {
            var t int
            x, t = expression(s, idx+3)
            idx = t
            putVars(ch, x)
        } else {
            x = getVars(ch)
            idx++
        }
    } else if c := safeChar(s, idx); c != 0 && (strings.ContainsRune(Lwordchars, rune(c)) || c == '.') {
        w, tIdx := getLabelWord(s, idx)
        if tIdx != idx {
            idx = tIdx
            x = getLabelValue(w)
        } else {
            x = 0
        }
    } else {
        x = 0
    }
    idx = skipspc(s, idx)
    return x, idx
}

func term0_0(s string, idx int) (int64, int) {
    x, idx := factor(s, idx)
    for {
        if q(s, "**", idx) {
            t, tIdx := factor(s, idx+2)
            idx = tIdx
            x = int64(math.Pow(float64(x), float64(t)))
        } else {
            break
        }
    }
    return x, idx
}

func term0(s string, idx int) (int64, int) {
    x, idx := term0_0(s, idx)
    for {
        if safeChar(s, idx) == '*' {
            t, tIdx := term0_0(s, idx+1)
            idx = tIdx
            x *= t
        } else if q(s, "//", idx) {
            t, tIdx := term0_0(s, idx+2)
            idx = tIdx
            if t == 0 {
                fmt.Println("Division by 0 error.")
            } else {
                x = x / t
            }
        } else if safeChar(s, idx) == '%' {
            t, tIdx := term0_0(s, idx+1)
            idx = tIdx
            if t == 0 {
                fmt.Println("Division by 0 error.")
            } else {
                x = x % t
            }
        } else {
            break
        }
    }
    return x, idx
}

func term1(s string, idx int) (int64, int) {
    x, idx := term0(s, idx)
    for {
        if safeChar(s, idx) == '+' {
            t, tIdx := term0(s, idx+1)
            idx = tIdx
            x += t
        } else if safeChar(s, idx) == '-' {
            t, tIdx := term0(s, idx+1)
            idx = tIdx
            x -= t
        } else {
            break
        }
    }
    return x, idx
}

func term2(s string, idx int) (int64, int) {
    x, idx := term1(s, idx)
    for {
        if q(s, "<<", idx) {
            t, tIdx := term1(s, idx+2)
            idx = tIdx
            x <<= t
        } else if q(s, ">>", idx) {
            t, tIdx := term1(s, idx+2)
            idx = tIdx
            x >>= t
        } else {
            break
        }
    }
    return x, idx
}

func term3(s string, idx int) (int64, int) {
    x, idx := term2(s, idx)
    for {
        if safeChar(s, idx) == '&' && safeChar(s, idx+1) != '&' {
            t, tIdx := term2(s, idx+1)
            idx = tIdx
            x = x & t
        } else {
            break
        }
    }
    return x, idx
}

func term4(s string, idx int) (int64, int) {
    x, idx := term3(s, idx)
    for {
        if safeChar(s, idx) == '|' && safeChar(s, idx+1) != '|' {
            t, tIdx := term3(s, idx+1)
            idx = tIdx
            x = x | t
        } else {
            break
        }
    }
    return x, idx
}

func term5(s string, idx int) (int64, int) {
    x, idx := term4(s, idx)
    for {
        if safeChar(s, idx) == '^' {
            t, tIdx := term4(s, idx+1)
            idx = tIdx
            x = x ^ t
        } else {
            break
        }
    }
    return x, idx
}

func term6(s string, idx int) (int64, int) {
    x, idx := term5(s, idx)
    for {
        if safeChar(s, idx) == '\'' {
            t, tIdx := term5(s, idx+1)
            idx = tIdx
            if t > 0 {
                var u uint64 = ^uint64(0)
                mask := *(*int64)(unsafe.Pointer(&u))
                x = (x & ^(mask<<t)) | ((mask << t) * (((x>>(t-1)) & 1)))
            }
        } else {
            break
        }
    }
    return x, idx
}

func term7(s string, idx int) (int64, int) {
    x, idx := term6(s, idx)
    for {
        if q(s, "<=", idx) {
            t, tIdx := term6(s, idx+2)
            idx = tIdx
            if x <= t {
                x = 1
            } else {
                x = 0
            }
        } else if safeChar(s, idx) == '<' {
            t, tIdx := term6(s, idx+1)
            idx = tIdx
            if x < t {
                x = 1
            } else {
                x = 0
            }
        } else if q(s, ">=", idx) {
            t, tIdx := term6(s, idx+2)
            idx = tIdx
            if x >= t {
                x = 1
            } else {
                x = 0
            }
        } else if safeChar(s, idx) == '>' {
            t, tIdx := term6(s, idx+1)
            idx = tIdx
            if x > t {
                x = 1
            } else {
                x = 0
            }
        } else if q(s, "==", idx) {
            t, tIdx := term6(s, idx+2)
            idx = tIdx
            if x == t {
                x = 1
            } else {
                x = 0
            }
        } else if q(s, "!=", idx) {
            t, tIdx := term6(s, idx+2)
            idx = tIdx
            if x != t {
                x = 1
            } else {
                x = 0
            }
        } else {
            break
        }
    }
    return x, idx
}

func term8(s string, idx int) (int64, int) {
    if idx+4 <= len(s) && s[idx:idx+4] == "not(" {
        x, tIdx := expression(s, idx+3)
        idx = tIdx
        if x == 0 {
            x = 1
        } else {
            x = 0
        }
        return x, idx
    }
    return term7(s, idx)
}

func term9(s string, idx int) (int64, int) {
    x, idx := term8(s, idx)
    for {
        if q(s, "&&", idx) {
            t, tIdx := term8(s, idx+2)
            idx = tIdx
            if x != 0 && t != 0 {
                x = 1
            } else {
                x = 0
            }
        } else {
            break
        }
    }
    return x, idx
}

func term10(s string, idx int) (int64, int) {
    x, idx := term9(s, idx)
    for {
        if q(s, "||", idx) {
            t, tIdx := term9(s, idx+2)
            idx = tIdx
            if x != 0 || t != 0 {
                x = 1
            } else {
                x = 0
            }
        } else {
            break
        }
    }
    return x, idx
}

func term11(s string, idx int) (int64, int) {
    x, idx := term10(s, idx)
    for {
        if safeChar(s, idx) == '?' {
            t, tIdx := term10(s, idx+1)
            idx = tIdx
            if safeChar(s, idx) == ':' {
                u, uIdx := term10(s, idx+1)
                idx = uIdx
                if x == 0 {
                    x = u
                } else {
                    x = t
                }
            }
        } else {
            break
        }
    }
    return x, idx
}

func expression(s string, idx int) (int64, int) {
    s2 := s + "\x00"
    idx = skipspc(s2, idx)
    return term11(s2, idx)
}

func expression0(s string, idx int) (int64, int) {
    ExpMode = EXP_PAT
    return expression(s, idx)
}

func expression1(s string, idx int) (int64, int) {
    ExpMode = EXP_ASM
    return expression(s, idx)
}

func expressionEsc(s string, idx int, stopchar byte) (int64, int) {
    ExpMode = EXP_PAT
    var result []byte
    depth := 0
    for i := 0; i < len(s); i++ {
        ch := s[i]
        if ch == '(' {
            depth++
            result = append(result, ch)
        } else if ch == ')' {
            if depth > 0 {
                depth--
            }
            result = append(result, ch)
        } else {
            if depth == 0 && ch == stopchar {
                result = append(result, 0)
            } else {
                result = append(result, ch)
            }
        }
    }
    replaced := string(result)
    return expression(replaced, idx)
}

func getSymVal(w string) int64 {
    w = strings.ToUpper(w)
    if v, ok := Symbols[w]; ok {
        return v
    }
    return 0
}

func getSymValWithOk(w string) (int64, bool) {
    w = strings.ToUpper(w)
    v, ok := Symbols[w]
    return v, ok
}

func clearSymbol(i []string) bool {
    if len(i) == 0 || i[0] != ".clearsym" {
        return false
    }
    if len(i) >= 3 {
        key := upper(i[2])
        if _, ok := Symbols[key]; ok {
            delete(Symbols, key)
            return true
        }
    }
    if len(i) == 1 {
        Symbols = map[string]int64{}
    }
    return true
}

func setSymbol(i []string) bool {
    if len(i) == 0 || i[0] != ".setsym" {
        return false
    }
    key := upper(i[1])
    var v int64
    if len(i) > 2 {
        v, _ = expression0(i[2], 0)
    }
    Symbols[key] = v
    return true
}

func bitsDirective(i []string) bool {
    if len(i) == 0 || i[0] != ".bits" {
        return false
    }
    if len(i) >= 2 && i[1] == "big" {
        Endian = "big"
    } else {
        Endian = "little"
    }
    var v int64
    if len(i) >= 3 {
        v, _ = expression0(i[2], 0)
    } else {
        v = 8
    }
    Bts = v
    return true
}

func paddingp(i []string) bool {
    if len(i) == 0 || i[0] != ".padding" {
        return false
    }
    var v int64
    if len(i) >= 3 {
        v, _ = expression0(i[2], 0)
    } else {
        v = 0
    }
    Padding = v
    return true
}

func symbolc(i []string) bool {
    if len(i) == 0 || i[0] != ".symbolc" {
        return false
    }
    if len(i) > 3 {
        Swordchars = Alphabet + Digit + i[2]
    }
    return true
}

func removeComment(line string) string {
    for i := 0; i+1 < len(line); i++ {
        if line[i:i+2] == "/*" {
            if i == 0 {
                return ""
            }
            return line[:i]
        }
    }
    return line
}

func removeCommentAsm(l string) string {
    if idx := strings.IndexByte(l, ';'); idx >= 0 {
        return strings.TrimRight(l[:idx], " \t\r\n")
    }
    return strings.TrimRight(l, " \t\r\n")
}

func getParams1(l string, idx int) (string, int) {
    idx = skipspc(l, idx)
    if idx >= len(l) {
        return "", idx
    }
    var s strings.Builder
    for idx < len(l) {
        if idx+2 <= len(l) && l[idx:idx+2] == "::" {
            idx += 2
            break
        }
        s.WriteByte(l[idx])
        idx++
    }
    return strings.TrimRight(s.String(), " "), idx
}

func reduceSpaces(text string) string {
    for strings.Contains(text,"  ") {
        text=strings.ReplaceAll(text,"  "," ")
    }
    return text
}

func readpat(fn string) [][]string {
    if fn == "" {
        return nil
    }
    var w [][]string
    f, err := os.Open(fn)
    if err != nil {
        return nil
    }
    defer f.Close()
    sc := bufio.NewScanner(f)
    for sc.Scan() {
        line := sc.Text()
        l := removeComment(line)
        l = strings.ReplaceAll(l, "\t", " ")
        l = strings.ReplaceAll(l, "\r", "")
        l = strings.ReplaceAll(l, "\n", "")
        l = strings.TrimRight(l," ")
        if ww := includePat(l); len(ww) > 0 {
            w = append(w, ww...)
            continue
        }
        var r []string
        idx := 0
        for {
            s, tIdx := getParams1(l, idx)
            idx = tIdx
            r = append(r, s)
            if idx >= len(l) {
                break
            }
        }
        var p []string
        switch len(r) {
        case 1:
            p = []string{r[0], "", "", "", "", ""}
        case 2:
            p = []string{r[0], "", r[1], "", "", ""}
        case 3:
            p = []string{r[0], r[1], r[2], "", "", ""}
        case 4:
            p = []string{r[0], r[1], r[2], r[3], "", ""}
        case 5:
            p = []string{r[0], r[1], r[2], r[3], r[4], ""}
        case 6:
            p = r[:6]
        default:
            p = []string{"", "", "", "", "", ""}
        }
        w = append(w, p)
    }
    return w
}

func fwrite(filePath string, position int64, x int64, prt int) int {
    b := Bts
    if b <= 8 {
        b = 8
    }
    byts := int((b + 7) / 8)
    cnt := 0
    if filePath != "" {
        f, err := os.OpenFile(filePath, os.O_RDWR|os.O_CREATE, 0644)
        if err != nil {
            return 0
        }
        defer f.Close()
        f.Seek(position*int64(byts), io.SeekStart)
        if Endian == "little" {
            mask := (int64(1) << Bts) - 1
            v := x & mask
            for i := 0; i < byts; i++ {
                vv := byte(v & 0xff)
                f.Write([]byte{vv})
                if prt == 1 {
                    fmt.Printf(" 0x%02x", vv)
                }
                v >>= 8
                cnt++
            }
        } else {
            mask := (int64(1) << Bts) - 1
            xMasked := x & mask
            p := int64(0xff) << (uint(byts)*8 - 8)
            for i := byts - 1; i >= 0; i-- {
                v := byte((xMasked & p) >> (uint(i) * 8))
                f.Write([]byte{v})
                if prt == 1 {
                    fmt.Printf(" 0x%02x", v)
                }
                p >>= 8
                cnt++
            }
        }
    } else {
        if Endian == "little" {
            mask := (int64(1) << Bts) - 1
            v := x & mask
            for i := 0; i < byts; i++ {
                vv := byte(v & 0xff)
                if prt == 1 {
                    fmt.Printf(" 0x%02x", vv)
                }
                v >>= 8
                cnt++
            }
        } else {
            mask := (int64(1) << Bts) - 1
            xMasked := x & mask
            p := int64(0xff) << (uint(byts)*8 - 8)
            for i := byts - 1; i >= 0; i-- {
                v := byte((xMasked & p) >> (uint(i) * 8))
                if prt == 1 {
                    fmt.Printf(" 0x%02x", v)
                }
                p >>= 8
                cnt++
            }
        }
    }
    return cnt
}

func align_(addr int64) int64 {
    a := addr % AlignVal
    if a == 0 {
        return addr
    }
    return addr + (AlignVal - a)
}

func makeobj(s string) []int64 {
    s2 := s + "\x00"
    idx := 0
    var objl []int64
    for safeChar(s2, idx) != 0 {
        if s2[idx] == ',' {
            idx++
            p := Pc + int64(len(objl))
            n := align_(p)
            for i := p; i < n; i++ {
                objl = append(objl, Padding)
            }
            continue
        }
        semicolon := false
        if s2[idx] == ';' {
            semicolon = true
            idx++
        }
        x, tIdx := expression0(s2, idx)
        idx = tIdx
        if !semicolon || (semicolon && x != 0) {
            objl = append(objl, x)
        }
        if s2[idx] == ',' {
            idx++
        }
    }
    return objl
}

func getSymbolWord(s string, idx int) (string, int) {
    var t strings.Builder
    if idx < len(s) && !strings.ContainsRune(Digit, rune(s[idx])) && strings.ContainsRune(Swordchars, rune(s[idx])) {
        t.WriteByte(s[idx])
        idx++
        for idx < len(s) && strings.ContainsRune(Swordchars, rune(s[idx])) {
            t.WriteByte(s[idx])
            idx++
        }
    }
    return strings.ToUpper(t.String()), idx
}

func getLabelWord(s string, idx int) (string, int) {
    var t strings.Builder
    if idx < len(s) && (s[idx] == '.' || (!strings.ContainsRune(Digit, rune(s[idx])) && strings.ContainsRune(Lwordchars, rune(s[idx])))) {
        t.WriteByte(s[idx])
        idx++
        for idx < len(s) && strings.ContainsRune(Lwordchars, rune(s[idx])) {
            t.WriteByte(s[idx])
            idx++
        }
        if idx < len(s) && s[idx] == ':' {
            idx++
        }
    }
    return t.String(), idx
}

func match(s, t string) bool {
    t2 := strings.ReplaceAll(strings.ReplaceAll(t, OB, ""), CB, "")
    idxS := skipspc(s, 0)
    idxT := skipspc(t2, 0)
    s2 := s + "\x00"
    t2 += "\x00"

    Deb1 = s2
    Deb2 = t2

    for {
        idxS = skipspc(s2, idxS)
        idxT = skipspc(t2, idxT)
        b := safeChar(s2, idxS)
        a := safeChar(t2, idxT)

        if a == 0 && b == 0 {
            return true
        }

        if a == '\\' {
            idxT++
            if safeChar(t2, idxT) == b {
                idxT++
                idxS++
                continue
            }
            return false
        } else if a >= 'A' && a <= 'Z' {
            if a == byte(unicode.ToUpper(rune(b))) {
                idxS++
                idxT++
                continue
            }
            return false
        } else if a == '!' {
            idxT++
            a = safeChar(t2, idxT)
            idxT++

            // !!x → factor 1 個だけ読む
            if a == '!' {
                a = safeChar(t2, idxT)
                idxT++
                v, tIdx := factor(s2, idxS)
                idxS = tIdx
                putVars(string(a), v)
                continue
            }

            // !x → 式を「次の区切り文字」まで読む
            idxT = skipspc(t2, idxT)

            // デフォルトの区切り文字は「次の非スペース文字」
            var stopchar byte
            if safeChar(t2, idxT) == '\\' {
                // !x\] みたいな場合：明示的に区切り文字を指定
                idxT = skipspc(t2, idxT+1)
                stopchar = safeChar(t2, idxT)
            } else {
                // 次の非スペース文字を区切り文字として扱う（例: ',', ']' など）
                stopchar = safeChar(t2, idxT)
            }

            v, tIdx := expressionEsc(s2, idxS, stopchar)
            idxS = tIdx
            putVars(string(a), v)
            continue
        } else if a >= 'a' && a <= 'z' {
            idxT++
            w, tIdx := getSymbolWord(s2, idxS)
            idxS = tIdx
            v,ok := getSymValWithOk(w)
            if !ok {
                return false
            }
            putVars(string(a), v)
            continue
        } else if a == b {
            idxT++
            idxS++
            continue
        }

        return false
    }
}

func removeBrackets(s string, remove []int) string {
    type bracket struct {
        depth int
        pos   int
        open  bool
    }
    var bs []bracket
    depth := 0
    for i := 0; i < len(s); i++ {
        if s[i] == OB[0] {
            depth++
            bs = append(bs, bracket{depth, i, true})
        } else if s[i] == CB[0] {
            bs = append(bs, bracket{depth, i, false})
            depth--
        }
    }
    removeSet := map[int]bool{}
    for _, d := range remove {
        removeSet[d] = true
    }
    toDelete := map[int]bool{}
    start := -1
    for _, b := range bs {
        if b.open && removeSet[b.depth] {
            start = b.pos
        }
        if !b.open && removeSet[b.depth] && start >= 0 {
            for i := start; i <= b.pos; i++ {
                toDelete[i] = true
            }
            start = -1
        }
    }
    var out []byte
    for i := 0; i < len(s); i++ {
        if !toDelete[i] {
            out = append(out, s[i])
        }
    }
    return string(out)
}

func match0(s, t string) bool {
    t2 := strings.ReplaceAll(strings.ReplaceAll(t, "[[", OB), "]]", CB)
    cnt := strings.Count(t2, OB)
    sl := make([]int, cnt)
    for i := 0; i < cnt; i++ {
        sl[i] = i + 1
    }
    for i := 0; i <= len(sl); i++ {
        found := false
        var comb func(start, k int, cur []int)
        comb = func(start, k int, cur []int) {
            if found {
                return
            }
            if k == 0 {
                lt := removeBrackets(t2, cur)
                if match(s, lt) {
                    found = true
                }
                return
            }
            for j := start; j <= len(sl)-k; j++ {
                comb(j+1, k-1, append(cur, sl[j]))
                if found {
                    return
                }
            }
        }
        comb(0, i, nil)
        if found {
            return true
        }
    }
    return false
}

func errorDirective(s string) {
    ss := strings.ReplaceAll(s, " ", "")
    if ss == "" {
        return
    }
    s2 := s + "\x00"
    idx := 0
    for safeChar(s2, idx) != 0 {
        ch := safeChar(s2, idx)
        if ch == ',' {
            idx++
            continue
        }
        u, tIdx := expression0(s2, idx)
        idx = tIdx
        if safeChar(s2, idx) == ';' {
            idx++
        }
        t, tIdx2 := expression0(s2, idx)
        idx = tIdx2
        if (Pas == 2 || Pas == 0) && u != 0 {
            fmt.Printf("Line %d Error code %d ", Ln, t)
            if t >= 0 && int(t) < len(Errors) {
                fmt.Print(Errors[t])
            }
            fmt.Println(": ")
        }
    }
}

func labelcProcessing(l, ll string) bool {
    if strings.ToUpper(l) != ".LABELC" {
        return false
    }
    if ll != "" {
        Lwordchars = Alphabet + Digit + ll
    }
    return true
}

func labelProcessing(l string) string {
    if l == "" {
        return ""
    }
    label, idx := getLabelWord(l, 0)
    lidx := idx
    if label != "" && safeChar(l, idx-1) == ':' {
        idx = skipspc(l, idx)
        e, tIdx := getParamToSpc(l, idx)
        idx = tIdx
        if strings.ToUpper(e) == ".EQU" {
            u, _ := expression1(l, idx)
            putLabelValue(label, u, CurrentSection)
            return ""
        }
        putLabelValue(label, Pc, CurrentSection)
        return l[lidx:]
    }
    return l
}

func getString(l2 string) string {
    idx := skipspc(l2, 0)
    if l2 == "" || safeChar(l2, idx) != '"' {
        return ""
    }
    idx++
    var s strings.Builder
    for idx < len(l2) {
        if l2[idx] == '"' {
            return s.String()
        }
        s.WriteByte(l2[idx])
        idx++
    }
    return ""
}

func asciistr(l2 string) bool {
    idx := skipspc(l2, 0)
    if l2 == "" || safeChar(l2, idx) != '"' {
        return false
    }
    idx++
    for idx < len(l2) {
        if l2[idx] == '"' {
            return true
        }
        var ch byte
        if idx+2 <= len(l2) && l2[idx:idx+2] == "\\0" {
            idx += 2
            ch = 0
        } else if idx+2 <= len(l2) && l2[idx:idx+2] == "\\t" {
            idx += 2
            ch = '\t'
        } else if idx+2 <= len(l2) && l2[idx:idx+2] == "\\n" {
            idx += 2
            ch = '\n'
        } else {
            ch = l2[idx]
            idx++
        }
        outbin(Pc, int64(ch))
        Pc++
    }
    return false
}

func exportProcessing(l1, l2 string) bool {
    if !(Pas == 2 || Pas == 0) {
        return false
    }
    if strings.ToUpper(l1) != ".EXPORT" {
        return false
    }
    idx := 0
    l2 += "\x00"
    for safeChar(l2, idx) != 0 {
        idx = skipspc(l2, idx)
        s, tIdx := getLabelWord(l2, idx)
        idx = tIdx
        if s == "" {
            break
        }
        if safeChar(l2, idx) == ':' {
            idx++
        }
        v := getLabelValue(s)
        sec := getLabelSectionName(s)
        ExportLabels[s] = struct {
            Value   int64
            Section string
        }{v, sec}
        if safeChar(l2, idx) == ',' {
            idx++
        }
    }
    return true
}

func zeroProcessing(l1, l2 string) bool {
    if strings.ToUpper(l1) != ".ZERO" {
        return false
    }
    x, _ := expression1(l2, 0)
    for i := int64(0); i <= x; i++ {
        outbin2(Pc, 0x00)
        Pc++
    }
    return true
}

func asciiProcessing(l1, l2 string) bool {
    if strings.ToUpper(l1) != ".ASCII" {
        return false
    }
    return asciistr(l2)
}

func asciizProcessing(l1, l2 string) bool {
    if strings.ToUpper(l1) != ".ASCIIZ" {
        return false
    }
    f := asciistr(l2)
    if f {
        outbin(Pc, 0x00)
        Pc++
    }
    return f
}

func includePat(l string) [][]string {
    idx := skipspc(l, 0)
    if idx+8 > len(l) {
        return nil
    }
    i := strings.ToUpper(l[idx : idx+8])
    if i != ".INCLUDE" {
        return nil
    }
    s := getString(l[8:])
    return readpat(s)
}

func vliwp(i []string) bool {
    if len(i) == 0 || i[0] != ".vliw" {
        return false
    }
    v1, _ := expression0(i[1], 0)
    v2, _ := expression0(i[2], 0)
    v3, _ := expression0(i[3], 0)
    v4, _ := expression0(i[4], 0)
    VliwBits = int(v1)
    VliwInstBits = int(v2)
    VliwTemplateBits = v3
    VliwFlag = true
    var l []int64
    n := int((float64(VliwInstBits) + 7) / 8)
    val := v4
    for j := 0; j < n; j++ {
        l = append(l, val&0xff)
        val >>= 8
    }
    VliwNop = l
    return true
}

func includeAsm(l1, l2 string) bool {
    if strings.ToUpper(l1) != ".INCLUDE" {
        return false
    }
    s := getString(l2)
    if s != "" {
        fileassemble(s)
    }
    return true
}

func sectionProcessing(l1, l2 string) bool {
    u := strings.ToUpper(l1)
    if u != "SECTION" && u != "SEGMENT" {
        return false
    }
    if l2 != "" {
        CurrentSection = l2
        Sections[l2] = [2]int64{Pc, 0}
    }
    return true
}

func alignProcessing(l1, l2 string) bool {
    if strings.ToUpper(l1) != ".ALIGN" {
        return false
    }
    if l2 != "" {
        u, _ := expression1(l2, 0)
        AlignVal = u
    }
    Pc = align_(Pc)
    return true
}

func endsectionProcessing(l1, l2 string) bool {
    u := strings.ToUpper(l1)
    if u != "ENDSECTION" && u != "ENDSEGMENT" {
        return false
    }
    start := Sections[CurrentSection][0]
    Sections[CurrentSection] = [2]int64{start, Pc - start}
    return true
}

func orgProcessing(l1, l2 string) bool {
    if strings.ToUpper(l1) != ".ORG" {
        return false
    }
    u, idx := expression1(l2, 0)
    if idx+2 <= len(l2) && strings.ToUpper(l2[idx:idx+2]) == ",P" {
        if u > Pc {
            for i := Pc; i < u; i++ {
                outbin2(i, Padding)
            }
        }
    }
    Pc = u
    return true
}

func epic(i []string) bool {
    if len(i) == 0 || strings.ToUpper(i[0]) != "EPIC" {
        return false
    }
    if len(i) <= 1 || i[1] == "" {
        return false
    }
    s := i[1]
    var idxs []int64
    idx := 0
    for {
        v, tIdx := expression0(s, idx)
        idx = tIdx
        idxs = append(idxs, v)
        if idx >= len(s) || s[idx] != ',' {
            break
        }
        idx++
    }
    s2 := i[2]
    VliwSet = append(VliwSet, VliwEntry{Idxs: idxs, Expr: s2})
    return true
}

func lineassemble2(line string, idx int) (int64, []int64, bool, int) {
    l, idx := getParamToSpc(line, idx)
    l2, idx := getParamToEon(line, idx)
    l = strings.TrimRight(l, " ")
    l2 = strings.TrimRight(l2, " ")
    l = strings.ReplaceAll(l, " ", "")
    if sectionProcessing(l, l2) {
        return 0, nil, true, idx
    }
    if endsectionProcessing(l, l2) {
        return 0, nil, true, idx
    }
    if zeroProcessing(l, l2) {
        return 0, nil, true, idx
    }
    if asciiProcessing(l, l2) {
        return 0, nil, true, idx
    }
    if asciizProcessing(l, l2) {
        return 0, nil, true, idx
    }
    if includeAsm(l, l2) {
        return 0, nil, true, idx
    }
    if alignProcessing(l, l2) {
        return 0, nil, true, idx
    }
    if orgProcessing(l, l2) {
        return 0, nil, true, idx
    }
    if labelcProcessing(l, l2) {
        return 0, nil, true, idx
    }
    if exportProcessing(l, l2) {
        return 0, nil, true, idx
    }
    if l == "" {
        return 0, nil, false, idx
    }

    var (
        se, oerr bool
        pln      int
        pl       []string
        idxs     int64
        objl     []int64
    )

    loopflag := true
    for _, i := range Pat {
        pln++
        pl = i
        for _, ch := range Lower {
            putVars(string(ch), 0)
        }
        if i == nil {
            continue
        }
        if setSymbol(i) {
            continue
        }
        if clearSymbol(i) {
            continue
        }
        if paddingp(i) {
            continue
        }
        if bitsDirective(i) {
            continue
        }
        if symbolc(i) {
            continue
        }
        if epic(i) {
            continue
        }
        if vliwp(i) {
            continue
        }
        lw := 0
        for _, x := range i {
            if x != "" {
                lw++
            }
        }
        if lw == 0 {
            continue
        }
        lin := reduceSpaces(strings.TrimSpace(l + " " + l2))
        if i[0] == "" {
            loopflag = false
            break
        }
        ErrorUndefinedLabel = false
        func() {
            defer func() {
                if r := recover(); r != nil {
                    oerr = true
                    loopflag = false
                }
            }()
            if match0(lin, i[0]) {
                errorDirective(i[1])
                objl = makeobj(i[2])
                idxs, _ = expression0(i[3], 0)
                loopflag = false
            }
        }()
        if !loopflag {
            break
        }
    }

    if loopflag {
        se = true
        pln = 0
        pl = nil
    }

    if Pas == 2 || Pas == 0 {
        if ErrorUndefinedLabel {
            fmt.Println(" error - undefined label error.")
            return 0, nil, false, idx
        }
        if se {
            fmt.Println(" error - Syntax error.")
            return 0, nil, false, idx
        }
        if oerr {
            fmt.Printf(" ; pat %d %v error - Illegal syntax in assemble line or pattern line.\n", pln, pl)
            return 0, nil, false, idx
        }
    }

    return idxs, objl, true, idx
}

func equalSet(a, b []int64) bool {
    if len(a) != len(b) {
        return false
    }
    ma := map[int64]int{}
    mb := map[int64]int{}
    for _, v := range a {
        ma[v]++
    }
    for _, v := range b {
        mb[v]++
    }
    if len(ma) != len(mb) {
        return false
    }
    for k, v := range ma {
        if mb[k] != v {
            return false
        }
    }
    return true
}

func abs64(x int64) int64 {
    if x < 0 {
        return -x
    }
    return x
}


func absInt64(x int64) int64 {
    if x < 0 {
        return -x
    }
    return x
}

// vliwset は Ruby の $vliwset と同じ構造を想定
// 例: type VliwEntry struct { Idxs []int64; Expr string }
// var vliwset []VliwEntry

func vliwprocess(line string, idxs int64, objl []int64, flag bool, idx int) bool {
    objs := [][]int64{objl}
    idxlst := []int64{idxs}
    VliwStop = 0

    // "!!!!" / "!!" を辿って VLIW の全スロットを集める
    for {
        idx = skipspc(line, idx)
        if idx+4 <= len(line) && line[idx:idx+4] == "!!!!" {
            idx += 4
            VliwStop = 1
            continue
        } else if idx+2 <= len(line) && line[idx:idx+2] == "!!" {
            idx += 2
            nidxs, nobjl, nflag, nidx := lineassemble2(line, idx)
            idxs = nidxs
            objl = nobjl
            flag = nflag
            idx = nidx
            objs = append(objs, objl)
            idxlst = append(idxlst, idxs)
            continue
        } else {
            break
        }
    }

    // テンプレートビットが 0 の場合、デフォルトセット
    if VliwTemplateBits == 0 {
        VliwSet = []VliwEntry{
            {Idxs: []int64{0}, Expr: "0"},
        }
    }

    vbits := absInt64(int64(VliwBits))
    instBits := int64(VliwInstBits)
    tbits := absInt64(int64(VliwTemplateBits))

    for _, k := range VliwSet {
        if !sameIdxSet(k.Idxs, idxlst) && VliwTemplateBits != 0 {
            continue
        }

        im := new(big.Int).Sub(
            new(big.Int).Lsh(big.NewInt(1), uint(instBits)),
            big.NewInt(1),
        )

        tm := new(big.Int).Sub(
            new(big.Int).Lsh(big.NewInt(1), uint(tbits)),
            big.NewInt(1),
        )

        pm := new(big.Int).Sub(
            new(big.Int).Lsh(big.NewInt(1), uint(vbits)),
            big.NewInt(1),
        )

        x, _ := expression0(k.Expr, 0)
        xBig := big.NewInt(x)
        templ := new(big.Int).And(xBig, tm)

        var values []int64
        for _, j := range objs {
            for _, m := range j {
                values = append(values, m)
            }
        }

        nob := (vbits + 7) / 8
        ibyte := (instBits + 7) / 8
        noi := (vbits - tbits) / instBits

        need := int64(ibyte*noi) - int64(len(values))
        for i := int64(0); i < need; i++ {
            for _, b := range VliwNop {
                values = append(values, int64(b))
            }
        }

        var v1 []*big.Int
        cnt := 0
        for i := int64(0); i < noi; i++ {
            vv := big.NewInt(0)
            for j := int64(0); j < ibyte; j++ {
                vv.Lsh(vv, 8)
                if cnt < len(values) {
                    vv.Or(vv, big.NewInt(values[cnt]&0xff))
                }
                cnt++
            }
            vv.And(vv, im)
            v1 = append(v1, vv)
        }

        r := big.NewInt(0)
        for _, v := range v1 {
            r.Lsh(r, uint(instBits))
            r.Or(r, v)
        }
        r.And(r, pm)

        res := big.NewInt(0)
        if VliwTemplateBits < 0 {
            tmp := new(big.Int).Lsh(templ, uint(vbits-tbits))
            res.Or(r, tmp)
        } else {
            tmp := new(big.Int).Lsh(r, uint(VliwTemplateBits))
            res.Or(tmp, templ)
        }

        q := int64(0)
        if VliwBits > 0 {
            bc := vbits - 8
            mask := big.NewInt(0xff)
            for i := int64(0); i < nob; i++ {
                tmp := new(big.Int).Rsh(res, uint(bc))
                tmp.And(tmp, mask)
                outbin(Pc+q, tmp.Int64())
                bc -= 8
                q++
            }
        } else {
            mask := big.NewInt(0xff)
            for i := int64(0); i < nob; i++ {
                tmp := new(big.Int).And(res, mask)
                outbin(Pc+q, tmp.Int64())
                res.Rsh(res, 8)
                q++
            }
        }

        Pc += q
        return true
    }

    if Pas == 0 || Pas == 2 {
        fmt.Println(" error - No vliw instruction-set defined.")
        return false
    }
    return false
}

// Ruby の k[0].to_set == idxlst.to_set 相当
func sameIdxSet(kIdxs []int64, idxlst []int64) bool {
    if len(kIdxs) != len(idxlst) {
        return false
    }

    m := map[int64]struct{}{}
    for _, v := range kIdxs {
        m[v] = struct{}{}
    }

    for _, v := range idxlst {
        if _, ok := m[v]; !ok {
            return false
        }
    }

    return true
}

func lineassemble(line string) bool {
    line = strings.ReplaceAll(line, "\t", " ")
    line = strings.ReplaceAll(line, "\n", "")
    line = reduceSpaces(line)
    line = removeCommentAsm(line)
    if line == "" {
        return false
    }
    line = labelProcessing(line)
    clearSymbol([]string{".clearsym", "", ""})
    parts := strings.Split(line, "!!")
    Vcnt = 0
    for _, p := range parts {
        if p != "" {
            Vcnt++
        }
    }
    idxs, objl, flag, idx := lineassemble2(line, 0)
    if !flag {
        return false
    }
    if !VliwFlag || (idx+2 > len(line) || line[idx:idx+2] != "!!") {
        of := len(objl)
        for cnt := 0; cnt < of; cnt++ {
            outbin(Pc+int64(cnt), objl[cnt])
        }
        Pc += int64(of)
    } else {
        defer func() {
            if r := recover(); r != nil {
                if Pas == 0 || Pas == 2 {
                    fmt.Println(" error - Some error(s) in vliw definition.")
                }
            }
        }()
        vflag := vliwprocess(line, idxs, objl, flag, idx)
        return vflag
    }
    return true
}

func lineassemble0(line string) bool {
    Cl = strings.ReplaceAll(line, "\n", "")
    if Pas == 2 || Pas == 0 {
        fmt.Printf("%016x %s %d %s ", Pc, CurrentFile, Ln, Cl)
    }
    f := lineassemble(Cl)
    if Pas == 2 || Pas == 0 {
        fmt.Println()
    }
    Ln++
    return f
}

func option(argv []string, o string) ([]string, string) {
    idx := -1
    for i, v := range argv {
        if v == o {
            idx = i
            break
        }
    }
    if idx == -1 {
        return argv, ""
    }
    if idx+1 < len(argv) {
        val := argv[idx+1]
        newArgv := append([]string{}, argv[:idx]...)
        if idx+2 < len(argv) {
            newArgv = append(newArgv, argv[idx+2:]...)
        }
        return newArgv, val
    }
    return argv[:idx], ""
}

func fileInputFromStdin() string {
    var af strings.Builder
    sc := bufio.NewScanner(os.Stdin)
    for sc.Scan() {
        line := strings.TrimSpace(sc.Text())
        if line == "" {
            break
        }
        af.WriteString(line)
        af.WriteByte('\n')
    }
    return af.String()
}

func setpatsymbols(pat [][]string) {
    for _, i := range pat {
        func() {
            defer func() { _ = recover() }()
            setSymbol(i)
        }()
    }
    for k, v := range Symbols {
        Patsymbols[k] = v
    }
}

func fileassemble(fn string) {
    FnStack = append(FnStack, CurrentFile)
    LnStack = append(LnStack, Ln)
    CurrentFile = fn
    Ln = 1
    if fn == "stdin" {
        if Pas != 2 && Pas != 0 {
            af := fileInputFromStdin()
            tmp := "axx.tmp"
            os.WriteFile(tmp, []byte(af), 0644)
            fn = tmp
        }
    }
    f, err := os.Open(fn)
    if err != nil {
        return
    }
    defer f.Close()
    sc := bufio.NewScanner(f)
    for sc.Scan() {
        lineassemble0(sc.Text())
    }
    if len(FnStack) > 0 {
        CurrentFile = FnStack[len(FnStack)-1]
        FnStack = FnStack[:len(FnStack)-1]
        Ln = LnStack[len(LnStack)-1]
        LnStack = LnStack[:len(LnStack)-1]
    }
}

func impLabel(l string) bool {
    idx := skipspc(l, 0)
    section, tIdx := getLabelWord(l, idx)
    idx = tIdx
    idx = skipspc(l, idx)
    label, tIdx2 := getLabelWord(l, idx)
    idx = tIdx2
    if label == "" {
        return false
    }
    idx = skipspc(l, idx)
    v, newIdx := expression(l, idx)
    if newIdx == idx {
        return false
    }
    putLabelValue(label, v, section)
    return true
}

func putLabelValue(k string, v int64, s string) bool {
    if Pas == 1 || Pas == 0 {
        if _, ok := Labels[k]; ok {
            ErrorAlreadyDefined = true
            fmt.Println(" error - label already defined.")
            return false
        }
    }
    for key := range Patsymbols {
        if key == upper(k) {
            fmt.Printf(" error - '%s' is a pattern file symbol.\n", k)
            return false
        }
    }
    ErrorAlreadyDefined = false
    Labels[k] = struct {
        Value   int64
        Dummy   int64
        Section string
    }{v, 0, s}
    return true
}

func getLabelSectionName(k string) string {
    if v, ok := Labels[k]; ok {
        return v.Section
    }
    ErrorUndefinedLabel = true
    return ""
}

func getLabelSection(k string) int64 {
    if v, ok := Labels[k]; ok {
        // not used numerically in Ruby; keep 0
        _ = v.Section
        return 0
    }
    ErrorUndefinedLabel = true
    return UNDEF
}

func getLabelValue(k string) int64 {
    if v, ok := Labels[k]; ok {
        return v.Value
    }
    ErrorUndefinedLabel = true
    return UNDEF
}

/*
func decimalToIEEE754_128bit_hex(a string) string {
    if a == "inf" {
        return "0x7FFF0000000000000000000000000000"
    }
    if a == "-inf" {
        return "0xFFFF0000000000000000000000000000"
    }
    if a == "nan" {
        return "0x7FFF8000000000000000000000000000"
    }
    f, _ := strconv.ParseFloat(a, 64)
    sign := int64(0)
    if math.Signbit(f) {
        sign = 1
        f = -f
    }
    if f == 0 {
        return fmt.Sprintf("0x%032X", sign<<127)
    }
    exp := int64(math.Floor(math.Log2(f)))
    bias := int64(16383)
    exponent := exp + bias
    normalized := f / math.Pow(2, float64(exp))
    fraction := int64((normalized - 1.0) * math.Pow(2, 112))
    bits := (sign << 127) | (exponent << 112) | (fraction & ((int64(1)<<112)-1))
    return fmt.Sprintf("0x%032X", bits)
}
*/

func main() {
    if len(os.Args) == 1 {
        fmt.Println("axx general assembler programmed and designed by Taisuke Maekawa")
        fmt.Println("Usage: axx patternfile.axx [sourcefile.s] [-o outfile.bin] [-e export_labels.tsv] [-i import_labels.tsv]")
        return
    }
    sysArgv := append([]string{}, os.Args[1:]...)
    if len(sysArgv) >= 1 {
        Pat = readpat(sysArgv[0])
        setpatsymbols(Pat)
    }
    var expefile string
    sysArgv, Expfile = option(sysArgv, "-e")
    sysArgv, expefile = option(sysArgv, "-E")
    sysArgv, Outfile = option(sysArgv, "-o")
    sysArgv, Impfile = option(sysArgv, "-i")

    if Impfile != "" {
        f, err := os.Open(Impfile)
        if err == nil {
            sc := bufio.NewScanner(f)
            for sc.Scan() {
                impLabel(sc.Text())
            }
            f.Close()
        }
    }

    if Outfile != "" {
        os.Remove(Outfile)
        f, _ := os.Create(Outfile)
        f.Close()
    }

    if len(sysArgv) == 1 {
        Pc = 0
        Pas = 0
        Ln = 1
        CurrentFile = "(stdin)"
        reader := bufio.NewReader(os.Stdin)
        for {
            fmt.Printf("%016x: >> ", Pc)
            line, err := reader.ReadString('\n')
            if err != nil {
                break
            }
            line = strings.ReplaceAll(line, "\\\\", "\\")
            line = strings.TrimSpace(line)
            if line == "" {
                continue
            }
            lineassemble0(line)
        }
    } else if len(sysArgv) >= 2 {
        Pc = 0
        Pas = 1
        Ln = 1
        fileassemble(sysArgv[1])
        Pc = 0
        Pas = 2
        Ln = 1
        fileassemble(sysArgv[1])
    }

    var elf int
    if expefile != "" {
        Expfile = expefile
        elf = 1
    } else {
        elf = 0
    }

    if Expfile != "" {
        f, err := os.Create(Expfile)
        if err == nil {
            w := bufio.NewWriter(f)
            for sec, v := range Sections {
                flag := ""
                if sec == ".text" && elf == 1 {
                    flag = "AX"
                }
                if sec == ".data" && elf == 1 {
                    flag = "WA"
                }
                start := v[0]
                fmt.Fprintf(w, "%s\t%#x\t%#x\t%s\n", sec, start, v[1], flag)
            }
            for k, v := range ExportLabels {
                fmt.Fprintf(w, "%s\t%#x\n", k, v.Value)
            }
            w.Flush()
            f.Close()
        }
    }
}
