// axx general assembler - Complete C translation
// Programmed and designed by Taisuke Maekawa
// C translation maintains full compatibility

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>
#include <stdint.h>
#include <math.h>
#include <stdbool.h>

#define EXP_PAT 0
#define EXP_ASM 1
#define MAX_OBJL 1000
#define MAX_LINE 65536
#define MAX_SYMBOLS 10000
#define MAX_LABELS 10000
#define MAX_PAT 10000
#define MAX_FIELDS 10
#define UNDEF_VAL -1


// Global constants
static char OB[2] = {(char)0x90, 0};
static char CB[2] = {(char)0x91, 0};
static int64_t UNDEF = -1;

static const char *Capital = "ABCDEFGHIJKLMNOPQRSTUVWXYZ";
static const char *Lower = "abcdefghijklmnopqrstuvwxyz";
static const char *Digit = "0123456789";
static const char *Xdigit = "0123456789ABCDEF";

static const char *Errors[] = {
    "Value out of range.",
    "Invalid syntax.",
    "Address out of range.",
    "",
    "",
    "Register out of range.",
    "Port number out of range.",
};

// Global variables
static char Outfile[256] = "";
static char Expfile[256] = "";
static char Impfile[256] = "";

static int64_t Pc = 0;
static int64_t Padding = 0;
static char Alphabet[512];
static char Lwordchars[512];
static char Swordchars[512];

static char CurrentSection[256] = ".text";
static char CurrentFile[256] = "";

// Sections
typedef struct {
    char name[256];
    int64_t start;
    int64_t size;
} SectionEntry;

static SectionEntry Sections[1000];
static int SectionCount = 0;

// Symbols
typedef struct {
    char name[256];
    int64_t value;
} SymbolEntry;

static SymbolEntry Symbols[MAX_SYMBOLS];
static int SymbolCount = 0;

static SymbolEntry Patsymbols[MAX_SYMBOLS];
static int PatsymbolCount = 0;

// Labels
typedef struct {
    char name[256];
    int64_t Value;
    int64_t Dummy;
    char Section[256];
} LabelEntry;

static LabelEntry Labels[MAX_LABELS];
static int LabelCount = 0;

// Export Labels
typedef struct {
    char name[256];
    int64_t Value;
    char Section[256];
} ExportLabelEntry;

static ExportLabelEntry ExportLabels[MAX_LABELS];
static int ExportLabelCount = 0;

// Patterns
typedef struct {
    char *fields[MAX_FIELDS];
    int field_count;
} PatternEntry;

static PatternEntry Pat[MAX_PAT];
static int PatCount = 0;

// VLIW
typedef struct {
    int64_t *Idxs;
    int IdxCount;
    char Expr[MAX_LINE];
} VliwEntry;

static int VliwInstBits = 41;
static int64_t *VliwNop = NULL;
static int VliwNopCount = 0;
static int VliwBits = 128;
static VliwEntry VliwSet[1000];
static int VliwSetCount = 0;
static bool VliwFlag = false;
static int64_t VliwTemplateBits = 0x00;
static int64_t VliwStop = 0;
static int64_t Vcnt = 1;

static int ExpMode = EXP_PAT;
static bool ErrorUndefinedLabel = false;
static bool ErrorAlreadyDefined = false;
static int64_t AlignVal = 16;
static int64_t Bts = 8;
static char Endian[20] = "little";
static char ByteFlag[10] = "yes";
static int Pas = 0;
static bool Debug = false;
static char Cl[MAX_LINE] = "";
static int Ln = 0;

static char FnStack[100][256];
static int FnStackCount = 0;
static int LnStack[100];
static int LnStackCount = 0;

static int64_t Vars[26];
static char Deb1[MAX_LINE] = "";
static char Deb2[MAX_LINE] = "";

// For qad{} 128-bit support
static __uint128_t LastQadValue = 0;
static bool LastQadValueValid = false;
static int64_t LastQadValueLow64 = 0;  // For matching

// Forward declarations
static void init_globals(void);
static char safe_char(const char *s, int idx);
static int skipspc(const char *s, int idx);
static void str_upper(char *dest, const char *src);
static bool q(const char *s, const char *t, int idx);
static int64_t nbit(int64_t l);
static int getParamToSpc(const char *s, int idx, char *result);
static int getParamToEon(const char *s, int idx, char *result);
static int getParams1(const char *s, int idx, char *result);
static int getIntStr(const char *s, int idx, char *result);
static int getFloatStr(const char *s, int idx, char *result);
static int getCurlb(const char *s, int idx, bool *found, char *result);
static int getSymbolWord(const char *s, int idx, char *result);
static int getLabelWord(const char *s, int idx, char *result);
static int64_t getSymVal(const char *t);
static bool getSymValWithOk(const char *w, int64_t *result);
static int64_t getVars(const char *s);
static void putVars(const char *s, int64_t v);
static int expression(const char *s, int idx, int64_t *result);
static int expression0(const char *s, int idx, int64_t *result);
static int expression1(const char *s, int idx, int64_t *result);
static int expressionEsc(const char *s, int idx, char stopchar, int64_t *result);
static int factor(const char *s, int idx, int64_t *result);
static int factor1(const char *s, int idx, int64_t *result);
static int term0_0(const char *s, int idx, int64_t *result);
static int term0(const char *s, int idx, int64_t *result);
static int term1(const char *s, int idx, int64_t *result);
static int term2(const char *s, int idx, int64_t *result);
static int term3(const char *s, int idx, int64_t *result);
static int term4(const char *s, int idx, int64_t *result);
static int term5(const char *s, int idx, int64_t *result);
static int term6(const char *s, int idx, int64_t *result);
static int term7(const char *s, int idx, int64_t *result);
static int term8(const char *s, int idx, int64_t *result);
static int term9(const char *s, int idx, int64_t *result);
static int term10(const char *s, int idx, int64_t *result);
static int term11(const char *s, int idx, int64_t *result);
static double pyEval(const char *expr);
static float enfloat(uint32_t a);
static double endouble(uint64_t a);
static void outbin(int64_t a, int64_t x);
static void outbin2(int64_t a, int64_t x);
static int fwrite_custom(const char *filePath, int64_t position, int64_t x, int prt);
static void setSymbol(const char **fields, int field_count);
static bool clearSymbol(const char **fields, int field_count);
static char *trim(char *str);
static char *reduceSpaces(char *s);
static char *removeComment(char *s);
static char *removeCommentAsm(char *s);
static char *labelProcessing(char *line);
static bool match(const char *s, const char *t);
static bool match0(const char *s, const char *t);
static bool generate_combinations(const char *s, const char *t2, int cnt, const int *sl, int start, int k, int *cur, int cur_count);
static void removeBrackets(const char *s, const int *remove, int remove_count, char *result);
static int makeobj(const char *s, int64_t *objl);
static void expandColonLabels(const char *input, char *output);
static bool lineassemble2(const char *line, int idx, int64_t *idxs_out, int64_t *objl, int *objl_count, int *idx_out);
static bool lineassemble(const char *line);
static bool lineassemble0(const char *line);
static void fileassemble(const char *fn);
static void readpat(const char *filename);
static void setpatsymbols(void);
static bool impLabel(const char *l);
static bool vliwp(const char **fields, int field_count);
static bool epic(const char **fields, int field_count);
static bool vliwprocess(const char *line, int64_t idxs, int64_t *objl, int objl_count, bool flag, int idx);
static bool putLabelValue(const char *k, int64_t v, const char *s);
static int64_t getLabelValue(const char *k);
static char *getLabelSectionName(const char *k);
static int64_t align_(int64_t addr);

// Helper functions
static void init_globals(void) {
    snprintf(Alphabet, sizeof(Alphabet), "%s%s", Lower, Capital);
    snprintf(Lwordchars, sizeof(Lwordchars), "%s%s_.", Digit, Alphabet);
    snprintf(Swordchars, sizeof(Swordchars), "%s%s_%%$-~&|", Digit, Alphabet);
    memset(Vars, 0, sizeof(Vars));
}

static void str_upper(char *dest, const char *src) {
    int i = 0;
    while (src[i]) {
        dest[i] = toupper((unsigned char)src[i]);
        i++;
    }
    dest[i] = '\0';
}

static char safe_char(const char *s, int idx) {
    if (idx < 0 || idx >= (int)strlen(s)) {
        return 0;
    }
    return s[idx];
}

static int skipspc(const char *s, int idx) {
    while (idx < (int)strlen(s) && s[idx] == ' ') {
        idx++;
    }
    return idx;
}

static bool q(const char *s, const char *t, int idx) {
    int tlen = strlen(t);
    if (idx + tlen > (int)strlen(s)) return false;
    
    for (int i = 0; i < tlen; i++) {
        if (toupper((unsigned char)s[idx + i]) != toupper((unsigned char)t[i])) {
            return false;
        }
    }
    return true;
}

static int64_t nbit(int64_t l) {
    int64_t b = 0;
    int64_t r = l;
    while (r != 0) {
        r >>= 1;
        b++;
    }
    return b;
}

static int getParamToSpc(const char *s, int idx, char *result) {
    idx = skipspc(s, idx);
    int start = idx;
    while (idx < (int)strlen(s) && s[idx] != ' ') {
        idx++;
    }
    int len = idx - start;
    strncpy(result, s + start, len);
    result[len] = '\0';
    return idx;
}

static int getParamToEon(const char *s, int idx, char *result) {
    idx = skipspc(s, idx);
    int start = idx;
    while (idx < (int)strlen(s) && !(idx + 2 <= (int)strlen(s) && s[idx] == '!' && s[idx+1] == '!')) {
        idx++;
    }
    int len = idx - start;
    strncpy(result, s + start, len);
    result[len] = '\0';
    return idx;
}

static int getParams1(const char *s, int idx, char *result) {
    idx = skipspc(s, idx);
    if (idx >= (int)strlen(s)) {
        result[0] = '\0';
        return idx;
    }
    
    int start = idx;
    while (idx < (int)strlen(s)) {
        if (idx + 2 <= (int)strlen(s) && s[idx] == ':' && s[idx+1] == ':') {
            idx += 2;
            break;
        }
        idx++;
    }
    
    int len = idx - start;
    if (len > 2 && s[idx-2] == ':' && s[idx-1] == ':') {
        len -= 2;
    }
    
    if (len > 0) {
        strncpy(result, s + start, len);
        result[len] = '\0';
        // Trim right spaces
        int i = len - 1;
        while (i >= 0 && result[i] == ' ') {
            result[i] = '\0';
            i--;
        }
    } else {
        result[0] = '\0';
    }
    
    return idx;
}

static int getIntStr(const char *s, int idx, char *result) {
    int start = idx;
    while (idx < (int)strlen(s) && s[idx] >= '0' && s[idx] <= '9') {
        idx++;
    }
    int len = idx - start;
    strncpy(result, s + start, len);
    result[len] = '\0';
    return idx;
}

static int getFloatStr(const char *s, int idx, char *result) {
    if (idx + 3 <= (int)strlen(s) && strncmp(s + idx, "inf", 3) == 0) {
        strcpy(result, "inf");
        return idx + 3;
    }
    if (idx + 4 <= (int)strlen(s) && strncmp(s + idx, "-inf", 4) == 0) {
        strcpy(result, "-inf");
        return idx + 4;
    }
    if (idx + 3 <= (int)strlen(s) && strncmp(s + idx, "nan", 3) == 0) {
        strcpy(result, "nan");
        return idx + 3;
    }
    
    int start = idx;
    while (idx < (int)strlen(s)) {
        char ch = s[idx];
        if ((ch >= '0' && ch <= '9') || ch == '-' || ch == '.' || ch == 'e' || ch == 'E') {
            idx++;
        } else {
            break;
        }
    }
    int len = idx - start;
    strncpy(result, s + start, len);
    result[len] = '\0';
    return idx;
}

static int getCurlb(const char *s, int idx, bool *found, char *result) {
    idx = skipspc(s, idx);
    if (safe_char(s, idx) != '{') {
        *found = false;
        result[0] = '\0';
        return idx;
    }
    idx++;
    idx = skipspc(s, idx);
    int start = idx;
    while (safe_char(s, idx) != '}' && safe_char(s, idx) != 0) {
        idx++;
    }
    int len = idx - start;
    strncpy(result, s + start, len);
    result[len] = '\0';
    if (safe_char(s, idx) == '}') {
        idx++;
    }
    *found = true;
    return idx;
}

static int getSymbolWord(const char *s, int idx, char *result) {
    int start = idx;
    if (idx < (int)strlen(s) && !strchr(Digit, s[idx]) && strchr(Swordchars, s[idx])) {
        idx++;
        while (idx < (int)strlen(s) && strchr(Swordchars, s[idx])) {
            idx++;
        }
    }
    int len = idx - start;
    strncpy(result, s + start, len);
    result[len] = '\0';
    str_upper(result, result);
    return idx;
}

static int getLabelWord(const char *s, int idx, char *result) {
    int start = idx;
    if (idx < (int)strlen(s) && (s[idx] == '.' || (!strchr(Digit, s[idx]) && strchr(Lwordchars, s[idx])))) {
        idx++;
        while (idx < (int)strlen(s) && strchr(Lwordchars, s[idx])) {
            idx++;
        }
        if (idx < (int)strlen(s) && s[idx] == ':') {
            idx++;
        }
    }
    int len = idx - start;
    if (len > 0 && s[start + len - 1] == ':') len--;
    strncpy(result, s + start, len);
    result[len] = '\0';
    return idx;
}

static int64_t getSymVal(const char *t) {
    char upper_t[256];
    str_upper(upper_t, t);
    
    for (int i = 0; i < SymbolCount; i++) {
        if (strcmp(Symbols[i].name, upper_t) == 0) {
            return Symbols[i].value;
        }
    }
    return 0;
}

static bool getSymValWithOk(const char *w, int64_t *result) {
    char upper_w[256];
    str_upper(upper_w, w);
    
    for (int i = 0; i < SymbolCount; i++) {
        if (strcmp(Symbols[i].name, upper_w) == 0) {
            *result = Symbols[i].value;
            return true;
        }
    }
    return false;
}

static int64_t getVars(const char *s) {
    char c[256];
    str_upper(c, s);
    if (strlen(c) == 0) return 0;
    int idx = c[0] - 'A';
    if (idx < 0 || idx >= 26) return 0;
    return Vars[idx];
}

static void putVars(const char *s, int64_t v) {
    char k[256];
    str_upper(k, s);
    if (strlen(k) == 1 && k[0] >= 'A' && k[0] <= 'Z') {
        Vars[k[0] - 'A'] = v;
    }
}

static double pyEval(const char *expr) {
    // Replace :label with label values
    char expanded[MAX_LINE * 2];
    int j = 0;
    for (int i = 0; i < (int)strlen(expr) && j < MAX_LINE * 2 - 50; i++) {
        if (expr[i] == ':' && i + 1 < (int)strlen(expr) && 
            (isalpha(expr[i+1]) || expr[i+1] == '.' || expr[i+1] == '_')) {
            // Extract label name
            char label[256];
            int k = 0;
            i++; // Skip ':'
            while (i < (int)strlen(expr) && 
                   (isalnum(expr[i]) || expr[i] == '_' || expr[i] == '.') && 
                   k < 255) {
                label[k++] = expr[i++];
            }
            label[k] = '\0';
            i--; // Back one position for loop increment
            
            // Get label value
            int64_t val = getLabelValue(label);
            j += snprintf(expanded + j, MAX_LINE * 2 - j, "%lld", (long long)val);
        } else {
            expanded[j++] = expr[i];
        }
    }
    expanded[j] = '\0';
    
    // Create Python command with enfloat and endouble support
    // Use a multi-line Python script
    char cmd[MAX_LINE * 3];
    snprintf(cmd, sizeof(cmd), 
        "python3 << 'PYEOF' 2>/dev/null\n"
        "import struct\n"
        "def enfloat(a): return struct.unpack('f', struct.pack('I', int(a)))[0]\n"
        "def endouble(a): return struct.unpack('d', struct.pack('Q', int(a)))[0]\n"
        "print(repr(eval('%s')))\n"
        "PYEOF\n",
        expanded);
    
    FILE *fp = popen(cmd, "r");
    if (fp) {
        char buf[256];
        if (fgets(buf, sizeof(buf), fp)) {
            pclose(fp);
            double result = atof(buf);
            return result;
        }
        pclose(fp);
    }
    
    // If Python evaluation fails, try to evaluate the expanded expression directly
    // This handles simple numeric expressions
    double result = atof(expanded);
    if (result == 0.0 && expanded[0] != '0') {
        // atof failed, return 0 to avoid NaN
        return 0.0;
    }
    return result;
}

// Convert uint32_t to float (IEEE 754 interpretation)
static float enfloat(uint32_t a) {
    union {
        uint32_t i;
        float f;
    } converter;
    converter.i = a;
    return converter.f;
}

// Convert uint64_t to double (IEEE 754 interpretation)
static double endouble(uint64_t a) {
    union {
        uint64_t i;
        double d;
    } converter;
    converter.i = a;
    return converter.d;
}

static int64_t getLabelValue(const char *k) {
    for (int i = 0; i < LabelCount; i++) {
        if (strcmp(Labels[i].name, k) == 0) {
            return Labels[i].Value;
        }
    }
    ErrorUndefinedLabel = true;
    return UNDEF;
}

static char *getLabelSectionName(const char *k) {
    static char result[256];
    for (int i = 0; i < LabelCount; i++) {
        if (strcmp(Labels[i].name, k) == 0) {
            strcpy(result, Labels[i].Section);
            return result;
        }
    }
    ErrorUndefinedLabel = true;
    result[0] = '\0';
    return result;
}

// Expression evaluation - complete implementation
static int expressionEsc(const char *s, int idx, char stopchar, int64_t *result) {
    // ExpMode should not be changed here - use caller's mode
    char replaced[MAX_LINE];
    int depth = 0;
    int j = 0;
    
    // Process from idx onwards
    for (int i = idx; i < (int)strlen(s) && j < MAX_LINE - 1; i++) {
        char ch = s[i];
        if (ch == '(') {
            depth++;
            replaced[j++] = ch;
        } else if (ch == ')') {
            if (depth > 0) depth--;
            replaced[j++] = ch;
        } else {
            if (depth == 0 && ch == stopchar) {
                break; // Stop at stopchar
            } else {
                replaced[j++] = ch;
            }
        }
    }
    replaced[j] = '\0';
    
    // Now evaluate from index 0 of replaced string
    int64_t val;
    int end_idx = expression(replaced, 0, &val);
    *result = val;
    
    // Return the new index in the original string
    return idx + end_idx;
}

static int factor1(const char *s, int idx, int64_t *result) {
    int64_t x = 0;
    idx = skipspc(s, idx);
    char c = safe_char(s, idx);
    

    // Character literals (Go patch)
    if (idx + 4 <= (int)strlen(s) && strncmp(s + idx, "'\n'", 4) == 0) {
        idx += 4;
        x = 0x0a;
    } else if (idx + 4 <= (int)strlen(s) && strncmp(s + idx, "'\t'", 4) == 0) {
        idx += 4;
        x = 0x09;
    } else if (idx + 3 <= (int)strlen(s) && strncmp(s + idx, "'\\'", 3) == 0) {
        idx += 3;
        x = (int64_t)'\\';
    } else if (idx + 4 <= (int)strlen(s) && strncmp(s + idx, "'\\''", 4) == 0) {
        idx += 4;
        x = (int64_t)'\'';
    } else if (idx + 3 <= (int)strlen(s) && s[idx] == '\'' && s[idx + 2] == '\'') {
        x = (int64_t)s[idx + 1];
        idx += 3;
    }
    
    if (c == '(') {
        idx = expression(s, idx + 1, &x);
        if (safe_char(s, idx) == ')') {
            idx++;
        }
    } else if (q(s, "$$", idx)) {
        idx += 2;
        x = Pc;
    } else if (q(s, "#", idx)) {
        idx++;
        char t[256];
        idx = getSymbolWord(s, idx, t);
        x = getSymVal(t);
    } else if (q(s, "0b", idx)) {
        idx += 2;
        while (idx < (int)strlen(s) && (s[idx] == '0' || s[idx] == '1')) {
            x = (x << 1) | (s[idx] - '0');
            idx++;
        }
    } else if (q(s, "0x", idx)) {
        idx += 2;
        while (idx < (int)strlen(s)) {
            char ch = toupper((unsigned char)s[idx]);
            if (strchr(Xdigit, ch)) {
                int val = (ch >= 'A') ? (ch - 'A' + 10) : (ch - '0');
                x = (x << 4) | val;
                idx++;
            } else {
                break;
            }
        }
    } else if (q(s, "0o", idx)) {
        idx += 2;
        while (idx < (int)strlen(s) && s[idx] >= '0' && s[idx] <= '7') {
            x = (x << 3) | (s[idx] - '0');
            idx++;
        }
    } else if (idx + 3 <= (int)strlen(s) && strncmp(s + idx, "qad", 3) == 0) {
        idx += 3;
        idx = skipspc(s, idx);
        if (safe_char(s, idx) == '{') {
            char floatstr[256];
            idx = getFloatStr(s, idx + 1, floatstr);
            
            // Use Python to compute IEEE 754 128-bit hex
            char cmd[MAX_LINE];
            snprintf(cmd, sizeof(cmd), 
                "python3 -c \"from decimal import Decimal, getcontext; "
                "getcontext().prec=34; "
                "a='%s'; "
                "BIAS=16383; SB=112; EB=15; "
                "d=Decimal(a if a not in ['inf','-inf','nan'] else ('Infinity' if a=='inf' else '-Infinity' if a=='-inf' else 'NaN')); "
                "sign=0 if (not d.is_nan() and d>=0) else (1 if not d.is_nan() else 0); "
                "d_abs=abs(d) if (not d.is_nan() and not d.is_infinite()) else d; "
                "exp=((1<<EB)-1 if (d.is_nan() or d.is_infinite()) else (0 if d==0 else int(d_abs.adjusted()+BIAS))); "
                "frac=((1<<(SB-1)) if d.is_nan() else 0) if (d.is_nan() or d.is_infinite() or d==0) else (int((d_abs/(Decimal(2)**d_abs.adjusted())-1)*(2**SB))&((1<<SB)-1)); "
                "bits=(sign<<127)|(exp<<SB)|frac; "
                "print('%%016x %%016x' %% (bits >> 64, bits & 0xffffffffffffffff))\" 2>/dev/null",
                floatstr);
            
            FILE *fp = popen(cmd, "r");
            if (fp) {
                char buf[256];
                if (fgets(buf, sizeof(buf), fp)) {
                    unsigned long long high, low;
                    if (sscanf(buf, "%llx %llx", &high, &low) == 2) {
                        LastQadValue = ((__uint128_t)high << 64) | (__uint128_t)low;
                        LastQadValueValid = true;
                        LastQadValueLow64 = (int64_t)low;
                        x = (int64_t)low;  // Store low 64 bits
                    }
                }
                pclose(fp);
            }
            
            if (safe_char(s, idx) == '}') {
                idx++;
            }
        }
    } else if (idx + 3 <= (int)strlen(s) && strncmp(s + idx, "dbl", 3) == 0) {
        idx += 3;
        bool found;
        char t[256];
        idx = getCurlb(s, idx, &found, t);
        if (found) {
            if (strcmp(t, "nan") == 0) {
                x = 0x7ff8000000000000LL;
            } else if (strcmp(t, "inf") == 0) {
                x = 0x7ff0000000000000LL;
            } else if (strcmp(t, "-inf") == 0) {
                x = (int64_t)0xfff0000000000000ULL;
            } else {
                double v = pyEval(t);
                union { double d; uint64_t u; } conv;
                conv.d = v;
                x = (int64_t)conv.u;
            }
        }
    } else if (idx + 3 <= (int)strlen(s) && strncmp(s + idx, "flt", 3) == 0) {
        idx += 3;
        bool found;
        char t[256];
        idx = getCurlb(s, idx, &found, t);
        if (found) {
            if (strcmp(t, "nan") == 0) {
                x = 0x7fc00000;
            } else if (strcmp(t, "inf") == 0) {
                x = 0x7f800000;
            } else if (strcmp(t, "-inf") == 0) {
                x = 0xff800000;
            } else {
                float v = (float)pyEval(t);
                union { float f; uint32_t u; } conv;
                conv.f = v;
                x = (int64_t)conv.u;
            }
        }
    } else if (c >= '0' && c <= '9') {
        char intstr[256];
        idx = getIntStr(s, idx, intstr);
        x = strtoll(intstr, NULL, 10);
    } else if (c == ':' && idx + 1 < (int)strlen(s) && 
               (isalpha(s[idx+1]) || s[idx+1] == '.' || s[idx+1] == '_')) {
        // :label syntax - get label value
        idx++; // Skip ':'
        char w[256];
        int old_idx = idx;
        idx = getLabelWord(s, idx, w);
        if (idx != old_idx) {
            x = getLabelValue(w);
        } else {
            x = 0;
        }
    } else if (ExpMode == EXP_PAT && strchr(Lower, c) && !(idx + 1 < (int)strlen(s) && strchr(Lower, s[idx + 1]))) {
        char ch[2] = {c, 0};
        if (idx + 3 <= (int)strlen(s) && s[idx + 1] == ':' && s[idx + 2] == '=') {
            idx = expression(s, idx + 3, &x);
            putVars(ch, x);
        } else {
            x = getVars(ch);
            idx++;
        }
    } else if (strchr(Lwordchars, c) || c == '.') {
        char w[256];
        int old_idx = idx;
        idx = getLabelWord(s, idx, w);
        if (idx != old_idx) {
            x = getLabelValue(w);
        } else {
            x = 0;
        }
    } else {
        x = 0;
    }
    
    idx = skipspc(s, idx);
    *result = x;
    return idx;
}

static int factor(const char *s, int idx, int64_t *result) {
    idx = skipspc(s, idx);
    int64_t x = 0;
    
    if (idx + 4 <= (int)strlen(s) && strncmp(s + idx, "!!!!", 4) == 0 && ExpMode == EXP_PAT) {
        x = VliwStop;
        idx += 4;
    } else if (idx + 3 <= (int)strlen(s) && strncmp(s + idx, "!!!", 3) == 0 && ExpMode == EXP_PAT) {
        x = Vcnt;
        idx += 3;
    } else if (safe_char(s, idx) == '-') {
        int64_t temp;
        idx = factor(s, idx + 1, &temp);
        x = -temp;
    } else if (safe_char(s, idx) == '~') {
        int64_t temp;
        idx = factor(s, idx + 1, &temp);
        x = ~temp;
    } else if (safe_char(s, idx) == '@') {
        int64_t temp;
        idx = factor(s, idx + 1, &temp);
        x = nbit(temp);
    } else if (safe_char(s, idx) == '*') {
        idx++;
        if (safe_char(s, idx) == '(') {
            int64_t x1;
            idx = expression(s, idx + 1, &x1);
            if (safe_char(s, idx) == ',') {
                int64_t x2;
                idx = expression(s, idx + 1, &x2);
                if (safe_char(s, idx) == ')') {
                    idx++;
                    x = x1 >> (x2 * 8);
                }
            } else {
                x = 0;
            }
        } else {
            x = 0;
        }
    } else {
        idx = factor1(s, idx, &x);
    }
    
    idx = skipspc(s, idx);
    *result = x;
    return idx;
}

static int term0_0(const char *s, int idx, int64_t *result) {
    int64_t x;
    idx = factor(s, idx, &x);
    
    while (q(s, "**", idx)) {
        int64_t t;
        idx = factor(s, idx + 2, &t);
        x = (int64_t)pow((double)x, (double)t);
    }
    
    *result = x;
    return idx;
}

static int term0(const char *s, int idx, int64_t *result) {
    int64_t x;
    idx = term0_0(s, idx, &x);
    
    while (true) {
        if (safe_char(s, idx) == '*') {
            int64_t t;
            idx = term0_0(s, idx + 1, &t);
            x *= t;
        } else if (q(s, "//", idx)) {
            int64_t t;
            idx = term0_0(s, idx + 2, &t);
            if (t == 0) {
                fprintf(stderr, "Division by 0 error.\n");
            } else {
                x = x / t;
            }
        } else if (safe_char(s, idx) == '%') {
            int64_t t;
            idx = term0_0(s, idx + 1, &t);
            if (t == 0) {
                fprintf(stderr, "Division by 0 error.\n");
            } else {
                x = x % t;
            }
        } else {
            break;
        }
    }
    
    *result = x;
    return idx;
}

static int term1(const char *s, int idx, int64_t *result) {
    int64_t x;
    idx = term0(s, idx, &x);
    
    while (true) {
        if (safe_char(s, idx) == '+') {
            int64_t t;
            idx = term0(s, idx + 1, &t);
            x += t;
        } else if (safe_char(s, idx) == '-') {
            int64_t t;
            idx = term0(s, idx + 1, &t);
            x -= t;
        } else {
            break;
        }
    }
    
    *result = x;
    return idx;
}

static int term2(const char *s, int idx, int64_t *result) {
    int64_t x;
    idx = term1(s, idx, &x);
    
    while (true) {
        if (q(s, "<<", idx)) {
            int64_t t;
            idx = term1(s, idx + 2, &t);
            x <<= t;
        } else if (q(s, ">>", idx)) {
            int64_t t;
            idx = term1(s, idx + 2, &t);
            x >>= t;
        } else {
            break;
        }
    }
    
    *result = x;
    return idx;
}

static int term3(const char *s, int idx, int64_t *result) {
    int64_t x;
    idx = term2(s, idx, &x);
    
    while (safe_char(s, idx) == '&' && safe_char(s, idx + 1) != '&') {
        int64_t t;
        idx = term2(s, idx + 1, &t);
        x = x & t;
    }
    
    *result = x;
    return idx;
}

static int term4(const char *s, int idx, int64_t *result) {
    int64_t x;
    idx = term3(s, idx, &x);
    
    while (safe_char(s, idx) == '|' && safe_char(s, idx + 1) != '|') {
        int64_t t;
        idx = term3(s, idx + 1, &t);
        x = x | t;
    }
    
    *result = x;
    return idx;
}

static int term5(const char *s, int idx, int64_t *result) {
    int64_t x;
    idx = term4(s, idx, &x);
    
    while (safe_char(s, idx) == '^') {
        int64_t t;
        idx = term4(s, idx + 1, &t);
        x = x ^ t;
    }
    
    *result = x;
    return idx;
}

static int term6(const char *s, int idx, int64_t *result) {
    int64_t x;
    idx = term5(s, idx, &x);
    
    while (safe_char(s, idx) == '\'') {
        int64_t t;
        idx = term5(s, idx + 1, &t);
        if (t > 0) {
            uint64_t u = ~(uint64_t)0;
            int64_t mask = (int64_t)u;
            x = (x & ~(mask << t)) | ((mask << t) * (((x >> (t - 1)) & 1)));
        }
    }
    
    *result = x;
    return idx;
}

static int term7(const char *s, int idx, int64_t *result) {
    int64_t x;
    idx = term6(s, idx, &x);
    
    while (true) {
        if (q(s, "<=", idx)) {
            int64_t t;
            idx = term6(s, idx + 2, &t);
            x = (x <= t) ? 1 : 0;
        } else if (safe_char(s, idx) == '<') {
            int64_t t;
            idx = term6(s, idx + 1, &t);
            x = (x < t) ? 1 : 0;
        } else if (q(s, ">=", idx)) {
            int64_t t;
            idx = term6(s, idx + 2, &t);
            x = (x >= t) ? 1 : 0;
        } else if (safe_char(s, idx) == '>') {
            int64_t t;
            idx = term6(s, idx + 1, &t);
            x = (x > t) ? 1 : 0;
        } else if (q(s, "==", idx)) {
            int64_t t;
            idx = term6(s, idx + 2, &t);
            x = (x == t) ? 1 : 0;
        } else if (q(s, "!=", idx)) {
            int64_t t;
            idx = term6(s, idx + 2, &t);
            x = (x != t) ? 1 : 0;
        } else {
            break;
        }
    }
    
    *result = x;
    return idx;
}

static int term8(const char *s, int idx, int64_t *result) {
    if (idx + 4 <= (int)strlen(s) && strncmp(s + idx, "not(", 4) == 0) {
        int64_t x;
        idx = expression(s, idx + 3, &x);
        x = (x == 0) ? 1 : 0;
        *result = x;
        return idx;
    }
    return term7(s, idx, result);
}

static int term9(const char *s, int idx, int64_t *result) {
    int64_t x;
    idx = term8(s, idx, &x);
    
    while (q(s, "&&", idx)) {
        int64_t t;
        idx = term8(s, idx + 2, &t);
        x = (x != 0 && t != 0) ? 1 : 0;
    }
    
    *result = x;
    return idx;
}

static int term10(const char *s, int idx, int64_t *result) {
    int64_t x;
    idx = term9(s, idx, &x);
    
    while (q(s, "||", idx)) {
        int64_t t;
        idx = term9(s, idx + 2, &t);
        x = (x != 0 || t != 0) ? 1 : 0;
    }
    
    *result = x;
    return idx;
}

static int term11(const char *s, int idx, int64_t *result) {
    int64_t x;
    idx = term10(s, idx, &x);
    
    while (safe_char(s, idx) == '?') {
        int64_t t;
        idx = term10(s, idx + 1, &t);
        if (safe_char(s, idx) == ':') {
            int64_t u;
            idx = term10(s, idx + 1, &u);
            x = (x == 0) ? u : t;
        }
    }
    
    *result = x;
    return idx;
}

static int expression(const char *s, int idx, int64_t *result) {
    char s2[MAX_LINE];
    snprintf(s2, sizeof(s2), "%s", s);
    idx = skipspc(s2, idx);
    return term11(s2, idx, result);
}

static int expression0(const char *s, int idx, int64_t *result) {
    ExpMode = EXP_PAT;
    return expression(s, idx, result);
}

static int expression1(const char *s, int idx, int64_t *result) {
    ExpMode = EXP_ASM;
    return expression(s, idx, result);
}

// File I/O
static int fwrite_custom(const char *filePath, int64_t position, int64_t x, int prt) {
    int64_t b = Bts;
    if (b <= 8) b = 8;
    int byts = (int)((b + 7) / 8);
    int cnt = 0;
    
    FILE *f = NULL;
    if (filePath && filePath[0]) {
        f = fopen(filePath, "r+b");
        if (!f) f = fopen(filePath, "wb");
        if (f) {
            fseek(f, position * byts, SEEK_SET);
        }
    }
    
    if (strcmp(Endian, "little") == 0) {
        int64_t mask = ((int64_t)1 << Bts) - 1;
        int64_t v = x & mask;
        for (int i = 0; i < byts; i++) {
            unsigned char vv = (unsigned char)(v & 0xff);
            if (f) fwrite(&vv, 1, 1, f);
            if (prt == 1) {
                printf(" 0x%02x", vv);
            }
            v >>= 8;
            cnt++;
        }
    } else {
        int64_t mask = ((int64_t)1 << Bts) - 1;
        int64_t xMasked = x & mask;
        for (int i = byts - 1; i >= 0; i--) {
            unsigned char v = (unsigned char)((xMasked >> (i * 8)) & 0xff);
            if (f) fwrite(&v, 1, 1, f);
            if (prt == 1) {
                printf(" 0x%02x", v);
            }
            cnt++;
        }
    }
    
    if (f) fclose(f);
    return cnt;
}

static void outbin2(int64_t a, int64_t x) {
    if (Pas == 2 || Pas == 0) {
        fwrite_custom(Outfile, a, x, 0);
    }
}

static void outbin(int64_t a, int64_t x) {
    if (Pas == 2 || Pas == 0) {
        fwrite_custom(Outfile, a, x, 1);
    }
}

// Symbol/Label management
static void setSymbol(const char **fields, int field_count) {
    if (field_count < 3) return;
    if (strcmp(fields[0], ".setsym") != 0) return;
    
    char upper_name[256];
    str_upper(upper_name, fields[1]);
    
    int64_t val;
    expression0(fields[2], 0, &val);
    
    for (int i = 0; i < SymbolCount; i++) {
        if (strcmp(Symbols[i].name, upper_name) == 0) {
            Symbols[i].value = val;
            return;
        }
    }
    
    if (SymbolCount < MAX_SYMBOLS) {
        strcpy(Symbols[SymbolCount].name, upper_name);
        Symbols[SymbolCount].value = val;
        SymbolCount++;
    }
}

static bool clearSymbol(const char **fields, int field_count) {
    if (field_count == 0 || strcmp(fields[0], ".clearsym") != 0) {
        return false;
    }
    
    if (field_count >= 3) {
        char key[256];
        str_upper(key, fields[2]);
        for (int i = 0; i < SymbolCount; i++) {
            if (strcmp(Symbols[i].name, key) == 0) {
                for (int j = i; j < SymbolCount - 1; j++) {
                    Symbols[j] = Symbols[j + 1];
                }
                SymbolCount--;
                return true;
            }
        }
    }
    
    if (field_count == 1) {
        SymbolCount = 0;
        for (int i = 0; i < PatsymbolCount && i < MAX_SYMBOLS; i++) {
            Symbols[i] = Patsymbols[i];
        }
        SymbolCount = PatsymbolCount;
    }
    
    return true;
}

static bool putLabelValue(const char *k, int64_t v, const char *s) {
    if (Pas == 1 || Pas == 0) {
        for (int i = 0; i < LabelCount; i++) {
            if (strcmp(Labels[i].name, k) == 0) {
                ErrorAlreadyDefined = true;
                printf(" error - label already defined.\n");
                return false;
            }
        }
    }
    
    for (int i = 0; i < PatsymbolCount; i++) {
        if (strcmp(Patsymbols[i].name, k) == 0) {
            printf(" error - '%s' is a pattern file symbol.\n", k);
            return false;
        }
    }
    
    ErrorAlreadyDefined = false;
    
    for (int i = 0; i < LabelCount; i++) {
        if (strcmp(Labels[i].name, k) == 0) {
            Labels[i].Value = v;
            strcpy(Labels[i].Section, s);
            return true;
        }
    }
    
    if (LabelCount < MAX_LABELS) {
        strcpy(Labels[LabelCount].name, k);
        Labels[LabelCount].Value = v;
        Labels[LabelCount].Dummy = 0;
        strcpy(Labels[LabelCount].Section, s);
        LabelCount++;
    }
    
    return true;
}

// String processing
static char *trim(char *str) {
    while (isspace((unsigned char)*str)) str++;
    if (*str == 0) return str;
    char *end = str + strlen(str) - 1;
    while (end > str && isspace((unsigned char)*end)) end--;
    end[1] = '\0';
    return str;
}

static char *reduceSpaces(char *s) {
    static char result[MAX_LINE];
    int j = 0;
    bool lastWasSpace = false;
    
    for (int i = 0; s[i] && j < MAX_LINE - 1; i++) {
        if (s[i] == ' ') {
            if (!lastWasSpace) {
                result[j++] = ' ';
                lastWasSpace = true;
            }
        } else {
            result[j++] = s[i];
            lastWasSpace = false;
        }
    }
    result[j] = '\0';
    
    strcpy(s, result);
    return trim(s);
}

static char *removeComment(char *s) {
    static char result[MAX_LINE];
    strcpy(result, s);
    
    // Look for /* comment
    char *comment = strstr(result, "/*");
    if (comment) {
        if (comment == result) {
            result[0] = '\0';
        } else {
            *comment = '\0';
        }
    }
    
    strcpy(s, result);
    return trim(s);
}

static char *removeCommentAsm(char *s) {
    static char result[MAX_LINE];
    strcpy(result, s);
    
    // Look for ; comment
    char *sem = strchr(result, ';');
    if (sem) *sem = '\0';
    
    strcpy(s, result);
    return trim(s);
}

static char *labelProcessing(char *line) {
    static char result[MAX_LINE];
    
    // Find the first ':' that is NOT inside curly braces
    char *colon = NULL;
    int brace_depth = 0;
    for (int i = 0; line[i]; i++) {
        if (line[i] == '{') {
            brace_depth++;
        } else if (line[i] == '}') {
            brace_depth--;
        } else if (line[i] == ':' && brace_depth == 0) {
            colon = &line[i];
            break;
        }
    }
    
    if (!colon) {
        strcpy(result, line);
        return result;
    }
    
    int colonPos = colon - line;
    char label[256];
    strncpy(label, line, colonPos);
    label[colonPos] = '\0';
    strcpy(label, trim(label));
    
    if (label[0]) {
        int idx = skipspc(line, colonPos + 1);
        char e[256];
        getParamToSpc(line, idx, e);
        
        char upper_e[256];
        str_upper(upper_e, e);
        
        if (strcmp(upper_e, ".EQU") == 0) {
            idx = skipspc(line, idx + strlen(e));
            int64_t u;
            expression1(line, idx, &u);
            putLabelValue(label, u, CurrentSection);
            result[0] = '\0';
            return result;
        }
        
        putLabelValue(label, Pc, CurrentSection);
    }
    
    strcpy(result, colon + 1);
    return result;
}

// Pattern matching
static void removeBrackets(const char *s, const int *remove, int remove_count, char *result) {
    typedef struct {
        int depth;
        int pos;
        bool open;
    } Bracket;
    
    Bracket bs[1000];
    int bs_count = 0;
    int depth = 0;
    
    for (int i = 0; i < (int)strlen(s) && bs_count < 1000; i++) {
        if (s[i] == OB[0]) {
            depth++;
            bs[bs_count].depth = depth;
            bs[bs_count].pos = i;
            bs[bs_count].open = true;
            bs_count++;
        } else if (s[i] == CB[0]) {
            bs[bs_count].depth = depth;
            bs[bs_count].pos = i;
            bs[bs_count].open = false;
            bs_count++;
            depth--;
        }
    }
    
    bool removeSet[100] = {false};
    for (int i = 0; i < remove_count; i++) {
        if (remove[i] < 100) {
            removeSet[remove[i]] = true;
        }
    }
    
    bool toDelete[MAX_LINE] = {false};
    int start = -1;
    
    for (int i = 0; i < bs_count; i++) {
        if (bs[i].open && removeSet[bs[i].depth]) {
            start = bs[i].pos;
        }
        if (!bs[i].open && removeSet[bs[i].depth] && start >= 0) {
            for (int j = start; j <= bs[i].pos; j++) {
                toDelete[j] = true;
            }
            start = -1;
        }
    }
    
    int j = 0;
    for (int i = 0; i < (int)strlen(s) && j < MAX_LINE - 1; i++) {
        if (!toDelete[i]) {
            result[j++] = s[i];
        }
    }
    result[j] = '\0';
}

static bool match(const char *s, const char *t) {
    char t2[MAX_LINE];
    strcpy(t2, t);
    
    // Replace [[ with OB and ]] with CB
    char *p;
    while ((p = strstr(t2, "[[")) != NULL) {
        *p = OB[0];
        memmove(p + 1, p + 2, strlen(p + 2) + 1);
    }
    while ((p = strstr(t2, "]]")) != NULL) {
        *p = CB[0];
        memmove(p + 1, p + 2, strlen(p + 2) + 1);
    }
    
    // Remove all OB and CB for actual matching
    char t3[MAX_LINE];
    int j = 0;
    for (int i = 0; t2[i] && j < MAX_LINE - 1; i++) {
        if (t2[i] != OB[0] && t2[i] != CB[0]) {
            t3[j++] = t2[i];
        }
    }
    t3[j] = '\0';
    
    int idxS = skipspc(s, 0);
    int idxT = skipspc(t3, 0);
    
    char s2[MAX_LINE];
    snprintf(s2, sizeof(s2), "%s", s);
    
    strcpy(Deb1, s2);
    strcpy(Deb2, t3);
    
    while (true) {
        idxS = skipspc(s2, idxS);
        idxT = skipspc(t3, idxT);
        char b = safe_char(s2, idxS);
        char a = safe_char(t3, idxT);
        
        if (a == 0 && b == 0) {
            return true;
        }
        
        if (a == '\\') {
            idxT++;
            if (safe_char(t3, idxT) == b) {
                idxT++;
                idxS++;
                continue;
            }
            return false;
        } else if (a >= 'A' && a <= 'Z') {
            if (a == toupper((unsigned char)b)) {
                idxS++;
                idxT++;
                continue;
            }
            return false;
        } else if (a == '!') {
            idxT++;
            a = safe_char(t3, idxT);
            idxT++;
            
            if (a == '!') {
                a = safe_char(t3, idxT);
                idxT++;
                int64_t v;
                idxS = factor(s2, idxS, &v);
                char var[2] = {a, 0};
                putVars(var, v);
                continue;
            }
            
            idxT = skipspc(t3, idxT);
            char stopchar;
            if (safe_char(t3, idxT) == '\\') {
                idxT = skipspc(t3, idxT + 1);
                stopchar = safe_char(t3, idxT);
            } else {
                stopchar = safe_char(t3, idxT);
            }
            
            int64_t v;
            idxS = expressionEsc(s2, idxS, stopchar, &v);
            char var[2] = {a, 0};
            putVars(var, v);
            continue;
        } else if (a >= 'a' && a <= 'z') {
            idxT++;
            char w[256];
            idxS = getSymbolWord(s2, idxS, w);
            int64_t v;
            if (!getSymValWithOk(w, &v)) {
                return false;
            }
            char var[2] = {a, 0};
            putVars(var, v);
            continue;
        } else if (a == b) {
            idxT++;
            idxS++;
            continue;
        }
        
        return false;
    }
}

// Recursive combination generator
static bool generate_combinations(const char *s, const char *t2, int cnt, 
                                  const int *sl, int start, int k, 
                                  int *cur, int cur_count) {
    if (k == 0) {
        char lt[MAX_LINE];
        removeBrackets(t2, cur, cur_count, lt);
        if (match(s, lt)) {
            return true;
        }
        return false;
    }
    
    for (int j = start; j <= cnt - k; j++) {
        cur[cur_count] = sl[j];
        if (generate_combinations(s, t2, cnt, sl, j + 1, k - 1, cur, cur_count + 1)) {
            return true;
        }
    }
    
    return false;
}

static bool match0(const char *s, const char *t) {
    char t2[MAX_LINE];
    strcpy(t2, t);
    
    // Replace [[ with OB and ]] with CB
    char result[MAX_LINE];
    int j = 0;
    
    for (int i = 0; i < (int)strlen(t2) && j < MAX_LINE - 1; ) {
        if (i + 2 <= (int)strlen(t2) && t2[i] == '[' && t2[i+1] == '[') {
            result[j++] = OB[0];
            i += 2;
        } else if (i + 2 <= (int)strlen(t2) && t2[i] == ']' && t2[i+1] == ']') {
            result[j++] = CB[0];
            i += 2;
        } else {
            result[j++] = t2[i];
            i++;
        }
    }
    result[j] = '\0';
    strcpy(t2, result);
    
    // Count OB occurrences
    int cnt = 0;
    for (int i = 0; t2[i]; i++) {
        if (t2[i] == OB[0]) cnt++;
    }
    
    if (cnt == 0) {
        return match(s, t2);
    }
    
    // Create index list
    int sl[100];
    for (int i = 0; i < cnt && i < 100; i++) {
        sl[i] = i + 1;
    }
    
    // Try all combinations of removing 0 to cnt brackets
    for (int num_remove = 0; num_remove <= cnt; num_remove++) {
        int cur[100];
        if (generate_combinations(s, t2, cnt, sl, 0, num_remove, cur, 0)) {
            return true;
        }
    }
    
    return false;
}

// Object generation
static int64_t align_(int64_t addr) {
    int64_t a = addr % AlignVal;
    if (a == 0) return addr;
    return addr + (AlignVal - a);
}

static void errorDirective(const char *s) {
    if (!s || s[0] == '\0') {
        return;
    }

    // 先頭・末尾の空白をスキップして実質的な内容を確認
    const char *p = s;
    while (*p == ' ' || *p == '\t') p++;
    if (*p == '\0') {
        return;  // 空白のみ → 何もしない
    }

    // スペースを全て削除したバージョンを生成
    char ss[MAX_LINE];
    int j = 0;
    for (int i = 0; s[i] && j < MAX_LINE - 1; i++) {
        if (s[i] != ' ' && s[i] != '\t') {
            ss[j++] = s[i];
        }
    }
    ss[j] = '\0';

    // 内容が空になった場合も早期リターン
    if (ss[0] == '\0') {
        return;
    }

    int idx = 0;
    int safeguard = 0;

    while (idx < (int)strlen(s) && safe_char(s, idx) != 0) {
        // 無限ループ防止
        if (++safeguard > 10000) {
            printf("Infinite loop detected in errorDirective: input='%s'\n", s);
            return;
        }

        if (s[idx] == ',') {
            idx++;
            continue;
        }

        int64_t u;
        int old_idx = idx;
        idx = expression0(s, idx, &u);

        // expression0 が進まなかった場合（無効な文字など）
        if (idx == old_idx && s[idx] != '\0') {
            // 1文字進める（ハング防止）
            idx++;
            continue;
        }

        if (safe_char(s, idx) == ';') {
            idx++;
        }

        int64_t t;
        old_idx = idx;
        idx = expression0(s, idx, &t);

        if (idx == old_idx && s[idx] != '\0') {
            idx++;
            continue;
        }

        // 出力（Pas == 2 || Pas == 0 のとき）
        if ((Pas == 2 || Pas == 0) && u != 0) {
            printf("Line %d Error code %ld ", Ln, t);
            if (t >= 0 && t < (int64_t)(sizeof(Errors)/sizeof(Errors[0]))) {
                printf("%s", Errors[t]);
            }
            printf(": \n");
        }
    }
}

// Expand rep[n,pattern] syntax
static void expand_rep(const char *input, char *output) {
    int in_idx = 0;
    int out_idx = 0;
    
    while (input[in_idx] != '\0' && out_idx < MAX_LINE - 1) {
        // Check for rep[ pattern
        if (strncmp(input + in_idx, "rep[", 4) == 0) {
            in_idx += 4;
            
            // Extract expression before comma
            char expr[256];
            int expr_idx = 0;
            int depth = 0;
            while (input[in_idx] != '\0' && expr_idx < 255) {
                if (input[in_idx] == '[') depth++;
                else if (input[in_idx] == ']') {
                    if (depth == 0) break;
                    depth--;
                }
                else if (input[in_idx] == ',' && depth == 0) break;
                expr[expr_idx++] = input[in_idx++];
            }
            expr[expr_idx] = '\0';
            
            if (input[in_idx] != ',') {
                // Invalid syntax, copy as-is
                strcpy(output + out_idx, "rep[");
                out_idx += 4;
                strcpy(output + out_idx, expr);
                out_idx += strlen(expr);
                continue;
            }
            in_idx++; // Skip comma
            
            // Extract pattern
            char pattern[256];
            int pat_idx = 0;
            depth = 0;
            while (input[in_idx] != '\0' && pat_idx < 255) {
                if (input[in_idx] == '[') depth++;
                else if (input[in_idx] == ']') {
                    if (depth == 0) break;
                    depth--;
                }
                pattern[pat_idx++] = input[in_idx++];
            }
            pattern[pat_idx] = '\0';
            
            if (input[in_idx] == ']') {
                in_idx++; // Skip ]
            }
            
            // Evaluate expression to get repeat count
            int64_t n;
            expression0(expr, 0, &n);
            
            // Expand pattern n times
            for (int64_t i = 0; i < n && out_idx < MAX_LINE - 10; i++) {
                if (i > 0 && out_idx < MAX_LINE - 1) {
                    output[out_idx++] = ',';
                }
                for (int j = 0; pattern[j] != '\0' && out_idx < MAX_LINE - 1; j++) {
                    output[out_idx++] = pattern[j];
                }
            }
        } else {
            output[out_idx++] = input[in_idx++];
        }
    }
    output[out_idx] = '\0';
}

// Expand @@[n,pattern] syntax - returns true if pattern is empty (all @@[])
static bool expand_atat(const char *input, char *output) {
    int in_idx = 0;
    int out_idx = 0;
    bool all_empty = true;
    
    while (input[in_idx] != '\0' && out_idx < MAX_LINE - 1) {
        // Check for @@[ pattern
        if (in_idx + 3 < (int)strlen(input) && strncmp(input + in_idx, "@@[", 3) == 0) {
            in_idx += 3;
            
            // Extract expression before comma
            char expr[256];
            int expr_idx = 0;
            int depth = 1;
            while (input[in_idx] != '\0' && expr_idx < 255) {
                if (input[in_idx] == '[') depth++;
                else if (input[in_idx] == ']') {
                    if (depth == 1) break;
                    depth--;
                }
                else if (input[in_idx] == ',' && depth == 1) break;
                expr[expr_idx++] = input[in_idx++];
            }
            expr[expr_idx] = '\0';
            
            if (input[in_idx] != ',') {
                // Invalid syntax, copy as-is
                strcpy(output + out_idx, "@@[");
                out_idx += 3;
                strcpy(output + out_idx, expr);
                out_idx += strlen(expr);
                all_empty = false;
                continue;
            }
            in_idx++; // Skip comma
            
            // Extract pattern
            char pattern[256];
            int pat_idx = 0;
            depth = 1;
            while (input[in_idx] != '\0' && pat_idx < 255) {
                if (input[in_idx] == '[') depth++;
                else if (input[in_idx] == ']') {
                    if (depth == 1) break;
                    depth--;
                }
                pattern[pat_idx++] = input[in_idx++];
            }
            pattern[pat_idx] = '\0';
            
            if (input[in_idx] == ']') {
                in_idx++; // Skip ]
            }
            
            // Evaluate expression to get repeat count
            int64_t n;
            expression0(expr, 0, &n);
            
            // Expand pattern n times
            if (n > 0) {
                all_empty = false;
                for (int64_t i = 0; i < n && out_idx < MAX_LINE - 10; i++) {
                    if (i > 0 && out_idx < MAX_LINE - 1) {
                        output[out_idx++] = ',';
                    }
                    for (int j = 0; pattern[j] != '\0' && out_idx < MAX_LINE - 1; j++) {
                        output[out_idx++] = pattern[j];
                    }
                }
            }
        } else {
            output[out_idx++] = input[in_idx++];
            all_empty = false;
        }
    }
    output[out_idx] = '\0';
    return all_empty;
}

// Replace %% with sequential numbers, %0 resets counter
static void replace_percent_with_index_v2(const char *input, char *output) {
    int in_idx = 0;
    int out_idx = 0;
    int count = 0;
    
    while (input[in_idx] != '\0' && out_idx < MAX_LINE - 20) {
        if (in_idx + 1 < (int)strlen(input)) {
            if (input[in_idx] == '%' && input[in_idx + 1] == '%') {
                // Replace %% with current count
                char num[20];
                snprintf(num, sizeof(num), "%d", count);
                strcpy(output + out_idx, num);
                out_idx += strlen(num);
                in_idx += 2;
                count++;
                continue;
            } else if (input[in_idx] == '%' && input[in_idx + 1] == '0') {
                // %0 resets counter
                count = 0;
                in_idx += 2;
                continue;
            }
        }
        output[out_idx++] = input[in_idx++];
    }
    output[out_idx] = '\0';
}



// Replace %% with sequential numbers starting from 1
static void replace_percent_with_index(const char *input, char *output) {
    int in_idx = 0;
    int out_idx = 0;
    int count = 1;
    
    while (input[in_idx] != '\0' && out_idx < MAX_LINE - 20) {
        if (in_idx + 1 < (int)strlen(input) && 
            input[in_idx] == '%' && input[in_idx + 1] == '%') {
            // Replace %% with current count
            char num[20];
            snprintf(num, sizeof(num), "%d", count);
            strcpy(output + out_idx, num);
            out_idx += strlen(num);
            in_idx += 2;
            count++;
        } else {
            output[out_idx++] = input[in_idx++];
        }
    }
    output[out_idx] = '\0';
}

static int makeobj(const char *s, int64_t *objl) {
    // ErrorUndefinedLabel = false;  // FIXED: Don't reset here
    
    // Step 1: Expand @@[] constructs - returns true if all patterns are empty
    char atat_expanded[MAX_LINE];
    bool all_empty = expand_atat(s, atat_expanded);
    
    // If all @@[] expanded to nothing, return empty
    if (all_empty && atat_expanded[0] == '\0') {
        return 0;
    }
    
    // Step 2: Expand rep[] constructs
    char rep_expanded[MAX_LINE];
    expand_rep(atat_expanded, rep_expanded);
    
    // Step 3: Replace %% with sequential numbers and handle %0
    char s2[MAX_LINE];
    replace_percent_with_index_v2(rep_expanded, s2);
    
    int idx = 0;
    int objl_count = 0;
    
    while (safe_char(s2, idx) != 0) {
        if (s2[idx] == ',') {
            idx++;
            int64_t p = Pc + objl_count;
            int64_t n = align_(p);
            for (int64_t i = p; i < n; i++) {
                objl[objl_count++] = Padding;
            }
            continue;
        }
        
        bool semicolon = false;
        if (s2[idx] == ';') {
            semicolon = true;
            idx++;
        }
        
        int64_t x;
        idx = expression0(s2, idx, &x);
        
        if (!semicolon || (semicolon && x != 0)) {
            objl[objl_count++] = x;
        }
        
        if (s2[idx] == ',') {
            idx++;
        }
    }
    
    return objl_count;
}

// Expand :label syntax in a line before pattern matching
static void expandColonLabels(const char *input, char *output) {
    int j = 0;
    for (int i = 0; input[i] && j < MAX_LINE - 50; i++) {
        if (input[i] == ':' && i + 1 < (int)strlen(input) && 
            (isalpha(input[i+1]) || input[i+1] == '.' || input[i+1] == '_')) {
            // Extract label name
            char label[256];
            int k = 0;
            i++; // Skip ':'
            while (input[i] && (isalnum(input[i]) || input[i] == '_' || input[i] == '.') && k < 255) {
                label[k++] = input[i++];
            }
            label[k] = '\0';
            i--; // Back one position for loop increment
            
            // Get label value and replace
            int64_t val = getLabelValue(label);
            j += snprintf(output + j, MAX_LINE - j, "%lld", (long long)val);
        } else {
            output[j++] = input[i];
        }
    }
    output[j] = '\0';
}

// Directive processing
static bool sectionProcessing(const char *l1, const char *l2) {
    char u[256];
    str_upper(u, l1);
    if (strcmp(u, "SECTION") != 0 && strcmp(u, "SEGMENT") != 0) {
        return false;
    }
    
    if (l2[0]) {
        strcpy(CurrentSection, l2);
        
        bool found = false;
        for (int i = 0; i < SectionCount; i++) {
            if (strcmp(Sections[i].name, l2) == 0) {
                Sections[i].start = Pc;
                found = true;
                break;
            }
        }
        if (!found && SectionCount < 1000) {
            strcpy(Sections[SectionCount].name, l2);
            Sections[SectionCount].start = Pc;
            Sections[SectionCount].size = 0;
            SectionCount++;
        }
    }
    return true;
}

static bool endsectionProcessing(const char *l1, const char *l2) {
    char u[256];
    str_upper(u, l1);
    if (strcmp(u, "ENDSECTION") != 0 && strcmp(u, "ENDSEGMENT") != 0) {
        return false;
    }
    
    for (int i = 0; i < SectionCount; i++) {
        if (strcmp(Sections[i].name, CurrentSection) == 0) {
            Sections[i].size = Pc - Sections[i].start;
            break;
        }
    }
    return true;
}

static bool zeroProcessing(const char *l1, const char *l2) {
    char u[256];
    str_upper(u, l1);
    if (strcmp(u, ".ZERO") != 0) {
        return false;
    }
    
    int64_t x;
    expression1(l2, 0, &x);
    for (int64_t i = 0; i <= x; i++) {
        outbin2(Pc, 0x00);
        Pc++;
    }
    return true;
}

static bool asciistr(const char *l2) {
    int idx = skipspc(l2, 0);
    if (safe_char(l2, idx) != '"') {
        return false;
    }
    idx++;
    
    while (idx < (int)strlen(l2)) {
        if (l2[idx] == '"') {
            return true;
        }
        
        char ch;
        if (idx + 2 <= (int)strlen(l2) && l2[idx] == '\\' && l2[idx + 1] == '0') {
            idx += 2;
            ch = 0;
        } else if (idx + 2 <= (int)strlen(l2) && l2[idx] == '\\' && l2[idx + 1] == 't') {
            idx += 2;
            ch = '\t';
        } else if (idx + 2 <= (int)strlen(l2) && l2[idx] == '\\' && l2[idx + 1] == 'n') {
            idx += 2;
            ch = '\n';
        } else {
            ch = l2[idx];
            idx++;
        }
        
        outbin(Pc, (int64_t)ch);
        Pc++;
    }
    return false;
}

static bool asciiProcessing(const char *l1, const char *l2) {
    char u[256];
    str_upper(u, l1);
    if (strcmp(u, ".ASCII") != 0) {
        return false;
    }
    return asciistr(l2);
}

static bool asciizProcessing(const char *l1, const char *l2) {
    char u[256];
    str_upper(u, l1);
    if (strcmp(u, ".ASCIIZ") != 0) {
        return false;
    }
    
    bool f = asciistr(l2);
    if (f) {
        outbin(Pc, 0x00);
        Pc++;
    }
    return f;
}

static bool includeAsm(const char *l1, const char *l2);

static bool alignProcessing(const char *l1, const char *l2) {
    char u[256];
    str_upper(u, l1);
    if (strcmp(u, ".ALIGN") != 0) {
        return false;
    }
    
    if (l2[0]) {
        int64_t val;
        expression1(l2, 0, &val);
        AlignVal = val;
    }
    Pc = align_(Pc);
    return true;
}

static bool orgProcessing(const char *l1, const char *l2) {
    char u[256];
    str_upper(u, l1);
    if (strcmp(u, ".ORG") != 0) {
        return false;
    }
    
    int64_t val;
    int idx = expression1(l2, 0, &val);
    
    char upper_rest[256];
    str_upper(upper_rest, l2 + idx);
    
    if (strstr(upper_rest, ",P")) {
        if (val > Pc) {
            for (int64_t i = Pc; i < val; i++) {
                outbin2(i, Padding);
            }
        }
    }
    Pc = val;
    return true;
}

static bool exportProcessing(const char *l1, const char *l2) {
    if (!(Pas == 2 || Pas == 0)) {
        return false;
    }
    
    char u[256];
    str_upper(u, l1);
    if (strcmp(u, ".EXPORT") != 0) {
        return false;
    }
    
    char l2_copy[MAX_LINE];
    snprintf(l2_copy, sizeof(l2_copy), "%s", l2);
    
    int idx = 0;
    while (safe_char(l2_copy, idx) != 0) {
        idx = skipspc(l2_copy, idx);
        char s[256];
        idx = getLabelWord(l2_copy, idx, s);
        if (s[0] == '\0') break;
        
        if (safe_char(l2_copy, idx) == ':') {
            idx++;
        }
        
        int64_t v = getLabelValue(s);
        char *sec = getLabelSectionName(s);
        
        if (ExportLabelCount < MAX_LABELS) {
            strcpy(ExportLabels[ExportLabelCount].name, s);
            ExportLabels[ExportLabelCount].Value = v;
            strcpy(ExportLabels[ExportLabelCount].Section, sec);
            ExportLabelCount++;
        }
        
        if (safe_char(l2_copy, idx) == ',') {
            idx++;
        }
    }
    return true;
}

static bool labelcProcessing(const char *l, const char *ll) {
    char u[256];
    str_upper(u, l);
    if (strcmp(u, ".LABELC") != 0) {
        return false;
    }
    
    if (ll[0]) {
        snprintf(Lwordchars, sizeof(Lwordchars), "%s%s%s", Alphabet, Digit, ll);
    }
    return true;
}

// Assembly functions
static bool lineassemble2(const char *line, int idx, int64_t *idxs_out, int64_t *objl, int *objl_count, int *idx_out) {
    // Note: :label expansion is done in lineassemble() before this function is called
    
    char l[MAX_LINE];
    idx = getParamToSpc(line, idx, l);
    
    char l2[MAX_LINE];
    idx = getParamToEon(line, idx, l2);
    
    strcpy(l, trim(l));
    strcpy(l2, trim(l2));
    
    // Remove all spaces from l
    char l_nospace[MAX_LINE];
    int j = 0;
    for (int i = 0; l[i] && j < MAX_LINE - 1; i++) {
        if (l[i] != ' ') {
            l_nospace[j++] = l[i];
        }
    }
    l_nospace[j] = '\0';
    strcpy(l, l_nospace);
    
    if (sectionProcessing(l, l2)) {
        *idx_out = idx;
        *objl_count = 0;
        return true;
    }
    if (endsectionProcessing(l, l2)) {
        *idx_out = idx;
        *objl_count = 0;
        return true;
    }
    if (zeroProcessing(l, l2)) {
        *idx_out = idx;
        *objl_count = 0;
        return true;
    }
    if (asciiProcessing(l, l2)) {
        *idx_out = idx;
        *objl_count = 0;
        return true;
    }
    if (asciizProcessing(l, l2)) {
        *idx_out = idx;
        *objl_count = 0;
        return true;
    }
    if (includeAsm(l, l2)) {
        *idx_out = idx;
        *objl_count = 0;
        return true;
    }
    if (alignProcessing(l, l2)) {
        *idx_out = idx;
        *objl_count = 0;
        return true;
    }
    if (orgProcessing(l, l2)) {
        *idx_out = idx;
        *objl_count = 0;
        return true;
    }
    if (labelcProcessing(l, l2)) {
        *idx_out = idx;
        *objl_count = 0;
        return true;
    }
    if (exportProcessing(l, l2)) {
        *idx_out = idx;
        *objl_count = 0;
        return true;
    }
    if (l[0] == '\0') {
        *idx_out = idx;
        *objl_count = 0;
        return false;
    }
    
    // Pattern matching
    bool se = false;
    bool oerr = false;
    int pln = 0;
    const char *pl[MAX_FIELDS] = {NULL};
    int64_t idxs = 0;
    
    bool loopflag = true;
    for (int i = 0; i < PatCount && loopflag; i++) {
        pln++;
        
        // Reset variables
        for (int k = 0; k < 26; k++) {
            Vars[k] = 0;
        }
        
        if (Pat[i].field_count == 0) continue;
        
        // Check for special directives
        const char *fields[MAX_FIELDS];
        for (int k = 0; k < Pat[i].field_count; k++) {
            fields[k] = Pat[i].fields[k];
        }
        
        setSymbol(fields, Pat[i].field_count);
        if (clearSymbol(fields, Pat[i].field_count)) continue;
        
        // Check for VLIW directives
        if (vliwp(fields, Pat[i].field_count)) continue;
        if (epic(fields, Pat[i].field_count)) continue;
        
        int lw = 0;
        for (int k = 0; k < Pat[i].field_count; k++) {
            if (Pat[i].fields[k] && Pat[i].fields[k][0]) {
                lw++;
            }
        }
        if (lw == 0) continue;
        
        char lin[MAX_LINE];
        snprintf(lin, sizeof(lin), "%s %s", l, l2);
        reduceSpaces(lin);
        strcpy(lin, trim(lin));
        
        if (Pat[i].fields[0][0] == '\0') {
            loopflag = false;
            break;
        }
        
        ErrorUndefinedLabel = false;
        
        ExpMode = EXP_ASM;  // Match assembly input
        if (match0(lin, Pat[i].fields[0])) {
            // ErrorUndefinedLabel = false;  // FIXED: Don't reset here
            
            // Check error directive (field 1)
            if (Pat[i].field_count > 1 && Pat[i].fields[1]) {
                errorDirective(Pat[i].fields[1]);
            }
            
            if (Pat[i].field_count > 2 && Pat[i].fields[2]) {
                *objl_count = makeobj(Pat[i].fields[2], objl);
            } else {
                *objl_count = 0;
            }
            
            if (Pat[i].field_count > 3 && Pat[i].fields[3]) {
                expression0(Pat[i].fields[3], 0, &idxs);
            }
            
            loopflag = false;
        }
    }
    
    if (loopflag) {
        se = true;
        pln = 0;
    }
    
    if (Pas == 2 || Pas == 0) {
        if (ErrorUndefinedLabel) {
            printf(" error - undefined label error.\n");
            *idx_out = idx;
            return false;
        }
        if (se) {
            printf(" error - Syntax error.\n");
            *idx_out = idx;
            return false;
        }
        if (oerr) {
            printf(" ; pat %d error - Illegal syntax in assemble line or pattern line.\n", pln);
            *idx_out = idx;
            return false;
        }
    }
    
    *idxs_out = idxs;
    *idx_out = idx;
    return true;
}

static bool lineassemble(const char *line) {
    char line_copy[MAX_LINE];
    strcpy(line_copy, line);
    
    // Replace tabs
    for (int i = 0; line_copy[i]; i++) {
        if (line_copy[i] == '\t') line_copy[i] = ' ';
        if (line_copy[i] == '\n') line_copy[i] = '\0';
    }
    
    reduceSpaces(line_copy);
    removeCommentAsm(line_copy);
    
    if (line_copy[0] == '\0') {
        return false;
    }
    
    char *processed_line = labelProcessing(line_copy);
    strcpy(line_copy,processed_line);
    
    // Expand :label syntax early, before any pattern matching
    char expanded_line[MAX_LINE];
    expandColonLabels(line_copy, expanded_line);
    strcpy(line_copy, expanded_line);
    
    const char *clear_fields[] = {".clearsym", "", ""};
    clearSymbol(clear_fields, 3);
    
    // Check for VLIW processing first
    if (VliwFlag) {
        char *vliw_marker = strstr(line_copy, "!!");
        if (vliw_marker && strncmp(vliw_marker, "!!!", 3) != 0) {
            // VLIW instruction detected
            // Process only the first instruction with lineassemble2
            char first_inst[MAX_LINE];
            int first_len = vliw_marker - line_copy;
            strncpy(first_inst, line_copy, first_len);
            first_inst[first_len] = '\0';
            
            int64_t idxs;
            int64_t objl[MAX_OBJL];
            int objl_count;
            int idx;
            bool flag = lineassemble2(first_inst, 0, &idxs, objl, &objl_count, &idx);
            
            if (!flag) {
                return false;
            }
            
            // Now call vliwprocess to handle the rest
            return vliwprocess(line_copy, idxs, objl, objl_count, flag, first_len);
        }
    }
    
    // Count !! separators
    Vcnt = 0;
    char *p = line_copy;
    Vcnt = 1;
    while ((p = strstr(p, "!!")) != NULL) {
        if (strncmp(p, "!!!!", 4) != 0 && strncmp(p, "!!!", 3) != 0) {
            Vcnt++;
        }
        p += 2;
    }
    
    int64_t idxs;
    int64_t objl[MAX_OBJL];
    int objl_count;
    int idx;
    bool flag = lineassemble2(line_copy, 0, &idxs, objl, &objl_count, &idx);
    
    if (!flag) {
        return false;
    }
    
    // Output
    for (int cnt = 0; cnt < objl_count; cnt++) {
        outbin(Pc + cnt, objl[cnt]);
    }
    Pc += objl_count;
    
    return true;
}

static bool lineassemble0(const char *line) {
    strcpy(Cl, line);
    char *nl = strchr(Cl, '\n');
    if (nl) *nl = '\0';
    
    if (Pas == 2 || Pas == 0) {
        printf("%016lx %s %d %s ", (long)Pc, CurrentFile, Ln, Cl);
    }
    
    bool f = lineassemble(Cl);
    
    if (Pas == 2 || Pas == 0) {
        printf("\n");
    }
    
    Ln++;
    return f;
}

// File processing
static char *getString(const char *l2) {
    static char result[MAX_LINE];
    int idx = skipspc(l2, 0);
    if (safe_char(l2, idx) != '"') {
        result[0] = '\0';
        return result;
    }
    idx++;
    
    int j = 0;
    while (idx < (int)strlen(l2) && j < MAX_LINE - 1) {
        if (l2[idx] == '"') {
            result[j] = '\0';
            return result;
        }
        result[j++] = l2[idx++];
    }
    result[j] = '\0';
    return result;
}

static bool includeAsm(const char *l1, const char *l2) {
    char u[256];
    str_upper(u, l1);
    if (strcmp(u, ".INCLUDE") != 0) {
        return false;
    }
    
    char *s = getString(l2);
    if (s[0]) {
        fileassemble(s);
    }
    return true;
}

static void fileassemble(const char *fn) {
    if (FnStackCount < 100) {
        strcpy(FnStack[FnStackCount], CurrentFile);
        FnStackCount++;
    }
    if (LnStackCount < 100) {
        LnStack[LnStackCount] = Ln;
        LnStackCount++;
    }
    
    strcpy(CurrentFile, fn);
    Ln = 1;
    
    FILE *fp = fopen(fn, "r");
    if (!fp) {
        if (FnStackCount > 0) {
            FnStackCount--;
            strcpy(CurrentFile, FnStack[FnStackCount]);
        }
        if (LnStackCount > 0) {
            LnStackCount--;
            Ln = LnStack[LnStackCount];
        }
        return;
    }
    
    char line[MAX_LINE];
    while (fgets(line, sizeof(line), fp)) {
        lineassemble0(line);
    }
    
    fclose(fp);
    
    if (FnStackCount > 0) {
        FnStackCount--;
        strcpy(CurrentFile, FnStack[FnStackCount]);
    }
    if (LnStackCount > 0) {
        LnStackCount--;
        Ln = LnStack[LnStackCount];
    }
}

static void readpat(const char *filename) {
    if (!filename || filename[0] == '\0') return;
    
    FILE *fp = fopen(filename, "r");
    if (!fp) return;
    
    char line[MAX_LINE];
    PatCount = 0;
    
    while (fgets(line, sizeof(line), fp) && PatCount < MAX_PAT) {
        
        removeComment(line);
        
        // Replace tabs and carriage returns
        for (int i = 0; line[i]; i++) {
            if (line[i] == '\t') line[i] = ' ';
            if (line[i] == '\r') line[i] = ' ';
            if (line[i] == '\n') line[i] = '\0';
        }
        
        // Trim right
        int len = strlen(line);
        while (len > 0 && line[len-1] == ' ') {
            line[--len] = '\0';
        }
        
        strcpy(line, trim(line));
        
        
        if (line[0] == '\0') continue;
        
        // Parse fields using getParams1
        char *r[MAX_FIELDS];
        int r_count = 0;
        
        int idx = 0;
        while (idx < (int)strlen(line) && r_count < MAX_FIELDS) {
            char param[MAX_LINE];
            int old_idx = idx;
            idx = getParams1(line, idx, param);
            
            // Always add, even if empty (like Go version)
            r[r_count] = strdup(param);
            r_count++;
            
            // Break if we didn't advance
            if (idx == old_idx || idx >= (int)strlen(line)) break;
        }
        
        // Map to pattern fields based on count (like Go version)
        Pat[PatCount].field_count = 6;
        for (int i = 0; i < 6; i++) {
            Pat[PatCount].fields[i] = strdup("");
        }
        
        
        if (r_count == 1) {
            if (r[0]) free(Pat[PatCount].fields[0]);
            Pat[PatCount].fields[0] = r[0];
        } else if (r_count == 2) {
            if (r[0]) { free(Pat[PatCount].fields[0]); Pat[PatCount].fields[0] = r[0]; }
            if (r[1]) { free(Pat[PatCount].fields[2]); Pat[PatCount].fields[2] = r[1]; }
        } else if (r_count == 3) {
            if (r[0]) { free(Pat[PatCount].fields[0]); Pat[PatCount].fields[0] = r[0]; }
            if (r[1]) { free(Pat[PatCount].fields[1]); Pat[PatCount].fields[1] = r[1]; }
            if (r[2]) { free(Pat[PatCount].fields[2]); Pat[PatCount].fields[2] = r[2]; }
        } else if (r_count == 4) {
            if (r[0]) { free(Pat[PatCount].fields[0]); Pat[PatCount].fields[0] = r[0]; }
            if (r[1]) { free(Pat[PatCount].fields[1]); Pat[PatCount].fields[1] = r[1]; }
            if (r[2]) { free(Pat[PatCount].fields[2]); Pat[PatCount].fields[2] = r[2]; }
            if (r[3]) { free(Pat[PatCount].fields[3]); Pat[PatCount].fields[3] = r[3]; }
        } else if (r_count == 5) {
            if (r[0]) { free(Pat[PatCount].fields[0]); Pat[PatCount].fields[0] = r[0]; }
            if (r[1]) { free(Pat[PatCount].fields[1]); Pat[PatCount].fields[1] = r[1]; }
            if (r[2]) { free(Pat[PatCount].fields[2]); Pat[PatCount].fields[2] = r[2]; }
            if (r[3]) { free(Pat[PatCount].fields[3]); Pat[PatCount].fields[3] = r[3]; }
            if (r[4]) { free(Pat[PatCount].fields[4]); Pat[PatCount].fields[4] = r[4]; }
        } else if (r_count >= 6) {
            for (int i = 0; i < 6; i++) {
                if (r[i]) { free(Pat[PatCount].fields[i]); Pat[PatCount].fields[i] = r[i]; }
            }
            // Free extras
            for (int i = 6; i < r_count; i++) {
                if (r[i]) free(r[i]);
            }
        }
        
        PatCount++;
    }
    
    fclose(fp);
}

static void setpatsymbols(void) {
    for (int i = 0; i < PatCount; i++) {
        const char *fields[MAX_FIELDS];
        for (int j = 0; j < Pat[i].field_count; j++) {
            fields[j] = Pat[i].fields[j];
        }
        setSymbol(fields, Pat[i].field_count);
    }
    
    PatsymbolCount = SymbolCount;
    for (int i = 0; i < SymbolCount && i < MAX_SYMBOLS; i++) {
        Patsymbols[i] = Symbols[i];
    }
}

// VLIW functions
static bool vliwp(const char **fields, int field_count) {
    if (field_count == 0 || strcmp(fields[0], ".vliw") != 0) {
        return false;
    }
    
    int64_t v1, v2, v3, v4;
    if (field_count > 1 && fields[1]) expression0(fields[1], 0, &v1);
    else v1 = 0;
    if (field_count > 2 && fields[2]) expression0(fields[2], 0, &v2);
    else v2 = 0;
    if (field_count > 3 && fields[3]) expression0(fields[3], 0, &v3);
    else v3 = 0;
    if (field_count > 4 && fields[4]) expression0(fields[4], 0, &v4);
    else v4 = 0;
    
    VliwBits = (int)v1;
    VliwInstBits = (int)v2;
    VliwTemplateBits = v3;
    VliwFlag = true;
    
    // Build VliwNop
    int n = (VliwInstBits + 7) / 8;
    if (VliwNop) free(VliwNop);
    VliwNop = malloc(n * sizeof(int64_t));
    if (!VliwNop) {
        VliwNopCount = 0;
        return true;
    }
    
    VliwNopCount = 0;
    int64_t val = v4;
    for (int j = 0; j < n; j++) {
        VliwNop[VliwNopCount++] = val & 0xff;
        val >>= 8;
    }
    
    return true;
}

static bool epic(const char **fields, int field_count) {
    if (field_count == 0) return false;
    
    char upper_field0[256];
    str_upper(upper_field0, fields[0]);
    if (strcmp(upper_field0, "EPIC") != 0) {
        return false;
    }
    
    if (field_count <= 1 || !fields[1] || fields[1][0] == '\0') {
        return false;
    }
    
    // Parse indices from field[1]
    const char *s = fields[1];
    int64_t *idxs = malloc(100 * sizeof(int64_t));
    if (!idxs) return false;
    
    int idxs_count = 0;
    int idx = 0;
    
    while (idx < (int)strlen(s) && idxs_count < 100) {
        int64_t v;
        int newIdx = expression0(s, idx, &v);
        if (newIdx == idx) break;
        idxs[idxs_count++] = v;
        idx = newIdx;
        
        if (idx < (int)strlen(s) && s[idx] == ',') {
            idx++;
        } else {
            break;
        }
    }
    
    // Add to VliwSet
    if (VliwSetCount < 1000) {
        VliwSet[VliwSetCount].Idxs = idxs;
        VliwSet[VliwSetCount].IdxCount = idxs_count;
        
        if (field_count > 2 && fields[2]) {
            strncpy(VliwSet[VliwSetCount].Expr, fields[2], MAX_LINE - 1);
            VliwSet[VliwSetCount].Expr[MAX_LINE - 1] = '\0';
        } else {
            VliwSet[VliwSetCount].Expr[0] = '\0';
        }
        VliwSetCount++;
    } else {
        free(idxs);
    }
    
    return true;
}

static bool vliwprocess(const char *line, int64_t idxs, int64_t *objl, int objl_count, bool flag, int idx) {
    if (!VliwFlag) return false;
    
    // Collect all VLIW slots
    __uint128_t objs[100][100];
    int objs_count[100];
    int slot_count = 0;
    
    // First slot
    if (slot_count < 100) {
        for (int i = 0; i < objl_count && i < 100; i++) {
            objs[slot_count][i] = (__uint128_t)objl[i];
        }
        objs_count[slot_count] = objl_count;
        slot_count++;
    }
    
    __uint128_t idxlst[100];
    idxlst[0] = (__uint128_t)idxs;
    int idxlst_count = 1;
    
    VliwStop = 0;
    
    // Look for !! and !!!! markers
    int loop_count = 0;
    while (idx < (int)strlen(line) && loop_count < 100) {
        loop_count++;
        idx = skipspc(line, idx);
        
        if (idx + 4 <= (int)strlen(line) && 
            strncmp(line + idx, "!!!!", 4) == 0) {
            idx += 4;
            VliwStop = 1;
            continue;
        } else if (idx + 2 <= (int)strlen(line) && 
                   strncmp(line + idx, "!!", 2) == 0) {
            idx += 2;
            
            // Extract instruction up to next !! or !!!!
            char next_inst[MAX_LINE];
            int inst_start = idx;
            int inst_end = idx;
            
            // Find the end of this instruction
            while (inst_end < (int)strlen(line)) {
                if (inst_end + 4 <= (int)strlen(line) && 
                    strncmp(line + inst_end, "!!!!", 4) == 0) {
                    break;
                }
                if (inst_end + 2 <= (int)strlen(line) && 
                    strncmp(line + inst_end, "!!", 2) == 0) {
                    break;
                }
                inst_end++;
            }
            
            int inst_len = inst_end - inst_start;
            strncpy(next_inst, line + inst_start, inst_len);
            next_inst[inst_len] = '\0';
            
            // Process next instruction
            int64_t nidxs;
            int64_t nobjl[1000];
            int nobjl_count = 0;
            int nidx;
            
            bool nflag = lineassemble2(next_inst, 0, &nidxs, nobjl, &nobjl_count, &nidx);
            
            if (nflag && slot_count < 100) {
                for (int i = 0; i < nobjl_count && i < 100; i++) {
                    objs[slot_count][i] = (__uint128_t)nobjl[i];
                }
                objs_count[slot_count] = nobjl_count;
                if (idxlst_count < 100) {
                    idxlst[idxlst_count++] = (__uint128_t)nidxs;
                }
                slot_count++;
            }
            
            idx = inst_end;
            continue;
        } else {
            break;
        }
    }
    
    // VLIW packing logic
    if (VliwTemplateBits == 0) {
        VliwSetCount = 1;
        if (VliwSet[0].Idxs) free(VliwSet[0].Idxs);
        VliwSet[0].IdxCount = 1;
        VliwSet[0].Idxs = malloc(sizeof(int64_t));
        if (!VliwSet[0].Idxs) return false;
        VliwSet[0].Idxs[0] = 0;
        strcpy(VliwSet[0].Expr, "0");
    }
    
    int vbits = VliwBits > 0 ? VliwBits : -VliwBits;
    
    for (int k_idx = 0; k_idx < VliwSetCount; k_idx++) {
        VliwEntry *k = &VliwSet[k_idx];
        
        // Check if idxlst matches k->Idxs
        bool match = true;
        if (VliwTemplateBits != 0) {
            if (k->IdxCount != idxlst_count) continue;
            for (int i = 0; i < k->IdxCount; i++) {
                bool found = false;
                for (int j = 0; j < idxlst_count; j++) {
                    if ((__uint128_t)k->Idxs[i] == idxlst[j]) {
                        found = true;
                        break;
                    }
                }
                if (!found) {
                    match = false;
                    break;
                }
            }
            if (!match) continue;
        }
        
        // Calculate template value with vliwstop
        int64_t templ_val;
        expression0(k->Expr, 0, &templ_val);
        
        // Collect all bytes from all instructions
        __uint128_t values[1000];
        int values_count = 0;
        
        for (int j = 0; j < slot_count; j++) {
            for (int m = 0; m < objs_count[j]; m++) {
                if (values_count < 1000) {
                    values[values_count++] = objs[j][m];
                }
            }
        }
        
        // Pad with nop bytes
        int ibyte = (VliwInstBits + 7) / 8;
        int noi = (vbits - labs(VliwTemplateBits)) / VliwInstBits;
        int needed = ibyte * noi;
        
        while (values_count < needed) {
            for (int i = 0; i < VliwNopCount && values_count < needed; i++) {
                values[values_count++] = (__uint128_t)VliwNop[i];
            }
        }
        
        // Pack bytes into instructions (big-endian within each instruction)
        __uint128_t v1[100];
        int v1_count = 0;
        int cnt = 0;
        
        __uint128_t im = ((__uint128_t)1 << VliwInstBits) - 1;
        
        for (int j = 0; j < noi; j++) {
            __uint128_t vv = 0;
            for (int i = 0; i < ibyte; i++) {
                vv <<= 8;
                if (cnt < values_count) {
                    vv |= values[cnt] & (__uint128_t)0xff;
                }
                cnt++;
            }
            v1[v1_count++] = vv & im;
        }
        
        // Pack instructions together using 128-bit arithmetic
        __uint128_t r = 0;
        for (int i = 0; i < v1_count; i++) {
            r = (r << VliwInstBits) | v1[i];
        }
        
        // Apply mask only if vbits < 128 (avoid undefined behavior with 128-bit shift)
        if (vbits < 128) {
            __uint128_t pm = ((__uint128_t)1 << vbits) - 1;
            r = r & pm;
        }
        
        // Add template bits
        __uint128_t tm = ((__uint128_t)1 << labs(VliwTemplateBits)) - 1;
        __uint128_t templ = (__uint128_t)templ_val & tm;
        
        __uint128_t res;
        if (VliwTemplateBits < 0) {
            res = r | (templ << (vbits - labs(VliwTemplateBits)));
        } else {
            res = (r << VliwTemplateBits) | templ;
        }
        
        // Output bytes
        int q = 0;
        if (VliwBits > 0) {
            // Big-endian output
            for (int cnt_out = 0; cnt_out < vbits / 8; cnt_out++) {
                int shift = (vbits - 8) - (cnt_out * 8);
                __uint128_t vm = (__uint128_t)0xff << shift;
                __uint128_t byte_val = ((res & vm) >> shift) & (__uint128_t)0xff;
                outbin(Pc + cnt_out, (uint64_t)byte_val);
                q++;
            }
        } else {
            // Little-endian output
            for (int cnt_out = 0; cnt_out < vbits / 8; cnt_out++) {
                outbin(Pc + cnt_out, (uint64_t)(res & (__uint128_t)0xff));
                res >>= 8;
                q++;
            }
        }
        
        Pc += q;
        return true;
    }
    
    if (Pas == 0 || Pas == 2) {
        printf(" error - No vliw instruction-set defined.\n");
        return false;
    }
    
    return true;
}


static bool impLabel(const char *l) {
    int idx = skipspc(l, 0);
    char section[256];
    idx = getLabelWord(l, idx, section);
    idx = skipspc(l, idx);
    char label[256];
    idx = getLabelWord(l, idx, label);
    
    if (label[0] == '\0') return false;
    
    idx = skipspc(l, idx);
    int64_t v;
    int newIdx = expression(l, idx, &v);
    if (newIdx == idx) return false;
    
    putLabelValue(label, v, section);
    return true;
}

// Main
int main(int argc, char *argv[]) {
    init_globals();
    
    if (argc == 1) {
        printf("axx general assembler programmed and designed by Taisuke Maekawa\n");
        printf("Usage: axx patternfile.axx [sourcefile.s] [-o outfile.bin] [-e export_labels.tsv] [-i import_labels.tsv]\n");
        return 0;
    }
    
    // Read pattern file
    if (argc >= 2) {
        readpat(argv[1]);
        setpatsymbols();
    }
    
    // Parse options
    char expefile[256] = "";
    int source_idx = -1;
    
    for (int i = 2; i < argc; i++) {
        if (strcmp(argv[i], "-o") == 0 && i + 1 < argc) {
            strcpy(Outfile, argv[i + 1]);
            i++;
        } else if (strcmp(argv[i], "-e") == 0 && i + 1 < argc) {
            strcpy(Expfile, argv[i + 1]);
            i++;
        } else if (strcmp(argv[i], "-E") == 0 && i + 1 < argc) {
            strcpy(expefile, argv[i + 1]);
            i++;
        } else if (strcmp(argv[i], "-i") == 0 && i + 1 < argc) {
            strcpy(Impfile, argv[i + 1]);
            i++;
        } else if (source_idx == -1) {
            source_idx = i;
        }
    }
    
    // Import labels
    if (Impfile[0]) {
        FILE *fp = fopen(Impfile, "r");
        if (fp) {
            char line[MAX_LINE];
            while (fgets(line, sizeof(line), fp)) {
                impLabel(line);
            }
            fclose(fp);
        }
    }
    
    // Create output file
    if (Outfile[0]) {
        remove(Outfile);
        FILE *fp = fopen(Outfile, "wb");
        if (fp) fclose(fp);
    }
    
    // Assemble
    if (source_idx == -1) {
        // Interactive mode
        Pc = 0;
        Pas = 0;
        Ln = 1;
        strcpy(CurrentFile, "(stdin)");
        
        char line[MAX_LINE];
        while (1) {
            printf("%016lx: >> ", (long)Pc);
            if (!fgets(line, sizeof(line), stdin)) break;
            
            char *nl = strchr(line, '\n');
            if (nl) *nl = '\0';
            
            strcpy(line, trim(line));
            if (line[0] == '\0') continue;
            
            lineassemble0(line);
        }
    } else {
        // Two-pass assembly
        Pc = 0;
        Pas = 1;
        Ln = 1;
        fileassemble(argv[source_idx]);
        
        Pc = 0;
        Pas = 2;
        Ln = 1;
        fileassemble(argv[source_idx]);
    }
    
    // Export labels
    int elf = 0;
    if (expefile[0]) {
        strcpy(Expfile, expefile);
        elf = 1;
    }
    
    if (Expfile[0]) {
        FILE *fp = fopen(Expfile, "w");
        if (fp) {
            for (int i = 0; i < SectionCount; i++) {
                char flag[10] = "";
                if (strcmp(Sections[i].name, ".text") == 0 && elf == 1) {
                    strcpy(flag, "AX");
                }
                if (strcmp(Sections[i].name, ".data") == 0 && elf == 1) {
                    strcpy(flag, "WA");
                }
                fprintf(fp, "%s\t%#lx\t%#lx\t%s\n",
                        Sections[i].name, (long)Sections[i].start,
                        (long)Sections[i].size, flag);
            }
            
            for (int i = 0; i < ExportLabelCount; i++) {
                fprintf(fp, "%s\t%#lx\n", ExportLabels[i].name, (long)ExportLabels[i].Value);
            }
            
            fclose(fp);
        }
    }
    
    // Cleanup
    for (int i = 0; i < PatCount; i++) {
        for (int j = 0; j < Pat[i].field_count; j++) {
            free(Pat[i].fields[j]);
        }
    }
    
    return 0;
}

// Missing impLabel implementation
