/*
 * axx general assembler designed and programmed by Taisuke Maekawa
 * C translation (complete, behavior-compatible)
 *
 * Bug fixes applied (bugs 2-8, original):
 *  2. remove_brackets_str(): use unique serials per OB so parallel groups are distinguishable
 *  3. pat_match0(): avoid UB from 1<<cnt when cnt>=32; use size_t/uint64 mask
 *  4. u256_pow(): use full 256-bit exponent (no 0xffff truncation)
 *  5. expr_term11(): lazy evaluation – only evaluate the chosen branch
 *  6. ieee754_128_from_str()/xeval(): shell-escape via execvp-style popen to avoid injection
 *  7. adir_label_processing(): pass l2 (expression tail) instead of full l to expr_expression_asm
 *  8. expr_term6(): guard tv==256 in sign-extension shl to avoid zero-mask
 *
 * Additional bug fixes (secondary pass):
 *  A. u256_pow(): avoid unnecessary base squarings after last set bit (performance fix)
 *  B. lmap_free(): reset nbuckets to 0 to prevent stale-count use after free
 *  C. secmap_clear(): zero out dangling pointers in order[] after freeing entries
 *  D. binary_flush(): guard max_pos==UINT64_MAX to prevent silent integer overflow
 *  E. ieee754_128_from_str(): unlink temp script on ALL exit paths (was leaking on !safe)
 *  F. xeval(): unlink temp script on ALL exit paths (was leaking on spawn failure)
 *  G. expr_term11(): add skip_ternary_expr() so nested ternaries in false-branch are
 *     fully skipped (not just up to the inner '?') when the condition is true
 *  H. ivv_push(): add NULL-check after realloc (was missing, unlike every other push helper)
 *  I. binary_flush(): guard total_size > SIZE_MAX before cast to size_t (32-bit heap corruption)
 *  J. weo_pad(): guard ftell() < 0 to avoid silent padding skip on I/O error
 *  K. int_cmp(): replace subtraction with branchless 3-way compare to avoid signed overflow
 *  L. expr_term0(): set x=0 on division by zero (was silently returning the dividend)
 */

#define _GNU_SOURCE
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>
#include <stdint.h>
#include <math.h>
#include <assert.h>
#include <errno.h>
#include <stdarg.h>
#include <unistd.h>
#include <libgen.h>
#include <limits.h>
#include <sys/wait.h>

/* Portability helper: suppress -Wunused-function for API utilities that are
 * defined now but may be referenced by future callers or external tools.    */
#ifdef __GNUC__
#  define AXX_UNUSED __attribute__((unused))
#else
#  define AXX_UNUSED
#endif

/* =========================================================
 * Big integer: 256-bit unsigned, stored as 4x uint64_t
 * lo[0] = least significant 64 bits ... lo[3] = most significant
 * Python's UNDEF = 0xffff...ff (256 bits of 1s)
 * ========================================================= */
typedef struct { uint64_t w[4]; } uint256_t;

static uint256_t u256_zero(void) {
    uint256_t r; memset(&r,0,sizeof(r)); return r;
}
static uint256_t u256_one(void) {
    uint256_t r = u256_zero(); r.w[0]=1; return r;
}
static uint256_t u256_from_i64(int64_t v) {
    uint256_t r;
    r.w[0] = (uint64_t)v;
    uint64_t fill = (v < 0) ? (uint64_t)-1 : 0;
    r.w[1]=r.w[2]=r.w[3]=fill;
    return r;
}
static uint256_t u256_from_u64(uint64_t v) {
    uint256_t r = u256_zero(); r.w[0]=v; return r;
}
static int u256_is_zero(uint256_t a) {
    return (a.w[0]|a.w[1]|a.w[2]|a.w[3]) == 0;
}
static int u256_eq(uint256_t a, uint256_t b) {
    return a.w[0]==b.w[0] && a.w[1]==b.w[1] && a.w[2]==b.w[2] && a.w[3]==b.w[3];
}
/* signed compare: treat as two's-complement 256-bit.
 *
 * Bug 1/3 fix: when both operands have the same sign, the correct ordering
 * is always the UNSIGNED ordering, regardless of sign.
 *
 * Proof: for two's-complement negatives, the more-negative (smaller signed)
 * value has a SMALLER unsigned representation.
 *   e.g. INT256_MIN = 0x8000...0  <  -1 = 0xFFFF...F  (both unsigned and signed)
 *   e.g. -2 = 0xFFFF...E  <  -1 = 0xFFFF...F          (both unsigned and signed)
 *
 * The original code inverted the comparison for negative operands (sa==1),
 * making every negative-vs-negative comparison return the wrong answer.
 */
static int u256_lt_signed(uint256_t a, uint256_t b) {
    int sa = (int)(a.w[3] >> 63);
    int sb = (int)(b.w[3] >> 63);
    /* Different signs: negative < positive */
    if (sa != sb) return sa > sb;
    /* Same sign: plain unsigned word-by-word comparison (correct for both signs) */
    if (a.w[3] != b.w[3]) return a.w[3] < b.w[3];
    if (a.w[2] != b.w[2]) return a.w[2] < b.w[2];
    if (a.w[1] != b.w[1]) return a.w[1] < b.w[1];
    return a.w[0] < b.w[0];
}
static int u256_le_signed(uint256_t a, uint256_t b) {
    return u256_eq(a,b) || u256_lt_signed(a,b);
}
static int u256_gt_signed(uint256_t a, uint256_t b) { return u256_lt_signed(b,a); }
static int u256_ge_signed(uint256_t a, uint256_t b) { return u256_le_signed(b,a); }

static uint256_t u256_add(uint256_t a, uint256_t b) {
    uint256_t r;
    uint64_t carry = 0;
    for (int i=0;i<4;i++){
        __uint128_t s = (__uint128_t)a.w[i] + b.w[i] + carry;
        r.w[i] = (uint64_t)s;
        carry = (uint64_t)(s >> 64);
    }
    return r;
}
static uint256_t u256_neg(uint256_t a) {
    uint256_t r;
    for(int i=0;i<4;i++) r.w[i]=~a.w[i];
    return u256_add(r, u256_one());
}
static uint256_t u256_sub(uint256_t a, uint256_t b) {
    return u256_add(a, u256_neg(b));
}
static uint256_t u256_not(uint256_t a) {
    uint256_t r; for(int i=0;i<4;i++) r.w[i]=~a.w[i]; return r;
}
static uint256_t u256_and(uint256_t a, uint256_t b) {
    uint256_t r; for(int i=0;i<4;i++) r.w[i]=a.w[i]&b.w[i]; return r;
}
static uint256_t u256_or(uint256_t a, uint256_t b) {
    uint256_t r; for(int i=0;i<4;i++) r.w[i]=a.w[i]|b.w[i]; return r;
}
static uint256_t u256_xor(uint256_t a, uint256_t b) {
    uint256_t r; for(int i=0;i<4;i++) r.w[i]=a.w[i]^b.w[i]; return r;
}
static uint256_t u256_shl(uint256_t a, int n) {
    if (n <= 0) return a;
    if (n >= 256) return u256_zero();
    uint256_t r = u256_zero();
    int word_shift = n / 64;
    int bit_shift  = n % 64;
    for (int i=0; i<4; i++){
        int dest = i + word_shift;
        if (dest < 4) r.w[dest] |= a.w[i] << bit_shift;
        if (bit_shift && dest+1 < 4) r.w[dest+1] |= a.w[i] >> (64-bit_shift);
    }
    return r;
}
/* arithmetic right shift */
static uint256_t u256_sar(uint256_t a, int n) {
    if (n <= 0) return a;
    if (n >= 256) {
        int sign = (int)(a.w[3] >> 63);
        uint64_t fill = sign ? (uint64_t)-1 : 0;
        uint256_t r; r.w[0]=r.w[1]=r.w[2]=r.w[3]=fill; return r;
    }
    uint256_t r = u256_zero();
    int sign = (int)(a.w[3] >> 63);
    uint64_t fill = sign ? (uint64_t)-1 : 0;
    int word_shift = n / 64;
    int bit_shift  = n % 64;
    for (int i=3; i>=0; i--){
        int src = i + word_shift;
        uint64_t hi = (src < 4) ? a.w[src] : fill;
        uint64_t lo_v = (src+1 < 4) ? a.w[src+1] : fill;
        if (bit_shift)
            r.w[i] = (hi >> bit_shift) | (lo_v << (64-bit_shift));
        else
            r.w[i] = hi;
    }
    return r;
}
/* unsigned multiply: only lower 256 bits */
static uint256_t u256_mul(uint256_t a, uint256_t b) {
    uint256_t r = u256_zero();
    for (int i=0;i<4;i++){
        uint64_t carry=0;
        for(int j=0; j<4-i; j++){
            __uint128_t p = (__uint128_t)a.w[i]*b.w[j] + r.w[i+j] + carry;
            r.w[i+j] = (uint64_t)p;
            carry = (uint64_t)(p>>64);
        }
    }
    return r;
}
/* signed multiply (Python semantics, lower 256 bits) */
static uint256_t u256_mul_signed(uint256_t a, uint256_t b) {
    return u256_mul(a,b);
}
/* unsigned divide: a // b */
static uint256_t u256_udiv(uint256_t a, uint256_t b) {
    if (u256_is_zero(b)) return u256_zero();
    uint256_t q = u256_zero();
    uint256_t r = u256_zero();
    for (int i=255; i>=0; i--) {
        r = u256_shl(r,1);
        int wi = i/64, bi = i%64;
        r.w[0] |= ((a.w[wi]>>bi)&1);
        int ge=0;
        for(int k=3;k>=0;k--){
            if(r.w[k]>b.w[k]){ge=1;break;}
            if(r.w[k]<b.w[k]){ge=0;break;}
            ge=1;
        }
        if(ge){ r=u256_sub(r,b); q.w[wi]|=((uint64_t)1<<bi); }
    }
    return q;
}
/* Python floor division (signed): truncates toward negative infinity */
static uint256_t u256_floordiv(uint256_t a, uint256_t b) {
    if (u256_is_zero(b)) { fprintf(stderr,"Division by zero\n"); return u256_zero(); }
    int sa = (int)(a.w[3]>>63);
    int sb = (int)(b.w[3]>>63);
    uint256_t ua = sa ? u256_neg(a) : a;
    uint256_t ub = sb ? u256_neg(b) : b;
    uint256_t q = u256_udiv(ua, ub);
    uint256_t rem = u256_sub(ua, u256_mul(q,ub));
    if (sa != sb) {
        q = u256_neg(q);
        if (!u256_is_zero(rem)) q = u256_sub(q, u256_one());
    }
    return q;
}
/* Python modulo */
static uint256_t u256_mod(uint256_t a, uint256_t b) {
    if (u256_is_zero(b)) { fprintf(stderr,"Division by zero\n"); return u256_zero(); }
    uint256_t q = u256_floordiv(a,b);
    return u256_sub(a, u256_mul(q,b));
}

/* -------------------------------------------------------
 * Bug 4 fix: u256_pow() – use the full 256-bit exponent.
 * The original truncated exp to 16 bits (& 0xffff), which
 * silently gave wrong results for any exponent >= 65536.
 * We now iterate over all 256 bits (square-and-multiply).
 * ------------------------------------------------------- */
/* Fix A: u256_pow() – avoid unnecessary base squarings after the last set bit.
 * The original always performed 256 squarings regardless of exp magnitude.
 * We now break as soon as all remaining exp words are zero, so small exponents
 * (the common case) run in O(log2(exp)) multiplications instead of O(256). */
static uint256_t u256_pow(uint256_t base, uint256_t exp) {
    uint256_t r = u256_one();
    for (int wi = 0; wi < 4; wi++) {
        uint64_t word = exp.w[wi];
        /* If this and all higher words are zero, nothing more to do */
        if (!word) {
            int all_zero = 1;
            for (int k = wi + 1; k < 4; k++) if (exp.w[k]) { all_zero = 0; break; }
            if (all_zero) break;
        }
        for (int bi = 0; bi < 64; bi++) {
            if (word & ((uint64_t)1 << bi))
                r = u256_mul(r, base);
            /* Only square base when there are more bits still to process */
            int last_bit = (wi == 3 && bi == 63);
            if (!last_bit)
                base = u256_mul(base, base);
        }
    }
    return r;
}

/* Convert to int64 (sign-extended from lower 64 bits for printing etc.) */
static int64_t u256_to_i64(uint256_t a) { return (int64_t)a.w[0]; }
static uint64_t u256_to_u64(uint256_t a) { return a.w[0]; }

/* nbit: number of bits needed.
 * Fix #3: the 256-bit signed minimum value (0x8000...0) is its own negation
 * under two's-complement, so the original "if negative, negate first" approach
 * left it unchanged and the while-loop ran forever.
 * Fix: use a pure unsigned bit-scan over all 256 bits instead. */
static int u256_nbit(uint256_t v) {
    /* Mirrors axx.py nbit(): count bits of abs(v).
     * abs() is the two's-complement absolute value: negate if the sign bit is set.
     * Special case: the minimum value (0x8000...0) negates to itself under two's-
     * complement, so we detect it separately and return 256. */
    int sign = (int)(v.w[3] >> 63);
    if(sign){
        /* Negative: compute abs = -v = ~v + 1 */
        uint256_t av = u256_neg(v);
        /* If negation overflowed back to the same value, it was INT256_MIN → 256 bits */
        if((int)(av.w[3] >> 63)){
            return 256;
        }
        v = av;
    }
    int b = 0;
    for (int wi = 3; wi >= 0; wi--) {
        if (v.w[wi]) {
            /* floor(log2(v.w[wi])) + 1 */
            uint64_t word = v.w[wi];
            int bits = 0;
            while (word) { word >>= 1; bits++; }
            b = wi * 64 + bits;
            break;
        }
    }
    return b;
}

/* UNDEF = 0xfff...f (256 bits) */
static uint256_t UNDEF_VAL(void) { return u256_not(u256_zero()); }
static int u256_is_undef(uint256_t a) { return u256_eq(a, UNDEF_VAL()); }
/* B (axx.py port): centralized "UNDEF-derived" detection.
 * Python raised the threshold from 2^128 to 2^192:
 *   axx legitimately handles up to 256-bit values and 128-bit (quad) floats,
 *   so values >= 2^128 can occur legitimately and must NOT be mistaken for
 *   undefined. Real addresses fit in 64 bits and quad immediates are < 2^128,
 *   so no legitimate value reaches 2^192, while UNDEF (2^256-1) and
 *   UNDEF +/- displacement (~2^256) all have the top 64-bit word (w[3]) set.
 * Using the existing unsigned convention of this file (w[3] != 0  <=>  >= 2^192),
 * this matches axx.py's `v == UNDEF or abs(v) >= 2^192` for the dominant
 * (large-positive, near-2^256) UNDEF-derived case.
 *
 * 破綻点修正2 (axx.py port, ただし本質的な制約あり):
 * axx.pyは任意精度整数なので、番兵UNDEFを2^1024級まで押し上げて実用上
 * 衝突しない安全域を作れた。しかしこのCポートの値は本物の固定幅256bit
 * 整数(uint256_t)であり、型自体が256bitを超える値を表現できないため、
 * 同じ手は使えない。つまり[2^192, 2^256)の範囲(値域の上位1/4)にある
 * 正当な256bit定数(例: 全ビット1のビットマスクや256bit表現の-1)は、
 * 現状のヒューリスティックでは原理的にUNDEF由来と誤判定されうる。
 * この誤判定を型レベルで完全に無くすには値の表現方法自体を変える必要が
 * あり(全呼び出し箇所に影響する非常に大規模な変更になる)、このセッション
 * の修正範囲を超える。ここでは最低限、実際にその境界値域に達したことを
 * 検出できる場合に一度だけ警告し、無警告での誤判定を防ぐに留める。 */
static int u256_is_undef_derived(uint256_t a) {
    if (u256_is_undef(a)) return 1;
    /* 破綻点修正: 以前は符号なしのまま w[3]!=0 (>=2^192) だけを見ていたため、
     * "全く普通の負の値" が軒並み誤判定されていた。uint256_tには符号の
     * 概念が無く、負の値は二の補数表現で符号拡張されるため、上位ワードが
     * 全て1になる点で「巨大な符号なし値」と見分けが付かない。例えば
     * ".equ 0-1"(-1)は全ビット1になり、これはUNDEF自体の値と完全に一致
     * するため u256_is_undef() で検出され、".equ 3-8"(-5)のような他の
     * 小さな負の値も w[3]!=0 の網に掛かって無警告でシンボルテーブルから
     * 消えていた(axx.pyは任意精度の符号付き整数なので abs(v) で正しく
     * 小さいと判定できるが、Cでは符号付き解釈の絶対値を計算して初めて
     * 同じ判定になる)。ここで符号付き絶対値を計算してから閾値と比較する
     * ことで、-1 以外の負の値(実用上ほぼ全て)を正しく「未定義由来ではない」
     * と判定できるようにする。値が厳密に-1(=UNDEFのビットパターンそのもの)
     * である場合だけは、型の値域に本質的な制約があるため区別できない。 */
    int sign = (int)(a.w[3] >> 63);
    uint256_t av = sign ? u256_neg(a) : a;
    if (av.w[3] != 0) {
        static int warned = 0;
        if (!warned) {
            warned = 1;
            fprintf(stderr,
                    " warning - a value whose signed absolute magnitude is >= 2**192 was "
                    "computed and is being treated as UNDEF-derived; this heuristic cannot "
                    "distinguish it from a genuine large 256-bit constant (e.g. an all-ones "
                    "bitmask) because uint256_t has no headroom beyond 256 bits for a true "
                    "out-of-band sentinel.\n");
        }
    }
    return av.w[3] != 0;          /* signed absolute value >= 2^192 */
}

/* =========================================================
 * Dynamic string
 * ========================================================= */
typedef struct {
    char   *buf;
    size_t  len;
    size_t  cap;
} DynStr;

static void ds_init(DynStr *d) { d->buf=NULL; d->len=0; d->cap=0; }
static AXX_UNUSED void ds_free(DynStr *d) { free(d->buf); ds_init(d); }
static void ds_ensure(DynStr *d, size_t need) {
    if (d->cap >= need+1) return;
    size_t nc = (need+1)*2;
    if(nc<32)nc=32;
    d->buf = realloc(d->buf, nc);
    if(!d->buf){perror("realloc");exit(1);}
    d->cap = nc;
}
static AXX_UNUSED void ds_set(DynStr *d, const char *s) {
    size_t l = strlen(s);
    ds_ensure(d, l);
    memcpy(d->buf, s, l+1);
    d->len = l;
}
static AXX_UNUSED void ds_setc(DynStr *d, char c) {
    ds_ensure(d,1);
    d->buf[0]=c; d->buf[1]=0; d->len=1;
}
static AXX_UNUSED void ds_append(DynStr *d, const char *s) {
    size_t l=strlen(s);
    ds_ensure(d, d->len+l);
    memcpy(d->buf+d->len, s, l+1);
    d->len+=l;
}
static AXX_UNUSED void ds_appendc(DynStr *d, char c) {
    ds_ensure(d, d->len+1);
    d->buf[d->len++]=c;
    d->buf[d->len]=0;
}
static AXX_UNUSED const char *ds_get(const DynStr *d) { return d->buf ? d->buf : ""; }

/* =========================================================
 * Dynamic array of uint256_t
 * ========================================================= */
typedef struct {
    uint256_t *data;
    int        len;
    int        cap;
} IntVec;

static void iv_init(IntVec *v) { v->data=NULL; v->len=0; v->cap=0; }
static void iv_free(IntVec *v) { free(v->data); iv_init(v); }
static void iv_push(IntVec *v, uint256_t x) {
    if(v->len>=v->cap){
        v->cap = v->cap ? v->cap*2 : 8;
        v->data = realloc(v->data, v->cap*sizeof(uint256_t));
        if(!v->data){perror("realloc");exit(1);}
    }
    v->data[v->len++]=x;
}
static void iv_clear(IntVec *v) { v->len=0; }
static void iv_copy(IntVec *dst, const IntVec *src) {
    iv_clear(dst);
    for(int i=0;i<src->len;i++) iv_push(dst, src->data[i]);
}
static AXX_UNUSED void iv_append(IntVec *dst, const IntVec *src) {
    for(int i=0;i<src->len;i++) iv_push(dst, src->data[i]);
}

/* =========================================================
 * String vector
 * ========================================================= */
typedef struct {
    char **data;
    int    len;
    int    cap;
} StrVec;
static void sv_init(StrVec *v){v->data=NULL;v->len=0;v->cap=0;}
static void sv_push(StrVec *v, const char *s){
    if(v->len>=v->cap){
        v->cap=v->cap?v->cap*2:8;
        v->data=realloc(v->data,v->cap*sizeof(char*));
        if(!v->data){perror("realloc");exit(1);}
    }
    v->data[v->len++]=strdup(s);
}
static void sv_pop(StrVec *v){
    if(v->len>0){free(v->data[--v->len]);}
}
static AXX_UNUSED void sv_free(StrVec *v){
    for(int i=0;i<v->len;i++)free(v->data[i]);
    free(v->data); sv_init(v);
}

/* =========================================================
 * int vector for file-line stack
 * ========================================================= */
typedef struct { int *data; int len; int cap; } IStack;
static void is_init(IStack*v){v->data=NULL;v->len=0;v->cap=0;}
static void is_push(IStack*v,int x){
    if(v->len>=v->cap){v->cap=v->cap?v->cap*2:8;v->data=realloc(v->data,v->cap*sizeof(int));if(!v->data){perror("realloc");exit(1);}}
    v->data[v->len++]=x;
}
static int is_pop(IStack*v){return v->len>0?v->data[--v->len]:0;}

/* =========================================================
 * Hash map: string -> [uint256_t value, string section]
 * ========================================================= */
#define HASH_INIT_CAP 64

typedef struct LabelEntry {
    char          *key;
    uint256_t      value;
    char          *section;
    int            is_equ;              /* 1 if defined via .equ – not relocatable */
    int            is_imported;         /* 1 if declared via .EXTERN – STB_GLOBAL/SHN_UNDEF in ELF */
    int            reloc_type_override; /* -1 = not set; otherwise ELF relocation type from .EXTERN label::rtype */
    struct LabelEntry *next;
} LabelEntry;

typedef struct {
    LabelEntry **buckets;
    int          nbuckets;
    int          count;
} LabelMap;

static uint32_t hash_str(const char *s) {
    uint32_t h=5381;
    unsigned char c;
    while((c=(unsigned char)*s++)) h=((h<<5)+h)+c;
    return h;
}
static void lmap_init(LabelMap *m) {
    m->nbuckets=HASH_INIT_CAP;
    m->buckets=calloc(m->nbuckets,sizeof(LabelEntry*));
    m->count=0;
}
/* Fix B: reset nbuckets to 0 so any stale use after free is detectable. */
static void lmap_free(LabelMap *m) {
    for(int i=0;i<m->nbuckets;i++){
        LabelEntry *e=m->buckets[i];
        while(e){ LabelEntry*n=e->next; free(e->key); free(e->section); free(e); e=n;}
    }
    free(m->buckets); m->buckets=NULL; m->count=0; m->nbuckets=0;
}
static LabelEntry *lmap_find(LabelMap *m, const char *key) {
    if(!m->nbuckets) return NULL;
    uint32_t h=hash_str(key)%(uint32_t)m->nbuckets;
    for(LabelEntry*e=m->buckets[h];e;e=e->next)
        if(strcmp(e->key,key)==0) return e;
    return NULL;
}
static int lmap_contains(LabelMap *m, const char *key) { return lmap_find(m,key)!=NULL; }
static void lmap_set(LabelMap *m, const char *key, uint256_t val, const char *sec, int is_equ) {
    if(!m->nbuckets) return;
    uint32_t h=hash_str(key)%(uint32_t)m->nbuckets;
    for(LabelEntry*e=m->buckets[h];e;e=e->next){
        if(strcmp(e->key,key)==0){
            e->value=val; free(e->section); e->section=strdup(sec); e->is_equ=is_equ;
            /* axx.py fix: ::reloctype を省略した場合は旧エントリの reloc_type_override を
             * 引き継がず -1 にリセットする。reloc_type が必要な場合は呼び出し側が
             * lmap_set_reloc_type() で明示的に設定する。
             *
             * 破綻点修正 (axx.py port): is_imported は以前「.EXTERNが独立して
             * 管理するので保持する」として引き継いでいたが、これはバグだった。
             * lmap_set() は「この名前に実際の値を設定する」呼び出しであり、
             * .EXTERNで仮登録された名前(is_imported=1)がローカルで実定義
             * されたときは、その時点で輸入(import)状態を終了させなければ
             * ならない。保持し続けると、write_elf_obj() がこのシンボルを
             * 永久にSTB_GLOBAL/SHN_UNDEFとして出力し、ローカルに正しい値を
             * 持つのにELF上では未定義シンボルのままになる
             * (label_put_value() 側でも .EXTERN プレースホルダの上書きを
             * 許可するよう対応済み)。 */
            e->is_imported = 0;
            e->reloc_type_override = -1;
            return;
        }
    }
    LabelEntry *e=calloc(1,sizeof(LabelEntry));
    e->key=strdup(key); e->value=val; e->section=strdup(sec);
    e->is_equ=is_equ; e->is_imported=0; e->reloc_type_override=-1;
    e->next=m->buckets[h]; m->buckets[h]=e; m->count++;
}
/* lmap_set の直後に reloc_type_override を設定するヘルパー。
 * label_put_value() が ::reloctype 付き .equ から呼ぶ。 */
static void lmap_set_reloc_type(LabelMap *m, const char *key, int reloc_type) {
    LabelEntry *e = lmap_find(m, key);
    if(e) e->reloc_type_override = reloc_type;
}
/* Set a label as an imported external symbol (.EXTERN).
 * Mirrors axx.py: labels[s] = [0, '.text', False, True, reloc_type] */
static void lmap_set_imported(LabelMap *m, const char *key, uint256_t val, const char *sec, int reloc_type) {
    uint32_t h=hash_str(key)%(uint32_t)m->nbuckets;
    for(LabelEntry*e=m->buckets[h];e;e=e->next){
        if(strcmp(e->key,key)==0){
            e->value=val; free(e->section); e->section=strdup(sec);
            e->is_equ=0; e->is_imported=1;
            if(reloc_type >= 0) e->reloc_type_override=reloc_type;
            return;
        }
    }
    LabelEntry *e=calloc(1,sizeof(LabelEntry));
    e->key=strdup(key); e->value=val; e->section=strdup(sec);
    e->is_equ=0; e->is_imported=1; e->reloc_type_override=reloc_type;
    e->next=m->buckets[h]; m->buckets[h]=e; m->count++;
}
/* Copy all label fields including is_imported and reloc_type_override. Used for relaxation snapshots. */
static void lmap_set_full(LabelMap *m, const char *key, uint256_t val,
                          const char *sec, int is_equ, int is_imported, int reloc_type_override) {
    uint32_t h=hash_str(key)%(uint32_t)m->nbuckets;
    for(LabelEntry*e=m->buckets[h];e;e=e->next){
        if(strcmp(e->key,key)==0){
            e->value=val; free(e->section); e->section=strdup(sec);
            e->is_equ=is_equ; e->is_imported=is_imported;
            e->reloc_type_override=reloc_type_override;
            return;
        }
    }
    LabelEntry *e=calloc(1,sizeof(LabelEntry));
    e->key=strdup(key); e->value=val; e->section=strdup(sec);
    e->is_equ=is_equ; e->is_imported=is_imported;
    e->reloc_type_override=reloc_type_override;
    e->next=m->buckets[h]; m->buckets[h]=e; m->count++;
}
static AXX_UNUSED void lmap_delete(LabelMap *m, const char *key) {
    uint32_t h=hash_str(key)%(uint32_t)m->nbuckets;
    LabelEntry **pp=&m->buckets[h];
    while(*pp){
        if(strcmp((*pp)->key,key)==0){
            LabelEntry*del=*pp; *pp=del->next;
            free(del->key); free(del->section); free(del); m->count--; return;
        }
        pp=&(*pp)->next;
    }
}
typedef void (*lmap_iter_fn)(const char*key, uint256_t val, const char*sec, void*user);
static AXX_UNUSED void lmap_iter(LabelMap *m, lmap_iter_fn fn, void*user){
    for(int i=0;i<m->nbuckets;i++)
        for(LabelEntry*e=m->buckets[i];e;e=e->next)
            fn(e->key,e->value,e->section,user);
}

/* =========================================================
 * Symbol map: string -> uint256_t
 * ========================================================= */
typedef struct SymEntry { char*key; uint256_t val; struct SymEntry*next; } SymEntry;
typedef struct { SymEntry**buckets; int nb; int count; } SymMap;
static void smap_init(SymMap*m){m->nb=HASH_INIT_CAP;m->buckets=calloc(m->nb,sizeof(SymEntry*));m->count=0;}
static void smap_free(SymMap*m){
    for(int i=0;i<m->nb;i++){SymEntry*e=m->buckets[i];while(e){SymEntry*n=e->next;free(e->key);free(e);e=n;}}
    free(m->buckets);m->buckets=NULL;
}
static SymEntry *smap_find(SymMap*m,const char*key){
    uint32_t h=hash_str(key)%(uint32_t)m->nb;
    for(SymEntry*e=m->buckets[h];e;e=e->next) if(strcmp(e->key,key)==0)return e;
    return NULL;
}
static int smap_get(SymMap*m,const char*key,uint256_t*out){
    SymEntry*e=smap_find(m,key); if(e){*out=e->val;return 1;} return 0;
}
static void smap_set(SymMap*m,const char*key,uint256_t val){
    uint32_t h=hash_str(key)%(uint32_t)m->nb;
    for(SymEntry*e=m->buckets[h];e;e=e->next) if(strcmp(e->key,key)==0){e->val=val;return;}
    SymEntry*e=calloc(1,sizeof(SymEntry)); e->key=strdup(key); e->val=val;
    e->next=m->buckets[h]; m->buckets[h]=e; m->count++;
}
static void smap_delete(SymMap*m,const char*key){
    uint32_t h=hash_str(key)%(uint32_t)m->nb;
    SymEntry**pp=&m->buckets[h];
    while(*pp){ if(strcmp((*pp)->key,key)==0){SymEntry*d=*pp;*pp=d->next;free(d->key);free(d);m->count--;return;} pp=&(*pp)->next; }
}
static void smap_clear(SymMap*m){
    for(int i=0;i<m->nb;i++){
        SymEntry*e=m->buckets[i];
        while(e){SymEntry*n=e->next;free(e->key);free(e);e=n;}
        m->buckets[i]=NULL;
    }
    m->count=0;
}

/* =========================================================
 * Section map: string -> [start uint256_t, size uint256_t]
 * ========================================================= */
typedef struct SecEntry {
    char       *name;
    uint256_t   start;
    uint256_t   size;
    uint256_t   entry_pc;   /* PC at last section entry (for incremental size update) */
    int         confirmed;  /* 1 = size set by .ENDSECTION, do not overwrite */
    struct SecEntry *next;
} SecEntry;
typedef struct { SecEntry**buckets; int nb; SecEntry**order; int count; int cap; } SecMap;
static void secmap_init(SecMap*m){m->nb=16;m->buckets=calloc(m->nb,sizeof(SecEntry*));m->count=0;m->cap=16;m->order=calloc(m->cap,sizeof(SecEntry*));}
static SecEntry *secmap_find(SecMap*m,const char*name){
    uint32_t h=hash_str(name)%(uint32_t)m->nb;
    for(SecEntry*e=m->buckets[h];e;e=e->next) if(strcmp(e->name,name)==0)return e;
    return NULL;
}
static void secmap_set(SecMap*m,const char*name,uint256_t start,uint256_t size){
    SecEntry*e=secmap_find(m,name);
    if(e){e->start=start;e->size=size;return;}
    uint32_t h=hash_str(name)%(uint32_t)m->nb;
    e=calloc(1,sizeof(SecEntry)); e->name=strdup(name); e->start=start; e->size=size;
    e->entry_pc=start; e->confirmed=0;
    e->next=m->buckets[h]; m->buckets[h]=e;
    if(m->count>=m->cap){
        m->cap*=2;
        SecEntry**tmp=realloc(m->order,m->cap*sizeof(SecEntry*));
        if(!tmp){perror("realloc");exit(1);}
        m->order=tmp;
    }
    m->order[m->count++]=e;
}
static AXX_UNUSED void secmap_free(SecMap*m){
    for(int i=0;i<m->nb;i++){
        SecEntry*e=m->buckets[i];
        while(e){SecEntry*n=e->next;free(e->name);free(e);e=n;}
        m->buckets[i]=NULL;
    }
    free(m->buckets); free(m->order);
    m->buckets=NULL; m->order=NULL; m->count=0; m->cap=0; m->nb=0;
}
/* Fix C: zero out freed pointers in order[] so they cannot be dereferenced.
 * Previously the order[] array retained dangling pointers even after entries
 * were freed; any code path that iterated up to the old count would crash. */
static void secmap_clear(SecMap*m){
    for(int i=0;i<m->nb;i++){
        SecEntry*e=m->buckets[i];
        while(e){SecEntry*n=e->next;free(e->name);free(e);e=n;}
        m->buckets[i]=NULL;
    }
    /* Null out stale pointers in the ordering array */
    for(int i=0;i<m->count;i++) m->order[i]=NULL;
    m->count=0;
}

/* 破綻点修正 (axx.py port): 各セクションへの訪問記録(名前, 開始pc,
 * ワード数)を時系列順に保持する。同じセクションに複数回出入りすると
 * (.text→.data→.text等)、真の内容はグローバルpc空間上で不連続な複数の
 * 断片に分かれる。write_elf_obj()相当のコードはこれを使って各断片を
 * 訪問順に連結し、アドレス→セクション内オフセットの変換も断片ごとの
 * 累積オフセットを使って正しく計算する。 */
typedef struct { char *name; uint256_t start; uint256_t len; } SecRange;
typedef struct { SecRange *data; int len; int cap; } SecRangeVec;
AXX_UNUSED static void secrangevec_init(SecRangeVec*v){v->data=NULL;v->len=0;v->cap=0;}
static void secrangevec_push(SecRangeVec*v, const char*name, uint256_t start, uint256_t len){
    if(v->len>=v->cap){
        v->cap = v->cap ? v->cap*2 : 8;
        SecRange *_tmp = realloc(v->data, (size_t)v->cap*sizeof(SecRange));
        if(!_tmp){ perror("realloc"); exit(1); }
        v->data = _tmp;
    }
    v->data[v->len].name = strdup(name);
    v->data[v->len].start = start;
    v->data[v->len].len = len;
    v->len++;
}
static void secrangevec_clear(SecRangeVec*v){
    for(int i=0;i<v->len;i++) free(v->data[i].name);
    v->len = 0;
}
AXX_UNUSED static void secrangevec_free(SecRangeVec*v){
    secrangevec_clear(v);
    free(v->data); v->data=NULL; v->cap=0;
}
/* word_pc がセクション name 内のどこに対応するか、断片を跨いだ累積ワード
 * オフセットを返す。属さない場合は -1 を返す(u256_to_i64(-1)と衝突しない
 * ようcallerはint型で受ける)。上限は閉区間(<=)で判定する: セクション末尾
 * ちょうど(そのセクションの最後に書かれたバイトの1つ先)を指す「終端
 * マーカー」ラベル(_etext的なもの)は正当なイディオムなので、境界値を
 * 除外する理由はない。 */
static int64_t addr_to_word_offset(SecRangeVec*ranges, const char*name, uint64_t word_pc){
    uint64_t cum = 0;
    for(int i=0;i<ranges->len;i++){
        if(strcmp(ranges->data[i].name,name)!=0) continue;
        uint64_t rs = u256_to_u64(ranges->data[i].start);
        uint64_t rl = u256_to_u64(ranges->data[i].len);
        if(word_pc >= rs && word_pc <= rs+rl) return (int64_t)(cum + (word_pc-rs));
        cum += rl;
    }
    return -1;
}

/* Finalize the current (last) section's size after fileassemble() completes.
 * Mirrors axx.py run():
 *   _last_sec = self.state.current_section
 *   if _last_sec in self.state.sections:
 *       _e = self.state.sections[_last_sec]
 *       if not _confirmed: _e[1] += (pc - entry_pc)
 * Must be called after every fileassemble() — relaxation passes and pass2. */
/* Note: AsmState is defined later; this function is defined after AsmState below. */
/* Forward declaration: */

/* =========================================================
 * Pattern: each entry has 6 string fields
 * ========================================================= */
#define PAT_FIELDS 6
typedef struct {
    char *f[PAT_FIELDS];
} PatEntry;

typedef struct {
    PatEntry *data;
    int       len;
    int       cap;
} PatVec;

static void pv_init(PatVec*v){v->data=NULL;v->len=0;v->cap=0;}
static PatEntry *pv_push_blank(PatVec*v){
    if(v->len>=v->cap){v->cap=v->cap?v->cap*2:32;v->data=realloc(v->data,v->cap*sizeof(PatEntry));if(!v->data){perror("realloc");exit(1);}}
    PatEntry *e=&v->data[v->len++];
    for(int i=0;i<PAT_FIELDS;i++) e->f[i]=strdup("");
    return e;
}
static AXX_UNUSED void pv_free(PatVec*v){
    for(int i=0;i<v->len;i++) for(int j=0;j<PAT_FIELDS;j++) free(v->data[i].f[j]);
    free(v->data); pv_init(v);
}
static void pat_set(PatEntry*e,int idx,const char*s){
    free(e->f[idx]); e->f[idx]=strdup(s);
}

/* =========================================================
 * VLIW set entry: int array + template string
 * ========================================================= */
typedef struct {
    int   *idxs;
    int    nidxs;
    char  *templ;
} VliwSetEntry;

typedef struct {
    VliwSetEntry *data;
    int           len;
    int           cap;
} VliwSet;

static void vset_init(VliwSet*v){v->data=NULL;v->len=0;v->cap=0;}
static AXX_UNUSED void vset_free(VliwSet*v){
    for(int i=0;i<v->len;i++){free(v->data[i].idxs);free(v->data[i].templ);}
    free(v->data);vset_init(v);
}
static void vset_clear(VliwSet*v){
    for(int i=0;i<v->len;i++){free(v->data[i].idxs);free(v->data[i].templ);}
    v->len=0;
}
static void vset_add(VliwSet*v,int*idxs,int n,const char*templ){
    for(int i=0;i<v->len;i++){
        if(v->data[i].nidxs==n && memcmp(v->data[i].idxs,idxs,n*sizeof(int))==0
           && strcmp(v->data[i].templ,templ)==0) return;
    }
    if(v->len>=v->cap){v->cap=v->cap?v->cap*2:8;v->data=realloc(v->data,v->cap*sizeof(VliwSetEntry));if(!v->data){perror("realloc");exit(1);}}
    v->data[v->len].idxs=malloc(n*sizeof(int));
    memcpy(v->data[v->len].idxs,idxs,n*sizeof(int));
    v->data[v->len].nidxs=n;
    v->data[v->len].templ=strdup(templ);
    v->len++;
}

/* =========================================================
 * Binary output buffer: position -> byte value
 * ========================================================= */
typedef struct BufEntry { uint64_t pos; uint64_t val; struct BufEntry*next; } BufEntry;
#define BUFMAP_NB 4096
typedef struct { BufEntry *buckets[BUFMAP_NB]; } BufMap;

static void bufmap_init(BufMap*m){ memset(m->buckets,0,sizeof(m->buckets)); }
static void bufmap_set(BufMap*m, uint64_t pos, uint64_t val){
    uint32_t h=(uint32_t)(pos % BUFMAP_NB);
    for(BufEntry*e=m->buckets[h];e;e=e->next) if(e->pos==pos){e->val=val;return;}
    BufEntry*e=malloc(sizeof(BufEntry)); if(!e){perror("malloc");exit(1);} e->pos=pos; e->val=val;
    e->next=m->buckets[h]; m->buckets[h]=e;
}
/* Fix (new): bufmap_max_key now writes the found flag into *found_out so that
 * binary_flush can distinguish "no bytes written" from "one byte at position 0".
 * The old signature returned 0 for both cases, silently writing a one-word file
 * even when the assembler produced no output at all. */
static uint64_t bufmap_max_key(BufMap*m, int *found_out){
    uint64_t mx=0; int found=0;
    for(int i=0;i<BUFMAP_NB;i++) for(BufEntry*e=m->buckets[i];e;e=e->next){
        if(!found||e->pos>mx){mx=e->pos;found=1;}
    }
    if(found_out) *found_out=found;
    return found?mx:0;
}
static AXX_UNUSED void bufmap_free(BufMap*m){
    for(int i=0;i<BUFMAP_NB;i++){BufEntry*e=m->buckets[i];while(e){BufEntry*n=e->next;free(e);e=n;}m->buckets[i]=NULL;}
}

/* =========================================================
 * AssemblerState
 * ========================================================= */
#define OB_CHAR  ((char)0x90)
#define CB_CHAR  ((char)0x91)
#define EXP_PAT  0
#define EXP_ASM  1

static const char *ERRORS_TABLE[] = {
    "",                          /* 0 – empty (Python ERRORS[0]) */
    "Invalid syntax.",           /* 1 */
    "Address out of range.",     /* 2 */
    "Value out of range.",       /* 3 */
    "",                          /* 4 – empty */
    "Register out of range.",    /* 5 */
    "Port number out of range."  /* 6 */
};
#define ERRORS_COUNT 7

typedef struct {
    char outfile[512];
    char expfile[512];
    char expfile_elf[512];   /* -E option: ELF-format export TSV */
    char impfile[512];
    int  osabi;

    uint256_t pc;
    uint256_t padding;

    char lwordchars[256];
    char swordchars[256];

    char current_section[512];
    char current_file[512];

    LabelMap   labels;
    SecMap     sections;
    SymMap     symbols;
    SymMap     patsymbols;
    LabelMap   export_labels;
    PatVec     pat;

    int        vliwinstbits;
    IntVec     vliwnop;
    int        vliwbits;
    VliwSet    vliwset;
    int        vliwflag;
    int        vliwtemplatebits;
    int        vliwstop;
    int        vcnt;

    int        expmode;
    /* exp_typ_float: 0 = integer mode (default), 1 = floating-point mode.
     * When 1, number literals are parsed as double and arithmetic operations
     * (+, -, *, /, **) are performed in double precision.  The double value
     * is carried inside uint256_t.w[0] as a raw bit-cast.
     * Mirrors axx.py AssemblerState.exp_typ ('i' vs 'f'). */
    int        exp_typ_float;
    int        error_undefined_label;
    int        error_already_defined;
    /* axx.py port (bugfix): persistent, never auto-reset per-line, unlike
     * error_undefined_label/error_already_defined above. Set once and left
     * set for the rest of the run whenever a user-facing " error - ..." is
     * actually reported during assembly. main() checks this after pass2 to
     * refuse to write output for a build that printed errors, instead of
     * silently exiting 0 with incomplete/wrong bytes. */
    int        had_error;
    /* axx.py port: パターンマッチ試行中フラグ。
     * match0() → match() → expression キャプチャ → label_get_value() の経路で
     * 失敗試行中のラベル未定義エラー表示を抑制する。
     * match0() が True を返した後の makeobj() 呼び出し前に 0 に戻す。 */
    int        in_match_attempt;

    /* 順序非依存マッチング (axx.py port): 直近の pat_match() 成功時の
     * 具体度スコア。(式キャプチャ数, シンボルキャプチャ数, リテラル一致文字数)。
     * lineassemble2() が全パターン走査後に最も具体的なマッチを選ぶために使う。 */
    int        match_score_expr;
    int        match_score_sym;
    int        match_score_lit;

    /* pc_instr_start: binary_list中の$$が命令先頭アドレスを指すように、
     * makeobj呼び出し前にst->pcの値を保存する。makeobj内のexpression評価では
     * st->pcではなくst->pc_instr_startを$$として使う。 */
    uint256_t  pc_instr_start;
    /* pc_instr_end: $.が返す「命令末尾(次命令の先頭)アドレス」。
     * パターンマッチ確定後・error()/makeobj()呼び出し前のサイズプローブで確定する。
     * binary_list中/外・pass0(対話モード)を問わず常にこの値を返す。 */
    uint256_t  pc_instr_end;
    /* in_binary_list: makeobj実行中は1。$$がpc_instr_startを返すのは
     * binary_list評価中のみ。.equなど他のコンテキストでは$$=現在のPC。 */
    int        in_binary_list;

    int        align;
    int        bts;
    int        endian_big;
    int        pas;
    int        debug;
    /* 互換(axx.py port): axx.py は verbose(-v: pass2のhexリスト出力) と
     * debug(-d: リラクゼーション収束等のデバッグ出力) を別フラグとして持つ。
     * C版は両者を debug に統合し -v に割り当てていたため挙動が非互換だった。
     * verbose を分離して axx.py に一致させる。 */
    int        verbose;

    char       cl[4096];
    int        ln;
    StrVec     fnstack;
    IStack     lnstack;

    uint256_t  vars[26];

    char deb1[4096];
    char deb2[4096];

    BufMap     buf;

    /* Fix C-3: Pass1 size-estimation mode.
     * When true, label_get_value() returns 0 for unknown labels instead of
     * UNDEF_VAL().  This lets makeobj() compute the correct byte count even
     * when a forward-referenced label is not yet defined. */
    int        pass1_size_mode;

    /* Fix C-6: per-process stdin temp file path (replaces fixed "axx.tmp").
     * NULL until first stdin read; freed and unlinked at the end of run(). */
    char       stdin_tmp_path[512];

    /* ELF relocatable object output (-o / -m options) */
    char       elf_objfile[512];
    int        elf_machine;   /* default 62 = EM_X86_64 */

    /* DWARF debug info generation (-g).
     * When gen_debug && elf_objfile is set, write_elf_obj() emits
     * .debug_abbrev / .debug_info / .debug_line (+ .rela.debug_*). */
    int        gen_debug;
    /* line_map: during pass2, for every assembly line that emits bytes we
     * record (section, word_pc_at_line_start, file, line). It is the source
     * data for the DWARF .debug_line line-number program. Reset at pass2
     * start; section/file strings are strdup'd and freed in run(). */
    struct { char *section; uint64_t word_pc; char *file; int line; } *line_map;
    int        line_map_len;
    int        line_map_cap;

    /* ELF relocation tracking (active during pass2 when elf_objfile is set) */
    int        elf_tracking;                /* 1 while assembling one instruction */
    /* dynamic array of refs seen in current insn: (name, val, word_idx)
     * word_idx = index into objl at which the reference was made (-1 = outside makeobj) */
    struct { char *name; uint64_t val; int word_idx; } *elf_refs;
    int        elf_refs_len;
    int        elf_refs_cap;
    /* makeobj() word-index sentinel: set to len(objl) before each expr eval,
     * -1 outside makeobj (sentinel). */
    int        elf_current_word_idx;
    /* variable -> label mapping captured during match() !var evaluation.
     * Indexed by var letter - 'a'.
     * set=0: unset  set=1: valid  set=-1: conflict (compound expr) */
    struct {
        int      set;
        char    *label_name;
        uint64_t label_val;
    }          elf_var_to_label[26];
    /* current variable being captured by match() !var; '\0' = not capturing */
    char       elf_capturing_var;
    /* accumulated relocations across all of pass2 */
    struct {
        char   *section;
        int64_t sec_offset;
        char   *sym;
        int     rtype;
        int64_t addend;
        int     nbytes;  /* encoded field byte width; needed for REL (non-RELA)
                           * targets to patch the addend directly into the
                           * relocated field's bytes -- see write_elf_obj(). */
    } *relocations;
    int        reloc_count;
    int        reloc_cap;

    /* Source-file `.RELOCTYPE` directive: per-encoded-field-width override
     * of this machine's built-in default width-guess reloc type
     * (elf_machine_width_guess()). Index 0/1/2/3 corresponds to encoded
     * field widths of 1/2/4/8 bytes; -1 = not overridden (fall back to the
     * machine's built-in wg1/wg2/wg4/wg8). Mirrors axx.py's
     * state.reloctype_override dict; see adir_reloctype() and its
     * consultation at the RTYPE_FOR() width-guess lookup. */
    int        reloctype_override[4];

    /* .check 拘束条件テーブル (変数 a-z に対応する 26 要素配列)。
     * check_constraints[i] は変数 'a'+i に対する許可シンボル名の StrVec。
     * 空 StrVec (len==0) はその変数に拘束なし。
     * .check::x::sym1,sym2,... で登録、.clrcheck::x で解除。
     * マッチ成功後・makeobj 前に pat_match() 内でインライン検証する。    */
    StrVec     check_constraints[26];

    /* C (axx.py port): expression recursion depth guard.
     * C has no exceptions; unbounded recursion (deeply nested parentheses or
     * unary operators) would overflow the native stack and segfault.
     * expr_factor() increments this on entry and decrements on exit, returning
     * 0 once EXPR_MAX_DEPTH is exceeded. */
    int        expr_depth;

    /* A (axx.py port): pass1 relaxation previous-iteration label values.
     * Points to the previous iteration's label snapshot during pass1 so that
     * forward references return a realistic estimate (their prior address)
     * instead of 0/UNDEF. This lets relaxation actually converge to the
     * optimal variable-length layout. NULL outside the pass1 relaxation loop. */
    LabelMap  *relax_prev;

    /* D8 (axx.py port): pattern-file .INCLUDE chain (canonical paths) for
     * circular-include detection, plus the current nesting depth. */
    char      *pat_include_chain[64];
    int        pat_include_depth;

    /* 破綻点修正5 (axx.py port): pat_match0()の組合せ数予算を使い切った
     * ことを警告済みかどうか。
     *
     * 破綻点修正 (再修正): 以前は単一のint(0/1)フラグだったため、パターン
     * ファイル中の複数箇所で組合せ爆発が起きても最初の1箇所しか警告が出ず、
     * 2箇所目以降は原因不明のまま「非マッチ」として静かに扱われていた
     * (axx.py側の同種の問題と合わせて修正)。ファイル名+行番号の組を
     * 最大64件までキャッシュし、「同じ箇所での繰り返し警告は1回に抑える」
     * という当初の意図を保ったまま、異なる箇所ではそれぞれ独立して1回ずつ
     * 警告できるようにする。キャッシュが溢れた場合は安全側(警告を出す側)
     * に倒す。 */
    char       combo_budget_warned_file[64][512];
    int        combo_budget_warned_line[64];
    int        combo_budget_warned_count;

    /* 破綻点修正 (axx.py port): 各セクションへの訪問記録(SecRangeVec参照)。
     * write_elf_obj相当のELF出力コードがこれを使って複数回の出入りで
     * 生じた不連続な断片を正しく連結・アドレス変換する。 */
    SecRangeVec section_ranges;

    /* 破綻点修正 (axx.py port): .EQU(reloc_type指定なし)の式評価中に1に
     * しておくと、label_get_value()が参照したラベルの所属セクションを
     * ここに記録する(tracking=0のときは何もしない)。異なるセクションの
     * ラベルを跨いで演算すると、結果はリンク時のセクション配置に依存する
     * 定数になってしまうにもかかわらずリロケーションが一切生成されない
     * ため、adir_label_processing()がこれを見て警告する。 */
    int        equ_section_tracking;
    char       equ_first_section[64];
    int        equ_multi_section;
} AsmState;

/* 破綻点修正7 (axx.py port): 「ユーザー向けエラーを表示すべきパスか」の
 * 判定 (pas==0:対話モード, pas==2:Pass2) が全体で16箇所に条件式として
 * 直書きされており、新しいpas値を追加する際の修正漏れの温床になって
 * いた。1箇所のヘルパーに集約する(axx.py側のAssemblerState.should_report_errors()
 * と対応)。 */
static inline int should_report_errors(const AsmState *st) {
    return st->pas == 2 || st->pas == 0;
}

/* =========================================================
 * ELF_MACHINES: consolidated per-e_machine relocation tables.
 *
 * axx.py port: this mirrors axx.py's ELF_MACHINES dict (top of axx.py)
 * exactly -- same architectures, same relocation-type numbers, same
 * width-guess/pc-relative/named-override/dwarf_abs/is_rela semantics. It
 * replaces what used to be 8 independently-maintained scattered
 * tables/branches in this file (the `.EQU`/`.EXTERN`/`-i` import/`-E`
 * export named-reloctype maps, the width->rtype `_rm[]` table, the
 * PC-relative classification branch, the absolute-rtype reclassification
 * guard, and the DWARF abs64 ternary) -- a 12th architecture now only
 * needs one new entry here instead of edits at 8 call sites.
 *
 * `named` is `{symbolic name usable in a "::name" override: reloc type,
 * expected encoded field byte width}` -- the single source of truth for
 * `.EXTERN`/`.EQU`/the `-i` import syntax's `::reloctype` overrides *and*
 * the reverse lookup `-E` export uses to print a symbolic name; the width
 * is what an override's field-width sanity check validates against.
 *
 * `is_rela` says whether this machine's psABI stores relocation addends
 * explicitly (RELA: separate addend field, `.rela.NAME` sections, SHT_RELA)
 * or implicitly (REL: no addend field -- baked directly into the relocated
 * field's bytes instead, `.rel.NAME` sections, SHT_REL). i386's REL
 * convention was confirmed against a real `gcc -m32`-produced object file;
 * the rest are this port's best-effort read of documented psABI
 * conventions, unverified against a real cross-linker for either file --
 * flag any that turn out wrong.
 * ========================================================= */
typedef struct { const char *name; int rtype; int width; } ElfNamedReloc;

typedef struct {
    int         machine;
    const char *name;
    int         elfclass;      /* 1 = ELFCLASS32, 2 = ELFCLASS64 */
    int         is_rela;       /* 1 = RELA (explicit addend), 0 = REL (implicit) */
    int         extern_default;
    int         dwarf_abs;
    /* Default-guess reloc type for an auto-detected label reference of
     * this many encoded bytes, when no explicit `::reloctype` override was
     * given; 0 = no entry for that width (no relocation emitted). */
    int         wg8, wg4, wg2, wg1;
    const int  *pc_rel;        /* reloc-type numbers that are PC-relative */
    int         pc_rel_n;
    const ElfNamedReloc *named; /* name==NULL terminated */
} ElfMachineInfo;

static const int _pcrel_i386[]    = {2, 13, 21, 23};
static const int _pcrel_m68k[]    = {4, 5, 6};
static const int _pcrel_ppc32[]   = {10, 26};
static const int _pcrel_ppc64[]   = {10, 26, 44};
static const int _pcrel_s390x[]   = {5, 16, 23};
static const int _pcrel_arm[]     = {1, 3};
static const int _pcrel_sh[]      = {2};
static const int _pcrel_sparcv9[] = {4, 5, 6, 46};
static const int _pcrel_x86_64[]  = {2, 4, 9, 13, 15, 24};
static const int _pcrel_aarch64[] = {260, 261, 262};

static const ElfNamedReloc _named_i386[] = {
    {"abs32", 1, 4}, {"pc32", 2, 4}, {"rel32", 2, 4},
    {"got32", 3, 4}, {"plt32", 4, 4},
    {"gotoff", 9, 4}, {"gotpc", 10, 4},
    {"abs16", 20, 2}, {"pc16", 21, 2},
    {"abs8", 22, 1}, {"pc8", 23, 1},
    {NULL, 0, 0},
};
static const ElfNamedReloc _named_m68k[] = {
    {"abs32", 1, 4}, {"abs16", 2, 2}, {"abs8", 3, 1},
    {"pc32", 4, 4}, {"rel32", 4, 4},
    {"pc16", 5, 2}, {"pc8", 6, 1},
    {NULL, 0, 0},
};
static const ElfNamedReloc _named_ppc32[] = {
    {"abs32", 1, 4}, {"abs16", 3, 2}, {"abs16lo", 4, 2},
    {"abs16hi", 5, 2}, {"abs16ha", 6, 2},
    {"pc32", 26, 4}, {"rel32", 26, 4},
    {"pc24", 10, 4}, {"rel24", 10, 4},
    {NULL, 0, 0},
};
static const ElfNamedReloc _named_ppc64[] = {
    {"abs64", 38, 8}, {"abs32", 1, 4},
    {"abs16", 3, 2}, {"abs16lo", 4, 2},
    {"abs16hi", 5, 2}, {"abs16ha", 6, 2},
    {"pc64", 44, 8}, {"rel64", 44, 8},
    {"pc32", 26, 4}, {"rel32", 26, 4},
    {"pc24", 10, 4}, {"rel24", 10, 4},
    {NULL, 0, 0},
};
static const ElfNamedReloc _named_s390x[] = {
    {"abs64", 22, 8}, {"abs32", 4, 4}, {"abs16", 3, 2}, {"abs8", 1, 1},
    {"pc64", 23, 8}, {"pc32", 5, 4}, {"rel32", 5, 4}, {"pc16", 16, 2},
    {NULL, 0, 0},
};
static const ElfNamedReloc _named_arm[] = {
    {"abs32", 2, 4}, {"pc24", 1, 4},
    {"pc32", 3, 4}, {"rel32", 3, 4},
    {"abs16", 5, 2}, {"abs12", 6, 4}, {"abs8", 8, 1},
    {NULL, 0, 0},
};
static const ElfNamedReloc _named_sh[] = {
    {"abs32", 1, 4}, {"pc32", 2, 4}, {"rel32", 2, 4},
    {NULL, 0, 0},
};
static const ElfNamedReloc _named_sparcv9[] = {
    {"abs64", 32, 8}, {"abs32", 3, 4}, {"abs16", 2, 2}, {"abs8", 1, 1},
    {"pc64", 46, 8}, {"rel64", 46, 8},
    {"pc32", 6, 4}, {"rel32", 6, 4},
    {"pc16", 5, 2}, {"pc8", 4, 1},
    {NULL, 0, 0},
};
static const ElfNamedReloc _named_x86_64[] = {
    {"abs64", 1, 8}, {"abs32", 10, 4}, {"abs32s", 11, 4},
    {"abs16", 12, 2}, {"abs8", 14, 1},
    {"pc32", 2, 4}, {"rel32", 2, 4}, {"plt32", 4, 4},
    {"pc16", 13, 2}, {"pc8", 15, 1}, {"pc64", 24, 8},
    {"got32", 3, 4}, {"gotpcrel", 9, 4}, {"got64", 27, 8},
    {NULL, 0, 0},
};
static const ElfNamedReloc _named_aarch64[] = {
    {"abs64", 257, 8}, {"abs32", 258, 4}, {"abs16", 259, 2},
    {"pc64", 260, 8}, {"rel64", 260, 8},
    {"pc32", 261, 4}, {"rel32", 261, 4},
    {"pc16", 262, 2}, {"rel16", 262, 2},
    {NULL, 0, 0},
};
static const ElfNamedReloc _named_riscv[] = {
    /* abs16/abs8 (34/33) reproduce this assembler's pre-existing
     * width-guess numbering as-is; unlike the other entries here they are
     * not independently confirmed against psABI documentation (RISC-V's
     * base spec does not define a plain absolute 16-/8-bit relocation the
     * way most other ISAs do) -- treat those two specifically as
     * low-confidence. */
    {"abs64", 2, 8}, {"abs32", 1, 4}, {"abs16", 34, 2}, {"abs8", 33, 1},
    {NULL, 0, 0},
};

static const ElfMachineInfo ELF_MACHINES[] = {
    /* EM_386: confirmed REL (not RELA) against a real `gcc -m32` object. */
    {3,   "i386",      1, 0, 2,   1,   0,  2, 20, 22, _pcrel_i386,    4, _named_i386},
    {4,   "m68k",       1, 1, 4,   1,   0,  4,  2,  3, _pcrel_m68k,    3, _named_m68k},
    {20,  "PowerPC",    1, 1, 26,  1,   0, 26,  4,  0, _pcrel_ppc32,   2, _named_ppc32},
    {21,  "PowerPC64",  2, 1, 26,  38,  38,26,  4,  0, _pcrel_ppc64,   3, _named_ppc64},
    {22,  "s390x",      2, 1, 5,   22,  22, 5,  3,  1, _pcrel_s390x,   3, _named_s390x},
    {40,  "ARM",        1, 0, 3,   2,   0,  3,  4,  8, _pcrel_arm,     2, _named_arm},
    {42,  "SuperH",     1, 1, 2,   1,   0,  2,  0,  0, _pcrel_sh,      1, _named_sh},
    {43,  "SPARCV9",    2, 1, 6,   32,  32,  6,  2,  1, _pcrel_sparcv9, 4, _named_sparcv9},
    {62,  "x86-64",     2, 1, 2,   1,   1,  2, 12, 14, _pcrel_x86_64,  6, _named_x86_64},
    {183, "AArch64",    2, 1, 261, 257, 257,261,262,  0, _pcrel_aarch64, 3, _named_aarch64},
    {243, "RISC-V",     2, 1, 1,   2,   2,  1, 34, 33, NULL,           0, _named_riscv},
};
#define ELF_MACHINES_N ((int)(sizeof(ELF_MACHINES)/sizeof(ELF_MACHINES[0])))

static const ElfMachineInfo *elf_machine_find(int machine){
    for(int i=0;i<ELF_MACHINES_N;i++)
        if(ELF_MACHINES[i].machine == machine) return &ELF_MACHINES[i];
    return NULL;
}

/* {name}::reloctype -> reloc type number, or -1 if unknown for this machine. */
static int elf_machine_named(const ElfMachineInfo *m, const char *name){
    if(!m) return -1;
    for(int i=0; m->named[i].name; i++)
        if(strcasecmp(m->named[i].name, name)==0) return m->named[i].rtype;
    return -1;
}

/* reloc type number -> its first matching symbolic name, or NULL. */
static const char *elf_machine_reverse(const ElfMachineInfo *m, int rtype){
    if(!m) return NULL;
    for(int i=0; m->named[i].name; i++)
        if(m->named[i].rtype == rtype) return m->named[i].name;
    return NULL;
}

/* reloc type number -> its expected encoded field byte width, or 0 if
 * this machine has no named entry for that number (override validation
 * then can't check it and accepts it as-is, mirroring axx.py). */
static int elf_machine_reloc_bytes(const ElfMachineInfo *m, int rtype){
    if(!m) return 0;
    for(int i=0; m->named[i].name; i++)
        if(m->named[i].rtype == rtype) return m->named[i].width;
    return 0;
}

static int elf_machine_is_pcrel(const ElfMachineInfo *m, int rtype){
    if(!m) return 0;
    for(int i=0;i<m->pc_rel_n;i++) if(m->pc_rel[i]==rtype) return 1;
    return 0;
}

static int elf_machine_width_guess(const ElfMachineInfo *m, int nbytes){
    if(!m) return 0;
    switch(nbytes){
        case 8: return m->wg8;
        case 4: return m->wg4;
        case 2: return m->wg2;
        case 1: return m->wg1;
        default: return 0;
    }
}

/* Like elf_machine_width_guess(), but first consults the source file's
 * `.RELOCTYPE` directive override (st->reloctype_override), if any was set
 * for this width; falls back to the machine's built-in default otherwise.
 * Mirrors axx.py's `{**width_guess, **state.reloctype_override}` merge at
 * the same call site (ObjectGenerator.makeobj()). */
static int reloctype_for(const AsmState *st, const ElfMachineInfo *m, int nbytes){
    int idx;
    switch(nbytes){
        case 1: idx=0; break;
        case 2: idx=1; break;
        case 4: idx=2; break;
        case 8: idx=3; break;
        default: idx=-1; break;
    }
    if(idx>=0 && st->reloctype_override[idx]>=0) return st->reloctype_override[idx];
    return elf_machine_width_guess(m, nbytes);
}

/* Finalize the current (last) section's size after fileassemble() completes.
 * adir_section() only updates the OLD section on switch; the final section is
 * never switched away from and stays at size=0.
 * Mirrors axx.py run() post-fileassemble logic for both pass1 and pass2. */
static void secmap_finalize_current(AsmState *st){
    SecEntry *e = secmap_find(&st->sections, st->current_section);
    if(!e) return;
    /* Bugfix (axx.py port): do NOT skip just because `confirmed` is set.
     * entry_pc is always advanced to the current pc at the moment a
     * fragment is flushed (here or in adir_endsection()/adir_section()),
     * so a fresh delta of 0 already makes this a safe no-op post-ENDSECTION.
     * But if more code ran in this section *after* that ENDSECTION (with no
     * intervening .SECTION), entry_pc is still behind pc and `confirmed`
     * would incorrectly suppress flushing that trailing fragment, silently
     * dropping it from section_ranges/the final output. */
    uint256_t delta = u256_sub(st->pc, e->entry_pc);
    if(u256_lt_signed(delta, u256_zero())) return;   /* negative delta: skip */
    e->size = u256_add(e->size, delta);
    if(!u256_is_zero(delta))
        secrangevec_push(&st->section_ranges, st->current_section, e->entry_pc, delta);
    e->entry_pc = st->pc;   /* prevent double-counting on re-call */
}

/* DWARF .debug_line生成用の小さなヘルパー: word_pc をセクションsec_name内の
 * バイトオフセットに変換する(断片を跨いだ累積オフセット)。該当する断片が
 * 見つからない場合は0にフォールバックする(DWARF生成自体をクラッシュ
 * させないため)。 */
static uint64_t dwarf_word_offset(AsmState *st, const char *sec_name, uint64_t word_pc, int bpw){
    int64_t o = addr_to_word_offset(&st->section_ranges, sec_name, word_pc);
    return (uint64_t)(o >= 0 ? o : 0) * (uint64_t)bpw;
}

/* 破綻点修正 (axx.py port): .EQU(reloc_type未指定)は最終的な定数として
 * そのままバイナリに焼き込まれ、後からリンカが補正することはない。一方
 * ラベルの値は「アセンブル全体を通した生のグローバルpc」で保持されて
 * おり、同じセクションに複数回出入りした場合(.text→.data→.text等)、
 * 出力ファイル上では断片が詰めて連結されるのに対し生pcは間に挟まった
 * 他セクション分だけ余分にズレたままになる。そのため「同じセクション内
 * の2ラベルの差分」のような計算が、セクション再入があると無警告で
 * 誤った値になっていた。実際の出力ファイルでの位置であるセクション内
 * 相対オフセットに変換する。section_rangesにまだ記録が無い場合(参照
 * している時点でまだ開いている現在のセクション)はst->sectionsの
 * (開始, 現在までのサイズ)にフォールバックする(axx.pyの
 * _section_word_ranges()と同じ)。解決できない場合は元の値をそのまま
 * 返す合図として-1を返す。 */
static int64_t equ_section_relative_offset(AsmState *st, const char *sec_name, uint64_t word_pc){
    int64_t o = addr_to_word_offset(&st->section_ranges, sec_name, word_pc);
    if(o >= 0) return o;
    /* 破綻点修正 (axx.py port): $$(現在pc)は、命令をエンコード中の「今
     * まさに開いていてまだ.ENDSECTION/セクション切替で確定していない
     * 断片」を指すことがほとんどだが、その断片はまだsection_rangesに
     * 乗っていない。size>0(=既に確定済みの累積サイズがある)を要求する
     * だけでは、現在オープン中の断片の途中にあるword_pcを解決できず
     * -1を返してしまい、$$を使うPC相対エンコード式が常に補正不能に
     * なっていた。entry_pc(直近の再入位置)以降かどうかを追加でチェック
     * し、確定済み累積(e->size)にその断片内オフセットを足して返す。 */
    SecEntry *e = secmap_find(&st->sections, sec_name);
    if(e){
        uint64_t entry_pc = u256_to_u64(e->entry_pc);
        uint64_t completed = u256_to_u64(e->size);
        if(word_pc >= entry_pc) return (int64_t)(completed + (word_pc - entry_pc));
    }
    return -1;
}

static void state_init(AsmState *st) {
    memset(st, 0, sizeof(*st));
    strcpy(st->lwordchars, "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz_.");
    strcpy(st->swordchars, "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz_%$-~&|");
    strcpy(st->current_section, ".text");
    lmap_init(&st->labels);
    secmap_init(&st->sections);
    smap_init(&st->symbols);
    smap_init(&st->patsymbols);
    lmap_init(&st->export_labels);
    pv_init(&st->pat);
    st->vliwinstbits = 41;
    iv_init(&st->vliwnop);
    st->vliwbits = 128;
    vset_init(&st->vliwset);
    st->vliwflag = 0;
    st->vliwtemplatebits = 0;
    st->vliwstop = 0;
    st->vcnt = 1;
    st->expmode = EXP_PAT;
    st->exp_typ_float = 0;
    st->align = 16;
    st->bts = 8;
    st->endian_big = 0;
    st->pas = 0;
    st->debug = 0;
    st->osabi = 9;
    st->ln = 0;
    sv_init(&st->fnstack);
    is_init(&st->lnstack);
    for(int i=0;i<26;i++) st->vars[i]=u256_zero();
    bufmap_init(&st->buf);
    st->pc = u256_zero();
    st->padding = u256_zero();
    st->pc_instr_start = u256_zero();
    st->pc_instr_end   = u256_zero();
    st->pass1_size_mode = 0;
    st->stdin_tmp_path[0] = '\0';
    st->expfile_elf[0] = '\0';
    st->elf_objfile[0] = '\0';
    st->elf_machine = 62;
    st->gen_debug = 0;
    st->line_map = NULL;
    st->line_map_len = 0;
    st->line_map_cap = 0;
    st->elf_tracking = 0;
    st->elf_refs = NULL;
    st->elf_refs_len = 0;
    st->elf_refs_cap = 0;
    st->elf_current_word_idx = -1;
    for(int _vi=0;_vi<26;_vi++){
        st->elf_var_to_label[_vi].set = 0;
        st->elf_var_to_label[_vi].label_name = NULL;
        st->elf_var_to_label[_vi].label_val = 0;
    }
    st->elf_capturing_var = '\0';
    st->relocations = NULL;
    st->reloc_count = 0;
    st->reloc_cap = 0;
    for(int _rti=0; _rti<4; _rti++) st->reloctype_override[_rti] = -1;
    /* .check 拘束テーブルは memset で既にゼロ初期化済みだが、
     * sv_init() と同等であることを明示的に保証する。              */
    for(int _ci=0; _ci<26; _ci++) sv_init(&st->check_constraints[_ci]);
}

/* =========================================================
 * String utilities
 * ========================================================= */
static char axx_upper_char(char c) {
    if(c>='a'&&c<='z') return c-32;
    return c;
}
static int is_lower(char c){ return c>='a'&&c<='z'; }
static int is_digit(char c){ return c>='0'&&c<='9'; }
static int is_xdigit_upper(char c){
    return (c>='0'&&c<='9')||(c>='A'&&c<='F');
}
static AXX_UNUSED int is_alpha(char c){ return (c>='A'&&c<='Z')||(c>='a'&&c<='z'); }

static char *axx_strupr(char *s) {
    for(char*p=s;*p;p++) *p=axx_upper_char(*p);
    return s;
}
static void axx_strupr_to(char *dst, const char *src, size_t maxlen) {
    size_t i=0;
    for(;src[i]&&i<maxlen-1;i++) dst[i]=axx_upper_char(src[i]);
    dst[i]=0;
}

static int axx_q(const char *s, int slen, const char *t, int idx) {
    int tlen=(int)strlen(t);
    if(idx+tlen>slen) return 0;
    for(int i=0;i<tlen;i++)
        if(axx_upper_char(s[idx+i])!=axx_upper_char(t[i])) return 0;
    return 1;
}

static int axx_skipspc(const char *s, int idx) {
    while(s[idx]==' ') idx++;
    return idx;
}

static void axx_reduce_spaces(char *s) {
    char *src=s, *dst=s;
    int in_ws=0;
    while(*src){
        if(*src==' '||*src=='\t'||*src=='\n'||*src=='\r'){
            if(!in_ws){*dst++=' ';in_ws=1;}
            src++;
        } else { *dst++=*src++; in_ws=0; }
    }
    *dst=0;
}

static void axx_remove_comment(char *l) {
    for(int i=0;l[i];i++){
        if(l[i]=='/'&&l[i+1]=='*'){
            l[i]=0; return;
        }
    }
}

static void axx_remove_comment_asm(char *l) {
    /* Fix C-N1: handle backslash-escaped quotes inside string literals.
     * Fix ⑦: also handle single-quote character literals ('x' and '\x')
     * so that semicolons inside them are not treated as comment starts.
     * Strategy: when we encounter a single quote outside a double-quoted
     * string, perform look-ahead to consume the entire literal:
     *   '\x' form (4 chars): quote + backslash + char + quote
     *   'x'  form (3 chars): quote + char + quote
     * An isolated quote (no matching close) is passed through silently. */
    int in_str=0;
    int i=0;
    while(l[i]){
        if(in_str && l[i]=='\\'){
            /* escape sequence inside double-quoted string: skip next char */
            i++;
            if(l[i]) i++;
            continue;
        }
        if(l[i]=='"'){ in_str=!in_str; i++; continue; }
        if(l[i]=='\'' && !in_str){
            /* Fix ⑦: single-quote look-ahead */
            int j=i+1;
            if(l[j]=='\\' && l[j+1] && l[j+2]=='\''){
                /* '\x' form: consume 4 chars */
                i=j+3; continue;
            } else if(l[j] && l[j+1]=='\''){
                /* 'x' form: consume 3 chars */
                i=j+2; continue;
            }
            /* isolated quote: pass through and continue */
            i++; continue;
        }
        if(l[i]==';'&&!in_str){
            int j=i-1;
            while(j>=0&&(l[j]==' '||l[j]=='\t')) j--;
            l[j+1]=0; return;
        }
        i++;
    }
    int j=(int)strlen(l)-1;
    while(j>=0&&(l[j]==' '||l[j]=='\t'||l[j]=='\n'||l[j]=='\r')) l[j--]=0;
}

static int axx_get_param_to_spc(const char *s, int idx, char *t, size_t tsz) {
    /* 破綻点修正 (axx.py port): "!!"は常にVLIWスロット区切り/終端マーカー
     * として予約されている。以前は空白のみを境界とみなしていたため、
     * オペランドを持たない命令(NOP等)をVLIWスロットとして空白なしで
     * "nop!!!!"のように書くと、"!!!!"ごとニーモニックとして取り込まれて
     * マッチに失敗していた(NOPのエンコード値がたまたまvliwnopの穴埋め値と
     * 同じ0x00だったため出力バイトはたまたま一致していたが、"Syntax error"
     * が誤って報告され、エンコードが異なる命令では実際にバイト列が壊れる)。 */
    idx=axx_skipspc(s,idx);
    size_t n=0;
    while(s[idx]&&s[idx]!=' '&&!(s[idx]=='!'&&s[idx+1]=='!')&&n<tsz-1) t[n++]=s[idx++];
    t[n]=0;
    return idx;
}

static int axx_get_param_to_eon(const char *s, int idx, char *t, size_t tsz) {
    idx=axx_skipspc(s,idx);
    size_t n=0;
    while(s[idx]&&!(s[idx]=='!'&&s[idx+1]=='!')&&n<tsz-1) t[n++]=s[idx++];
    while(n>0&&(t[n-1]==' '||t[n-1]=='\t')) n--;
    t[n]=0;
    return idx;
}

static void axx_get_string(const char *l2, char *out, size_t osz) {
    int idx=axx_skipspc(l2,0);
    out[0]=0;
    if(!l2[idx]||l2[idx]!='"') return;
    idx++;
    size_t n=0;
    while(l2[idx]&&l2[idx]!='"'&&n<osz-1){
        if(l2[idx]=='\\'&&l2[idx+1]){
            char nc=l2[idx+1];
            if     (nc=='"')  { out[n++]='"';  idx+=2; }
            else if(nc=='\\') { out[n++]='\\'; idx+=2; }
            else if(nc=='n')  { out[n++]='\n'; idx+=2; }
            else if(nc=='t')  { out[n++]='\t'; idx+=2; }
            else if(nc=='r')  { out[n++]='\r'; idx+=2; }
            else if(nc=='x'||nc=='X'){
                /* Fix (axx.py port): \xNN hex escape – consume up to 2 hex digits. */
                idx+=2;
                char hex[3]; int hn=0;
                while(l2[idx]&&is_xdigit_upper(axx_upper_char(l2[idx]))&&hn<2)
                    hex[hn++]=l2[idx++];
                hex[hn]=0;
                if(hn>0){
                    out[n++]=(char)(int)strtol(hex,NULL,16);
                } else {
                    /* \x with no hex digits: output literal 'x' */
                    if(n<osz-1) out[n++]='x';
                }
            }
            else              { out[n++]=nc;   idx+=2; }
        } else {
            out[n++]=l2[idx++];
        }
    }
    out[n]=0;
    if(!l2[idx])
        fprintf(stderr, " warning - unterminated string literal: %s\n", l2);
}

/* =========================================================
 * Parser helpers
 * ========================================================= */
static int char_in(char c, const char *set){
    return strchr(set,c)!=NULL;
}

static int axx_get_intstr(const char *s, int idx, char *fs, size_t fsz){
    size_t n=0;
    while(s[idx]&&is_digit(s[idx])&&n<fsz-1) fs[n++]=s[idx++];
    fs[n]=0;
    return idx;
}

static int axx_get_floatstr(const char *s, int idx, char *fs, size_t fsz){
    /* Fix 11: leading '-' is handled by expr_factor() as unary minus;
     * consuming it here would double-interpret it.  Only '-inf' is kept
     * as a single special token (axx.py treats '-inf' as one literal). */
    if(strncmp(s+idx,"-inf",4)==0){strcpy(fs,"-inf");return idx+4;}
    if(strncmp(s+idx,"inf",3)==0){strcpy(fs,"inf");return idx+3;}
    if(strncmp(s+idx,"nan",3)==0){strcpy(fs,"nan");return idx+3;}
    size_t n=0;
    /* NOTE: do NOT consume a leading '-' here (Fix 11). */
    while(s[idx]&&(is_digit(s[idx])||s[idx]=='.')&&n<fsz-1) fs[n++]=s[idx++];
    if((s[idx]=='e'||s[idx]=='E') && n<fsz-1){
        /* Fix (axx.py port): roll back exponent part when no digits follow 'e'/'E'.
         * e.g. "1e" or "1e+" would produce an invalid float string – discard. */
        int saved_idx = idx;
        size_t saved_n = n;
        fs[n++]=s[idx++];
        if((s[idx]=='+'||s[idx]=='-')&&n<fsz-1) fs[n++]=s[idx++];
        int digits_start = idx;
        while(s[idx]&&is_digit(s[idx])&&n<fsz-1) fs[n++]=s[idx++];
        if(idx == digits_start){
            /* no digits after exponent marker: discard and roll back */
            idx = saved_idx;
            n   = saved_n;
        }
    }
    fs[n]=0;
    return idx;
}

static int axx_get_curlb(const char *s, int idx, int *f_out, char *t_out, size_t tsz){
    idx=axx_skipspc(s,idx);
    *f_out=0; t_out[0]=0;
    if(s[idx]!='{') return idx;
    idx++;
    idx=axx_skipspc(s,idx);
    size_t n=0;
    while(s[idx]&&s[idx]!='}'&&n<tsz-1) t_out[n++]=s[idx++];
    while(n>0&&t_out[n-1]==' ') n--;
    t_out[n]=0;
    if(!s[idx]){
        /* 修正③: closing '}' not found – report error.
         * axx.py returns len(s) to force parse termination (not start_idx). */
        fprintf(stderr," error - missing closing '}' in expression: '{%s'\n", t_out);
        return (int)strlen(s);
    }
    idx++; /* consume '}' */
    *f_out=1;
    return idx;
}

static int axx_get_symbol_word(const char *s, int idx, const char *swordchars, char *t_out, size_t tsz){
    t_out[0]=0;
    if(!s[idx]||is_digit(s[idx])||!char_in(s[idx],swordchars)) return idx;
    size_t n=0;
    /* Fix: idx must always advance over the *entire* word in the source,
     * even once the output buffer is full. Previously the loop condition
     * "n<tsz-1" also gated idx's advance, so a word longer than tsz-1
     * bytes left its unconsumed tail in the source string, causing the
     * remainder to be misparsed as a following token (idx/n desync).
     * Writing into t_out and advancing idx are now independent: t_out is
     * truncated (with a warning) but idx always reflects the true word end,
     * matching axx.py's unbounded get_symbol_word(). */
    int truncated = 0;
    t_out[n++]=s[idx++];
    while(s[idx]&&char_in(s[idx],swordchars)){
        if(n<tsz-1) t_out[n++]=s[idx];
        else truncated = 1;
        idx++;
    }
    t_out[n]=0;
    axx_strupr(t_out);
    if(truncated){
        fprintf(stderr,"warning - symbol name truncated to %zu characters\n", tsz-1);
    }
    return idx;
}

static int axx_get_label_word(const char *s, int idx, const char *lwordchars, char *t_out, size_t tsz){
    t_out[0]=0;
    if(!s[idx]) return idx;
    if(s[idx]!='.'&&(is_digit(s[idx])||!char_in(s[idx],lwordchars))) return idx;
    size_t n=0;
    /* Fix: same idx/n desync as axx_get_symbol_word above; idx now always
     * advances over the full label word regardless of buffer capacity. */
    int truncated = 0;
    t_out[n++]=s[idx++];
    while(s[idx]&&char_in(s[idx],lwordchars)){
        if(n<tsz-1) t_out[n++]=s[idx];
        else truncated = 1;
        idx++;
    }
    t_out[n]=0;
    if(truncated){
        fprintf(stderr,"warning - label name truncated to %zu characters\n", tsz-1);
    }
    if(s[idx]==':'&&s[idx+1]!='=') idx++;
    return idx;
}

static int axx_get_params1(const char *l, int idx, char *s_out, size_t ssz){
    idx=axx_skipspc(l,idx);
    if(!l[idx]){ s_out[0]=0; return idx; }
    size_t n=0;
    while(l[idx]){
        if(l[idx]==':'&&l[idx+1]==':'){idx+=2;break;}
        if(n<ssz-1) s_out[n++]=l[idx];
        idx++;
    }
    while(n>0&&(s_out[n-1]==' '||s_out[n-1]=='\t')) n--;
    s_out[n]=0;
    return idx;
}

/* =========================================================
 * IEEE754 conversion helpers (used by expr_factor1 via direct call;
 * the 32/64 variants are also retained as API for future extensions)
 * ========================================================= */
static AXX_UNUSED uint32_t ieee754_32_from_str(const char *a){
    if(strcmp(a,"inf")==0) return 0x7F800000u;
    if(strcmp(a,"-inf")==0) return 0xFF800000u;
    if(strcmp(a,"nan")==0) return 0x7FC00000u;
    float f=(float)strtod(a,NULL);
    uint32_t r; memcpy(&r,&f,4); return r;
}
static AXX_UNUSED uint64_t ieee754_64_from_str(const char *a){
    if(strcmp(a,"inf")==0) return 0x7FF0000000000000ULL;
    if(strcmp(a,"-inf")==0) return 0xFFF0000000000000ULL;
    if(strcmp(a,"nan")==0) return 0x7FF8000000000000ULL;
    double d=strtod(a,NULL);
    uint64_t r; memcpy(&r,&d,8); return r;
}

/* -------------------------------------------------------
 * Note: safe_spawn_read() / safe_spawn_close() have been removed.
 * ieee754_128_from_str() and xeval() no longer spawn subprocesses;
 * they use pure C implementations instead (Fix P11, Fix P12).
 * sys/wait.h is still included for completeness.
 * ------------------------------------------------------- */

/* -------------------------------------------------------
 * Fix P11 (rev2): ieee754_128_from_str() -- two bugs fixed.
 *
 * Bug A (byte order): The previous little-endian loop read raw[7-i]
 *   and shifted left, placing raw[0] in the MSB -- big-endian semantics.
 *   On a little-endian machine, raw[0] is the LSB; the correct copy is
 *   simply memcpy(&result.w[0], raw, 8) and memcpy(&result.w[1], raw+8, 8).
 *
 * Bug B (precision): (__float128)strtold(a, NULL) parses the string with
 *   long-double precision (~18–19 decimal digits / 64 mantissa bits), then
 *   promotes to __float128.  Promotion zero-pads the lower 48 mantissa bits,
 *   giving a wrong result compared to mpmath which parses the decimal with
 *   full 113-bit binary128 precision.
 *
 *   Fix B: parse the decimal string directly using __float128 arithmetic
 *   (+, -, *, / on __float128 operands) so every intermediate value has
 *   113-bit precision.  This matches Python/mpmath output exactly.
 *
 * No subprocess, no temp files, no mpmath, no quadmath.
 * ------------------------------------------------------- */

#if defined(__GNUC__) && !defined(__STRICT_ANSI__) && \
    (defined(__x86_64__) || defined(__i386__) || defined(__aarch64__) || \
     defined(__arm__) || defined(__riscv))

/* Parse a finite decimal string into __float128 with full 113-bit precision.
 *
 * Key insight: per-digit division by place (= place / 10 each step) accumulates
 * rounding errors because 1/10 is not exactly representable in binary.
 * Instead, collect ALL significant digits as one big __float128 integer (exact,
 * since typical decimal inputs have ≤20 digits which fit well within 113 bits),
 * then divide ONCE by 10^(num_fraction_digits).  One correctly-rounded division
 * produces the closest binary128 to the input decimal — matching mpmath.
 *
 * Handles: optional sign, integer digits, optional '.', fraction digits,
 * optional 'e'/'E' followed by a signed integer exponent.
 * nan/inf are handled before this is called.                               */
static __float128 f128_from_decimal(const char *s)
{
    const __float128 ten  = (__float128)10;
    const __float128 one  = (__float128)1;

    int sign = 0;
    if(*s == '-'){ sign = 1; s++; }
    else if(*s == '+'){ s++; }

    /* Collect all significant digits (integer + fraction) as one __float128
     * integer, tracking how many belong to the fraction part.              */
    __float128 int_val    = (__float128)0;
    int        frac_digits = 0;
    int        in_frac    = 0;

    while((*s >= '0' && *s <= '9') || *s == '.'){
        if(*s == '.'){
            in_frac = 1;
            s++;
            continue;
        }
        int_val = int_val * ten + (__float128)(*s - '0');
        if(in_frac) frac_digits++;
        s++;
    }

    /* Divide once by 10^frac_digits (one correctly-rounded __float128 op). */
    __float128 denom = one;
    for(int i = 0; i < frac_digits; i++) denom *= ten;
    __float128 result = int_val / denom;

    /* Apply explicit exponent if present */
    if(*s == 'e' || *s == 'E'){
        s++;
        int esign = 1;
        if(*s == '-'){ esign = -1; s++; }
        else if(*s == '+'){ s++; }
        int eabs = 0;
        while(*s >= '0' && *s <= '9'){ eabs = eabs*10 + (*s-'0'); s++; }
        __float128 scale = one;
        __float128 base  = (esign > 0) ? ten : (one / ten);
        while(eabs-- > 0) scale *= base;
        result *= scale;
    }

    return sign ? -result : result;
}

/* -------------------------------------------------------
 * f128_eval_expr(): evaluate a simple arithmetic expression
 * in __float128 precision.
 *
 * Grammar:
 *   expr   := term   (('+' | '-') term)*
 *   term   := factor (('*' | '/') factor)*
 *   factor := '(' expr ')'  |  '-' factor  |  '+' factor  |  number
 *   number := decimal literal parsed by f128_from_decimal
 *
 * Used by both qad{} and !Q so that "3.14*2+1" is evaluated with
 * full 113-bit binary128 precision, matching Python mpmath exactly.
 * Non-parseable tokens (labels/symbols) cause ok=0; callers fall
 * back to the existing double-mode evaluator.                        */
typedef struct { __float128 val; const char *end; int ok; } F128R;

static F128R f128_expr_fn(const char *s);   /* forward declaration */

static F128R f128_factor_fn(const char *s)
{
    while(*s==' '||*s=='\t') s++;
    F128R r = {(__float128)0, s, 1};
    if(*s=='('){
        r = f128_expr_fn(s+1);
        if(!r.ok) return r;
        while(*r.end==' '||*r.end=='\t') r.end++;
        if(*r.end==')') r.end++;
        return r;
    }
    if(*s=='-'){ r=f128_factor_fn(s+1); r.val=-r.val; return r; }
    if(*s=='+'){ return f128_factor_fn(s+1); }
    /* decimal number literal */
    if((*s>='0'&&*s<='9')||*s=='.'){
        char buf[80]; int n=0;
        while(((*s>='0'&&*s<='9')||*s=='.')&&n<78) buf[n++]=*s++;
        if((*s=='e'||*s=='E')&&n<77){
            buf[n++]=*s++;
            if((*s=='+'||*s=='-')&&n<77) buf[n++]=*s++;
            while(*s>='0'&&*s<='9'&&n<78) buf[n++]=*s++;
        }
        buf[n]='\0';
        r.val=f128_from_decimal(buf);
        r.end=s;
        return r;
    }
    r.ok=0; return r;
}

static F128R f128_term_fn(const char *s)
{
    while(*s==' '||*s=='\t') s++;
    F128R r=f128_factor_fn(s);
    if(!r.ok) return r;
    while(1){
        const char *p=r.end;
        while(*p==' '||*p=='\t') p++;
        if(*p=='*'){
            F128R r2=f128_factor_fn(p+1); if(!r2.ok) break;
            r.val*=r2.val; r.end=r2.end;
        } else if(*p=='/'){
            F128R r2=f128_factor_fn(p+1); if(!r2.ok) break;
            if(r2.val!=(__float128)0){ r.val/=r2.val; }
            r.end=r2.end;
        } else break;
    }
    return r;
}

static F128R f128_expr_fn(const char *s)
{
    while(*s==' '||*s=='\t') s++;
    F128R r=f128_term_fn(s);
    if(!r.ok) return r;
    while(1){
        const char *p=r.end;
        while(*p==' '||*p=='\t') p++;
        if(*p=='+'){
            F128R r2=f128_term_fn(p+1); if(!r2.ok) break;
            r.val+=r2.val; r.end=r2.end;
        } else if(*p=='-'){
            F128R r2=f128_term_fn(p+1); if(!r2.ok) break;
            r.val-=r2.val; r.end=r2.end;
        } else break;
    }
    return r;
}

/* Convert __float128 to uint256_t bit pattern.
 * w[0] = lower 64 bits (LE) / upper 64 bits (BE).                   */
static uint256_t f128_to_u256(__float128 v)
{
    unsigned char raw[16];
    memcpy(raw, &v, 16);
    uint256_t res = u256_zero();
#if defined(__BYTE_ORDER__) && (__BYTE_ORDER__ == __ORDER_BIG_ENDIAN__)
    for(int i=0;i<8;i++)  res.w[1]=(res.w[1]<<8)|raw[i];
    for(int i=8;i<16;i++) res.w[0]=(res.w[0]<<8)|raw[i];
#else
    memcpy(&res.w[0], raw,   8);
    memcpy(&res.w[1], raw+8, 8);
#endif
    return res;
}

/* Evaluate text as __float128 expression. ok_out=0 on failure.       */
static uint256_t f128_eval_text(const char *text, int *ok_out)
{
    F128R r = f128_expr_fn(text);
    if(ok_out) *ok_out = r.ok;
    if(!r.ok)  return u256_zero();
    return f128_to_u256(r.val);
}

#endif /* __GNUC__ block */

static uint256_t ieee754_128_from_str(const char *a){
    /* Special values */
    if(strcmp(a,"inf")==0){
        uint256_t r=u256_zero(); r.w[1]=0x7FFF000000000000ULL; return r;
    }
    if(strcmp(a,"-inf")==0){
        uint256_t r=u256_zero(); r.w[1]=0xFFFF000000000000ULL; return r;
    }
    if(strcmp(a,"nan")==0){
        uint256_t r=u256_zero(); r.w[1]=0x7FFF800000000000ULL; return r;
    }

#if defined(__GNUC__) && !defined(__STRICT_ANSI__) && \
    (defined(__x86_64__) || defined(__i386__) || defined(__aarch64__) || \
     defined(__arm__) || defined(__riscv))
    /* Path A: use __float128 arithmetic via f128_eval_text (full 113-bit
     * precision, same result as Python mpmath with mp.prec=128).            */
    int ok = 0;
    uint256_t r = f128_eval_text(a, &ok);
    if(ok) return r;
    /* Fall through to Path B if the expression couldn't be parsed
     * (e.g. something other than a plain decimal literal).                  */
#endif

    /* Path B: long double iterative extraction (portable fallback).         */
    /* Warn once if long double has the same precision as double (64-bit).  */
    {
        static int warned = 0;
        if(!warned && sizeof(long double)==sizeof(double)){
            fprintf(stderr,"ieee754_128_from_str: long double == double on this "
                           "platform; qad{} literals will have 53-bit precision "
                           "instead of 112-bit.\n");
            warned = 1;
        }
    }
    long double ld = strtold(a, NULL);
    if(ld == 0.0L){
        return u256_zero();
    }
    int sign = (ld < 0.0L) ? 1 : 0;
    if(ld < 0.0L) ld = -ld;
    int fe = 0;
    /* Use frexpl: returns value in [0.5, 1.0) and sets fe such that
     * ld == significand * 2^fe.  We want form 1.frac * 2^exp so:
     * exp = fe-1, significand_normalized = ld * 2^(1-fe) */
    long double sig = frexpl(ld, &fe);
    /* sig is in [0.5, 1.0), multiply by 2 to get [1.0, 2.0) */
    sig *= 2.0L;
    int exp_unbiased = fe - 1;
    int biased_exp = exp_unbiased + 16383;
    /* Guard against exponent overflow / underflow */
    if(biased_exp <= 0)  biased_exp = 0;  /* subnormal – treat as zero */
    if(biased_exp >= 32767) {
        /* Infinity */
        uint256_t r=u256_zero();
        r.w[1] = (uint64_t)(sign?1ULL:0ULL)<<63 | 0x7FFF000000000000ULL;
        return r;
    }
    long double frac_part = sig - 1.0L;  /* fractional part after hidden bit */
    /* Extract 48 high mantissa bits (bits 111..64 of the 112-bit field) */
    uint64_t hi = 0;
    for(int b=47;b>=0;b--){
        frac_part *= 2.0L;
        if(frac_part >= 1.0L){ hi |= ((uint64_t)1<<b); frac_part -= 1.0L; }
    }
    /* Extract 64 low mantissa bits (bits 63..0) */
    uint64_t lo = 0;
    for(int b=63;b>=0;b--){
        frac_part *= 2.0L;
        if(frac_part >= 1.0L){ lo |= ((uint64_t)1<<b); frac_part -= 1.0L; }
    }
    uint256_t result = u256_zero();
    result.w[0] = lo;
    result.w[1] = (hi & 0x0000FFFFFFFFFFFFull)
                | ((uint64_t)(unsigned)biased_exp << 48)
                | ((uint64_t)(unsigned)sign << 63);
    return result;
}

static double enfloat_bits(uint64_t a){
    uint32_t u=(uint32_t)a; float f; memcpy(&f,&u,4); return (double)f;
}
static double endouble_bits(uint64_t a){
    double d; memcpy(&d,&a,8); return d;
}

/* =========================================================
 * Float-mode helpers for the expression evaluator.
 *
 * When AsmState.exp_typ_float == 1, the expression evaluator carries
 * double values as raw bit-casts inside uint256_t.w[0].  The two
 * conversion helpers below perform the bit-cast in both directions.
 *
 * axx_isfloatstr() returns 1 when the character at s[idx] can start a
 * floating-point literal recognised by axx_get_floatstr().  It is used
 * in expr_factor1() to dispatch between float and integer number parsing,
 * mirroring axx.py Parser.isfloatstr() / ExpressionEvaluator.factor1().
 * ========================================================= */
static inline double u256_to_double(uint256_t v){
    double d; memcpy(&d, &v.w[0], 8); return d;
}
static inline uint256_t double_to_u256(double d){
    uint256_t r = u256_zero(); memcpy(&r.w[0], &d, 8); return r;
}
/* Returns 1 when s[idx] starts a float literal (digit, '.', 'i'nf, 'n'an, '-inf').
 * Leading '-' for regular numbers is NOT checked here because unary minus is
 * handled by expr_factor().  Only '-inf' is kept as a single special token. */
static int axx_isfloatstr(const char *s, int idx){
    if(!s[idx]) return 0;
    if(strncmp(s+idx,"-inf",4)==0) return 1;
    if(strncmp(s+idx,"inf",3)==0) return 1;
    if(strncmp(s+idx,"nan",3)==0) return 1;
    if(is_digit(s[idx])) return 1;
    if(s[idx]=='.' && is_digit((unsigned char)s[idx+1])) return 1;
    return 0;
}

/* =========================================================
 * Forward declarations
 * ========================================================= */
typedef struct Assembler Assembler;
static uint256_t expr_expression(Assembler *asmb, const char *s, int idx, int *idx_out);
static uint256_t expr_expression_pat(Assembler *asmb, const char *s, int idx, int *idx_out);
static uint256_t expr_expression_asm(Assembler *asmb, const char *s, int idx, int *idx_out);
static uint256_t expr_expression_esc(Assembler *asmb, const char *s, int idx, char stopchar, int *idx_out);

static int lineassemble2(Assembler *asmb, const char *line, int idx,
                         IntVec *idxs_out, IntVec *objl_out, int *idx_out);
static int lineassemble(Assembler *asmb, const char *line);
static int lineassemble0(Assembler *asmb, const char *line);
static void fileassemble(Assembler *asmb, const char *fn);

/* =========================================================
 * Assembler struct
 * ========================================================= */
struct Assembler {
    AsmState st;
    /* imp_label: section info parsed from the import TSV file.
     * Built while reading section lines; used by subsequent label lines
     * to resolve label -> section membership.
     * Kept in Assembler (not AsmState) because it belongs to the import
     * phase only and must not be confused with st.sections (assembly output).
     * 破綻点修正 (axx.py port): SecMap(secmap_set)は同名キーの2回目の
     * set()が1回目を上書きするため、再入セクションの断片ごとに複数行
     * 書き出されるようになったTSVを読むと、名前ごとに最後の断片しか
     * 残らず、それ以前の断片に定義されたラベルの所属セクションを
     * 誤判定していた。SecRangeVec(重複キー可・追記のみ)に変更する。 */
    SecRangeVec imp_sections;
};

static void assembler_init(Assembler *a){
    state_init(&a->st);
    secrangevec_init(&a->imp_sections);
}

/* =========================================================
 * BinaryWriter helpers
 * ========================================================= */
static uint64_t align_addr(AsmState *st, uint64_t addr){
    uint64_t a=addr%(uint64_t)st->align;
    if(a==0) return addr;
    return addr+(uint64_t)st->align-a;
}

static void outbin_store(AsmState *st, uint64_t position, uint256_t word_val){
    uint64_t mask = (st->bts<64) ? ((uint64_t)1<<st->bts)-1 : (uint64_t)-1;
    uint64_t v = u256_to_u64(word_val) & mask;
    bufmap_set(&st->buf, position, v);
}

static void fwrite_word(AsmState *st, uint64_t position, uint256_t x, int prt){
    uint64_t mask = (st->bts<64) ? ((uint64_t)1<<st->bts)-1 : (uint64_t)-1;
    uint64_t val = u256_to_u64(x) & mask;
    if(prt){
        int colm=(st->bts+3)/4;
        printf(" 0x%0*llx",(int)colm,(unsigned long long)val);
    }
    outbin_store(st, position, u256_from_u64(val));
}

static void outbin(AsmState *st, uint256_t a, uint256_t x){
    if(should_report_errors(st))
        fwrite_word(st, u256_to_u64(a), x, (st->pas==0)||st->verbose);
}
static void outbin2(AsmState *st, uint256_t a, uint256_t x){
    if(should_report_errors(st))
        fwrite_word(st, u256_to_u64(a), x, 0);
}

static void binary_flush(AsmState *st){
    if(!st->outfile[0]) return;
    int buf_found = 0;
    uint64_t max_pos = bufmap_max_key(&st->buf, &buf_found);
    /* Fix (new): if nothing was ever written to the buffer, bail out now.
     * Previously max_pos==0 was returned for both "empty buffer" and "one word
     * at position 0", so an empty assembly would create a one-word output file. */
    if(!buf_found) return;
    int word_bits = st->bts;
    int bytes_per_word = (word_bits+7)/8;
    /* Fix D: max_pos+1 wraps to 0 when max_pos==UINT64_MAX, producing a
     * bogus total_size==0 that silently discards the entire binary.  Treat
     * UINT64_MAX as an impossible address and bail out with an error. */
    if(max_pos == (uint64_t)-1){
        fprintf(stderr,"binary_flush: max_pos overflow (UINT64_MAX), skipping output.\n");
        return;
    }
    uint64_t total_size = (max_pos+1)*(uint64_t)bytes_per_word;
    if(total_size==0) return;
    /* Fix I: on 32-bit systems SIZE_MAX is ~4 GB.  If total_size exceeds it,
     * the cast to size_t wraps silently, calloc allocates far too little, and
     * subsequent writes corrupt the heap.  Fail loudly instead. */
    if(total_size > (uint64_t)(size_t)-1){
        fprintf(stderr,"binary_flush: output too large (%llu bytes) for this platform's size_t.\n",
                (unsigned long long)total_size);
        return;
    }
    unsigned char *data = calloc(1, (size_t)total_size);
    if(!data){perror("calloc");return;}

    /* Fix #6: fill every word-slot with the padding value first,
     * then overwrite only the positions that were actually written.
     * The original calloc() always pre-filled with 0, ignoring st->padding. */
    uint64_t pad_val = u256_to_u64(st->padding);
    if(pad_val != 0){
        for(uint64_t pos = 0; pos <= max_pos; pos++){
            uint64_t base_idx = pos*(uint64_t)bytes_per_word;
            uint64_t tmp = pad_val;
            if(!st->endian_big){
                for(int j=0;j<bytes_per_word;j++){
                    if(base_idx+j<total_size)
                        data[base_idx+j]=(unsigned char)(tmp&0xff);
                    tmp>>=8;
                }
            } else {
                for(int j=bytes_per_word-1;j>=0;j--){
                    if(base_idx+j<total_size)
                        data[base_idx+j]=(unsigned char)(tmp&0xff);
                    tmp>>=8;
                }
            }
        }
    }

    for(int i=0;i<BUFMAP_NB;i++){
        for(BufEntry*e=st->buf.buckets[i];e;e=e->next){
            uint64_t base_idx = e->pos*(uint64_t)bytes_per_word;
            uint64_t tmp_val = e->val;
            if(!st->endian_big){
                for(int j=0;j<bytes_per_word;j++){
                    if(base_idx+j<total_size)
                        data[base_idx+j]=(unsigned char)(tmp_val&0xff);
                    tmp_val>>=8;
                }
            } else {
                for(int j=bytes_per_word-1;j>=0;j--){
                    if(base_idx+j<total_size)
                        data[base_idx+j]=(unsigned char)(tmp_val&0xff);
                    tmp_val>>=8;
                }
            }
        }
    }
    FILE *fp=fopen(st->outfile,"wb");
    if(!fp){perror(st->outfile);free(data);return;}
    fwrite(data,1,(size_t)total_size,fp);
    fclose(fp);
    fprintf(stderr,"wrote raw binary %s (%llu bytes)\n",st->outfile,(unsigned long long)total_size);
    free(data);
}

/* =========================================================
 * VariableManager
 * ========================================================= */
static uint256_t var_get(AsmState *st, char ch){
    ch=(char)axx_upper_char(ch);
    if(ch>='A'&&ch<='Z') return st->vars[ch-'A'];
    return u256_zero();
}
static void var_put(AsmState *st, char ch, uint256_t v){
    ch=(char)axx_upper_char(ch);
    if(ch>='A'&&ch<='Z') st->vars[ch-'A']=v;
}

/* =========================================================
 * LabelManager
 * ========================================================= */
static uint256_t label_get_value(AsmState *st, const char *k){
    /* Bugfix (axx.py port): this used to unconditionally clear
     * error_undefined_label here on every call, clobbering the signal
     * from an EARLIER label reference in the same compound expression
     * (e.g. "undefined_label + defined_label": the first operand's lookup
     * correctly sets the flag, but the second operand's lookup --
     * succeeding -- reset it right back to 0, since none of the
     * expr_termN() binary-operator levels save/restore or OR-merge the
     * flag around each operand). Only ever SET it (on failure, below);
     * never clear it here on success, so it correctly accumulates for the
     * whole expression. Top-level callers that need a "fresh" check
     * (.ORG/.RESB/.ZERO/etc.) reset it themselves immediately before
     * evaluating their own expression. */
    LabelEntry *e=lmap_find(&st->labels,k);
    if(e){
        uint256_t ret_val = e->value;
        const char *sec = e->section ? e->section : "";
        if(st->equ_section_tracking){
            if(!st->equ_first_section[0]){
                strncpy(st->equ_first_section, sec, sizeof(st->equ_first_section)-1);
                st->equ_first_section[sizeof(st->equ_first_section)-1]='\0';
            } else if(strcmp(st->equ_first_section, sec) != 0){
                st->equ_multi_section = 1;
            }
            int64_t _adj = equ_section_relative_offset(st, sec, u256_to_u64(e->value));
            if(_adj >= 0) ret_val = u256_from_u64((uint64_t)_adj);
        } else if(st->in_binary_list && strcmp(sec, st->current_section) == 0){
            /* 破綻点修正 (axx.py port): .EQU以外でも、命令エンコード式
             * (パターンファイルの$$/ラベル参照の組合せ、例: z80の
             * "JR !e :: 0x18,e-$$-2")は生のグローバルpcで計算されており、
             * 同じセクションへの再入で生じるズレの影響を受けていた
             * (上の.EQUと同じ根本原因)。$$は常に現在セクション内の値
             * なので、参照ラベルが現在セクションと同じ場合に限り、両者を
             * 同じ基準(セクション内相対オフセット)に揃える。異なる
             * セクションを参照する場合は、既存のELFリロケーション機構が
             * 別途正しく処理するためここでは変更しない。
             *
             * 破綻点修正2 (重大): st->in_binary_list の条件を追加した。
             * これが無いと、reloc_type付き.EQU(例:
             * "tape_a: .equ tape::abs32")が同じセクション内のアドレス
             * ラベル(tape)を参照した際にもこの変換が誤って適用され、
             * tape_a の値が「tapeの生pc」ではなく「セクション先頭からの
             * 相対オフセット」に壊されてしまっていた(bf.sで実際に
             * 発生・確認済み: tape_a が0になり、[tape_a+r15] SIB
             * アドレッシングが.textの先頭を指してbus errorでクラッシュ
             * した)。reloc_type付き.EQUやその他の通常の式評価
             * (in_binary_list=0)では、ラベルの生の値をそのまま維持
             * しなければならない。 */
            int64_t _adj = equ_section_relative_offset(st, sec, u256_to_u64(e->value));
            if(_adj >= 0) ret_val = u256_from_u64((uint64_t)_adj);
        }
        /* ELF relocation tracking.
         * .equ-defined labels は原則として絶対定数であり追跡しない。
         * ただし .equ $$::reloctype のように reloc_type_override が設定されている場合は
         * アドレスラベルと同様に追跡してリロケーションを生成する必要がある。 */
        int _equ_has_reloc = e->is_equ && (e->reloc_type_override >= 0);
        if(st->elf_tracking && (!e->is_equ || _equ_has_reloc)){
            if(st->elf_capturing_var != '\0'){
                /* match() is capturing !var: record variable->label mapping.
                 * If the same var gets two different get_value() calls the
                 * expression is compound (e.g. label1+label2) – mark invalid. */
                int vi = (unsigned char)st->elf_capturing_var - 'a';
                if(vi >= 0 && vi < 26){
                    if(st->elf_var_to_label[vi].set == 0){
                        st->elf_var_to_label[vi].set = 1;
                        free(st->elf_var_to_label[vi].label_name);
                        st->elf_var_to_label[vi].label_name = strdup(k);
                        st->elf_var_to_label[vi].label_val = u256_to_u64(e->value);
                    } else {
                        /* conflict – compound expression, not directly relocatable */
                        st->elf_var_to_label[vi].set = -1;
                        free(st->elf_var_to_label[vi].label_name);
                        st->elf_var_to_label[vi].label_name = NULL;
                    }
                }
            } else if(st->elf_current_word_idx >= 0){
                /* Inside makeobj(): direct label reference in object expression */
                if(st->elf_refs_len >= st->elf_refs_cap){
                    st->elf_refs_cap = st->elf_refs_cap ? st->elf_refs_cap*2 : 8;
                    st->elf_refs = realloc(st->elf_refs,
                        st->elf_refs_cap * sizeof(st->elf_refs[0]));
                    if(!st->elf_refs){ perror("realloc"); exit(1); }
                }
                st->elf_refs[st->elf_refs_len].name     = strdup(k);
                st->elf_refs[st->elf_refs_len].val      = u256_to_u64(e->value);
                st->elf_refs[st->elf_refs_len].word_idx = st->elf_current_word_idx;
                st->elf_refs_len++;
            }
        }
        return ret_val;
    }
    /* A (axx.py port): pass1 forward reference uses the previous relaxation
     * iteration's resolved address as an estimate. This (1) lets relaxation
     * actually converge for variable-length forward branches and (2) makes the
     * size-probe and the error-condition see the same realistic displacement.
     * An estimate is trusted (no error_undefined_label) so makeobj proceeds.
     * pass2 (pas==2) never takes this path, so a truly undefined label still
     * errors there. UNDEF-derived estimates are ignored (treated as no estimate). */
    if(st->pas == 1 && st->relax_prev){
        LabelEntry *pe = lmap_find(st->relax_prev, k);
        if(pe && !u256_is_undef_derived(pe->value)){
            return pe->value;
        }
    }
    st->error_undefined_label = 1;
    if(st->pass1_size_mode) return u256_zero();
    /* in_match_attempt が 1 のときはパターンマッチ試行中であり、
     * このラベル参照は後に別パターンに差し替えられる可能性があるためエラーを表示しない。
     * （例: OUT (!n),A が OUT (C),E を試みる際に !n キャプチャで C がラベル評価される。） */
    if(!st->in_match_attempt && should_report_errors(st)){
        fprintf(stderr, " error - Label undefined: '%s'  [%s:%d]\n",
            k, st->current_file, (int)st->ln);
    }
    return UNDEF_VAL();
}
static const char *label_get_section(AsmState *st, const char *k){
    /* Same fix as label_get_value() above: only ever set the flag, never
     * clear it on success. */
    LabelEntry *e=lmap_find(&st->labels,k);
    if(e) return e->section;
    st->error_undefined_label=1;
    return "";
}
static int label_put_value(AsmState *st, const char *k, uint256_t v, const char *sec, int is_equ, int reloc_type){
    if(st->pas==1||st->pas==0){
        LabelEntry *_existing = lmap_find(&st->labels,k);
        /* 破綻点修正 (axx.py port): .EXTERNで仮登録された名前(is_imported=1)は
         * まだ実体を持たないプレースホルダなので、同名のローカル定義で
         * 上書きすることを許可する(axx.py側の put_value() と同じ仕様)。
         * 従来はis_imported を無視して無条件に「既に定義済み」エラーに
         * していたため、.EXTERN後に同名をローカル定義する正当なパターンが
         * 常に失敗していた。 */
        if(_existing && !_existing->is_imported){
            st->error_already_defined=1;
            st->had_error=1;
            fprintf(stderr," error - label already defined.\n");
            return 0;
        }
    } else if(st->pas==2){
        if(!lmap_contains(&st->labels,k)){
            st->error_already_defined=1;
            st->had_error=1;
            fprintf(stderr," error - label '%s' not defined in pass 1.\n",k);
            return 0;
        }
    }
    char uk[512]; axx_strupr_to(uk,k,sizeof(uk));
    uint256_t dummy;
    if(smap_get(&st->patsymbols,uk,&dummy)){
        st->had_error=1;
        fprintf(stderr," error - '%s' is a pattern file symbol.\n",k);
        return 0;
    }
    st->error_already_defined=0;
    /* lmap_set は reloc_type_override を -1 にリセットする（旧値を引き継がない）。
     * ::reloctype が明示指定された場合のみ直後に設定する。 */
    lmap_set(&st->labels,k,v,sec,is_equ);
    if(reloc_type >= 0)
        lmap_set_reloc_type(&st->labels, k, reloc_type);
    return 1;
}
/* label_print_all: mirrors Python LabelManager.printlabels()
 *   result = {}
 *   for key, value in self.state.labels.items():
 *       num = value[0]; section = value[1]
 *       result[key] = [hex(num), section]
 *   print(result)
 * Output: {'label': ['0xVAL', 'section'], ...} on one line */
static void label_print_all(AsmState *st){
    int first=1;
    fprintf(stderr, "{");
    for(int i=0;i<st->labels.nbuckets;i++){
        for(LabelEntry*e=st->labels.buckets[i];e;e=e->next){
            if(!first) fprintf(stderr, ", ");
            fprintf(stderr, "'%s': ['0x%llx', '%s']",
                   e->key,
                   (unsigned long long)u256_to_u64(e->value),
                   e->section);
            first=0;
        }
    }
    fprintf(stderr, "}\n");
}

/* =========================================================
 * SymbolManager
 * ========================================================= */
static int symbol_get(AsmState *st, const char *w, uint256_t *out){
    char uw[512]; axx_strupr_to(uw,w,sizeof(uw));
    return smap_get(&st->symbols,uw,out);
}

/* =========================================================
 * xeval: qad{}/dbl{}/flt{} float-notation expression evaluator.
 *
 * axx.py port: mirrors axx.py's xeval() -- a SEPARATE, restricted
 * arithmetic-expression language (not the general expr_expression()
 * grammar used everywhere else in this file), used only to evaluate
 * qad{}/dbl{}/flt{} bodies. Supports +,-,*,/,//,%,**, &,|,^,<<,>>, unary
 * +,-,~, parentheses, ":labelname" label-value references, and calls to
 * enfloat/endouble/enflt/endbl (bit-reinterpret an integer as a float).
 * Values are represented as `double` throughout, matching how axx.py's
 * xeval() duck-types int/float together for this use case.
 *
 * Was previously entirely unimplemented in the C port: flt{}/dbl{}/qad{}
 * fell back to running the raw body text through the general expression
 * evaluator, which has no notion of ":label" or enfloat(...)-style calls
 * at all -- "enfloat" parsed as an (always-undefined) bare label
 * reference and ":label" mostly got silently dropped, producing a wrong
 * numeric result with no diagnostic. That silent-wrong-answer bug is
 * exactly what motivated implementing this properly instead of just
 * working around the symptom.
 *
 * Scope note: axx.py's xeval() also allows and/or/not, chained
 * comparisons, and a Python `a if b else c` ternary (it parses the whole
 * Python expression grammar via ast.parse). Those are not reproduced
 * here -- they don't serve xeval()'s actual purpose (building a
 * float32/float64/binary128 bit pattern from label values and
 * constants), and no shipped .axx pattern file relies on them there.
 * Extend the same way (see xeval_primary()/xeval_term()) if real usage
 * turns up.
 * ========================================================= */
typedef struct { const char *s; int i; int len; int ok; Assembler *asmb; } XEP;

static double xeval_expr(XEP *p);

static void xeval_skip(XEP *p){
    while(p->i<p->len && (p->s[p->i]==' '||p->s[p->i]=='\t')) p->i++;
}

/* NUMBER | ":labelname" | NAME '(' expr ')' | '(' expr ')' */
static double xeval_primary(XEP *p){
    xeval_skip(p);
    if(!p->ok || p->i>=p->len){ p->ok=0; return 0; }
    char c = p->s[p->i];
    if(c=='('){
        p->i++;
        double v = xeval_expr(p);
        xeval_skip(p);
        if(p->i<p->len && p->s[p->i]==')') p->i++;
        else p->ok=0;
        return v;
    }
    if(c==':'){
        p->i++;
        int start=p->i;
        while(p->i<p->len && (isalnum((unsigned char)p->s[p->i])||p->s[p->i]=='_'||p->s[p->i]=='.')) p->i++;
        if(p->i==start){ p->ok=0; return 0; }
        char name[512]; int n=p->i-start; if(n>(int)sizeof(name)-1) n=(int)sizeof(name)-1;
        memcpy(name,p->s+start,(size_t)n); name[n]='\0';
        /* Direct label-table lookup (mirrors axx.py xeval()'s replacer(),
         * which reads self.state.labels[...] directly rather than going
         * through get_value()/label_get_value() -- deliberately, so a
         * failed lookup here only sets error_undefined_label without
         * also printing its own "Label undefined" message; the outer
         * caller (whatever ends up checking the flag) is what reports
         * it, exactly once, if it's still set once evaluation finishes. */
        AsmState *st=&p->asmb->st;
        LabelEntry *e = lmap_find(&st->labels, name);
        if(!e || u256_is_undef_derived(e->value)){
            st->error_undefined_label = 1;
            return 0;
        }
        return (double)u256_to_i64(e->value);
    }
    if(isalpha((unsigned char)c) || c=='_'){
        int start=p->i;
        while(p->i<p->len && (isalnum((unsigned char)p->s[p->i])||p->s[p->i]=='_')) p->i++;
        char name[64]; int n=p->i-start; if(n>(int)sizeof(name)-1) n=(int)sizeof(name)-1;
        memcpy(name,p->s+start,(size_t)n); name[n]='\0';
        xeval_skip(p);
        if(p->i>=p->len || p->s[p->i]!='('){
            /* xeval() only allows bare names that are label placeholders
             * (handled above via ':') or calls to the 4 allowed
             * functions; anything else is a disallowed name in axx.py. */
            p->ok=0; return 0;
        }
        p->i++;
        double arg = xeval_expr(p);
        xeval_skip(p);
        if(p->i<p->len && p->s[p->i]==')') p->i++;
        else { p->ok=0; return 0; }
        if(strcmp(name,"enfloat")==0 || strcmp(name,"enflt")==0)
            return enfloat_bits((uint64_t)(int64_t)arg);
        if(strcmp(name,"endouble")==0 || strcmp(name,"endbl")==0)
            return endouble_bits((uint64_t)(int64_t)arg);
        p->ok=0; return 0;
    }
    if(isdigit((unsigned char)c) || c=='.'){
        int start=p->i;
        while(p->i<p->len && (isdigit((unsigned char)p->s[p->i])||p->s[p->i]=='.')) p->i++;
        if(p->i<p->len && (p->s[p->i]=='e'||p->s[p->i]=='E')){
            int save=p->i;
            p->i++;
            if(p->i<p->len && (p->s[p->i]=='+'||p->s[p->i]=='-')) p->i++;
            if(p->i<p->len && isdigit((unsigned char)p->s[p->i])){
                while(p->i<p->len && isdigit((unsigned char)p->s[p->i])) p->i++;
            } else p->i=save;
        }
        char buf[80]; int n=p->i-start; if(n>(int)sizeof(buf)-1) n=(int)sizeof(buf)-1;
        memcpy(buf,p->s+start,(size_t)n); buf[n]='\0';
        return atof(buf);
    }
    p->ok=0; return 0;
}

static double xeval_unary(XEP *p);

/* primary ('**' unary)?  -- right-associative, exponent may itself be unary
 * (so "2**-1" parses), matching Python's ** precedence/associativity. */
static double xeval_power(XEP *p){
    double base = xeval_primary(p);
    xeval_skip(p);
    if(p->ok && p->i+1<p->len && p->s[p->i]=='*' && p->s[p->i+1]=='*'){
        p->i+=2;
        double e = xeval_unary(p);
        return pow(base, e);
    }
    return base;
}

/* ('+'|'-'|'~') unary | power */
static double xeval_unary(XEP *p){
    xeval_skip(p);
    if(p->ok && p->i<p->len && p->s[p->i]=='+'){ p->i++; return xeval_unary(p); }
    if(p->ok && p->i<p->len && p->s[p->i]=='-'){ p->i++; return -xeval_unary(p); }
    if(p->ok && p->i<p->len && p->s[p->i]=='~'){
        p->i++;
        double v = xeval_unary(p);
        return (double)(~(int64_t)v);
    }
    return xeval_power(p);
}

/* unary (('//'|'/'|'%'|'*') unary)*  -- '//' checked before '/' */
static double xeval_term(XEP *p){
    double v = xeval_unary(p);
    while(p->ok){
        xeval_skip(p);
        if(p->i+1<p->len && p->s[p->i]=='/' && p->s[p->i+1]=='/'){
            p->i+=2; double t=xeval_unary(p);
            if(t==0){ p->ok=0; break; }
            v = floor(v/t);
        } else if(p->i<p->len && p->s[p->i]=='/'){
            p->i++; double t=xeval_unary(p);
            if(t==0){ p->ok=0; break; }
            v /= t;
        } else if(p->i<p->len && p->s[p->i]=='%'){
            p->i++; double t=xeval_unary(p);
            if(t==0){ p->ok=0; break; }
            v = v - floor(v/t)*t;
        } else if(p->i<p->len && p->s[p->i]=='*'
                  && !(p->i+1<p->len && p->s[p->i+1]=='*')){
            p->i++; v *= xeval_unary(p);
        } else break;
    }
    return v;
}

/* term (('+'|'-') term)* */
static double xeval_addsub(XEP *p){
    double v = xeval_term(p);
    while(p->ok){
        xeval_skip(p);
        if(p->i<p->len && p->s[p->i]=='+'){ p->i++; v += xeval_term(p); }
        else if(p->i<p->len && p->s[p->i]=='-'){ p->i++; v -= xeval_term(p); }
        else break;
    }
    return v;
}

/* addsub (('<<'|'>>') addsub)* */
static double xeval_shift(XEP *p){
    double v = xeval_addsub(p);
    while(p->ok){
        xeval_skip(p);
        if(p->i+1<p->len && p->s[p->i]=='<' && p->s[p->i+1]=='<'){
            p->i+=2; double t=xeval_addsub(p);
            v = (double)((int64_t)v << (int64_t)t);
        } else if(p->i+1<p->len && p->s[p->i]=='>' && p->s[p->i+1]=='>'){
            p->i+=2; double t=xeval_addsub(p);
            v = (double)((int64_t)v >> (int64_t)t);
        } else break;
    }
    return v;
}

/* shift ('&' shift)* */
static double xeval_band(XEP *p){
    double v = xeval_shift(p);
    while(p->ok){
        xeval_skip(p);
        if(p->i<p->len && p->s[p->i]=='&'){ p->i++; v = (double)((int64_t)v & (int64_t)xeval_shift(p)); }
        else break;
    }
    return v;
}

/* band ('^' band)* */
static double xeval_bxor(XEP *p){
    double v = xeval_band(p);
    while(p->ok){
        xeval_skip(p);
        if(p->i<p->len && p->s[p->i]=='^'){ p->i++; v = (double)((int64_t)v ^ (int64_t)xeval_band(p)); }
        else break;
    }
    return v;
}

/* bxor ('|' bxor)* */
static double xeval_expr(XEP *p){
    double v = xeval_bxor(p);
    while(p->ok){
        xeval_skip(p);
        if(p->i<p->len && p->s[p->i]=='|'){ p->i++; v = (double)((int64_t)v | (int64_t)xeval_bxor(p)); }
        else break;
    }
    return v;
}

/* Evaluate `text` (a qad{}/dbl{}/flt{} body) as an xeval expression.
 * Returns 1 and sets *out on success, 0 on a genuine parse/syntax error
 * (mirrors axx.py xeval() raising ValueError -- callers report their own
 * "cannot convert expression" message in that case). An undefined
 * ":label" reference is NOT a parse error: it returns 1 with *out=0, and
 * the caller finds out via st->error_undefined_label (set above),
 * exactly like axx.py's xeval(). */
static int xeval_eval(Assembler *asmb, const char *text, double *out){
    XEP p; p.s=text; p.i=0; p.len=(int)strlen(text); p.ok=1; p.asmb=asmb;
    double v = xeval_expr(&p);
    xeval_skip(&p);
    if(!p.ok || p.i<p.len) return 0;
    *out = v;
    return 1;
}

/* =========================================================
 * Expression evaluator
 * ========================================================= */
/* C (axx.py port): max expression recursion depth. Each nesting level consumes
 * several C stack frames; 500 is far beyond any real assembler expression yet
 * safely under typical 8MB stack limits. */
#define EXPR_MAX_DEPTH 500
static uint256_t expr_factor(Assembler *asmb, const char *s, int idx, int *idx_out);
static uint256_t expr_factor_impl(Assembler *asmb, const char *s, int idx, int *idx_out);
static uint256_t expr_factor1(Assembler *asmb, const char *s, int idx, int *idx_out);
static uint256_t expr_term0_0(Assembler *asmb, const char *s, int idx, int *idx_out);
static uint256_t expr_term0(Assembler *asmb, const char *s, int idx, int *idx_out);
static uint256_t expr_term1(Assembler *asmb, const char *s, int idx, int *idx_out);
static uint256_t expr_term2(Assembler *asmb, const char *s, int idx, int *idx_out);
static uint256_t expr_term3(Assembler *asmb, const char *s, int idx, int *idx_out);
static uint256_t expr_term4(Assembler *asmb, const char *s, int idx, int *idx_out);
static uint256_t expr_term5(Assembler *asmb, const char *s, int idx, int *idx_out);
static uint256_t expr_term6(Assembler *asmb, const char *s, int idx, int *idx_out);
static uint256_t expr_term7(Assembler *asmb, const char *s, int idx, int *idx_out);
static uint256_t expr_term8(Assembler *asmb, const char *s, int idx, int *idx_out);
static uint256_t expr_term9(Assembler *asmb, const char *s, int idx, int *idx_out);
static uint256_t expr_term10(Assembler *asmb, const char *s, int idx, int *idx_out);
static uint256_t expr_term11(Assembler *asmb, const char *s, int idx, int *idx_out);

/* Bug 4 fix: expr_terminate()
 * The original had a dead branch `if(l>0 && s[l-1]=='\0')` which can never
 * be true: strlen() returns the index of the first NUL, so s[l-1] is always
 * a non-NUL character when l>0.  The then-branch was therefore unreachable.
 * Simplified to the single always-taken path. */
static char *expr_terminate(const char *s){
    size_t l = strlen(s);
    char *r = malloc(l + 2);
    if(!r){ perror("malloc"); exit(1); }
    memcpy(r, s, l);
    r[l]   = '\0';
    r[l+1] = '\0';
    return r;
}

static uint256_t expr_expression_pat(Assembler *asmb, const char *s, int idx, int *idx_out){
    asmb->st.expmode=EXP_PAT;
    char *ts=expr_terminate(s);
    uint256_t r=expr_expression(asmb,ts,idx,idx_out);
    free(ts);
    return r;
}
static uint256_t expr_expression_asm(Assembler *asmb, const char *s, int idx, int *idx_out){
    asmb->st.expmode=EXP_ASM;
    char *ts=expr_terminate(s);
    uint256_t r=expr_expression(asmb,ts,idx,idx_out);
    free(ts);
    return r;
}
/* Fix C-4: expr_expression_esc() – stack-based bracket matching.
 *
 * The old implementation used two independent counters (depth for '()'
 * and bracket_depth for '[]').  This failed for mixed-bracket patterns
 * such as "([)]" or when stopchar is ')' while '[' is open: the counters
 * could go out of sync.
 *
 * Fix: push the opening bracket type onto a stack; pop only when the
 * matching closing bracket arrives.  stopchar is recognized only when the
 * stack is empty (depth == 0). */
static uint256_t expr_expression_esc(Assembler *asmb, const char *s, int idx, char stopchar, int *idx_out){
    size_t l = strlen(s);
    char *buf = malloc(l + 2);
    if(!buf){ perror("malloc"); exit(1); }
    memcpy(buf, s, idx);   /* copy prefix unchanged */

    /* Stack of opening brackets seen so far. */
    char stk[256];
    int  stkp = 0;

    for(size_t i = (size_t)idx; i < l; i++){
        char c = s[i];
        /* 【バグ修正①】Check depth-0 stopchar BEFORE opening-bracket test.
         * If stopchar is '(' or '[' or OB_CHAR, the old code pushed it onto
         * the stack instead of terminating the expression.  By checking
         * (stkp==0 && c==stopchar) first, any stopchar works correctly.
         *
         * Fix C-N5: include OB_CHAR(0x90)/CB_CHAR(0x91) in the bracket stack. */
        if(stkp == 0 && c == stopchar){
            /* Depth-0 stopchar → terminate expression */
            buf[i] = '\0';
        } else if(c == '(' || c == '[' || c == OB_CHAR){
            /* Opening bracket: push and copy */
            if(stkp < (int)(sizeof(stk)-1)) stk[stkp++] = c;
            buf[i] = c;
        } else if(c == ')' || c == ']' || c == CB_CHAR){
            /* Closing bracket – determine the matching opener */
            char expected = (c == ')') ? '(' : (c == ']') ? '[' : OB_CHAR;
            if(stkp > 0 && stk[stkp-1] == expected){
                /* Matched: pop, copy normally */
                stkp--;
                buf[i] = c;
            } else if(stkp == 0 && c == stopchar){
                /* Depth-0 match of stopchar → terminate expression */
                buf[i] = '\0';
            } else {
                /* Mismatched closing bracket (malformed input) – copy as-is */
                buf[i] = c;
            }
        } else {
            if(stkp == 0 && c == stopchar)
                buf[i] = '\0';
            else
                buf[i] = c;
        }
    }
    buf[l] = '\0';
    char *ts = expr_terminate(buf);
    free(buf);
    uint256_t r = expr_expression(asmb, ts, idx, idx_out);
    free(ts);
    return r;
}

/* Note: xeval() has been removed (Fix P12). Float-mode expressions that
 * previously required a python3 subprocess are now evaluated directly by
 * the assembler's own expression evaluator in float mode.                    */

static uint256_t expr_factor(Assembler *asmb, const char *s, int idx, int *idx_out){
    /* C (axx.py port): recursion depth guard. expr_factor is the hub through
     * which all recursion passes (unary -,~,@ recurse into expr_factor; '('
     * recurses expr_factor1 -> expr_expression -> ... -> expr_factor), so
     * guarding here protects every nested-expression path from a native stack
     * overflow. Mirrors axx.py's factor/_factor_impl split. */
    AsmState *st=&asmb->st;
    if(st->expr_depth >= EXPR_MAX_DEPTH){
        if(should_report_errors(st))
            fprintf(stderr," error - expression nesting too deep.\n");
        if(idx_out) *idx_out = idx;
        return u256_zero();
    }
    st->expr_depth++;
    uint256_t r = expr_factor_impl(asmb,s,idx,idx_out);
    st->expr_depth--;
    return r;
}
static uint256_t expr_factor_impl(Assembler *asmb, const char *s, int idx, int *idx_out){
    AsmState *st=&asmb->st;
    idx=axx_skipspc(s,idx);
    uint256_t x=u256_zero();
    int slen=(int)strlen(s);

    if(idx+4<=slen && strncmp(s+idx,"!!!!",4)==0 && st->expmode==EXP_PAT){
        x=u256_from_i64(st->vliwstop); idx+=4;
        if(asmb->st.exp_typ_float) x=double_to_u256((double)st->vliwstop);
    } else if(idx+3<=slen && strncmp(s+idx,"!!!",3)==0 && st->expmode==EXP_PAT){
        x=u256_from_i64(st->vcnt); idx+=3;
        if(asmb->st.exp_typ_float) x=double_to_u256((double)st->vcnt);
    } else if(s[idx]=='-'){
        x=expr_factor(asmb,s,idx+1,&idx);
        if(asmb->st.exp_typ_float){
            double d=u256_to_double(x);
            x=double_to_u256(-d);
        } else {
            x=u256_neg(x);
        }
    } else if(s[idx]=='~'){
        x=expr_factor(asmb,s,idx+1,&idx);
        /* ~ is bitwise NOT: always integer, same as Python (int only) */
        x=u256_not(x);
    } else if(s[idx]=='@'){
        x=expr_factor(asmb,s,idx+1,&idx);
        /* nbit(x) is always integer; in float mode promote to double */
        int nb = u256_nbit(x);
        if(asmb->st.exp_typ_float)
            x=double_to_u256((double)nb);
        else
            x=u256_from_i64(nb);
    } else if(s[idx]=='*'){
        if(idx+1<slen && s[idx+1]=='('){
            int i2;
            x=expr_expression(asmb,s,idx+2,&i2); idx=i2;
            if(s[idx]==','){
                int i3;
                uint256_t x2=expr_expression(asmb,s,idx+1,&i3); idx=i3;
                if(s[idx]==')'){
                    idx++;
                    int shift=(int)(u256_to_i64(x2)*8);
                    x=u256_sar(x,shift);
                } else {
                    /* 修正⑩: missing ')' – report error and return 0 */
                    fprintf(stderr," error - missing ')' in *(expr, expr) expression.\n");
                    x=u256_zero();
                }
            } else {
                /* 修正⑩: missing ',' – report error and return 0 */
                fprintf(stderr," error - missing ',' in *(expr, expr) expression.\n");
                x=u256_zero();
            }
        } else x=u256_zero();
    } else {
        x=expr_factor1(asmb,s,idx,&idx);
    }
    idx=axx_skipspc(s,idx);
    *idx_out=idx;
    return x;
}

/* Parse a C-style '\xHH' character literal (1-2 hex digits) at s[idx]
 * (pointing at the opening quote). Fix (axx.py port): expr_factor1() below
 * hand-lists a fixed set of '\t'/'\''/'\\'/... escapes plus a generic 3-char
 * 'x' literal, but had no case for '\xHH' -- so e.g. "MOV '\x41'" (meant to
 * be equivalent to "MOV 'A'") failed with a syntax error even though it's a
 * form axx documents/recognizes elsewhere (skip_squote_literal handling in
 * axx.py; the C comment-stripper here also tolerates a bare backslash before
 * a quoted-out ';'). Returns 1 and sets *val/*out_idx on success, 0 (idx
 * unchanged) otherwise so the caller can fall through to other literal forms. */
static int parse_hex_char_literal(const char *s, int idx, int slen, int *val, int *out_idx){
    if(!(idx+3<=slen && s[idx]=='\'' && s[idx+1]=='\\' && (s[idx+2]=='x'||s[idx+2]=='X')))
        return 0;
    int j = idx+3;
    int v = 0, ndig = 0;
    while(j<slen && ndig<2 && is_xdigit_upper(axx_upper_char(s[j]))){
        char c = axx_upper_char(s[j]);
        v = v*16 + (is_digit(c) ? c-'0' : c-'A'+10);
        j++; ndig++;
    }
    if(ndig>0 && j<slen && s[j]=='\''){
        *val=v; *out_idx=j+1; return 1;
    }
    return 0;
}

static uint256_t expr_factor1(Assembler *asmb, const char *s, int idx, int *idx_out){
    AsmState *st=&asmb->st;
    uint256_t x=u256_zero();
    idx=axx_skipspc(s,idx);
    int slen=(int)strlen(s);
    int _hexlit_val=0, _hexlit_end=idx;
    int _hexlit_ok = parse_hex_char_literal(s, idx, slen, &_hexlit_val, &_hexlit_end);

    if(idx>=slen||s[idx]=='\0'){ *idx_out=idx; return x; }

    if(s[idx]=='('){
        x=expr_expression(asmb,s,idx+1,&idx);
        if(s[idx]==')') idx++;
    }
    else if(idx+4<=slen && strncmp(s+idx,"'\\t'",4)==0){ x=u256_from_i64(0x09); idx+=4;
        if(asmb->st.exp_typ_float) x=double_to_u256(9.0); }
    else if(idx+4<=slen && strncmp(s+idx,"'\\''",4)==0){ x=u256_from_i64('\''); idx+=4;
        if(asmb->st.exp_typ_float) x=double_to_u256((double)'\''); }
    else if(idx+4<=slen && strncmp(s+idx,"'\\\\'",4)==0){ x=u256_from_i64('\\'); idx+=4;
        if(asmb->st.exp_typ_float) x=double_to_u256((double)'\\'); }
    else if(idx+4<=slen && strncmp(s+idx,"'\\n'",4)==0){ x=u256_from_i64(0x0a); idx+=4;
        if(asmb->st.exp_typ_float) x=double_to_u256(10.0); }
    else if(idx+4<=slen && strncmp(s+idx,"'\\0'",4)==0){ x=u256_from_i64(0x00); idx+=4;
        if(asmb->st.exp_typ_float) x=double_to_u256(0.0); }
    else if(idx+4<=slen && strncmp(s+idx,"'\\r'",4)==0){ x=u256_from_i64(0x0d); idx+=4;
        if(asmb->st.exp_typ_float) x=double_to_u256(13.0); }
    else if(idx+4<=slen && strncmp(s+idx,"'\\a'",4)==0){ x=u256_from_i64(0x07); idx+=4;
        if(asmb->st.exp_typ_float) x=double_to_u256(7.0); }
    else if(idx+4<=slen && strncmp(s+idx,"'\\b'",4)==0){ x=u256_from_i64(0x08); idx+=4;
        if(asmb->st.exp_typ_float) x=double_to_u256(8.0); }
    else if(idx+4<=slen && strncmp(s+idx,"'\\f'",4)==0){ x=u256_from_i64(0x0c); idx+=4;
        if(asmb->st.exp_typ_float) x=double_to_u256(12.0); }
    else if(idx+4<=slen && strncmp(s+idx,"'\\v'",4)==0){ x=u256_from_i64(0x0b); idx+=4;
        if(asmb->st.exp_typ_float) x=double_to_u256(11.0); }
    else if(_hexlit_ok){ x=u256_from_i64(_hexlit_val); idx=_hexlit_end;
        if(asmb->st.exp_typ_float) x=double_to_u256((double)_hexlit_val); }
    /* Fix: 3-char 'x' literal: only when s[idx+1] is NOT backslash (so '\x' forms above
     * are not double-consumed). Mirrors axx.py factor1() Fix 3 guard. */
    else if(idx+3<=slen && s[idx]=='\'' && s[idx+1] != '\\' && s[idx+2]=='\''){
        unsigned char cv=(unsigned char)s[idx+1]; x=u256_from_i64(cv); idx+=3;
        if(asmb->st.exp_typ_float) x=double_to_u256((double)cv); }
    else if(axx_q(s,slen,"$$",idx)){
        idx+=2;
        /* binary_list中(makeobj内)では命令先頭アドレスpc_instr_startを返す。
         * .equなど他のコンテキストでは現在のPC(st->pc)を返す。 */
        x = st->in_binary_list ? st->pc_instr_start : st->pc;
        /* 破綻点修正 (axx.py port): $$は常に現在セクション(current_section)
         * 内の生グローバルpcだった。同じセクションへの再入があると、ラベル
         * 参照(label_get_value(), 同じセクションの場合はセクション内相対
         * オフセットへ変換済み)と単位が食い違い、"e-$$-2"のようなPC相対
         * エンコード式(z80のJR等)が誤った値になっていた。$$も同じ
         * セクション内相対オフセットに揃える。
         *
         * 破綻点修正2 (重大): ただしこの変換は、命令のバイト列を組み立てて
         * いる最中(in_binary_list、makeobj())か、reloc_type未指定の.EQU式
         * 評価中(equ_section_tracking)に限定する。これら以外(reloc_type
         * 付き.EQUの右辺など)で$$が使われる場合、その値は「生のpc」の
         * まま維持されるべきであり、無条件に変換すると別の破綻点を生む
         * (label_get_value()の同種の条件分岐を参照。bf.sのtape_aが
         * 壊れてbus errorになった実例で確認済み)。 */
        if(st->in_binary_list || st->equ_section_tracking){
            int64_t _adj = equ_section_relative_offset(st, st->current_section, u256_to_u64(x));
            if(_adj >= 0) x = u256_from_u64((uint64_t)_adj);
        }
        /* In float mode, treat PC as an integer-valued double (int→float). */
        if(asmb->st.exp_typ_float)
            x=double_to_u256((double)(int64_t)u256_to_u64(x));
    }
    else if(axx_q(s,slen,"$.",idx)){
        idx+=2;
        /* $.は常に「その命令の次のアドレス」を返す。
         * binary_list中/外・pass0(対話モード)を問わず pc_instr_end を返す。
         * pc_instr_end はパターンマッチ確定直後のサイズプローブで設定済み。 */
        x = st->pc_instr_end;
        if(st->in_binary_list || st->equ_section_tracking){
            int64_t _adj = equ_section_relative_offset(st, st->current_section, u256_to_u64(x));
            if(_adj >= 0) x = u256_from_u64((uint64_t)_adj);
        }
        if(asmb->st.exp_typ_float)
            x=double_to_u256((double)(int64_t)u256_to_u64(x));
    }
    else if(axx_q(s,slen,"#",idx)){
        idx++;
        char t[512];
        idx=axx_get_symbol_word(s,idx,st->swordchars,t,sizeof(t));
        uint256_t sv;
        if(symbol_get(st,t,&sv)) x=sv; else x=u256_zero();
        if(asmb->st.exp_typ_float)
            x=double_to_u256((double)(int64_t)u256_to_u64(x));
    }
    else if(axx_q(s,slen,"0b",idx)){
        idx+=2;
        while(s[idx]=='0'||s[idx]=='1'){
            x=u256_add(u256_mul(x,u256_from_u64(2)), u256_from_u64(s[idx]-'0'));
            idx++;
        }
        /* In float mode, promote integer value to double (Python auto-promotion) */
        if(asmb->st.exp_typ_float)
            x=double_to_u256((double)(int64_t)u256_to_i64(x));
    }
    else if(axx_q(s,slen,"0x",idx)){
        idx+=2;
        while(s[idx]&&is_xdigit_upper(axx_upper_char(s[idx]))){
            int d; char c=axx_upper_char(s[idx]);
            d=(c>='A')?(c-'A'+10):(c-'0');
            x=u256_add(u256_mul(x,u256_from_u64(16)), u256_from_u64((uint64_t)d));
            idx++;
        }
        /* In float mode, promote integer value to double (Python auto-promotion) */
        if(asmb->st.exp_typ_float)
            x=double_to_u256((double)(int64_t)u256_to_i64(x));
    }
    /* Fix: guard all keyword tokens (qad/dbl/flt/enflt/endbl) so labels like
     * qad_foo, dbl_val, etc. are NOT consumed as keywords.
     * Mirrors axx.py factor1(): only treat as keyword when '{' follows (after spaces). */
    else if(idx+3<=slen && strncmp(s+idx,"qad",3)==0 &&
            ({ int _j=axx_skipspc(s,idx+3); _j<slen && s[_j]=='{'; })){
        idx+=3;
        idx=axx_skipspc(s,idx);
        if(s[idx]=='{'){
            idx++;
            /* Read full expression up to matching '}', handling nested '()' */
            char expr_buf[1024]; size_t en=0; int depth=0;
            while(s[idx] && en<sizeof(expr_buf)-1){
                if(s[idx]=='('||s[idx]=='[') depth++;
                else if((s[idx]==')'||s[idx]==']')&&depth>0) depth--;
                else if(s[idx]=='}'&&depth==0) break;
                expr_buf[en++]=s[idx++];
            }
            expr_buf[en]='\0';
            if(s[idx]=='}') idx++;
#if defined(__GNUC__) && !defined(__STRICT_ANSI__) && \
    (defined(__x86_64__) || defined(__i386__) || defined(__aarch64__) || \
     defined(__arm__) || defined(__riscv))
            /* Evaluate in full __float128 precision matching mpmath */
            int q_ok=0;
            uint256_t qbits = f128_eval_text(expr_buf, &q_ok);
            if(q_ok){ x=qbits; }
            else
#endif
            {
                /* axx.py port: f128_eval_text() only handles pure
                 * arithmetic (no labels/functions), mirroring
                 * decimal_eval_expr() on the Python side -- try xeval()
                 * next (":label" references, enfloat/endouble/enflt/
                 * endbl calls), matching axx.py's qad{} handler, which
                 * falls back from decimal_eval_expr() to xeval() before
                 * giving up. Only fall further back to the general
                 * expression evaluator (no label/function support
                 * either, but historically what this file did) if even
                 * that fails to parse. */
                double xv;
                if(xeval_eval(asmb, expr_buf, &xv)){
                    char fstr[64]; snprintf(fstr,sizeof(fstr),"%.17g",xv);
                    x=ieee754_128_from_str(fstr);
                } else {
                    int io2;
                    int prev_flt=asmb->st.exp_typ_float;
                    /* Bugfix: this fallback tier doesn't exist in axx.py at
                     * all (its qad{}/dbl{}/flt{} handlers only ever call
                     * xeval(), never a general evaluator) -- it's a C-only
                     * robustness addition for bodies xeval() can't parse.
                     * Since axx.py never fails the whole build over what
                     * happens inside qad{}/dbl{}/flt{}'s own evaluation
                     * (e.g. "qad{1/0}" just prints its own message and uses
                     * 0, exit 0), this fallback must not be able to set
                     * had_error either -- otherwise a div-by-zero inside it
                     * (which expr_term0() now correctly flags as a build
                     * failure for ordinary operands) would abort a build
                     * that axx.py completes successfully. */
                    int _prior_had_error=asmb->st.had_error;
                    asmb->st.exp_typ_float=1;
                    uint256_t fv=expr_expression_pat(asmb,expr_buf,0,&io2);
                    asmb->st.exp_typ_float=prev_flt;
                    asmb->st.had_error=_prior_had_error;
                    double dv=u256_to_double(fv);
                    char fstr[64]; snprintf(fstr,sizeof(fstr),"%.17g",dv);
                    x=ieee754_128_from_str(fstr);
                }
            }
        }
    }
    /* enflt{expr}: evaluate expr in integer mode, interpret 32 low bits as
     * IEEE754 float32, return the float value.
     * Mirrors axx.py factor1():
     *   v, _ = self.expression(t + chr(0), 0)   # integer mode
     *   x = enflt(int(v))                        # = enfloat(int(v))
     * The result is a floating-point value; callers should use this inside
     * flt{} / dbl{} or in a float-mode context. */
    else if(idx+5<=slen && strncmp(s+idx,"enflt",5)==0 &&
            ({ int _j=axx_skipspc(s,idx+5); _j<slen && s[_j]=='{'; })){
        idx+=5;
        int f; char t[512];
        idx=axx_get_curlb(s,idx,&f,t,sizeof(t));
        if(f){
            /* Always evaluate inner expression in integer mode */
            int prev_flt=asmb->st.exp_typ_float;
            asmb->st.exp_typ_float=0;
            int io2; uint256_t iv=expr_expression_pat(asmb,t,0,&io2);
            asmb->st.exp_typ_float=prev_flt;
            double fval=enfloat_bits(u256_to_u64(iv));
            /* Return as double bit-cast (float mode value) */
            x=double_to_u256(fval);
        }
    }
    /* endbl{expr}: evaluate expr in integer mode, interpret 64 bits as
     * IEEE754 float64, return the double value.
     * Mirrors axx.py factor1():
     *   v, _ = self.expression(t + chr(0), 0)   # integer mode
     *   x = endbl(int(v))                        # = endouble(int(v))  */
    else if(idx+5<=slen && strncmp(s+idx,"endbl",5)==0 &&
            ({ int _j=axx_skipspc(s,idx+5); _j<slen && s[_j]=='{'; })){
        idx+=5;
        int f; char t[512];
        idx=axx_get_curlb(s,idx,&f,t,sizeof(t));
        if(f){
            int prev_flt=asmb->st.exp_typ_float;
            asmb->st.exp_typ_float=0;
            int io2; uint256_t iv=expr_expression_pat(asmb,t,0,&io2);
            asmb->st.exp_typ_float=prev_flt;
            double fval=endouble_bits(u256_to_u64(iv));
            x=double_to_u256(fval);
        }
    }
    else if(idx+3<=slen && strncmp(s+idx,"dbl",3)==0 &&
            ({ int _j=axx_skipspc(s,idx+3); _j<slen && s[_j]=='{'; })){
        idx+=3;
        int f; char t[512];
        idx=axx_get_curlb(s,idx,&f,t,sizeof(t));
        if(f){
            uint64_t bits;
            if(strcmp(t,"nan")==0) bits=0x7ff8000000000000ULL;
            else if(strcmp(t,"inf")==0) bits=0x7ff0000000000000ULL;
            else if(strcmp(t,"-inf")==0) bits=0xfff0000000000000ULL;
            else {
                /* axx.py port: dbl{} always evaluates its body via
                 * xeval() (":label" refs, enfloat/endouble/enflt/endbl
                 * calls) -- it never falls back to the general
                 * expression grammar, which doesn't understand either of
                 * those. Only fall back here (native C evaluator, no
                 * label/function support) if xeval() can't parse the
                 * body at all, for robustness on anything relying on
                 * plain arithmetic this port's xeval() doesn't cover. */
                double xv;
                if(xeval_eval(asmb, t, &xv)){
                    memcpy(&bits,&xv,8);
                } else {
                    /* Bugfix: see the identical comment in qad{}'s fallback
                     * above -- this native-evaluator tier is C-only and
                     * must not be able to set had_error, or a div-by-zero
                     * inside it would abort a build axx.py completes
                     * successfully (dbl{1/0} just prints its own message
                     * and uses 0 there). */
                    int prev_flt = asmb->st.exp_typ_float;
                    int _prior_had_error = asmb->st.had_error;
                    asmb->st.exp_typ_float = 1;
                    int io2; uint256_t fv = expr_expression_pat(asmb,t,0,&io2);
                    asmb->st.exp_typ_float = prev_flt;
                    asmb->st.had_error = _prior_had_error;
                    double v = u256_to_double(fv);
                    memcpy(&bits,&v,8);
                }
            }
            /* Bugfix: dbl{}'s result is conceptually an INTEGER (the
             * float64 bit-pattern, matching axx.py's plain Python int),
             * usable directly in an integer-mode encoding expression --
             * but in float mode this file represents every uint256_t
             * "value" as the bit-cast of a C double (see u256_to_double()/
             * double_to_u256(), and the identical promotion already done
             * for 0x.../0b... literals just above in this same function).
             * Storing `bits` via u256_from_u64() unconditionally left a
             * float-mode consumer's later u256_to_double() call
             * bit-reinterpreting the raw integer bits as if they were
             * already an encoded double -- garbage in every realistic
             * case (e.g. dbl{}/flt{} nested inside a !D/!F capture, which
             * evaluates its source text in float mode) instead of the
             * intended numeric value. */
            x = asmb->st.exp_typ_float ? double_to_u256((double)bits) : u256_from_u64(bits);
        }
    }
    else if(idx+3<=slen && strncmp(s+idx,"flt",3)==0 &&
            ({ int _j=axx_skipspc(s,idx+3); _j<slen && s[_j]=='{'; })){
        idx+=3;
        int f; char t[512];
        idx=axx_get_curlb(s,idx,&f,t,sizeof(t));
        if(f){
            uint32_t bits;
            if(strcmp(t,"nan")==0) bits=0x7fc00000u;
            else if(strcmp(t,"inf")==0) bits=0x7f800000u;
            else if(strcmp(t,"-inf")==0) bits=0xff800000u;
            else {
                /* See dbl{}'s comment just above: xeval() first, native
                 * evaluator only as a fallback for anything xeval() can't
                 * parse. */
                double xv;
                if(xeval_eval(asmb, t, &xv)){
                    float v = (float)xv;
                    memcpy(&bits,&v,4);
                } else {
                    /* Bugfix: see qad{}'s fallback comment above -- must
                     * not let this C-only tier set had_error. */
                    int prev_flt = asmb->st.exp_typ_float;
                    int _prior_had_error = asmb->st.had_error;
                    asmb->st.exp_typ_float = 1;
                    int io2; uint256_t fv = expr_expression_pat(asmb,t,0,&io2);
                    asmb->st.exp_typ_float = prev_flt;
                    asmb->st.had_error = _prior_had_error;
                    float v = (float)u256_to_double(fv);
                    memcpy(&bits,&v,4);
                }
            }
            /* See dbl{}'s comment above: same integer-vs-float-mode
             * value-representation fix. */
            x = asmb->st.exp_typ_float ? double_to_u256((double)bits) : u256_from_u64(bits);
        }
    }
    else if(idx+4<=slen && axx_q(s,slen,"not(",idx)){
        /* not(expr): logical negation, written as a call-like form rather
         * than a prefix operator so it reads unambiguously in pattern text.
         * Bugfix (mirrors the identical fix applied to axx.py
         * ExpressionEvaluator.factor1()/term8()): this used to be handled
         * in expr_term8() (between expr_term7 comparisons and expr_term9
         * &&), calling expr_expression() starting at the '(' itself. That
         * re-entered the ENTIRE term-chain, so after the matching ')' was
         * consumed, the surrounding term7/term9/term10/term11 layers of
         * that SAME re-entrant call kept consuming any trailing operator
         * (+, -, comparisons, &&, ||, ?:) as if it were still part of
         * not()'s argument -- e.g. "not(0)+5" evaluated as "not(0+5)".
         * Handling it here instead (expr_factor1, the base of the
         * precedence chain) makes its result an ordinary atom to every
         * operator above it on EITHER side, exactly like the plain '('
         * grouping case just above. */
        x=expr_expression(asmb,s,idx+4,&idx);
        idx=axx_skipspc(s,idx);
        if(idx<slen && s[idx]==')') idx++;
        else fprintf(stderr," error - missing closing ')' in not(...) expression.\n");
        x=u256_from_i64(u256_is_zero(x)?1:0);
    }
    /* Float-mode number literal: parsed by axx_get_floatstr() as a double.
     * This branch is checked BEFORE the integer branch so that "3.14" is
     * consumed as a float literal when exp_typ_float == 1.
     * Mirrors axx.py factor1():
     *   elif self.state.exp_typ=='f' and isfloatstr(s,idx): x = float(fs) */
    else if(asmb->st.exp_typ_float && axx_isfloatstr(s,idx)){
        char fs[64];
        idx=axx_get_floatstr(s,idx,fs,sizeof(fs));
        if(fs[0]) x=double_to_u256(strtod(fs,NULL));
    }
    else if(is_digit(s[idx])){
        char fs[64];
        idx=axx_get_intstr(s,idx,fs,sizeof(fs));
        x=u256_zero();
        uint256_t ten=u256_from_u64(10);
        for(int di=0;fs[di];di++) x=u256_add(u256_mul(x,ten),u256_from_u64((uint64_t)(fs[di]-'0')));
    }
    else if(st->expmode==EXP_PAT && is_lower(s[idx]) && (s[idx+1]=='\0'||!is_lower(s[idx+1]))){
        char ch=s[idx];
        if(idx+3<=slen && s[idx+1]==':'&&s[idx+2]=='='){
            x=expr_expression(asmb,s,idx+3,&idx);
            var_put(st,ch,x);
        } else {
            x=var_get(st,ch);
            idx++;
            /* Fix (axx.py port): detect UNDEF values in pattern variables during
             * makeobj evaluation.
             *
             * When in_match_attempt=1, label_get_value() suppresses its error
             * output and stores UNDEF (0xff…ff) in the variable via var_put().
             * makeobj() later reads the variable through var_get() — NOT through
             * label_get_value() — so error_undefined_label is never set and no
             * error is emitted even though the assembled word is garbage.
             *
             * Fix: when NOT in a match attempt, NOT in pass1_size_mode, and in
             * pass2 or interactive mode, check whether the variable holds UNDEF
             * (0xff…ff) or an UNDEF-derived value (>= 2^128, which can arise from
             * arithmetic on UNDEF).  If so, set error_undefined_label and emit
             * the error, matching the behaviour of label_get_value() for directly
             * referenced undefined labels.
             *
             * Mirrors the identical fix applied to axx.py factor1():
             *   _UNDEF_THRESHOLD = 1 << 128
             *   if (not _in_match_attempt and not _pass1_size_mode
             *           and (pas==2 or pas==0)
             *           and (x == UNDEF or x >= _UNDEF_THRESHOLD)):
             *       error_undefined_label = True
             *       print(" error - Label undefined: variable … ")
             */
            if(!st->in_match_attempt
               && !st->pass1_size_mode
               && should_report_errors(st)){
                /* B (axx.py port): centralized detection, threshold raised to 2^192. */
                if(u256_is_undef_derived(x)){
                    st->error_undefined_label = 1;
                    fprintf(stderr,
                        " error - Label undefined: variable '%c' contains undefined value"
                        "  [%s:%d]\n",
                        ch, st->current_file, (int)st->ln);
                }
            }
            /* In float mode, promote the variable's stored integer value to
             * double, matching Python's automatic int→float type promotion.
             * Exception: if the variable was captured by !F/!D (float bit-
             * pattern), the value is already stored as a double bit-cast and
             * must NOT be re-promoted.  We detect this by checking whether the
             * raw w[0] pattern, when decoded as int64, produces the same double
             * as when decoded as a double — if different, it's a double already.
             *
             * Simpler heuristic: just convert via (double)(int64_t)val.
             * This is what Python does: all values in the assembler are Python
             * ints; float mode only changes how *literals* are parsed.  When a
             * pattern variable is read in float mode it starts as an int and
             * Python auto-promotes it in any float arithmetic/comparison.
             * Variables set by !F/!D store integer BIT PATTERNS, not floats;
             * their bit-patterns happen to be used in integer-mode makeobj, not
             * in float-mode expressions.  So (double)(int64_t)val is correct. */
            if(asmb->st.exp_typ_float)
                x=double_to_u256((double)(int64_t)u256_to_i64(x));
            /* ELF tracking: if inside makeobj and the variable was captured
             * from a single label by match(), record it as a relocation ref. */
            if(st->elf_tracking && st->elf_current_word_idx >= 0){
                int _vi = (unsigned char)ch - 'a';
                if(_vi >= 0 && _vi < 26 && st->elf_var_to_label[_vi].set == 1){
                    if(st->elf_refs_len >= st->elf_refs_cap){
                        st->elf_refs_cap = st->elf_refs_cap ? st->elf_refs_cap*2 : 8;
                        st->elf_refs = realloc(st->elf_refs,
                            st->elf_refs_cap * sizeof(st->elf_refs[0]));
                        if(!st->elf_refs){ perror("realloc"); exit(1); }
                    }
                    st->elf_refs[st->elf_refs_len].name     = strdup(st->elf_var_to_label[_vi].label_name);
                    st->elf_refs[st->elf_refs_len].val      = st->elf_var_to_label[_vi].label_val;
                    st->elf_refs[st->elf_refs_len].word_idx = st->elf_current_word_idx;
                    st->elf_refs_len++;
                }
            }
        }
    }
    else if(s[idx]&&char_in(s[idx],st->lwordchars)){
        char w[512];
        int new_idx=axx_get_label_word(s,idx,st->lwordchars,w,sizeof(w));
        if(new_idx!=idx){
            idx=new_idx;
            x=label_get_value(st,w);
            /* In float mode, treat label's integer address as an integer-valued
             * double (int→float), not as a bit-cast of the address bits.
             * Mirrors Python: label values are substituted as decimal strings
             * in xeval(), then parsed as integers before float promotion. */
            if(asmb->st.exp_typ_float && !st->error_undefined_label)
                x=double_to_u256((double)(int64_t)u256_to_u64(x));
        }
    }

    idx=axx_skipspc(s,idx);
    *idx_out=idx;
    return x;
}

static uint256_t expr_term0_0(Assembler *asmb, const char *s, int idx, int *idx_out){
    uint256_t x=expr_factor(asmb,s,idx,&idx);
    int slen=(int)strlen(s);
    while(idx<slen && axx_q(s,slen,"**",idx)){
        uint256_t t=expr_factor(asmb,s,idx+2,&idx);
        if(asmb->st.exp_typ_float){
            double a=u256_to_double(x), b=u256_to_double(t);
            x=double_to_u256(pow(a,b));
        } else {
            x=u256_pow(x,t);
        }
    }
    *idx_out=idx; return x;
}

static uint256_t expr_term0(Assembler *asmb, const char *s, int idx, int *idx_out){
    uint256_t x=expr_term0_0(asmb,s,idx,&idx);
    int slen=(int)strlen(s);
    while(idx<slen){
        int flt=asmb->st.exp_typ_float;
        if(s[idx]=='*'&&s[idx+1]!='*'){
            uint256_t t=expr_term0_0(asmb,s,idx+1,&idx);
            if(flt) x=double_to_u256(u256_to_double(x)*u256_to_double(t));
            else    x=u256_mul_signed(x,t);
        } else if(axx_q(s,slen,"//",idx)){
            /* Floor division */
            uint256_t t=expr_term0_0(asmb,s,idx+2,&idx);
            if(flt){
                double b=u256_to_double(t);
                if(b==0.0){
                    /* Bugfix (axx.py port): this used to print a bare
                     * "Division by 0 error." with no " error -" prefix and
                     * no had_error, so a division-by-zero in an ordinary
                     * instruction operand silently produced a plausible-
                     * looking 0 with a build that still reported success. */
                    if(should_report_errors(&asmb->st)){
                        fprintf(stderr," error - Division by 0 error.\n");
                        asmb->st.had_error = 1;
                    }
                    x=double_to_u256(0.0);
                }
                else x=double_to_u256(floor(u256_to_double(x)/b));
            } else {
                /* Fix L: set x=0 on div-by-zero; previously x kept the old
                 * dividend value, making 'a//0' silently return 'a'. */
                if(u256_is_zero(t)){
                    if(should_report_errors(&asmb->st)){
                        fprintf(stderr," error - Division by 0 error.\n");
                        asmb->st.had_error = 1;
                    }
                    x=u256_zero();
                }
                else x=u256_floordiv(x,t);
            }
        } else if(s[idx]=='/'&&s[idx+1]!='/'){
            /* True division */
            uint256_t t=expr_term0_0(asmb,s,idx+1,&idx);
            if(flt){
                double b=u256_to_double(t);
                if(b==0.0){
                    /* Bugfix (axx.py port): this used to print a bare
                     * "Division by 0 error." with no " error -" prefix and
                     * no had_error, so a division-by-zero in an ordinary
                     * instruction operand silently produced a plausible-
                     * looking 0 with a build that still reported success. */
                    if(should_report_errors(&asmb->st)){
                        fprintf(stderr," error - Division by 0 error.\n");
                        asmb->st.had_error = 1;
                    }
                    x=double_to_u256(0.0);
                }
                else x=double_to_u256(u256_to_double(x)/b);
            } else {
                /* Fix L: same as // fix */
                if(u256_is_zero(t)){
                    if(should_report_errors(&asmb->st)){
                        fprintf(stderr," error - Division by 0 error.\n");
                        asmb->st.had_error = 1;
                    }
                    x=u256_zero();
                }
                else x=u256_floordiv(x,t);
            }
        } else if(s[idx]=='%'){
            uint256_t t=expr_term0_0(asmb,s,idx+1,&idx);
            if(flt){
                double b=u256_to_double(t);
                if(b==0.0){
                    /* Bugfix (axx.py port): this used to print a bare
                     * "Division by 0 error." with no " error -" prefix and
                     * no had_error, so a division-by-zero in an ordinary
                     * instruction operand silently produced a plausible-
                     * looking 0 with a build that still reported success. */
                    if(should_report_errors(&asmb->st)){
                        fprintf(stderr," error - Division by 0 error.\n");
                        asmb->st.had_error = 1;
                    }
                    x=double_to_u256(0.0);
                }
                else x=double_to_u256(fmod(u256_to_double(x),b));
            } else {
                /* Fix L: same as // fix */
                if(u256_is_zero(t)){
                    if(should_report_errors(&asmb->st)){
                        fprintf(stderr," error - Division by 0 error.\n");
                        asmb->st.had_error = 1;
                    }
                    x=u256_zero();
                }
                else x=u256_mod(x,t);
            }
        } else break;
    }
    *idx_out=idx; return x;
}

static uint256_t expr_term1(Assembler *asmb, const char *s, int idx, int *idx_out){
    uint256_t x=expr_term0(asmb,s,idx,&idx);
    int slen=(int)strlen(s);
    while(idx<slen){
        int flt=asmb->st.exp_typ_float;
        if(s[idx]=='+'){
            uint256_t t=expr_term0(asmb,s,idx+1,&idx);
            if(flt) x=double_to_u256(u256_to_double(x)+u256_to_double(t));
            else    x=u256_add(x,t);
        } else if(s[idx]=='-'){
            uint256_t t=expr_term0(asmb,s,idx+1,&idx);
            if(flt) x=double_to_u256(u256_to_double(x)-u256_to_double(t));
            else    x=u256_sub(x,t);
        } else break;
    }
    *idx_out=idx; return x;
}

static uint256_t expr_term2(Assembler *asmb, const char *s, int idx, int *idx_out){
    uint256_t x=expr_term1(asmb,s,idx,&idx);
    int slen=(int)strlen(s);
    while(idx<slen){
        if(axx_q(s,slen,"<<",idx)){
            uint256_t t=expr_term1(asmb,s,idx+2,&idx);
            int64_t sv=u256_to_i64(t);
            if(sv<0){ if(should_report_errors(&asmb->st)) fprintf(stderr," error - negative shift count.\n"); x=u256_zero(); }
            else x=u256_shl(x,(int)sv);
        } else if(axx_q(s,slen,">>",idx)){
            uint256_t t=expr_term1(asmb,s,idx+2,&idx);
            int64_t sv=u256_to_i64(t);
            if(sv<0){ if(should_report_errors(&asmb->st)) fprintf(stderr," error - negative shift count.\n"); x=u256_zero(); }
            else x=u256_sar(x,(int)sv);
        } else break;
    }
    *idx_out=idx; return x;
}

static uint256_t expr_term3(Assembler *asmb, const char *s, int idx, int *idx_out){
    uint256_t x=expr_term2(asmb,s,idx,&idx);
    int slen=(int)strlen(s);
    while(idx<slen && s[idx]=='&' && s[idx+1]!='&'){
        uint256_t t=expr_term2(asmb,s,idx+1,&idx);
        x=u256_and(x,t);
    }
    *idx_out=idx; return x;
}

static uint256_t expr_term4(Assembler *asmb, const char *s, int idx, int *idx_out){
    uint256_t x=expr_term3(asmb,s,idx,&idx);
    int slen=(int)strlen(s);
    while(idx<slen && s[idx]=='|' && s[idx+1]!='|'){
        uint256_t t=expr_term3(asmb,s,idx+1,&idx);
        x=u256_or(x,t);
    }
    *idx_out=idx; return x;
}

static uint256_t expr_term5(Assembler *asmb, const char *s, int idx, int *idx_out){
    uint256_t x=expr_term4(asmb,s,idx,&idx);
    int slen=(int)strlen(s);
    while(idx<slen && s[idx]=='^'){
        uint256_t t=expr_term4(asmb,s,idx+1,&idx);
        x=u256_xor(x,t);
    }
    *idx_out=idx; return x;
}

/* -------------------------------------------------------
 * Bug 8 fix: expr_term6() sign extension operator x'n
 * When tv == 256 the original u256_shl(~0, 256) returned 0,
 * making the mask all-1s and bypassing the sign extension
 * entirely.  Guard with tv < 256; for tv >= 256 the value
 * already fits and no extension is needed.
 *
 * 修正⑨: mirror axx.py term6(): for tv > 128 (_SEXT_MAX_BITS)
 * emit a warning and return 0 (not a silent no-op).  Bit widths
 * larger than 128 are unrealistic in an assembler context and
 * usually indicate a malformed operand.
 * ------------------------------------------------------- */
#define SEXT_MAX_BITS 128
static uint256_t expr_term6(Assembler *asmb, const char *s, int idx, int *idx_out){
    uint256_t x=expr_term5(asmb,s,idx,&idx);
    int slen=(int)strlen(s);
    while(idx<slen && s[idx]=='\''){
        int ni=idx+1; ni=axx_skipspc(s,ni);
        if(ni>=slen||((s[ni]<'0'||s[ni]>'9')&&s[ni]!='(')) break;
        uint256_t t=expr_term5(asmb,s,idx+1,&idx);
        int64_t tv=u256_to_i64(t);
        if(tv<=0){
            x=u256_zero();
        } else if(tv > SEXT_MAX_BITS){
            /* 修正⑨: 非現実的なビット幅は警告を出して 0 を返す (axx.py term6) */
            fprintf(stderr, " warning - sign-extension bit width %lld exceeds maximum %d, result set to 0.\n",
                   (long long)tv, SEXT_MAX_BITS);
            x=u256_zero();
        } else {
            /* mask = ~(~0 << tv)  -- safe because 0 < tv <= 128 < 256 */
            uint256_t mask = u256_not(u256_shl(u256_not(u256_zero()), (int)tv));
            x = u256_and(x, mask);
            /* sign_bit = (x >> (tv-1)) & 1 */
            uint256_t sign_bit = u256_sar(x, (int)(tv - 1));
            sign_bit = u256_and(sign_bit, u256_one());
            if(!u256_is_zero(sign_bit)){
                /* extend: or in all-ones above bit tv */
                uint256_t ext = u256_shl(u256_not(u256_zero()), (int)tv);
                x = u256_or(x, ext);
            }
        }
    }
    *idx_out=idx; return x;
}
#undef SEXT_MAX_BITS

static uint256_t expr_term7(Assembler *asmb, const char *s, int idx, int *idx_out){
    uint256_t x=expr_term6(asmb,s,idx,&idx);
    int slen=(int)strlen(s);
    while(idx<slen){
        int flt=asmb->st.exp_typ_float;
        if(axx_q(s,slen,"<=",idx)){
            uint256_t t=expr_term6(asmb,s,idx+2,&idx);
            x=u256_from_i64(flt ? (u256_to_double(x)<=u256_to_double(t)?1:0)
                                : (u256_le_signed(x,t)?1:0));
        } else if(s[idx]=='<'&&s[idx+1]!='<'){
            uint256_t t=expr_term6(asmb,s,idx+1,&idx);
            x=u256_from_i64(flt ? (u256_to_double(x)< u256_to_double(t)?1:0)
                                : (u256_lt_signed(x,t)?1:0));
        } else if(axx_q(s,slen,">=",idx)){
            uint256_t t=expr_term6(asmb,s,idx+2,&idx);
            x=u256_from_i64(flt ? (u256_to_double(x)>=u256_to_double(t)?1:0)
                                : (u256_ge_signed(x,t)?1:0));
        } else if(s[idx]=='>'&&s[idx+1]!='>'){
            uint256_t t=expr_term6(asmb,s,idx+1,&idx);
            x=u256_from_i64(flt ? (u256_to_double(x)> u256_to_double(t)?1:0)
                                : (u256_gt_signed(x,t)?1:0));
        } else if(axx_q(s,slen,"==",idx)){
            uint256_t t=expr_term6(asmb,s,idx+2,&idx);
            x=u256_from_i64(flt ? (u256_to_double(x)==u256_to_double(t)?1:0)
                                : (u256_eq(x,t)?1:0));
        } else if(axx_q(s,slen,"!=",idx)){
            uint256_t t=expr_term6(asmb,s,idx+2,&idx);
            x=u256_from_i64(flt ? (u256_to_double(x)!=u256_to_double(t)?1:0)
                                : (!u256_eq(x,t)?1:0));
        } else break;
    }
    *idx_out=idx; return x;
}

/* Placeholder level between expr_term7 (comparisons) and expr_term9 (&&).
 * `not(expr)` used to be special-cased here, but that meant only operators
 * ABOVE this level (&&, ||, ternary) could combine with its result; anything
 * below (comparisons, +/-, etc.) is only ever invoked while parsing a fresh
 * left-hand operand, so e.g. "not(0)+5" silently dropped the "+5". `not(...)`
 * is now handled in expr_factor1() instead, the base of the chain, so its
 * result is an ordinary atom to every operator on either side. Mirrors the
 * identical fix applied to axx.py ExpressionEvaluator.term8(). */
static uint256_t expr_term8(Assembler *asmb, const char *s, int idx, int *idx_out){
    return expr_term7(asmb,s,idx,idx_out);
}

/* Fix C-2: expr_term9() – short-circuit &&
 * The original always evaluated both sides.  When the left operand is
 * zero the right side must be skipped, otherwise ':=' assignments in the
 * unchosen branch fire as side-effects.
 * Note: skip_subexpr() is defined after expr_term11(); forward-declare it. */
static int skip_subexpr(const char *s, int idx);

static uint256_t expr_term9(Assembler *asmb, const char *s, int idx, int *idx_out){
    uint256_t x=expr_term8(asmb,s,idx,&idx);
    int slen=(int)strlen(s);
    while(idx<slen && axx_q(s,slen,"&&",idx)){
        idx+=2; /* consume '&&' */
        if(u256_is_zero(x)){
            /* Short-circuit: skip right-hand side without evaluating */
            idx = skip_subexpr(s, axx_skipspc(s, idx));
            /* result stays zero */
        } else {
            uint256_t t=expr_term8(asmb,s,idx,&idx);
            x=u256_from_i64((!u256_is_zero(t))?1:0);
        }
    }
    *idx_out=idx; return x;
}

/* Fix C-2: expr_term10() – short-circuit ||
 * When the left operand is non-zero the right side must be skipped. */
static uint256_t expr_term10(Assembler *asmb, const char *s, int idx, int *idx_out){
    uint256_t x=expr_term9(asmb,s,idx,&idx);
    int slen=(int)strlen(s);
    while(idx<slen && axx_q(s,slen,"||",idx)){
        idx+=2; /* consume '||' */
        if(!u256_is_zero(x)){
            /* Short-circuit: skip right-hand side without evaluating */
            idx = skip_subexpr(s, axx_skipspc(s, idx));
            /* result stays 1 */
            x = u256_one();
        } else {
            uint256_t t=expr_term9(asmb,s,idx,&idx);
            x=u256_from_i64((!u256_is_zero(t))?1:0);
        }
    }
    *idx_out=idx; return x;
}

/* -------------------------------------------------------
 * Bug 5 fix: expr_term11() ternary operator lazy evaluation.
 * The original eagerly evaluated both branches before
 * choosing.  This caused side-effects (variable assignments
 * via :=) in the unchosen branch to execute.
 *
 * Fix: parse past the true-expression token boundary without
 * evaluating it, then only evaluate the chosen branch.
 * We use a helper that advances idx without calling expr.
 * ------------------------------------------------------- */

/* skip_subexpr: advance idx over a sub-expression without evaluating it.
 * Stops at depth-0 delimiters that cannot be part of an expression:
 *   '?'  – ternary operator start
 *   ':'  – ternary else separator
 *   ','  – object-list separator in makeobj  ← Bug fix: was missing,
 *            causing ";z?0xf3:0,0xa4" to skip "0,0xa4" as the false
 *            branch instead of stopping at the comma.
 *   ';'  – 互換修正(axx.py port): error-field "condition;code" separator and
 *            makeobj conditional-byte prefix. The evaluating path (expr_term9/10)
 *            naturally stops at ';' because it is not an operator, but the SKIP
 *            path did not, so a short-circuited '||'/'&&' RHS in an error
 *            condition (e.g. "(a)>5||(a)<0;1") skipped PAST ";1", making
 *            dir_error() read error code 0 instead of 1. axx.py's parser stops
 *            at ';' in both paths; matching that here restores compatibility.
 * ')' at depth 0 stops because we are inside a caller's parentheses.
 */
static int skip_subexpr(const char *s, int idx) {
    int slen = (int)strlen(s);
    int paren_depth = 0;   /* depth for '(' / ')' */
    int brack_depth = 0;   /* depth for '[' / ']'  – Fix C-N7: was missing    */
    int ob_depth    = 0;   /* Fix (new): depth for OB_CHAR(0x90) / CB_CHAR(0x91)
                            * Pattern-file optional groups use these special bracket
                            * chars.  Skipping without tracking them caused depth-0
                            * '?' or ':' inside OB…CB groups to be treated as ternary
                            * delimiters, cutting off the skip too early. */
    while(idx < slen && s[idx]){
        char c = s[idx];
        if(c == '(') { paren_depth++; idx++; }
        else if(c == ')') {
            if(paren_depth > 0){ paren_depth--; idx++; }
            else break;  /* depth-0 ')': stop (we are inside caller's parens) */
        }
        else if(c == '[') { brack_depth++; idx++; }
        else if(c == ']') {
            if(brack_depth > 0){ brack_depth--; idx++; }
            else break;  /* depth-0 ']': stop */
        }
        else if(c == OB_CHAR) { ob_depth++; idx++; }
        else if(c == CB_CHAR) {
            if(ob_depth > 0){ ob_depth--; idx++; }
            else break;  /* depth-0 CB_CHAR: stop */
        }
        /* ':=' is a variable-assignment operator, not a ternary separator.
         * Stop at ':' only when the next character is NOT '='. */
        else if(paren_depth == 0 && brack_depth == 0 && ob_depth == 0
                && (c == '?' || c == ',' || c == ';')) break;
        else if(paren_depth == 0 && brack_depth == 0 && ob_depth == 0
                && c == ':' && s[idx+1] != '=') break;
        else idx++;
    }
    return idx;
}

/* Fix G: skip_ternary_expr() – recursively skip a full ternary expression.
 *
 * skip_subexpr() alone stops at the first depth-0 '?', which is correct for
 * skipping a simple operand (e.g. the true-branch 'b' in 'a ? b : c').
 * However, when the false-branch itself is a nested ternary (e.g. 'c ? d : e')
 * we must skip the *entire* nested expression, not just up to its inner '?'.
 *
 * This function handles that by:
 *   1. Calling skip_subexpr() to advance past the base expression.
 *   2. If a '?' follows at depth 0, consuming it and recursing for both
 *      the true-branch and the false-branch.
 *
 * The caller in expr_term11 (condition-true path) uses this instead of the
 * bare skip_subexpr() so that 'a ? b : c ? d : e' leaves idx pointing past
 * 'e', not stranded at '? d : e'.
 */
static int skip_ternary_expr(const char *s, int idx) {
    int slen = (int)strlen(s);
    /* Skip the leading operand (stops at '?', ':', ',', ')' at depth 0) */
    idx = skip_subexpr(s, idx);
    /* If a ternary '?' follows, consume it and skip both branches */
    if(idx < slen && s[idx] == '?' && s[idx+1] != '='){
        idx++; /* consume '?' */
        idx = axx_skipspc(s, idx);
        idx = skip_ternary_expr(s, idx); /* skip true-branch recursively */
        idx = axx_skipspc(s, idx);
        if(idx < slen && s[idx] == ':' && s[idx+1] != '='){
            idx++; /* consume ':' */
            idx = axx_skipspc(s, idx);
            idx = skip_ternary_expr(s, idx); /* skip false-branch recursively */
        }
    }
    return idx;
}

/* Fix #5 + Fix G: expr_term11() – ternary operator, right-associative and
 * fully lazy.
 *
 * Fix #5 (existing): replaced the left-associative while-loop with a single
 * if + right-recursive call so 'a ? b : c ? d : e' parses as
 * 'a ? b : (c ? d : e)'.
 *
 * Fix G (new): when the condition is TRUE, the false-branch must be skipped
 * entirely, including any nested ternary chains.  The old code called
 * skip_subexpr() for the false-branch, which stops at the first depth-0 '?'.
 * For an input like 'a ? b : c ? d : e' with a==true this left idx pointing
 * at '? d : e', causing the outer parser to misinterpret the remaining tokens.
 * Fix: use skip_ternary_expr() instead, which recurses through '?…:…' chains.
 */
static uint256_t expr_term11(Assembler *asmb, const char *s, int idx, int *idx_out){
    uint256_t x = expr_term10(asmb, s, idx, &idx);
    int slen = (int)strlen(s);
    if(idx < slen && axx_q(s, slen, "?", idx)){
        idx++; /* consume '?' */
        idx = axx_skipspc(s, idx);
        if(u256_is_zero(x)){
            /* condition false: skip true-branch (simple operand), then
             * right-recurse into the false-branch. */
            int skip_end = skip_subexpr(s, idx);
            if(axx_q(s, slen, ":", skip_end) && s[skip_end+1] != '='){
                int false_start = axx_skipspc(s, skip_end + 1);
                x = expr_term11(asmb, s, false_start, &idx);  /* right-recursive */
                /* Fix ⑦: error_undefined_label stays as the false-branch's value
                 * (already current after the recursive call – no action needed). */
            } else {
                idx = skip_end;
                x = u256_zero();
            }
        } else {
            /* condition true: snapshot vars, evaluate true-branch, save its state,
             * restore vars, evaluate false-branch for extent only, then restore.
             *
             * Fix ⑦ (axx.py term11): adopt the error_undefined_label flag from
             * the chosen (true) branch.  The old code let the false-branch's flag
             * persist, so whenever the false-branch contained an undefined label
             * the error was spuriously reported even when condition was true. */
            uint256_t saved_vars[26];
            memcpy(saved_vars, asmb->st.vars, sizeof(saved_vars));

            x = expr_term10(asmb, s, idx, &idx);
            uint256_t vars_after_true[26];
            memcpy(vars_after_true, asmb->st.vars, sizeof(vars_after_true));
            int err_after_true = asmb->st.error_undefined_label;

            idx = axx_skipspc(s, idx);
            if(axx_q(s, slen, ":", idx) && s[idx+1] != '='){
                idx++; /* consume ':' */
                /* Restore vars to pre-true-branch state before evaluating false */
                memcpy(asmb->st.vars, saved_vars, sizeof(saved_vars));
                /* Fix G: use skip_ternary_expr so nested ternaries are fully
                 * consumed, not just the leading operand before the inner '?'. */
                idx = skip_ternary_expr(s, axx_skipspc(s, idx));
            }
            /* Restore true-branch vars and error flag (condition was true) */
            memcpy(asmb->st.vars, vars_after_true, sizeof(vars_after_true));
            asmb->st.error_undefined_label = err_after_true;
        }
    }
    *idx_out = idx;
    return x;
}

static uint256_t expr_expression(Assembler *asmb, const char *s, int idx, int *idx_out){
    idx=axx_skipspc(s,idx);
    return expr_term11(asmb,s,idx,idx_out);
}

/* =========================================================
 * DirectiveProcessor (pattern file directives)
 * ========================================================= */
static int dir_set_symbol(Assembler *asmb, PatEntry *e){
    if(!e||strcmp(e->f[0],".setsym")!=0) return 0;
    /* Bugfix (axx.py port): readpat()'s field mapping puts a lone
     * ".setsym::NAME" argument (2 fields) in f[2], not f[1] -- only the
     * 3-field ".setsym::NAME::value" form uses f[1] for the name (same
     * quirk dir_clrcheck already accounts for). This used to always read
     * the name from f[1], so the name-only form stored an empty-string key
     * and evaluated the name itself as an (undefined-label) expression. */
    const char *name_field = e->f[1][0] ? e->f[1] : e->f[2];
    const char *value_field = e->f[1][0] ? e->f[2] : "";
    char key[512]; axx_strupr_to(key,name_field,sizeof(key));
    int io;
    uint256_t v = value_field[0] ? expr_expression_pat(asmb,value_field,0,&io) : u256_zero();
    smap_set(&asmb->st.symbols,key,v);
    return 1;
}

static int dir_clear_symbol(Assembler *asmb, PatEntry *e){
    if(!e||strcmp(e->f[0],".clearsym")!=0) return 0;
    if(e->f[2][0]){
        char key[512]; axx_strupr_to(key,e->f[2],sizeof(key));
        smap_delete(&asmb->st.symbols,key);
    } else {
        smap_clear(&asmb->st.symbols);
    }
    return 1;
}

static int dir_bits(Assembler *asmb, PatEntry *e){
    if(!e||strcmp(e->f[0],".bits")!=0) return 0;
    asmb->st.endian_big=(strcmp(e->f[1],"big")==0);
    int io;
    uint256_t v = e->f[2][0] ? expr_expression_pat(asmb,e->f[2],0,&io) : u256_from_i64(8);
    asmb->st.bts=(int)u256_to_i64(v);
    return 1;
}

static int dir_padding(Assembler *asmb, PatEntry *e){
    if(!e||strcmp(e->f[0],".padding")!=0) return 0;
    int io;
    uint256_t v = e->f[2][0] ? expr_expression_pat(asmb,e->f[2],0,&io) : u256_zero();
    asmb->st.padding=v;
    return 1;
}

static int dir_symbolc(Assembler *asmb, PatEntry *e){
    if(!e||strcmp(e->f[0],".symbolc")!=0) return 0;
    if(e->f[2][0]){
        snprintf(asmb->st.swordchars, sizeof(asmb->st.swordchars),
                 "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789%s",
                 e->f[2]);
    }
    return 1;
}

static int dir_vliwp(Assembler *asmb, PatEntry *e){
    if(!e||strcmp(e->f[0],".vliw")!=0) return 0;
    int io;
    uint256_t v1=expr_expression_pat(asmb,e->f[1],0,&io);
    uint256_t v2=expr_expression_pat(asmb,e->f[2],0,&io);
    uint256_t v3=expr_expression_pat(asmb,e->f[3],0,&io);
    uint256_t v4=expr_expression_pat(asmb,e->f[4],0,&io);
    asmb->st.vliwbits=(int)u256_to_i64(v1);
    asmb->st.vliwinstbits=(int)u256_to_i64(v2);
    asmb->st.vliwtemplatebits=(int)u256_to_i64(v3);
    /* 破綻点修正 (axx.py port): ソース1行ごとにパターンファイル全体が
     * 再スキャンされる設計のため(lineassemble2相当のメインループ参照)、
     * .vliwディレクティブに出会うたびにdir_vliwp()が呼ばれ、直後のNOP
     * バイト列構築ループがvliwinstbits/8回実行される。vliwinstbitsは
     * 本来ちいさな命令幅を表す値だが上限チェックが無いため、桁を書き
     * 間違える(例: 80000000)とソース1行あたり数秒かかる処理が行数分
     * 積み上がり、通常サイズのソースファイルでも事実上ハングする。 */
    if(asmb->st.vliwinstbits < 0 || asmb->st.vliwinstbits > 8192){
        fprintf(stderr," error - .vliw: vliwinstbits %d is out of range (must be 0-8192).\n",
                asmb->st.vliwinstbits);
        asmb->st.had_error = 1;
        return 1;
    }
    asmb->st.vliwflag=1;
    iv_clear(&asmb->st.vliwnop);
    uint64_t v4v=u256_to_u64(v4);
    int nbytes=asmb->st.vliwinstbits/8+(asmb->st.vliwinstbits%8?1:0);
    for(int i=0;i<nbytes;i++){
        iv_push(&asmb->st.vliwnop, u256_from_u64(v4v&0xff));
        v4v>>=8;
    }
    return 1;
}

static int dir_epic(Assembler *asmb, PatEntry *e){
    if(!e) return 0;
    char uf[16]; axx_strupr_to(uf,e->f[0],sizeof(uf));
    if(strcmp(uf,"EPIC")!=0) return 0;
    if(!e->f[1][0]) return 0;
    const char *s=e->f[1];
    int idx=0;
    int idxs[64]; int ni=0;
    while(1){
        int io;
        uint256_t v=expr_expression_pat(asmb,s,idx,&io);
        if(ni<64) idxs[ni++]=(int)u256_to_i64(v);
        idx=io;
        if(s[idx]==','){idx++;continue;}
        break;
    }
    vset_add(&asmb->st.vliwset,idxs,ni,e->f[2]);
    return 1;
}

/* =========================================================
 * .check / .clrcheck ディレクティブ (パターンファイル専用)
 *
 * dir_check():
 *   PatEntry フィールド配置:
 *     f[0] = ".check"
 *     f[1] = 変数名 (小文字1文字, e.g. "x")
 *     f[2] = 許可シンボル名をカンマ区切りで列挙 (e.g. "R0,R1,R2")
 *   当該変数に対する拘束を st->check_constraints[var-'a'] に登録する。
 *   既存の拘束は上書きされる。
 *
 * dir_clrcheck():
 *   PatEntry フィールド配置:
 *     f[0] = ".clrcheck"
 *     f[1] = 変数名 (省略時は全変数の拘束を解除)
 *   対象変数の拘束を解除する。
 *
 * 適用範囲についての訂正 (axx.py port): 拘束の実際の評価は
 * pat_match() 内 `a>='a'&&a<='z'` 分岐 (このファイル内の該当箇所を
 * 参照) 1箇所のみで行われ、パターンテンプレート中の素の小文字1文字
 * (例: "MOV a,b" の a のように、ソース上の .setsym シンボル語に直接
 * マッチする形) にのみ効く。"!x" 形式(任意の式を捕捉する)で束縛された
 * 変数には一切適用されない -- !x は数値を計算する式であり、リストと
 * 比較すべき単一の「シンボル名」が存在しないため。以前このコメントが
 * 言及していた独立した dir_check_eval() 関数は実装として存在せず
 * (grep しても本コメント以外に出現しない)、拘束評価は上記の pat_match()
 * 内インライン処理がそのまま最終的な適用箇所である。axx.pyの
 * check_processing() のdocstringも同じ誤りがあったため合わせて訂正した。
 * ========================================================= */
static int dir_check(Assembler *asmb, PatEntry *e){
    if(!e || strcmp(e->f[0], ".check") != 0) return 0;
    /* Bugfix (axx.py port): same readpat() field-mapping quirk fixed in
     * dir_set_symbol()/dir_clrcheck() -- a var-only ".check::c" line (2
     * fields) puts "c" in f[2], not f[1]; only the 3-field
     * ".check::c::LIST" form uses f[1] for the var and f[2] for the list.
     * This used to always read the var from f[1], so the list-less form
     * always hit the "not specified" error below. */
    const char *var_str  = e->f[1][0] ? e->f[1] : e->f[2];
    const char *syms_str = e->f[1][0] ? e->f[2] : "";
    if(!var_str[0]){
        fprintf(stderr, " error - .check: variable name is not specified.\n");
        asmb->st.had_error = 1;
        return 1;
    }
    char var = (char)tolower((unsigned char)var_str[0]);
    if(var < 'a' || var > 'z' || var_str[1] != '\0'){
        fprintf(stderr,
            " error - .check: variable should be a lower case letter ('%s').\n",
            var_str);
        asmb->st.had_error = 1;
        return 1;
    }
    int idx = var - 'a';
    /* Clear existing constraint for this variable */
    sv_free(&asmb->st.check_constraints[idx]);
    sv_init(&asmb->st.check_constraints[idx]);
    /* Parse comma-separated symbol names from syms_str; store uppercased */
    const char *p = syms_str;
    while(*p){
        while(*p == ' ' || *p == '\t') p++;
        if(!*p) break;
        char buf[512]; int j = 0;
        while(*p && *p != ',' && j < (int)sizeof(buf)-1)
            buf[j++] = (char)toupper((unsigned char)*p++);
        buf[j] = '\0';
        /* trim trailing spaces */
        while(j > 0 && (buf[j-1] == ' ' || buf[j-1] == '\t')) buf[--j] = '\0';
        if(j > 0) sv_push(&asmb->st.check_constraints[idx], buf);
        if(*p == ',') p++;
    }
    return 1;
}

static int dir_clrcheck(Assembler *asmb, PatEntry *e){
    if(!e || strcmp(e->f[0], ".clrcheck") != 0) return 0;
    /* 仕様: 変数名はフィールド2 (f[2]) を参照する。
     * readpat のフィールドマッピングにより `.clrcheck::var` 形式
     * （2フィールド）は f[1]="" / f[2]="var" となるため、
     * .setsym 等と同様に引数はフィールド2 に格納される。
     * f[2] が空の場合は引数省略とみなし全拘束を解除する。 */
    const char *var_str = e->f[2];
    if(var_str[0]){
        char var = (char)tolower((unsigned char)var_str[0]);
        if(var < 'a' || var > 'z' || var_str[1] != '\0'){
            fprintf(stderr,
                " error - .clrcheck: variable should be a lower case letter ('%s').\n",
                var_str);
            asmb->st.had_error = 1;
            return 1;
        }
        int idx = var - 'a';
        sv_free(&asmb->st.check_constraints[idx]);
        sv_init(&asmb->st.check_constraints[idx]);
    } else {
        /* No variable specified: clear all constraints */
        for(int i = 0; i < 26; i++){
            sv_free(&asmb->st.check_constraints[i]);
            sv_init(&asmb->st.check_constraints[i]);
        }
    }
    return 1;
}

/* Fix 10 (axx.py): dir_error() now returns 1 when at least one condition
 * fired (triggered), 0 otherwise.  The caller uses this to skip makeobj()
 * when the .error directive raised an error, preventing bad object code from
 * being emitted.  Mirrors axx.py DirectiveProcessor.error() returning
 * (triggered: bool, code: int). */
static int dir_error(Assembler *asmb, const char *s){
    AsmState *st=&asmb->st;
    int has_content=0;
    for(const char*p=s;*p;p++) if(*p!=' '){has_content=1;break;}
    if(!has_content) return 0;

    char buf[4096];
    size_t l=strlen(s);
    if(l>=sizeof(buf)) l=sizeof(buf)-1;
    memcpy(buf,s,l); buf[l]='\0';

    int idx=0;
    int triggered=0;
    while(1){
        if(!buf[idx]) break;
        if(buf[idx]==','){idx++;continue;}
        /* Python evaluates the condition (u) in float mode, matching:
         *   self.expr_eval.state.exp_typ = 'f'
         *   u, idxn = self.expr_eval.expression_pat(s, idx)
         *   self.expr_eval.state.exp_typ = prev_typ               */
        int io;
        int prev_flt = st->exp_typ_float;
        st->exp_typ_float = 1;
        uint256_t u=expr_expression_pat(asmb,buf,idx,&io);
        st->exp_typ_float = prev_flt;
        idx=io;
        if(buf[idx]==';') idx++;
        uint256_t t=expr_expression_pat(asmb,buf,idx,&io);
        idx=io;
        if((should_report_errors(st))&&!u256_is_zero(u)){
            int64_t tc=u256_to_i64(t);
            fprintf(stderr,"Line %d Error code %lld ",(int)st->ln,(long long)tc);
            if(tc>=0&&tc<ERRORS_COUNT) fprintf(stderr,"%s",ERRORS_TABLE[tc]);
            fprintf(stderr,": \n");
            triggered=1;
        }
    }
    return triggered;
}

/* -------------------------------------------------------
 * expr_expression_esc_float():
 *   Evaluate expression in floating-point mode for !F/!D/!Q pattern capture.
 *
 *   Temporarily sets exp_typ_float=1 and calls expr_expression_esc()
 *   (the native C evaluator) so that number literals are parsed as
 *   doubles and arithmetic is done in double precision.
 *
 *   Mirrors axx.py ExpressionEvaluator.expression_esc_float():
 *     prev = self.state.exp_typ
 *     self.state.exp_typ = 'f'
 *     try:
 *         v,idx = self.expression_esc(s,idx,stopchar)
 *     finally:
 *         self.state.exp_typ = prev
 *     return (v,idx)
 *
 *   Returns the raw double result as a uint256_t bit-cast (w[0] holds
 *   the IEEE754 bits).  The caller converts to float/double/quad as
 *   appropriate.
 * ------------------------------------------------------- */
static uint256_t expr_expression_esc_float(Assembler *asmb, const char *s,
                                            int idx, char stopchar, int *idx_out)
{
    int prev = asmb->st.exp_typ_float;
    asmb->st.exp_typ_float = 1;
    uint256_t r = expr_expression_esc(asmb, s, idx, stopchar, idx_out);
    asmb->st.exp_typ_float = prev;
    return r;
}

/* =========================================================
 * PatternMatcher
 * ========================================================= */

/* -------------------------------------------------------
 * Bug 2 fix: remove_brackets_str()
 * Original used nesting depth as the group ID, so two
 * sibling optional groups "[[A]] [[B]]" both got level=1
 * and could not be addressed individually.
 *
 * Fix: assign a unique monotone serial number to each OB,
 * matched with its corresponding CB via an open-stack.
 * remove_idx[] now refers to these serials.
 * ------------------------------------------------------- */
static char *remove_brackets_str(const char *s, int *remove_idx, int nr){
    int len=(int)strlen(s);
    typedef struct { int serial; int pos; int is_open; } BP;
    BP *bps = calloc(len + 1, sizeof(BP)); int nbps = 0;
    int serial = 0;
    int *stk = calloc(len + 1, sizeof(int)); int stkp = 0;
    for(int i = 0; i < len; i++){
        if(s[i] == OB_CHAR){
            serial++;
            stk[stkp++] = serial;
            bps[nbps++] = (BP){serial, i, 1};
        } else if(s[i] == CB_CHAR && stkp > 0){
            int matched = stk[--stkp];
            bps[nbps++] = (BP){matched, i, 0};
        }
    }
    free(stk);

    /* Fix (new): the original used '\x01' as an in-band sentinel inside the
     * result buffer to mark positions to be deleted.  Any genuine '\x01' byte
     * in the input (e.g. from an embedded control character) would be silently
     * stripped even when it was not inside a removed bracket group.
     *
     * Fix: use a separate boolean array to track which positions to delete,
     * so the result buffer is never modified with an in-band sentinel value. */
    char *del = calloc(len + 1, 1);  /* del[i] = 1 → position i is removed */
    for(int ri = 0; ri < nr; ri++){
        int ridx = remove_idx[ri];
        int start_pos = -1, end_pos = -1;
        for(int b = 0; b < nbps; b++){
            if(bps[b].serial == ridx && bps[b].is_open)  start_pos = bps[b].pos;
            if(bps[b].serial == ridx && !bps[b].is_open) end_pos   = bps[b].pos;
        }
        if(start_pos >= 0 && end_pos >= 0)
            for(int j = start_pos; j <= end_pos; j++) del[j] = 1;
    }
    char *out = malloc(len + 1); int n = 0;
    for(int i = 0; i < len; i++) if(!del[i]) out[n++] = s[i];
    out[n] = 0;
    free(del); free(bps);
    return out;
}

static int pat_match(Assembler *asmb, const char *s_orig, const char *t_orig){
    AsmState *st=&asmb->st;
    /* deb1/deb2 are debug-only buffers (4096 B); truncate long patterns safely */
    snprintf(st->deb1, sizeof(st->deb1), "%.*s",
             (int)(sizeof(st->deb1)-1), s_orig);
    snprintf(st->deb2, sizeof(st->deb2), "%.*s",
             (int)(sizeof(st->deb2)-1), t_orig);

    char *t_nobr=strdup(t_orig);
    char *t_clean=malloc(strlen(t_nobr)+1); int n2=0;
    for(int i=0;t_nobr[i];i++) if(t_nobr[i]!=OB_CHAR&&t_nobr[i]!=CB_CHAR) t_clean[n2++]=t_nobr[i];
    t_clean[n2]=0; free(t_nobr);

    char *s=malloc(strlen(s_orig)+2); strcpy(s,s_orig); s[strlen(s_orig)+1]=0;
    char *t=malloc(strlen(t_clean)+2); strcpy(t,t_clean); t[strlen(t_clean)+1]=0;
    free(t_clean);

    int idx_s=0,idx_t=0;
    idx_s=axx_skipspc(s,idx_s);
    idx_t=axx_skipspc(t,idx_t);
    int tlen=(int)strlen(t);
    int result=0;

    /* 順序非依存マッチング用の具体度カウンタ (axx.py port)。
     * スコアは (n_expr, -n_lit, n_sym) の辞書式比較で小さいほど具体的:
     *   リテラルのみ  LD A,(HL)  →  最優先
     *   シンボル捕捉  LD A,r     →  次点
     *   式キャプチャ  LD A,!e    →  最後
     * 修正: 第2キーをシンボル数からリテラル一致文字数に変更 (axx.py と同期)。
     * 旧順序では式キャプチャ数が同じ2パターンのうちシンボル数の少ない方が
     * リテラル一致がどれほど多くても勝ってしまい、`ld a,(iy+9)` で
     * LD A,(!n) が LD s,(IY[[+!d]]) に勝って iy+9 が式に飲み込まれ、
     * 未定義ラベル iy のエラーになっていた。                              */
    int n_expr=0, n_sym=0, n_lit=0;

    /* 直前に消費したパターン文字が英数字リテラルだったか(単語境界判定用) */
    int prev_alnum=0;

    while(1){
        /* 単語境界ルール(axx.py側と同期): アセンブリ行側の空白は「トークン
         * の区切り」として扱う。以前はここで無条件に axx_skipspc() を両側に
         * かけていたため、空白がマッチに一切影響せず、例えば `jl exit_error`
         * がパターン `JLE !a` にマッチしてしまっていた(JLの後の空白を飛ばして
         * exit_errorの先頭'e'がパターンの'E'に食われ、!aが'xit_error'を捕捉
         * して未定義エラーになる)。
         * 空白スキップ自体は従来どおり行うが、「行側に空白があった」
         * 「パターン側に空白があった」を記録しておき、英数字リテラル同士の
         * 連続(=1つの単語)の途中で行側だけに空白があった場合はマッチ失敗と
         * する。カンマ・括弧など英数字以外の前後の空白は従来どおり自由
         * (互換性維持)。 */
        int s_sp = (s[idx_s]==' '||s[idx_s]=='\t');
        int t_sp = (t[idx_t]==' '||t[idx_t]=='\t');
        idx_s=axx_skipspc(s,idx_s);
        idx_t=axx_skipspc(t,idx_t);
        /* 行側だけに空白があった位置は単語境界。パターン側にも空白が
         * あればパターンもそこで単語が切れているので境界違反にならない。 */
        int word_break = s_sp && !t_sp;
        char b=s[idx_s], a=t[idx_t];

        if(a=='\0'&&b=='\0'){
            result=1;
            st->match_score_expr = n_expr;
            st->match_score_sym  = n_sym;
            st->match_score_lit  = n_lit;
            break;
        }

        if(a=='\\'){
            idx_t++;
            if(idx_t<tlen && t[idx_t]==b){
                int lit_alnum = isalnum((unsigned char)t[idx_t]) ? 1 : 0;
                if(lit_alnum && prev_alnum && word_break){ result=0; break; }
                idx_t++; idx_s++; n_lit++;
                prev_alnum = lit_alnum;
                continue;
            }
            else { result=0; break; }
        } else if(a>='A'&&a<='Z'){
            if(a==axx_upper_char(b)){
                /* 英数字リテラルの連続途中に行側の空白は入れない
                 * (JLE が 'jl e...' にマッチするのを防ぐ) */
                if(prev_alnum && word_break){ result=0; break; }
                idx_s++; idx_t++; n_lit++;
                prev_alnum=1;
                continue;
            }
            else { result=0; break; }
        } else if(a=='!'){
            prev_alnum=0;
            n_expr++;
            idx_t++;
            a=t[idx_t]; idx_t++;
            /* --- !F : capture float32 bit-pattern -------------------------
             *   !F<var>[\stopchar]  reads a float expression from source,
             *   packs as IEEE754 32-bit and stores the integer bit-pattern.
             *   Mirrors axx.py match() case a=='F'. */
            if(a=='F' || a=='D' || a=='Q'){
                char ftype = a;
                a = t[idx_t]; idx_t++;          /* variable name (single char) */
                idx_t = axx_skipspc(t, idx_t);
                char stopchar = '\0';
                if(idx_t < tlen && t[idx_t] == '\\'){
                    idx_t++;                    /* skip '\' */
                    idx_t = axx_skipspc(t, idx_t);
                    stopchar = t[idx_t]; idx_t++; /* stopchar, then advance */
                }
                /* Evaluate in float mode to get the expression extent.
                 * Save source position first so we can extract the raw text
                 * for __float128 re-evaluation.                             */
                int idx_s_q_start = idx_s;
                uint256_t fv = expr_expression_esc_float(asmb, s, idx_s, stopchar, &idx_s);
                double dv = u256_to_double(fv);
                /* consume stopchar from source if present */
                if(stopchar != '\0' && idx_s < (int)strlen(s) && s[idx_s] == stopchar)
                    idx_s++;
                if(ftype == 'F'){
                    /* float32: pack → integer bit-pattern */
                    float fval = (float)dv;
                    uint32_t bits; memcpy(&bits, &fval, 4);
                    var_put(st, a, u256_from_u64((uint64_t)bits));
                } else if(ftype == 'D'){
                    /* float64: pack → integer bit-pattern */
                    uint64_t bits; memcpy(&bits, &dv, 8);
                    var_put(st, a, u256_from_u64(bits));
                } else {
                    /* !Q : IEEE754 128-bit (quad) bit-pattern.
                     * Extract the raw source text and evaluate in __float128
                     * for full precision matching Python mpmath.            */
                    /* The stopchar (if any) was consumed above; the extent
                     * idx_s_q_start..idx_s covers text + optional stopchar */
                    int raw_len = idx_s - idx_s_q_start;
                    if(stopchar && raw_len > 0 &&
                       s[idx_s_q_start + raw_len - 1] == stopchar)
                        raw_len--;  /* trim trailing stopchar */
                    uint256_t qbits;
#if defined(__GNUC__) && !defined(__STRICT_ANSI__) && \
    (defined(__x86_64__) || defined(__i386__) || defined(__aarch64__) || \
     defined(__arm__) || defined(__riscv))
                    if(raw_len > 0 && raw_len < 1024){
                        char expr_text[1024];
                        memcpy(expr_text, s + idx_s_q_start, (size_t)raw_len);
                        expr_text[raw_len] = '\0';
                        /* Strip "qad{...}" wrapper if present so that both
                         *   !Q  3.14*2+1
                         *   !Q  qad{3.14*2+1}
                         * are evaluated identically in __float128.          */
                        const char *f128_text = expr_text;
                        char stripped[1024];
                        if(raw_len > 4 &&
                           strncmp(expr_text, "qad{", 4) == 0 &&
                           expr_text[raw_len-1] == '}'){
                            int inner = raw_len - 5; /* strip "qad{" and "}" */
                            memcpy(stripped, expr_text + 4, (size_t)inner);
                            stripped[inner] = '\0';
                            f128_text = stripped;
                        }
                        int q_ok = 0;
                        qbits = f128_eval_text(f128_text, &q_ok);
                        if(!q_ok){
                            /* fall back: double→string→binary128 */
                            char fstr[64];
                            snprintf(fstr, sizeof(fstr), "%.17g", dv);
                            qbits = ieee754_128_from_str(fstr);
                        }
                    } else
#endif
                    {
                        char fstr[64];
                        snprintf(fstr, sizeof(fstr), "%.17g", dv);
                        qbits = ieee754_128_from_str(fstr);
                    }
                    var_put(st, a, qbits);
                }
                continue;
            } else if(a=='!'){
                a=t[idx_t]; idx_t++;
                /* ELF tracking: record which variable is being captured */
                st->elf_capturing_var = a;
                uint256_t v=expr_factor(asmb,s,idx_s,&idx_s);
                st->elf_capturing_var = '\0';
                var_put(st,a,v);
                continue;
            } else {
                idx_t=axx_skipspc(t,idx_t);
                char stopchar='\0';
                if(idx_t<tlen && t[idx_t]=='\\'){
                    idx_t++;
                    idx_t=axx_skipspc(t,idx_t);
                    stopchar=t[idx_t];
                    idx_t++;
                }
                /* ELF tracking: record which variable is being captured */
                st->elf_capturing_var = a;
                uint256_t v=expr_expression_esc(asmb,s,idx_s,stopchar,&idx_s);
                st->elf_capturing_var = '\0';
                var_put(st,a,v);
                if(stopchar && s[idx_s]==stopchar) idx_s++;
                continue;
            }
        } else if(a>='a'&&a<='z'){
            prev_alnum=0;
            idx_t++;
            int prev_idx_s = idx_s;
            char w[512];
            idx_s=axx_get_symbol_word(s,idx_s,st->swordchars,w,sizeof(w));
            uint256_t sv;
            if(!symbol_get(st,w,&sv)){ result=0; break; }
            
            /* .check constraint validation (name-based) */
            int vi = a - 'a';
            StrVec *cv = &st->check_constraints[vi];
            if(cv->len > 0){
                int ok = 0;
                for(int si = 0; si < cv->len; si++){
                    if(strcmp(cv->data[si], w) == 0){
                        ok = 1;
                        break;
                    }
                }
                if(!ok){ result=0; break; }
            }
            
            /* Fix 5 (new): if get_symbol_word didn't advance, it's a match failure. */
            if(idx_s == prev_idx_s){ result=0; break; }
            
            var_put(st,a,sv);
            n_sym++;
            continue;
        } else if(a=='[' || a==']'){
            prev_alnum=0;
            idx_t++;
            idx_s=axx_skipspc(s,idx_s);
            if(s[idx_s]==a){ idx_s++; n_lit++; continue; }
            else { result=0; break; }
        } else if(a==b){
            /* 数字リテラル等も英数字リテラル連続の一部として扱う
             * (パターン 'R1' が行 'r 1' にマッチしないように) */
            int lit_alnum = isalnum((unsigned char)a) ? 1 : 0;
            if(lit_alnum && prev_alnum && word_break){ result=0; break; }
            idx_t++; idx_s++; n_lit++;
            prev_alnum = lit_alnum;
            continue;
        }
        else { result=0; break; }
    }
    free(s); free(t);
    return result;
}

/* -------------------------------------------------------
 * Bug 3 fix: pat_match0() – undefined behaviour from 1<<cnt
 * When cnt >= 32, (1<<cnt) is UB in C (signed int overflow).
 *
 * Fix: use uint64_t for the mask.
 *
 * 破綻点修正: 上記のuint64_t化だけでは、2^cnt通りの組合せを全探索する
 * コストそのものは解消されない。axx.py 版は "現実のパターンファイルで
 * [[]] が20を超えることはない" という前提で _MAX_OPT_GROUPS=20 を上限に
 * 設定している（2^20 ≈ 100万通りが実用上の上限）。
 * このCポートは「uint64_tに収まる」という理由だけでcnt<=63を許容して
 * いたが、2^63通りは事実上無限であり、axx.pyでは即座に処理される
 * cnt=18程度のパターンでも、この上限のせいでハングし続ける
 * （実測: cnt=18でCコード0.6秒 vs cnt=24で30秒超）。
 * axx.py と同じ実用上限20に揃える。 */
static int pat_match0(Assembler *asmb, const char *s, const char *t_orig){
    char *t=malloc(strlen(t_orig)+1);
    strcpy(t,t_orig);
    char *out=malloc(strlen(t)*2+4);
    int n=0;
    for(int i=0;t[i];){
        if(t[i]=='['&&t[i+1]=='['){ out[n++]=OB_CHAR; i+=2; }
        else if(t[i]==']'&&t[i+1]==']'){ out[n++]=CB_CHAR; i+=2; }
        else out[n++]=t[i++];
    }
    out[n]=0; free(t); t=out;

    int cnt=0; for(const char*p=t;*p;p++) if(*p==OB_CHAR) cnt++;

    /* axx.py の _MAX_OPT_GROUPS と同じ実用上限。2^20 ≈ 100万通りに
     * 抑えることで、超過分は「常に含む」扱いにして事実上無限の
     * 組合せ爆発によるハングを防ぐ。 */
    enum { MAX_OPT_GROUPS = 20 };
    if(cnt > MAX_OPT_GROUPS){
        fprintf(stderr,
                " warning - pattern has %d optional groups (max %d); "
                "first %d are treated as optional, remainder are always included.\n",
                cnt, MAX_OPT_GROUPS, MAX_OPT_GROUPS);
        cnt = MAX_OPT_GROUPS;
    }

    int *sl=malloc((cnt+1)*sizeof(int));
    for(int i=0;i<cnt;i++) sl[i]=i+1;   /* serials 1..cnt */

    /* 破綻点修正5 (axx.py port): MAX_OPT_GROUPS=20 だけではcnt=20で
     * 2^20 ≈ 100万通りに達しうる。グループ数の上限とは別に、1回の
     * pat_match0()呼び出しが試してよい組合せの総数にも予算を設け、
     * 予算を使い切ったら「不成立」として安全側に倒す(誤ったマッチを
     * 返すことはない)。 */
    const uint64_t MAX_COMBINATIONS = (uint64_t)1 << 16;
    uint64_t tried = 0;

    int found=0;
    uint64_t total = (uint64_t)1 << cnt; /* 2^cnt subsets; safe for cnt<=63 */
    for(uint64_t mask=0; mask<total && !found; mask++){
        if(++tried > MAX_COMBINATIONS){
            int _already_warned = 0;
            for(int _wi=0; _wi<asmb->st.combo_budget_warned_count; _wi++){
                if(asmb->st.combo_budget_warned_line[_wi] == asmb->st.ln &&
                   strcmp(asmb->st.combo_budget_warned_file[_wi], asmb->st.current_file) == 0){
                    _already_warned = 1;
                    break;
                }
            }
            if(!_already_warned){
                if(asmb->st.combo_budget_warned_count <
                        (int)(sizeof(asmb->st.combo_budget_warned_line)/sizeof(int))){
                    int _wi = asmb->st.combo_budget_warned_count++;
                    strncpy(asmb->st.combo_budget_warned_file[_wi], asmb->st.current_file,
                            sizeof(asmb->st.combo_budget_warned_file[_wi])-1);
                    asmb->st.combo_budget_warned_file[_wi][sizeof(asmb->st.combo_budget_warned_file[_wi])-1]=0;
                    asmb->st.combo_budget_warned_line[_wi] = asmb->st.ln;
                }
                fprintf(stderr,
                        " warning - a pattern with %d optional group(s) exceeded the "
                        "%llu-combination match budget and was treated as non-matching; "
                        "consider splitting it into multiple explicit pattern entries.\n",
                        cnt, (unsigned long long)MAX_COMBINATIONS);
            }
            break;
        }
        int ri[64]; int nr=0;
        for(int i=0;i<cnt;i++) if(mask & ((uint64_t)1<<i)) ri[nr++]=sl[i];
        char *lt=remove_brackets_str(t,ri,nr);

        /* Fix C-1 / Fix ④ (axx.py): snapshot vars AND ELF tracking state before
         * each trial.  Failed match attempts must not leave partial variable
         * writes or spurious ELF ref entries visible to the next attempt. */
        uint256_t saved_vars[26];
        memcpy(saved_vars, asmb->st.vars, sizeof(saved_vars));

        /* Snapshot ELF refs */
        int saved_elf_refs_len = asmb->st.elf_refs_len;
        /* Snapshot elf_var_to_label (set/label_name/label_val per slot) */
        struct {int set; char *label_name; uint64_t label_val;} saved_vtl[26];
        for(int vi=0;vi<26;vi++){
            saved_vtl[vi].set       = asmb->st.elf_var_to_label[vi].set;
            saved_vtl[vi].label_val = asmb->st.elf_var_to_label[vi].label_val;
            saved_vtl[vi].label_name = asmb->st.elf_var_to_label[vi].label_name
                                       ? strdup(asmb->st.elf_var_to_label[vi].label_name)
                                       : NULL;
        }

        if(pat_match(asmb,s,lt)){
            found=1;
            /* Free the pre-match snapshot (keep current ELF state) */
            for(int vi=0;vi<26;vi++) free(saved_vtl[vi].label_name);
        } else {
            /* restore vars on failure */
            memcpy(asmb->st.vars, saved_vars, sizeof(saved_vars));
            /* restore ELF refs: free any names added during the failed attempt */
            for(int ri2=saved_elf_refs_len; ri2<asmb->st.elf_refs_len; ri2++)
                free(asmb->st.elf_refs[ri2].name);
            asmb->st.elf_refs_len = saved_elf_refs_len;
            /* restore elf_var_to_label */
            for(int vi=0;vi<26;vi++){
                free(asmb->st.elf_var_to_label[vi].label_name);
                asmb->st.elf_var_to_label[vi].set       = saved_vtl[vi].set;
                asmb->st.elf_var_to_label[vi].label_val = saved_vtl[vi].label_val;
                asmb->st.elf_var_to_label[vi].label_name = saved_vtl[vi].label_name;
                saved_vtl[vi].label_name = NULL; /* ownership transferred */
            }
        }
        free(lt);
    }
    free(sl); free(t);
    return found;
}

/* =========================================================
 * PatternFileReader
 * ========================================================= */
/* -------------------------------------------------------
 * axx_resolve_path(): resolve a (possibly relative) filename
 * against base_dir.  If base_dir is NULL or empty, or fn is
 * absolute, fn is returned unchanged (copied into out).
 * Mirrors axx.py readpat() / include_asm() path resolution:
 *   if base_dir and not os.path.isabs(fn):
 *       fn = os.path.join(base_dir, fn)
 * ------------------------------------------------------- */
static void axx_resolve_path(const char *base_dir, const char *fn,
                              char *out, size_t osz)
{
    if(!fn || !fn[0]){ out[0]='\0'; return; }
    /* absolute path: use as-is */
    if(fn[0]=='/' || !base_dir || !base_dir[0]){
        strncpy(out, fn, osz-1); out[osz-1]='\0'; return;
    }
    snprintf(out, osz, "%s/%s", base_dir, fn);
}

/* axx_dir_of(): extract the directory component of path into out.
 * If path has no directory part (no '/'), out is set to ".". */
static void axx_dir_of(const char *path, char *out, size_t osz)
{
    strncpy(out, path, osz-1); out[osz-1]='\0';
    /* Use dirname() from libgen.h – it modifies the buffer in-place */
    char *d = dirname(out);
    if(d != out) strncpy(out, d, osz-1);
}

static void readpat(Assembler *asmb, const char *fn);
static void include_pat(Assembler *asmb, const char *l, const char *base_dir);

/* Bug 5 fix + relative-path fix: include_pat()
 * Now accepts base_dir (the directory of the calling pattern file) and
 * resolves the .INCLUDE filename relative to it, exactly as axx.py does:
 *   this_dir = os.path.dirname(os.path.abspath(fn))
 *   ww = self.include_pat(l, this_dir)  */
static void include_pat(Assembler *asmb, const char *l, const char *base_dir){
    int idx=axx_skipspc(l,0);
    char upper8[16]={0};
    for(int i=0;i<8&&l[idx+i];i++) upper8[i]=axx_upper_char(l[idx+i]);
    if(strcmp(upper8,".INCLUDE")!=0) return;
    /* 修正⑦ (axx.py): use l+idx+8 (not l+8) to skip past any leading spaces */
    const char *after_kw = l + idx + 8;
    char raw[512]; axx_get_string(after_kw,raw,sizeof(raw));
    if(!raw[0]){
        /* Fix ⑥ (axx.py): don't silently return – try unquoted fallback or error. */
        char trimmed[512];
        int ti=axx_skipspc(after_kw,0);
        int tn=0;
        while(after_kw[ti]&&after_kw[ti]!=' '&&after_kw[ti]!='\t'&&tn<(int)sizeof(trimmed)-1)
            trimmed[tn++]=after_kw[ti++];
        trimmed[tn]=0;
        if(trimmed[0]){
            fprintf(stderr," warning - .INCLUDE filename not quoted: '%s'. "
                           "Please use double quotes.\n", trimmed);
            strncpy(raw, trimmed, sizeof(raw)-1); raw[sizeof(raw)-1]='\0';
        } else {
            fprintf(stderr," error - .INCLUDE directive has no filename: %s\n", l);
            return;
        }
    }
    char resolved[1024];
    axx_resolve_path(base_dir, raw, resolved, sizeof(resolved));
    readpat(asmb, resolved);
}

static void readpat(Assembler *asmb, const char *fn){
    if(!fn||!fn[0]) return;

    /* D8 (axx.py port): pattern .INCLUDE depth limit + circular-include detection.
     * The Python original limited nesting to 50 and (after the recent fix)
     * detects cycles via a chain of canonical paths. The C port previously had
     * NEITHER, so a self-including pattern file would recurse until it crashed
     * (native stack overflow) instead of stopping cleanly. */
    enum { MAX_PAT_DEPTH = 50 };
    if(asmb->st.pat_include_depth > MAX_PAT_DEPTH){
        fprintf(stderr," error - pattern .INCLUDE nesting exceeds %d: '%s'\n",
                MAX_PAT_DEPTH, fn);
        return;
    }
    /* Canonicalize for reliable cycle keys (resolves symlinks / './' / '..'). */
    char real[PATH_MAX];
    if(!realpath(fn, real)){
        /* file may be unreadable; fall back to the raw name as the cycle key */
        strncpy(real, fn, sizeof(real)-1); real[sizeof(real)-1]='\0';
    }
    for(int i=0;i<asmb->st.pat_include_depth;i++){
        if(asmb->st.pat_include_chain[i]
           && strcmp(asmb->st.pat_include_chain[i], real)==0){
            fprintf(stderr," error - circular pattern .INCLUDE detected: '%s' "
                    "(already in include chain). Skipped.\n", fn);
            return;
        }
    }

    FILE *f=fopen(fn,"rt");
    if(!f){ fprintf(stderr,"Cannot open pattern file: %s\n",fn); return; }

    /* push this file onto the include chain */
    if(asmb->st.pat_include_depth < (int)(sizeof(asmb->st.pat_include_chain)
                                          / sizeof(asmb->st.pat_include_chain[0]))){
        asmb->st.pat_include_chain[asmb->st.pat_include_depth] = strdup(real);
    }
    asmb->st.pat_include_depth++;

    /* Compute this file's directory for recursive .INCLUDE resolution */
    char this_dir[1024];
    axx_dir_of(fn, this_dir, sizeof(this_dir));

    /* Fix: pattern files were read with a fixed 4096-byte fgets() buffer,
     * so any single logical line at or beyond that length was silently
     * split into two lines (fgets() just returns without a trailing '\n'
     * and the remainder is picked up on the next call as if it were a
     * separate line) -- no error, no warning. fileassemble() already reads
     * source files via getline() with no length limit; do the same here
     * so pattern files have the same guarantee as source files. */
    char *line=NULL; size_t lcap=0;
    while(getline(&line,&lcap,f)!=-1){
        axx_remove_comment(line);
        for(char*p=line;*p;p++){ if(*p=='\t') *p=' '; if(*p=='\r') *p=' '; }
        int l=(int)strlen(line);
        while(l>0&&(line[l-1]=='\n'||line[l-1]=='\r')) line[--l]=0;
        axx_reduce_spaces(line);

        char uline[16]={0};
        int si=axx_skipspc(line,0);
        for(int i=0;i<8&&line[si+i];i++) uline[i]=axx_upper_char(line[si+i]);
        if(strcmp(uline,".INCLUDE")==0){ include_pat(asmb,line+si,this_dir); continue; }

        char fields[8][1024]; int nf=0;
        int idx=0;
        while(1){
            char f_out[1024];
            idx=axx_get_params1(line,idx,f_out,sizeof(f_out));
            fields[nf][0]=0; snprintf(fields[nf], sizeof(fields[nf]), "%s", f_out);
            nf++;
            if(idx>=(int)strlen(line)||nf>=8) break;
        }

        PatEntry *pe=pv_push_blank(&asmb->st.pat);
        if(nf==1){ pat_set(pe,0,fields[0]); }
        else if(nf==2){ pat_set(pe,0,fields[0]); pat_set(pe,2,fields[1]); }
        else if(nf==3){ pat_set(pe,0,fields[0]); pat_set(pe,1,fields[1]); pat_set(pe,2,fields[2]); }
        else if(nf==4){ pat_set(pe,0,fields[0]); pat_set(pe,1,fields[1]); pat_set(pe,2,fields[2]); pat_set(pe,3,fields[3]); }
        else if(nf==5){ for(int i=0;i<5;i++) pat_set(pe,i,fields[i]); }
        else if(nf>=6){ for(int i=0;i<6;i++) pat_set(pe,i,fields[i]); }
    }
    free(line);
    fclose(f);
    /* D8: pop this file off the include chain */
    asmb->st.pat_include_depth--;
    if(asmb->st.pat_include_depth >= 0
       && asmb->st.pat_include_depth < (int)(sizeof(asmb->st.pat_include_chain)
                                             / sizeof(asmb->st.pat_include_chain[0]))){
        free(asmb->st.pat_include_chain[asmb->st.pat_include_depth]);
        asmb->st.pat_include_chain[asmb->st.pat_include_depth] = NULL;
    }
}

/* =========================================================
 * ObjectGenerator
 * ========================================================= */
static void replace_percent_with_index(const char *s, char *out, size_t osz){
    int count=0,i=0; size_t n=0;
    while(s[i]&&n<osz-1){
        if(s[i]=='%'&&s[i+1]=='%'){
            char num[16]; snprintf(num,sizeof(num),"%d",count++);
            for(const char*p=num;*p&&n<osz-1;) out[n++]=*p++;
            i+=2;
        } else if(s[i]=='%'&&s[i+1]=='0'){ count=0; i+=2; }
        else { out[n++]=s[i++]; }
    }
    out[n]=0;
}

static void e_p(const char *pattern, char *out, size_t osz, int *is_empty, Assembler *asmb){
    size_t n=0; int has_content=0;
    int i=0; int plen=(int)strlen(pattern);
    while(i<plen&&n<osz-1){
        if(i+3<=plen && strncmp(pattern+i,"@@[",3)==0){
            i+=3;
            int depth=1, expr_start=i, comma_pos=-1;
            while(i<plen&&depth>0){
                if(pattern[i]=='[') depth++;
                else if(pattern[i]==']'){ depth--; if(depth==0) break; }
                else if(pattern[i]==','&&depth==1&&comma_pos<0) comma_pos=i;
                i++;
            }
            if(comma_pos>0){
                char expr_part[1024]={0};
                int el=comma_pos-expr_start; if(el>=(int)sizeof(expr_part)) el=sizeof(expr_part)-1;
                memcpy(expr_part,pattern+expr_start,el);
                char rep_pat[1024]={0};
                int rl=i-comma_pos-1; if(rl>=(int)sizeof(rep_pat)) rl=sizeof(rep_pat)-1;
                memcpy(rep_pat,pattern+comma_pos+1,rl);
                int io;
                /* 修正: 直前の処理でerror_undefined_labelが残っていると
                 * nrep=0と誤判定されるため、評価前にリセットする。 */
                asmb->st.error_undefined_label = 0;
                uint256_t nv=expr_expression_pat(asmb,expr_part,0,&io);
                int64_t nrep=u256_to_i64(nv);
                if(nrep>0){
                    has_content=1;
                    for(int j=0;j<nrep;j++){
                        if(j>0&&n<osz-1) out[n++]=',';
                        for(const char*p=rep_pat;*p&&n<osz-1;) out[n++]=*p++;
                    }
                }
                i++;
            } else {
                if(n+3<osz){ out[n++]='@'; out[n++]='@'; out[n++]='['; has_content=1; }
            }
        } else { out[n++]=pattern[i++]; has_content=1; }
    }
    out[n]=0;
    *is_empty=!has_content;
}

static void makeobj(Assembler *asmb, const char *s_in, IntVec *objl){
    AsmState *st=&asmb->st;
    iv_clear(objl);

    /* Fix P6: replace fixed-size ep_buf[8192]/s[8192] with dynamically grown
     * buffers so that long @@[N,...] expansions cannot silently truncate the
     * binary_list.  The old post-overflow check fired too late.              */
    size_t ep_cap = 8192;
    char *ep_buf = NULL;
    int is_empty = 0;
    while(1){
        ep_buf = realloc(ep_buf, ep_cap);
        if(!ep_buf){ perror("realloc"); exit(1); }
        memset(ep_buf, 0, ep_cap);
        e_p(s_in, ep_buf, ep_cap, &is_empty, asmb);
        size_t used = strlen(ep_buf);
        if(used < ep_cap - 16) break;          /* fits with margin */
        ep_cap *= 2;
        if(ep_cap > (size_t)256*1024*1024){
            fprintf(stderr,"makeobj: expanded pattern too large (>256 MB), truncating.\n");
            break;
        }
    }
    if(is_empty){ free(ep_buf); return; }

    size_t s_cap = strlen(ep_buf) + 64;
    char *s = malloc(s_cap);
    if(!s){ perror("malloc"); free(ep_buf); return; }
    replace_percent_with_index(ep_buf, s, s_cap);
    free(ep_buf);

    int slen = (int)strlen(s);

    /* binary_list評価中フラグ: $$がpc_instr_startを返すのはこの期間のみ */
    st->in_binary_list = 1;
    /* Bugfix (axx.py port): this used to unconditionally clear
     * error_undefined_label here, discarding any "undefined label" status
     * the caller had already established BEFORE calling makeobj() -- in
     * particular, a !x-captured pattern variable's value is computed once
     * during trial pattern-matching (label_get_value() calls happen
     * there, not here), so if that capture referenced an undefined label,
     * the only trace of it is the flag the caller carries into this call.
     * Save it and OR it back in at the end (see any_undef below) instead
     * of dropping it on the floor. */
    int _prior_undef = st->error_undefined_label;
    st->error_undefined_label = 0;
    int any_undef = 0;

    /* Fix P9: use a separate logical index for ELF word tracking so that
     * UNDEF-skipped elements do not cause subsequent elements to inherit a
     * stale/duplicate word_idx (the old code used objl->len which does not
     * advance when an element is skipped).                                   */
    int logical_word_idx = 0;
    int idx=0;
    while(1){
        if(idx>=slen||s[idx]=='\0') break;
        if(s[idx]==','){
            /* 修正: ','はセパレータのみ。alignment paddingは挿入しない。
             * 旧コードはcommaごとにalign_addr()でパディングを入れていたが、
             * binary_listパターン内の','はフィールド区切りであって
             * アライメント指示ではない。 */
            idx++;
            continue;
        }
        int semicolon=0;
        if(s[idx]==';'){ semicolon=1; idx++; }
        st->elf_current_word_idx = logical_word_idx;
        /* pass==1では常にpass1_size_modeで評価する。
         * 未定義ラベル(EXTERN等)がある場合でも0として扱い、
         * @@[8,*(e,%%)]のような式でも8バイト分のサイズが正しく計上される。
         * pass==2/0では通常通りerror_undefined_labelフラグで判定する。 */
        if(st->pas==1) st->pass1_size_mode=1;
        st->error_undefined_label = 0;
        int io;
        uint256_t x=expr_expression_pat(asmb,s,idx,&io);
        if(st->pas==1){ st->pass1_size_mode=0; st->error_undefined_label=0; }
        idx=io;
        logical_word_idx++;
        if(st->error_undefined_label){
            any_undef = 1;
            if(s[idx]==','){idx++;continue;}
            continue;
        }
        if(semicolon?!u256_is_zero(x):1){
            iv_push(objl,x);
        } else if(semicolon){
            /* semicolon && x==0: element suppressed; remove any ELF refs recorded
             * at this word_idx to avoid generating spurious relocations.
             * Mirrors axx.py makeobj(): self.state._elf_label_refs_seen = [e for e in ... if e[2] != idx] */
            int cur_widx = logical_word_idx - 1;
            int wi2 = 0;
            for(int ri2 = 0; ri2 < st->elf_refs_len; ri2++){
                if(st->elf_refs[ri2].word_idx != cur_widx)
                    st->elf_refs[wi2++] = st->elf_refs[ri2];
                else
                    free(st->elf_refs[ri2].name);
            }
            st->elf_refs_len = wi2;
        }
        if(s[idx]==','){idx++;continue;}
        break;
    }
    st->elf_current_word_idx = -1;
    st->in_binary_list = 0;
    st->error_undefined_label = any_undef || _prior_undef;
    free(s);
}

/* =========================================================
 * VLIWProcessor
 * ========================================================= */
typedef struct { IntVec *data; int len; int cap; } IVVec;
static void ivv_init(IVVec*v){v->data=NULL;v->len=0;v->cap=0;}
/* Fix H: add NULL check after realloc, matching the guard in iv_push/sv_push.
 * The original silently continued to &v->data[v->len] after a failed realloc,
 * producing a NULL-dereference crash on the very next line. */
static void ivv_push(IVVec*v,IntVec*iv){
    if(v->len>=v->cap){
        v->cap=v->cap?v->cap*2:8;
        v->data=realloc(v->data,v->cap*sizeof(IntVec));
        if(!v->data){perror("realloc");exit(1);}
    }
    IntVec *dst=&v->data[v->len++]; iv_init(dst); iv_copy(dst,iv);
}
static void ivv_free(IVVec*v){
    for(int i=0;i<v->len;i++) iv_free(&v->data[i]);
    free(v->data); ivv_init(v);
}

/* Fix K: int_cmp used subtraction (*(int*)a - *(int*)b) which overflows when
 * a is large-positive and b is large-negative (or vice-versa), producing the
 * wrong sort order.  Use a branchless 3-way compare instead. */
static int int_cmp(const void*a,const void*b){
    int ia=*(const int*)a, ib=*(const int*)b;
    return (ia > ib) - (ia < ib);
}

static int vliwprocess(Assembler *asmb, const char *line, IntVec *idxs_in, IntVec *objl_in,
                       int idx, int *idx_out){
    AsmState *st=&asmb->st;
    IVVec objs; ivv_init(&objs);
    ivv_push(&objs,objl_in);

    int *idxlst=malloc(256*sizeof(int)); int nidxlst=0;
    /* The guard is inside the for-loop so each element is individually checked.
     * The original had `if(nidxlst<256) for(...)` which checks BEFORE the loop,
     * allowing nidxlst to overflow the buffer if new_idxs.len > 1. */
    for(int i=0;i<idxs_in->len;i++) if(nidxlst<256) idxlst[nidxlst++]=(int)u256_to_i64(idxs_in->data[i]);

    st->vliwstop=0;
    int slen=(int)strlen(line);
    while(1){
        idx=axx_skipspc(line,idx);
        if(idx+4<=slen && strncmp(line+idx,"!!!!",4)==0){ idx+=4; st->vliwstop=1; continue; }
        else if(idx+2<=slen && strncmp(line+idx,"!!",2)==0){
            idx+=2;
            /* 破綻点修正 (axx.py port): VLIWスロットの内容が".section"/
             * ".endsection"/".INCLUDE"等のディレクティブだった場合、
             * lineassemble2()はそれを即座に処理してしまう。しかしこの
             * パケット全体のバイトはまだ書き込まれておらず、st->pcも
             * パケット先頭のままである(st->pc += q はパケット全体の
             * 組み立てが終わった後に1回だけ行われる)。そのため.section
             * が行うセクション切替え等の副作用は誤った(パケット末尾では
             * なく先頭の)pcを基準に記録されてしまい、検出困難な形で
             * このパケットや後続バイトがセクション取り違えにより出力から
             * 消える/誤配置される事故になっていた。ディレクティブは
             * VLIWスロットの内容として意味を持たないため、明確なエラー
             * として打ち切る。 */
            { int _peek=idx; while(_peek<slen && (line[_peek]==' '||line[_peek]=='\t')) _peek++;
              if(_peek<slen && line[_peek]=='.'){
                  if(should_report_errors(st))
                      fprintf(stderr," error - directives (e.g. .section/.endsection/.INCLUDE) "
                              "are not allowed inside VLIW slots (the packet's PC has not "
                              "advanced yet at this point in the packet).\n");
                  ivv_free(&objs); free(idxlst);
                  if(idx_out) *idx_out=idx;
                  return 0;
              }
            }
            IntVec new_idxs; iv_init(&new_idxs);
            IntVec new_objl; iv_init(&new_objl);
            int new_idx;
            int _slot_ok = lineassemble2(asmb,line,idx,&new_idxs,&new_objl,&new_idx);
            idx=new_idx;
            if(!_slot_ok){
                iv_free(&new_idxs); iv_free(&new_objl);
                ivv_free(&objs); free(idxlst);
                if(idx_out) *idx_out=idx;
                return 0;
            }
            ivv_push(&objs,&new_objl);
            for(int i=0;i<new_idxs.len;i++) if(nidxlst<256) idxlst[nidxlst++]=(int)u256_to_i64(new_idxs.data[i]);
            iv_free(&new_idxs); iv_free(&new_objl);
            continue;
        } else break;
    }

    if(st->vliwtemplatebits==0){
        vset_clear(&st->vliwset);
        int tmp_idx[1]={0};
        vset_add(&st->vliwset,tmp_idx,1,"0");
    }

    int vbits=(st->vliwbits<0)?-st->vliwbits:st->vliwbits;
    int found=0;

    /* Fix ③ (axx.py): vliwinstbits==0 causes division by zero in noi calculation.
     * Guard and report an error, matching axx.py VLIWProcessor.vliwprocess(). */
    if(st->vliwinstbits == 0){
        if(should_report_errors(st))
            fprintf(stderr," error - vliwinstbits is zero; cannot compute instruction slots.\n");
        ivv_free(&objs); free(idxlst);
        if(idx_out) *idx_out=idx;
        return 0;
    }

    for(int ki=0;ki<st->vliwset.len;ki++){
        VliwSetEntry *k=&st->vliwset.data[ki];
        int *sorted_k=malloc(k->nidxs*sizeof(int));
        memcpy(sorted_k,k->idxs,k->nidxs*sizeof(int));
        qsort(sorted_k,k->nidxs,sizeof(int),int_cmp);
        int *sorted_l=malloc(nidxlst*sizeof(int));
        memcpy(sorted_l,idxlst,nidxlst*sizeof(int));
        qsort(sorted_l,nidxlst,sizeof(int),int_cmp);
        int match=(k->nidxs==nidxlst && memcmp(sorted_k,sorted_l,k->nidxs*sizeof(int))==0);
        free(sorted_k); free(sorted_l);
        if(!match && st->vliwtemplatebits!=0) continue;

        int io;
        uint256_t xv=expr_expression_pat(asmb,k->templ,0,&io);
        int at=st->vliwtemplatebits<0?-st->vliwtemplatebits:st->vliwtemplatebits;
        uint256_t tmask=u256_is_zero(u256_from_u64((uint64_t)at))?u256_zero():u256_sub(u256_shl(u256_one(),at),u256_one());
        uint256_t templ=u256_and(xv,tmask);

        IntVec values; iv_init(&values);
        for(int oi=0;oi<objs.len;oi++) for(int mi=0;mi<objs.data[oi].len;mi++) iv_push(&values,objs.data[oi].data[mi]);

        int ibyte=st->vliwinstbits/8+(st->vliwinstbits%8?1:0);
        int noi=(vbits-at)/st->vliwinstbits;
        /* 破綻点修正 (axx.py port): vliwtemplatebits(at)がvbitsを超える
         * (パケット幅よりテンプレート自体が大きい)矛盾した.vliw定義では、
         * noiが負になりtarget_lenも負になって、以降のfor(j=0;j<noi;j++)相当
         * のループが実質空になり、命令スロットの内容が無警告のまま失われた
         * 状態で何らかのパケットが出力されてしまう。noiが0以下の場合は
         * 明確なエラーで打ち切る。 */
        if(noi <= 0){
            if(should_report_errors(st))
                fprintf(stderr," error - .vliw: vliwtemplatebits (%d) leaves no room for "
                        "instruction slots in a %d-bit packet (vliwinstbits=%d).\n",
                        st->vliwtemplatebits, vbits, st->vliwinstbits);
            iv_free(&values);
            ivv_free(&objs); free(idxlst);
            if(idx_out) *idx_out=idx;
            return 0;
        }
        int target_len=ibyte*noi;
        if(values.len > target_len){
            if(should_report_errors(st))
                fprintf(stderr,"warning-VLIW:%d values exceed slot capacity %d,truncating.\n",values.len,target_len);
            values.len=target_len;
        } else {
            int needed=target_len-values.len;
            for(int pi=0;pi<needed;pi++) for(int ni=0;ni<st->vliwnop.len;ni++) iv_push(&values,st->vliwnop.data[ni]);
        }

        IntVec v1; iv_init(&v1);
        int cnt2=0;
        uint256_t im=u256_sub(u256_shl(u256_one(),st->vliwinstbits),u256_one());
        for(int j=0;j<noi;j++){
            uint256_t vv=u256_zero();
            for(int ii=0;ii<ibyte;ii++){
                vv=u256_shl(vv,8);
                if(values.len>cnt2) vv=u256_or(vv,u256_and(values.data[cnt2++],u256_from_u64(0xff)));
            }
            iv_push(&v1,u256_and(vv,im));
        }

        uint256_t pm=u256_sub(u256_shl(u256_one(),vbits),u256_one());
        uint256_t r=u256_zero();
        for(int vi=0;vi<v1.len;vi++){ r=u256_shl(r,st->vliwinstbits); r=u256_or(r,v1.data[vi]); }
        r=u256_and(r,pm);

        /* res: combine instruction words with template bits.
         * vliwtemplatebits<0 means template is placed at the MSB side;
         * otherwise template is placed at the LSB side.
         * This computation does not depend on the sign of vliwbits
         * (that only affects the byte-output order below). */
        uint256_t res;
        if(st->vliwtemplatebits<0) res=u256_or(r,u256_shl(templ,(int)(vbits-at)));
        else res=u256_or(u256_shl(r,at),templ);

        int q=0;
        uint64_t pc64=u256_to_u64(st->pc);
        if(st->vliwbits>0){
            int bc=vbits-8;
            for(int c2=0;c2<vbits/8;c2++){
                uint256_t byte_v=u256_and(u256_sar(res,bc),u256_from_u64(0xff));
                outbin(st,u256_from_u64(pc64+c2),byte_v);
                bc-=8; q++;
            }
        } else {
            for(int c2=0;c2<vbits/8;c2++){
                uint256_t byte_v=u256_and(res,u256_from_u64(0xff));
                outbin(st,u256_from_u64(pc64+c2),byte_v);
                res=u256_sar(res,8); q++;
            }
        }
        st->pc=u256_add(st->pc,u256_from_u64((uint64_t)q));
        iv_free(&values); iv_free(&v1);
        found=1; break;
    }

    if(!found && (should_report_errors(st)))
        fprintf(stderr," error - No vliw instruction-set defined.\n");

    ivv_free(&objs); free(idxlst);
    *idx_out=idx;
    return found;
}

/* =========================================================
 * AssemblyDirectiveProcessor
 * ========================================================= */
static int adir_labelc(AsmState *st, const char *l, const char *ll){
    char up[32]; axx_strupr_to(up,l,sizeof(up));
    if(strcmp(up,".LABELC")!=0) return 0;
    if(ll&&ll[0]){
        snprintf(st->lwordchars, sizeof(st->lwordchars),
                 "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789%s", ll);
    }
    return 1;
}

/* -------------------------------------------------------
 * Bug 7 fix: adir_label_processing()
 * For "label: .EQU expr", the original called
 *   expr_expression_asm(asmb, l, idx, &io)
 * where l is the full line and idx points past ".EQU".
 * This is correct as long as the expression parser ignores
 * everything before idx -- which it does via skipspc --
 * EXCEPT when the label name is itself a valid lwordchars
 * token at the start of l.  In that case the recursive
 * descent would try to parse the label name as a label
 * reference.
 *
 * Fix: pass (l + idx) as the string and reset idx to 0, so
 * the expression parser only ever sees the expression tail.
 * ------------------------------------------------------- */
static char *adir_label_processing(Assembler *asmb, const char *l, char *out, size_t osz){
    AsmState *st=&asmb->st;
    if(!l[0]){ out[0]=0; return out; }
    char label[512]; int idx;
    idx=axx_get_label_word(l,0,st->lwordchars,label,sizeof(label));
    int lidx=idx;
    if(label[0]&&lidx>0&&l[lidx-1]==':'){
        idx=axx_skipspc(l,idx);
        char e[256]; idx=axx_get_param_to_spc(l,idx,e,sizeof(e));
        char ue[256]; axx_strupr_to(ue,e,sizeof(ue));
        if(strcmp(ue,".EQU")==0){
            int io;
            /* axx.py fix: .EQU で ::reloctype 構文をサポートする。
             *   label: .equ <式>::<reloctype>  → reloc_type_override を設定
             *   label: .equ <式>              → reloc_type_override = -1（情報なし）
             * ::reloctype を省略すると label_put_value が -1 を渡し lmap_set が
             * 旧エントリの reloc_type_override をリセットする。 */
            const char *expr_tail = l + idx;
            int reloc_type = -1;
            /* expr_tail に '::' が含まれるか検索 */
            const char *dcolon = strstr(expr_tail, "::");
            char expr_buf[1024];
            if(dcolon){
                /* 式部分をコピー */
                size_t elen = (size_t)(dcolon - expr_tail);
                if(elen >= sizeof(expr_buf)) elen = sizeof(expr_buf)-1;
                memcpy(expr_buf, expr_tail, elen); expr_buf[elen] = '\0';
                expr_tail = expr_buf;
                /* reloctype 文字列 */
                const char *rt_str = dcolon + 2;
                char rt_lc[64]; int ri=0;
                while(rt_str[ri] && ri < 63){ rt_lc[ri]=(char)tolower((unsigned char)rt_str[ri]); ri++; }
                rt_lc[ri]='\0';
                reloc_type = elf_machine_named(elf_machine_find(st->elf_machine), rt_lc);
                if(reloc_type < 0)
                    fprintf(stderr," warning - unknown reloctype '%s' in .EQU for machine %d\n",
                            rt_lc, st->elf_machine);
            }

            /* === ここが修正箇所：.equ 内の forward reference を pass1 で正しく扱う === */
            uint256_t u;
            int saved_mode = st->pass1_size_mode;
            if(st->pas == 1)
                st->pass1_size_mode = 1;   /* forward ref を 0 として扱う */
            /* 破綻点修正 (axx.py port): reloc_type未指定の.EQUで異なる
             * セクションのラベルを跨いで演算すると(例: a_in_text -
             * b_in_data)、結果はアセンブラが暗黙に仮定する「連続配置」
             * でのみ正しい値になり、リロケーションが一切生成されない
             * ため、リンカがセクションを別配置にした瞬間に無警告で
             * 不正な定数になる。参照したラベルの所属セクションを記録し、
             * 2つ以上の異なるセクションに跨っていたら警告する。 */
            int track_sections = (reloc_type < 0);
            if(track_sections){
                st->equ_section_tracking = 1;
                st->equ_first_section[0] = '\0';
                st->equ_multi_section = 0;
            }
            u = expr_expression_asm(asmb, expr_tail, 0, &io);
            st->pass1_size_mode = saved_mode;
            if(track_sections){
                st->equ_section_tracking = 0;
                if(st->equ_multi_section && should_report_errors(st)){
                    fprintf(stderr, " warning - .EQU '%s': expression combines labels from "
                            "multiple sections without an explicit ::reloctype; the resulting "
                            "constant assumes a specific section layout and will NOT be "
                            "relocated by the linker.\n", label);
                }
            }
            /* Bugfix (axx.py port): an undefined label referenced by this
             * .EQU's expression used to go completely unnoticed here -- no
             * print, no had_error -- silently baking the UNDEF sentinel
             * (or 0, during pass1's size-probe mode) into `label`'s value
             * as if it were a legitimate constant. Mirrors the same check
             * every other directive that evaluates an expression already
             * performs (.ORG/.RESB/.ZERO/.ALIGN). */
            if(st->error_undefined_label && should_report_errors(st)){
                fprintf(stderr, " error - .EQU '%s': expression contains undefined label.\n",
                        label);
                st->had_error = 1;
            }
            /* ====================================================================== */

            label_put_value(st,label,u,st->current_section,1,reloc_type);  /* is_equ=1 */
            out[0]=0; return out;
        } else {
            label_put_value(st,label,st->pc,st->current_section,0,-1);  /* is_equ=0 */
            strncpy(out,l+lidx,osz-1); out[osz-1]=0; return out;
        }
    }
    strncpy(out,l,osz-1); out[osz-1]=0; return out;
}

/* asciistr: output quoted string bytes.
 * Returns 1 if l2 started with '"' (valid quoted string), 0 otherwise.
 * Mirrors axx.py asciistr() which returns True/False. */
static int asciistr(Assembler *asmb, const char *l2){
    AsmState *st=&asmb->st;
    if(!l2[0]||l2[0]!='"') return 0;
    int idx=1;
    while(l2[idx]&&l2[idx]!='"'){
        unsigned char ch;
        if(l2[idx]=='\\'&&l2[idx+1]=='0'){ ch=0; idx+=2; }
        else if(l2[idx]=='\\'&&l2[idx+1]=='t'){ ch='\t'; idx+=2; }
        else if(l2[idx]=='\\'&&l2[idx+1]=='n'){ ch='\n'; idx+=2; }
        else if(l2[idx]=='\\'&&l2[idx+1]=='r'){ ch='\r'; idx+=2; }
        else if(l2[idx]=='\\'&&l2[idx+1]=='\\'){ ch='\\'; idx+=2; }
        else if(l2[idx]=='\\'&&l2[idx+1]=='"'){ ch='"'; idx+=2; }
        else { ch=(unsigned char)l2[idx]; idx++; }
        outbin(st,st->pc,u256_from_u64(ch));
        st->pc=u256_add(st->pc,u256_one());
    }
    return 1;
}

static int adir_section(AsmState *st, const char *l, const char *l2){
    char up[32]; axx_strupr_to(up,l,sizeof(up));
    if(strcmp(up,".SECTION")!=0 && strcmp(up,".SEGMENT")!=0) return 0;
    if(l2&&l2[0]){
        /* Fix: mirror axx.py section_processing():
         * 1. Before switching, register the OLD section if not already registered,
         *    so sections appear in the order they are first WRITTEN TO (not declared).
         * 2. Update the old section's tentative size (if not confirmed by ENDSECTION).
         * 3. Register or update the NEW section, preserving confirmed sizes. */
        const char *old_sec = st->current_section;

        /* If old section is not yet registered, create it with start=0 entry_pc=0.
         * This handles the initial ".text" that is active before any .SECTION directive. */
        if(!secmap_find(&st->sections, old_sec)){
            SecEntry *ne = calloc(1, sizeof(SecEntry));
            ne->name = strdup(old_sec);
            ne->start = u256_zero();
            ne->size  = u256_zero();
            ne->entry_pc = u256_zero();
            ne->confirmed = 0;
            uint32_t h = hash_str(old_sec) % (uint32_t)st->sections.nb;
            ne->next = st->sections.buckets[h];
            st->sections.buckets[h] = ne;
            if(st->sections.count >= st->sections.cap){
                st->sections.cap *= 2;
                SecEntry**_tmp=realloc(st->sections.order,
                                      st->sections.cap * sizeof(SecEntry*));
                if(!_tmp){perror("realloc");exit(1);}
                st->sections.order=_tmp;
            }
            st->sections.order[st->sections.count++] = ne;
        }
        /* Update old section's tentative size (cumulative).
         * Bugfix (axx.py port): this used to skip entirely when
         * oe->confirmed was set (i.e. the old section was already closed by
         * .ENDSECTION). That gate is unnecessary for avoiding double-counting
         * -- entry_pc is already advanced to pc at every flush point, so the
         * delta below is naturally 0 right after a matching .ENDSECTION --
         * and it actively drops any code that ran in old_sec *after* that
         * .ENDSECTION but before this .SECTION switch, since that content's
         * nonzero delta never got flushed anywhere. Relying on the delta
         * alone (below) handles both cases correctly. */
        {
            SecEntry *oe = secmap_find(&st->sections, old_sec);
            if(oe){
                uint256_t delta = u256_sub(st->pc, oe->entry_pc);
                if(!u256_lt_signed(delta, u256_zero())){   /* delta >= 0 */
                    oe->size = u256_add(oe->size, delta);
                    if(!u256_is_zero(delta))
                        secrangevec_push(&st->section_ranges, old_sec, oe->entry_pc, delta);
                }
                /* entry_pc will be updated on re-entry */
            }
        }

        /* Switch to new section */
        snprintf(st->current_section, sizeof(st->current_section), "%s", l2);

        SecEntry *ne = secmap_find(&st->sections, l2);
        if(!ne){
            /* First visit: register new section at current pc */
            uint32_t h = hash_str(l2) % (uint32_t)st->sections.nb;
            ne = calloc(1, sizeof(SecEntry));
            ne->name = strdup(l2);
            ne->start = st->pc;
            ne->size  = u256_zero();
            ne->entry_pc = st->pc;
            ne->confirmed = 0;
            ne->next = st->sections.buckets[h];
            st->sections.buckets[h] = ne;
            if(st->sections.count >= st->sections.cap){
                st->sections.cap *= 2;
                SecEntry**_tmp=realloc(st->sections.order,
                                      st->sections.cap * sizeof(SecEntry*));
                if(!_tmp){perror("realloc");exit(1);}
                st->sections.order=_tmp;
            }
            st->sections.order[st->sections.count++] = ne;
        } else {
            /* Re-entry: update entry_pc so next ENDSECTION measures from here.
             * If confirmed, keep size unchanged. If not confirmed and size==0,
             * this was a dummy entry created as old_sec — update start. */

            if(u256_is_zero(ne->size) && !ne->confirmed){
                ne->start = st->pc;
            } else if(!ne->confirmed){
                /* multi-block: keep the minimum start */
                if(u256_lt_signed(st->pc, ne->start)) ne->start = st->pc;
            }
            ne->entry_pc = st->pc;
            /* 破綻点修正 (axx.py port): confirmedを前回訪問終了時の値の
             * ままにしていたため、以前.ENDSECTIONで確定済み(confirmed=1)
             * だったセクションに再入すると、今回の訪問が一度も.ENDSECTION
             * で閉じられていないのにconfirmed=1のままになっていた。この
             * 状態でファイル末尾までこのセクションが再度閉じられずに
             * 終わると、secmap_finalize_current()(ファイル末尾で開いた
             * ままの最終セクションを確定する処理)がconfirmed=1を見て
             * 「既に確定済み」と誤認し、今回の訪問分のバイト列が
             * section_rangesに一切登録されないまま(=最終出力から丸ごと
             * 欠落したまま)出力されていた。再入は必ず新しい未確定の訪問
             * なので、confirmedは0にリセットする。 */
            ne->confirmed = 0;
        }
    }
    return 1;
}
static int adir_endsection(AsmState *st, const char *l){
    char up[32]; axx_strupr_to(up,l,sizeof(up));
    if(strcmp(up,".ENDSECTION")!=0 && strcmp(up,".ENDSEGMENT")!=0) return 0;
    SecEntry *e=secmap_find(&st->sections,st->current_section);
    if(!e){
        fprintf(stderr," error - .ENDSECTION without matching .SECTION for '%s'.\n",
               st->current_section);
        st->had_error = 1;
        return 1;
    }
    /* Confirmed size: measure from entry_pc (last re-entry) to current pc.
     * Mirrors axx.py endsection_processing() using entry_pc for accuracy. */
    uint256_t delta = u256_sub(st->pc, e->entry_pc);
    if(!u256_lt_signed(delta, u256_zero())){
        e->size = u256_add(e->size, delta);
        if(!u256_is_zero(delta))
            secrangevec_push(&st->section_ranges, st->current_section, e->entry_pc, delta);
    }
    /* Bugfix (axx.py port): advance entry_pc to the current pc, mirroring
     * axx.py endsection_processing()'s
     *   self.state.sections[...] = [start, new_size, self.state.pc, True]
     * Without this, entry_pc is left pointing at the START of the fragment
     * just closed. adir_section()'s old-section-close logic and
     * secmap_finalize_current() no longer gate on `confirmed` (that gate
     * used to hide this), so leaving entry_pc stale would make either of
     * them recompute the exact same [entry_pc, pc) span again later and
     * double-count/double-push this fragment's bytes. */
    e->entry_pc = st->pc;
    e->confirmed = 1;
    return 1;
}
/* Helper shared by .RESB / .RESW / .RESD / .RESQ.
 * Advances PC by (cnt * mul) word-units without writing bytes to output.
 * The corresponding range is filled with the padding value at binary_flush()
 * time because BufMap entries are absent for the reserved region.
 * Mirrors axx.py AssemblyDirectiveProcessor.resb_processing() etc. */
static int adir_resX(Assembler *asmb, const char *l, const char *l2,
                     const char *directive, uint64_t mul){
    char up[16]; axx_strupr_to(up,l,sizeof(up));
    if(strcmp(up,directive)!=0) return 0;
    /* label_get_value() no longer clears this for us on a successful
     * lookup (see its Bugfix comment); reset before evaluating for a
     * fresh check. */
    asmb->st.error_undefined_label = 0;
    int io;
    uint256_t x=expr_expression_asm(asmb,l2,0,&io);
    if(asmb->st.error_undefined_label){
        if(should_report_errors(&asmb->st)){
            fprintf(stderr," error - %s argument contains undefined label.\n",directive);
            asmb->st.had_error = 1;
        }
        return 1;
    }
    int64_t cnt=u256_to_i64(x);
    if(cnt < 0){
        if(should_report_errors(&asmb->st)){
            fprintf(stderr," error - %s requires a non-negative count, got %lld.\n",
                    directive,(long long)cnt);
            asmb->st.had_error = 1;
        }
        return 1;
    }
    /* 256 MB guard: check before multiplying to avoid signed overflow */
    if(cnt > (int64_t)(1 << 28) / (int64_t)mul){
        if(should_report_errors(&asmb->st)){
            fprintf(stderr," error - %s count %lld (x%llu) exceeds maximum %d words.\n",
                    directive,(long long)cnt,(unsigned long long)mul,1<<28);
            asmb->st.had_error = 1;
        }
        return 1;
    }
    int64_t total = cnt * (int64_t)mul;
    asmb->st.pc = u256_add(asmb->st.pc, u256_from_u64((uint64_t)total));
    return 1;
}

/* .RESB N  -- reserve N byte-units (×1): advance PC by N. */
static int adir_resb(Assembler *asmb, const char *l, const char *l2){
    return adir_resX(asmb,l,l2,".RESB",1);
}
/* .RESW N  -- reserve N word-units (×2): advance PC by N*2. */
static int adir_resw(Assembler *asmb, const char *l, const char *l2){
    return adir_resX(asmb,l,l2,".RESW",2);
}
/* .RESD N  -- reserve N dword-units (×4): advance PC by N*4. */
static int adir_resd(Assembler *asmb, const char *l, const char *l2){
    return adir_resX(asmb,l,l2,".RESD",4);
}
/* .RESQ N  -- reserve N qword-units (×8): advance PC by N*8. */
static int adir_resq(Assembler *asmb, const char *l, const char *l2){
    return adir_resX(asmb,l,l2,".RESQ",8);
}
static int adir_zero(Assembler *asmb, const char *l, const char *l2){
    char up[16]; axx_strupr_to(up,l,sizeof(up));
    if(strcmp(up,".ZERO")!=0) return 0;
    /* See adir_resX()'s comment: reset before evaluating for a fresh check. */
    asmb->st.error_undefined_label = 0;
    int io;
    uint256_t x=expr_expression_asm(asmb,l2,0,&io);
    /* Fix ②: guard against UNDEF (undefined label) to avoid range(UNDEF) freeze.
     * Also guard against negative values. Mirrors axx.py zero_processing(). */
    if(asmb->st.error_undefined_label){
        if(should_report_errors(&asmb->st)){
            fprintf(stderr," error - .ZERO argument contains undefined label.\n");
            asmb->st.had_error = 1;
        }
        return 1;
    }
    int64_t cnt=u256_to_i64(x);
    if(cnt < 0){
        if(should_report_errors(&asmb->st)){
            fprintf(stderr," error - .ZERO requires a non-negative count, got %lld.\n", (long long)cnt);
            asmb->st.had_error = 1;
        }
        return 1;
    }
    for(int64_t i=0;i<cnt;i++){
        outbin2(&asmb->st,asmb->st.pc,u256_from_u64(0));
        asmb->st.pc=u256_add(asmb->st.pc,u256_one());
    }
    return 1;
}
static int adir_ascii(Assembler *asmb, const char *l, const char *l2){
    char up[16]; axx_strupr_to(up,l,sizeof(up));
    if(strcmp(up,".ASCII")!=0) return 0;
    /* Return the result of asciistr: 0 if l2 is not a quoted string.
     * Mirrors axx.py ascii_processing() which returns asciistr(). */
    return asciistr(asmb,l2);
}
static int adir_asciiz(Assembler *asmb, const char *l, const char *l2){
    char up[16]; axx_strupr_to(up,l,sizeof(up));
    if(strcmp(up,".ASCIZ")!=0) return 0;
    int f=asciistr(asmb,l2);
    if(!f){
        if(should_report_errors(&asmb->st)){
            fprintf(stderr," error - .ASCIZ requires a quoted string.\n");
            asmb->st.had_error = 1;
        }
        return 0;
    }
    outbin(&asmb->st,asmb->st.pc,u256_zero());
    asmb->st.pc=u256_add(asmb->st.pc,u256_one());
    return 1;
}
static int adir_align(Assembler *asmb, const char *l, const char *l2){
    char up[16]; axx_strupr_to(up,l,sizeof(up));
    if(strcmp(up,".ALIGN")!=0) return 0;
    if(l2&&l2[0]){
        /* Bugfix (axx.py port): this never checked error_undefined_label
         * at all -- an undefined label as the boundary argument evaluated
         * to the UNDEF sentinel (an enormous but finite value), which then
         * sailed past the `u_int <= 0` guard below (it's huge and
         * positive) and got assigned directly to st->align, silently
         * corrupting all subsequent .ALIGN padding computations. Same
         * reset-before-evaluate-then-check pattern as .ORG/.RESB/.ZERO. */
        asmb->st.error_undefined_label = 0;
        int io; uint256_t u=expr_expression_asm(asmb,l2,0,&io);
        if(asmb->st.error_undefined_label){
            if(should_report_errors(&asmb->st)){
                fprintf(stderr," error - .ALIGN argument contains undefined label.\n");
                asmb->st.had_error = 1;
            }
            return 1;
        }
        int64_t u_int=u256_to_i64(u);
        /* 破綻点修正 (axx.py port): 値の検証が一切なかったため、".ALIGN 0"が
         * align_addr()内の"addr % st->align"でゼロ除算を起こし、SIGFPEで
         * 即座にクラッシュしていた(axx.py側は元々 u_int<=0 をエラーとして
         * 弾いており、Cポートだけこのガードが欠落していた)。 */
        if(u_int <= 0){
            if(should_report_errors(&asmb->st)){
                fprintf(stderr," error - .ALIGN requires a positive value, got %lld.\n",
                        (long long)u_int);
                asmb->st.had_error = 1;
            }
            return 1;
        }
        asmb->st.align=(int)u_int;
    }
    /* 破綻点修正 (axx.py port): align_addr()はstate.pc(生のグローバルpc)を
     * そのまま境界に揃えていたが、境界判定に本来使うべきなのは出力
     * ファイル上の実際の位置であるセクション内相対オフセットである。
     * 同じセクションへの再入があると、間に挟まった他セクション分だけ
     * 生pcとセクション内相対オフセットがズレるため、生pc基準では
     * たまたま境界に乗っていても実際の出力上では境界からズレたままに
     * なる無警告の不整合が起きていた。セクション内相対オフセット基準で
     * 必要なパディング量を計算し、そのパディング量をそのまま生pcにも
     * 加算する。 */
    {
        uint64_t _raw = u256_to_u64(asmb->st.pc);
        int64_t _adj = equ_section_relative_offset(&asmb->st, asmb->st.current_section, _raw);
        uint64_t _base = (_adj >= 0) ? (uint64_t)_adj : _raw;
        uint64_t _aligned_base = align_addr(&asmb->st, _base);
        uint64_t _padding = _aligned_base - _base;
        asmb->st.pc = u256_from_u64(_raw + _padding);
    }
    return 1;
}
static int adir_org(Assembler *asmb, const char *l, const char *l2){
    char up[16]; axx_strupr_to(up,l,sizeof(up));
    if(strcmp(up,".ORG")!=0) return 0;
    /* See adir_resX()'s comment: reset before evaluating for a fresh check. */
    asmb->st.error_undefined_label = 0;
    int io;
    uint256_t u=expr_expression_asm(asmb,l2,0,&io);
    /* Fix ②: guard against UNDEF to prevent pc being set to 0xffff…ff.
     * Mirrors axx.py org_processing() which checks error_undefined_label. */
    if(asmb->st.error_undefined_label){
        if(should_report_errors(&asmb->st)){
            fprintf(stderr," error - .ORG argument contains undefined label.\n");
            asmb->st.had_error = 1;
        }
        return 1;
    }
    if(io+2<=(int)strlen(l2) && axx_upper_char(l2[io])==','&&axx_upper_char(l2[io+1])=='P'){
        if(u256_gt_signed(u,asmb->st.pc)){
            uint64_t from=u256_to_u64(asmb->st.pc);
            uint64_t to=u256_to_u64(u);
            for(uint64_t i=from;i<to;i++) outbin2(&asmb->st,u256_from_u64(i),asmb->st.padding);
        }
    }
    asmb->st.pc=u;
    return 1;
}
static int adir_export(Assembler *asmb, const char *l, const char *l2){
    AsmState *st=&asmb->st;
    if(st->pas!=2&&st->pas!=0) return 0;
    char up[16]; axx_strupr_to(up,l,sizeof(up));
    /* axx.py export_processing(): handles both .EXPORT and .GLOBAL */
    if(strcmp(up,".EXPORT")!=0 && strcmp(up,".GLOBAL")!=0) return 0;
    char buf[4096]; strncpy(buf,l2,sizeof(buf)-1); buf[sizeof(buf)-1]=0;
    int idx=0; int blen=(int)strlen(buf);
    while(idx<blen&&buf[idx]){
        idx=axx_skipspc(buf,idx);
        char s[512];
        idx=axx_get_label_word(buf,idx,st->lwordchars,s,sizeof(s));
        if(!s[0]) break;
        if(buf[idx]==':') idx++;
        uint256_t v=label_get_value(st,s);
        const char *sec=label_get_section(st,s);
        /* Preserve the is_equ flag so that .equ-defined constants get
         * SHN_ABS treatment in the ELF symbol table.
         * Mirrors axx.py export_processing() which stores the full label entry. */
        LabelEntry *le=lmap_find(&st->labels,s);
        int is_equ_v = le ? le->is_equ : 0;
        lmap_set(&st->export_labels,s,v,sec,is_equ_v);
        if(buf[idx]==',') idx++;
    }
    return 1;
}

/* axx.py extern_processing():
 * .EXTERN label [::rtype] [, label [::rtype] ...]
 * Declares external (undefined) symbols.  Each name is registered in
 * st->labels as an imported label (is_imported=1, value=0, section=".text")
 * so that references do NOT raise "undefined label" errors, and
 * write_elf_obj() emits the symbol as STB_GLOBAL / SHN_UNDEF.
 * If the label is already locally defined (.EXTERN is processed in all passes
 * to support forward references in the pass1 relaxation loop).
 * Optional ::rtype suffix (e.g. ::plt32) overrides the ELF relocation type
 * for references to this symbol.  Mirrors axx.py extern_processing(). */
static int adir_extern(Assembler *asmb, const char *l, const char *l2){
    AsmState *st=&asmb->st;
    char up[16]; axx_strupr_to(up,l,sizeof(up));
    if(strcmp(up,".EXTERN")!=0) return 0;
    char buf[4096]; strncpy(buf,l2,sizeof(buf)-1); buf[sizeof(buf)-1]=0;
    int idx=0; int blen=(int)strlen(buf);
    while(idx<blen&&buf[idx]){
        idx=axx_skipspc(buf,idx);
        char s[512]; s[0]=0;
        idx=axx_get_label_word(buf,idx,st->lwordchars,s,sizeof(s));
        if(!s[0]) break;
        /* axx.py: get_label_word consumes a trailing ':'; if the consumed char
         * was the first ':' of '::' we need to step back so '::' is detected. */
        if(idx > 0 && buf[idx-1]==':' && idx < blen && buf[idx]==':')
            idx--;  /* back up to expose '::' */
        /* Parse optional ::rtype suffix. Default relocation type and the
         * ::name -> reloc-type-number lookup both come from ELF_MACHINES
         * (axx.py port: single source of truth, see its definition above). */
        const ElfMachineInfo *_mtbl_ext = elf_machine_find(st->elf_machine);
        int reloc_type = _mtbl_ext ? _mtbl_ext->extern_default : 2;
        if(idx+1 < blen && buf[idx]==':' && buf[idx+1]==':'){
            idx += 2;
            int rt_start = idx;
            while(idx < blen && buf[idx]!=' ' && buf[idx]!='\t'
                  && buf[idx]!=',' && buf[idx]!=':' && buf[idx]!='\0')
                idx++;
            char rt_str[64]={0};
            int rt_len = idx - rt_start;
            if(rt_len > 0 && rt_len < (int)sizeof(rt_str)-1){
                memcpy(rt_str, buf+rt_start, (size_t)rt_len);
                rt_str[rt_len]=0;
                /* lower-case for comparison */
                for(int _ci=0;rt_str[_ci];_ci++)
                    if(rt_str[_ci]>='A'&&rt_str[_ci]<='Z') rt_str[_ci]+=32;
                int rtype = elf_machine_named(_mtbl_ext, rt_str);
                if(rtype < 0)
                    fprintf(stderr," warning - unknown reloc type '%s' in .EXTERN for machine %d\n",
                            rt_str, st->elf_machine);
                else
                    reloc_type = rtype;
            }
        }
        if(idx < blen && buf[idx]==':') idx++;
        /* Only register if NOT already locally defined.
         * A locally defined label has is_imported==0 (or absent). */
        LabelEntry *existing=lmap_find(&st->labels,s);
        int is_locally_defined = (existing && !existing->is_imported);
        if(!is_locally_defined){
            lmap_set_imported(&st->labels, s, u256_zero(), ".text", reloc_type);
        } else if(existing && reloc_type >= 0) {
            existing->reloc_type_override = reloc_type;
        }
        idx=axx_skipspc(buf,idx);
        if(buf[idx]==',') idx++;
    }
    return 1;
}

/* axx.py reloctype_processing() port:
 * .RELOCTYPE name8,name16,name32,name64
 * Overrides, per encoded-field byte width, the default relocation type
 * that the auto-detect path (RTYPE_FOR() / elf_machine_width_guess())
 * picks for a label reference with no explicit `::reloctype` suffix on its
 * own label (that per-label form is still `.EXTERN`/`.EQU ::reloctype`).
 *
 * The four comma-separated positions correspond, in order, to encoded
 * field widths of 1, 2, 4, and 8 bytes. Fewer than four may be given, and a
 * blank position (two consecutive commas, or a trailing comma) leaves that
 * width's mapping untouched -- e.g. `.reloctype ,,,abs64` only changes the
 * 8-byte width. Each name must be registered for the target machine
 * (the same set `.EXTERN`/`.EQU` accept) and its registered width must
 * match the position it's given in; otherwise it's rejected with a warning
 * and that position keeps its previous mapping (built-in default, or an
 * earlier `.reloctype` for the same width). Repeated `.RELOCTYPE`
 * directives accumulate: only the widths named in the latest directive are
 * touched. This is a whole-file, order-independent setting, like axx.py's
 * counterpart -- it applies to every subsequent auto-detected relocation
 * for the rest of the assembly (both passes) until changed again. */
static int adir_reloctype(Assembler *asmb, const char *l, const char *l2){
    AsmState *st=&asmb->st;
    char up[16]; axx_strupr_to(up,l,sizeof(up));
    if(strcmp(up,".RELOCTYPE")!=0) return 0;

    const ElfMachineInfo *_mtbl_rt = elf_machine_find(st->elf_machine);
    if(!_mtbl_rt){
        fprintf(stderr," warning - .RELOCTYPE: no relocation table for machine %d\n",
                st->elf_machine);
        return 1;
    }
    static const int _widths[4] = {1, 2, 4, 8};

    char buf[4096]; strncpy(buf,l2,sizeof(buf)-1); buf[sizeof(buf)-1]=0;
    int blen=(int)strlen(buf);
    int idx=0, pos=0;
    while(idx<=blen){
        int tok_start = idx;
        while(idx<blen && buf[idx]!=',') idx++;
        int tok_len = idx - tok_start;

        if(pos >= 4){
            if(tok_len > 0)
                fprintf(stderr," warning - .RELOCTYPE: too many arguments "
                        "(only 4 widths -- 8/16/32/64-bit -- are supported)\n");
            break;
        }

        char name[64]={0};
        /* trim surrounding spaces/tabs, lower-case, bounds-checked copy */
        int a=tok_start, b=idx;
        while(a<b && (buf[a]==' '||buf[a]=='\t')) a++;
        while(b>a && (buf[b-1]==' '||buf[b-1]=='\t')) b--;
        int nlen = b - a;
        if(nlen > 0 && nlen < (int)sizeof(name)-1){
            memcpy(name, buf+a, (size_t)nlen);
            name[nlen]=0;
            for(int _ci=0; name[_ci]; _ci++)
                if(name[_ci]>='A' && name[_ci]<='Z') name[_ci]+=32;
        }

        if(name[0]){
            int rtype = elf_machine_named(_mtbl_rt, name);
            if(rtype < 0){
                fprintf(stderr," warning - unknown reloc type '%s' in "
                        ".RELOCTYPE for machine %d\n", name, st->elf_machine);
            } else {
                int expected_width = _widths[pos];
                int actual_width = elf_machine_reloc_bytes(_mtbl_rt, rtype);
                if(actual_width != 0 && actual_width != expected_width){
                    fprintf(stderr," warning - .RELOCTYPE: '%s' is a %d-bit "
                            "relocation type, but was given in the %d-bit "
                            "position; ignored\n",
                            name, actual_width*8, expected_width*8);
                } else {
                    st->reloctype_override[pos] = rtype;
                }
            }
        }

        pos++;
        if(idx>=blen) break;
        idx++;  /* skip ',' */
    }
    return 1;
}

/* =========================================================
 * Main assembly loop
 * ========================================================= */
/* =========================================================
 * 順序非依存パターン選択 (order-independent pattern matching)
 *
 * 旧実装は「ファイル中で最初にマッチしたパターン」を採用していたため、
 * LD A,(HL) / LD A,r / LD A,!e のようなパターン群はファイル内の出現順に
 * 依存していた（例: LD A,!e が先にあると LD A,(HL) の (HL) が式として
 * 捕捉されてしまう）。
 *
 * 新実装は全パターンを走査し、マッチしたものの中から具体度スコア
 *     (式キャプチャ数, シンボルキャプチャ数, -リテラル一致文字数)
 * が最小（=最も具体的）なパターンを採用する。優先順位は
 *     リテラル完全一致 > シンボル(小文字)一致 > 式キャプチャ(!e等)
 * となり、同点の場合はファイル内で先に出現したパターンを採用する
 * （従来動作との互換性を保つ）。
 *
 * ディレクティブ (.setsym / .check / .bits 等) はファイル順に効果を持つ
 * ため走査中は従来通り逐次適用し、マッチ成功時点のディレクティブ状態を
 * BestMatch にスナップショットとして保存する。採用パターンのオブジェクト
 * 生成は走査完了後にそのスナップショットを復元してから行うので、
 * 「そのパターン位置までのディレクティブが適用された状態で生成する」
 * という従来のセマンティクスが保たれる。
 *
 * 注: すべてファイルスコープの static 関数で実装する（ネスト関数不使用）。
 * ========================================================= */
typedef struct {
    int       valid;
    int       score_expr, score_sym, score_lit;
    int       pln;
    PatEntry *pat;
    /* マッチで確定したキャプチャ変数 */
    uint256_t vars[26];
    /* マッチ中に追加された ELF 参照の差分（name は strdup 所有） */
    struct { char *name; uint64_t val; int word_idx; } *refs;
    int       refs_len;
    /* elf_var_to_label のスナップショット（label_name は strdup 所有） */
    struct { int set; char *label_name; uint64_t label_val; } vtl[26];
    /* --- このパターン位置までのディレクティブ状態 --- */
    SymMap    symbols;
    StrVec    check_constraints[26];
    char      swordchars[256];
    uint256_t padding;
    int       bts;
    int       endian_big;
    int       vliwbits, vliwinstbits, vliwtemplatebits, vliwflag;
    IntVec    vliwnop;
    VliwSet   vliwset;
    /* Bugfix (axx.py port): a !x-captured pattern variable's value is
     * computed once during THIS trial match (label_get_value() calls
     * happen inside pat_match0() above, not later), so if that capture
     * referenced an undefined label, this flag is the only record of it.
     * Without saving/restoring it here, it was always discarded before
     * the real makeobj() call and the final "Undefined label in
     * expression" check downstream could ever see it. */
    int       error_undefined_label;
} BestMatch;

static void best_init(BestMatch *b){
    memset(b, 0, sizeof(*b));
}

static void best_free(BestMatch *b){
    if(!b->valid){ memset(b, 0, sizeof(*b)); return; }
    for(int i=0;i<b->refs_len;i++) free(b->refs[i].name);
    free(b->refs);
    for(int i=0;i<26;i++) free(b->vtl[i].label_name);
    smap_free(&b->symbols);
    for(int i=0;i<26;i++) sv_free(&b->check_constraints[i]);
    iv_free(&b->vliwnop);
    vset_free(&b->vliwset);
    memset(b, 0, sizeof(*b));
}

/* スコア (e1,-l1,s1) < (e2,-l2,s2) の辞書式比較。1 なら左辺がより具体的。
 * 修正: リテラル一致文字数をシンボル数より優先する (axx.py と同期)。 */
static int score_less(int e1,int s1,int l1, int e2,int s2,int l2){
    if(e1 != e2) return e1 < e2;
    if(l1 != l2) return l1 > l2;   /* リテラル一致文字数は多いほど具体的 */
    return s1 < s2;
}

/* 現在のマッチ結果とディレクティブ状態を best にスナップショットする。
 * saved_refs_len はマッチ試行直前の elf_refs_len（差分抽出用）。 */
static void best_capture(AsmState *st, BestMatch *b, PatEntry *pat, int pln,
                         int saved_refs_len){
    best_free(b);
    b->valid      = 1;
    b->score_expr = st->match_score_expr;
    b->score_sym  = st->match_score_sym;
    b->score_lit  = st->match_score_lit;
    b->pln        = pln;
    b->pat        = pat;
    b->error_undefined_label = st->error_undefined_label;
    memcpy(b->vars, st->vars, sizeof(b->vars));

    /* マッチで追加された ELF 参照の差分を複製 */
    b->refs_len = st->elf_refs_len - saved_refs_len;
    b->refs = NULL;
    if(b->refs_len > 0){
        b->refs = malloc((size_t)b->refs_len * sizeof(b->refs[0]));
        if(!b->refs){ perror("malloc"); exit(1); }
        for(int i=0;i<b->refs_len;i++){
            b->refs[i].name = st->elf_refs[saved_refs_len+i].name
                              ? strdup(st->elf_refs[saved_refs_len+i].name) : NULL;
            b->refs[i].val      = st->elf_refs[saved_refs_len+i].val;
            b->refs[i].word_idx = st->elf_refs[saved_refs_len+i].word_idx;
        }
    }
    /* elf_var_to_label のスナップショット */
    for(int i=0;i<26;i++){
        b->vtl[i].set       = st->elf_var_to_label[i].set;
        b->vtl[i].label_val = st->elf_var_to_label[i].label_val;
        b->vtl[i].label_name = st->elf_var_to_label[i].label_name
                               ? strdup(st->elf_var_to_label[i].label_name) : NULL;
    }
    /* ディレクティブ状態 */
    smap_init(&b->symbols);
    for(int bi=0; bi<st->symbols.nb; bi++)
        for(SymEntry *e=st->symbols.buckets[bi]; e; e=e->next)
            smap_set(&b->symbols, e->key, e->val);
    for(int i=0;i<26;i++){
        sv_init(&b->check_constraints[i]);
        for(int j=0;j<st->check_constraints[i].len;j++)
            sv_push(&b->check_constraints[i], st->check_constraints[i].data[j]);
    }
    memcpy(b->swordchars, st->swordchars, sizeof(b->swordchars));
    b->padding          = st->padding;
    b->bts              = st->bts;
    b->endian_big       = st->endian_big;
    b->vliwbits         = st->vliwbits;
    b->vliwinstbits     = st->vliwinstbits;
    b->vliwtemplatebits = st->vliwtemplatebits;
    b->vliwflag         = st->vliwflag;
    iv_init(&b->vliwnop);
    iv_copy(&b->vliwnop, &st->vliwnop);
    vset_init(&b->vliwset);
    for(int i=0;i<st->vliwset.len;i++)
        vset_add(&b->vliwset, st->vliwset.data[i].idxs,
                 st->vliwset.data[i].nidxs, st->vliwset.data[i].templ);
}

/* best に保存したディレクティブ状態を st に復元する。 */
static void best_restore_dirstate(AsmState *st, const BestMatch *b){
    smap_clear(&st->symbols);
    for(int bi=0; bi<b->symbols.nb; bi++)
        for(SymEntry *e=b->symbols.buckets[bi]; e; e=e->next)
            smap_set(&st->symbols, e->key, e->val);
    for(int i=0;i<26;i++){
        sv_free(&st->check_constraints[i]);
        for(int j=0;j<b->check_constraints[i].len;j++)
            sv_push(&st->check_constraints[i], b->check_constraints[i].data[j]);
    }
    memcpy(st->swordchars, b->swordchars, sizeof(st->swordchars));
    st->padding          = b->padding;
    st->bts              = b->bts;
    st->endian_big       = b->endian_big;
    st->vliwbits         = b->vliwbits;
    st->vliwinstbits     = b->vliwinstbits;
    st->vliwtemplatebits = b->vliwtemplatebits;
    st->vliwflag         = b->vliwflag;
    iv_copy(&st->vliwnop, &b->vliwnop);
    vset_clear(&st->vliwset);
    for(int i=0;i<b->vliwset.len;i++)
        vset_add(&st->vliwset, b->vliwset.data[i].idxs,
                 b->vliwset.data[i].nidxs, b->vliwset.data[i].templ);
}

/* st->elf_refs に1件追加する（name は strdup 複製）。 */
static void elf_refs_push_copy(AsmState *st, const char *name,
                               uint64_t val, int word_idx){
    if(st->elf_refs_len >= st->elf_refs_cap){
        st->elf_refs_cap = st->elf_refs_cap ? st->elf_refs_cap*2 : 8;
        st->elf_refs = realloc(st->elf_refs,
            st->elf_refs_cap * sizeof(st->elf_refs[0]));
        if(!st->elf_refs){ perror("realloc"); exit(1); }
    }
    st->elf_refs[st->elf_refs_len].name     = name ? strdup(name) : NULL;
    st->elf_refs[st->elf_refs_len].val      = val;
    st->elf_refs[st->elf_refs_len].word_idx = word_idx;
    st->elf_refs_len++;
}

/* 事前フィルタ: パターン先頭のリテラル大文字列（ニーモニック部）が
 * 入力行と一致するかを判定する。pat_match() の大文字分岐は
 * 「パターンの大文字は入力と大文字小文字を無視して完全一致、空白は
 * 両側で読み飛ばし」なので、この前置部分が一致しないパターンは
 * pat_match0() を呼ぶまでもなく不成立と判定できる
 * （結果を変えない純粋な高速化）。
 * 大文字・空白以外の文字（!, 小文字, 記号, [[ 等）が現れた時点で
 * 前置部分を打ち切る。前置部分が空ならフィルタ不可として 1 を返す。 */
static int pat_prefix_matches(const char *pat, const char *lin){
    char pfx[64];
    int np = 0;
    for(const char *p = pat; *p && np < (int)sizeof(pfx)-1; p++){
        if(*p >= 'A' && *p <= 'Z') pfx[np++] = *p;
        else if(*p == ' ') continue;
        else break;
    }
    if(np == 0) return 1;   /* フィルタ不可: 常に pat_match0 を試行 */
    int k = 0;
    for(const char *q = lin; *q; q++){
        if(*q == ' ') continue;
        if(axx_upper_char(*q) != pfx[k]) return 0;
        k++;
        if(k == np) return 1;
    }
    return 0;   /* 入力行が前置部分より短い */
}

static int lineassemble2(Assembler *asmb, const char *line, int idx,
                         IntVec *idxs_out, IntVec *objl_out, int *idx_out){
    AsmState *st=&asmb->st;
    iv_clear(idxs_out); iv_clear(objl_out);

    char l[1024]={0}, l2[4096]={0};
    idx=axx_get_param_to_spc(line,idx,l,sizeof(l));
    idx=axx_get_param_to_eon(line,idx,l2,sizeof(l2));
    int ll=(int)strlen(l); while(ll>0&&(l[ll-1]==' '||l[ll-1]=='\t')) l[--ll]=0;
    char l_nospace[1024]={0}; int nn=0;
    for(int i=0;l[i];i++) if(l[i]!=' ') l_nospace[nn++]=l[i];
    l_nospace[nn]=0;
    snprintf(l, sizeof(l), "%s", l_nospace);

    if(adir_section(st,l,l2)){ *idx_out=idx; return 1; }
    if(adir_endsection(st,l)){ *idx_out=idx; return 1; }
    if(adir_resb(asmb,l,l2)){ *idx_out=idx; return 1; }
    if(adir_resw(asmb,l,l2)){ *idx_out=idx; return 1; }
    if(adir_resd(asmb,l,l2)){ *idx_out=idx; return 1; }
    if(adir_resq(asmb,l,l2)){ *idx_out=idx; return 1; }
    if(adir_zero(asmb,l,l2)){ *idx_out=idx; return 1; }
    if(adir_ascii(asmb,l,l2)){ *idx_out=idx; return 1; }
    if(adir_asciiz(asmb,l,l2)){ *idx_out=idx; return 1; }
    { char up[16]; axx_strupr_to(up,l,sizeof(up));
      if(strcmp(up,".INCLUDE")==0){
          char raw[512]; axx_get_string(l2,raw,sizeof(raw));
          if(raw[0]){
              /* Resolve relative path against the currently assembling file.
               * Mirrors axx.py include_asm():
               *   if not os.path.isabs(s):
               *       base = os.path.dirname(os.path.abspath(cur))
               *       s = os.path.join(base, s)  */
              char resolved[1024];
              const char *cur = st->current_file;
              /* 破綻点修正 (axx.py port): raw(インクルード対象)が特殊
               * マーカー文字列"stdin"そのものである場合、fileassemble()が
               * fn=="stdin"を厳密一致で見て標準入力を読み込む特別扱いを
               * するためのリテラルマーカーであり、実在するファイルパス
               * ではない。base_dirと結合してしまうと厳密一致が壊れ、
               * 存在しないファイルを開こうとして失敗していた。 */
              if(strcmp(raw,"stdin")==0){
                  strncpy(resolved, raw, sizeof(resolved)-1);
                  resolved[sizeof(resolved)-1]='\0';
              } else if(cur && cur[0] && strcmp(cur,"(stdin)")!=0 && strcmp(cur,"stdin")!=0){
                  char dir_buf[1024];
                  axx_dir_of(cur, dir_buf, sizeof(dir_buf));
                  axx_resolve_path(dir_buf, raw, resolved, sizeof(resolved));
              } else {
                  strncpy(resolved, raw, sizeof(resolved)-1);
                  resolved[sizeof(resolved)-1]='\0';
              }
              fileassemble(asmb,resolved);
          }
          *idx_out=idx; return 1;
      }
    }
    if(adir_align(asmb,l,l2)){ *idx_out=idx; return 1; }
    if(adir_org(asmb,l,l2)){ *idx_out=idx; return 1; }
    if(adir_labelc(st,l,l2)){ *idx_out=idx; return 1; }
    if(adir_extern(asmb,l,l2)){ *idx_out=idx; return 1; }
    if(adir_reloctype(asmb,l,l2)){ *idx_out=idx; return 1; }
    if(adir_export(asmb,l,l2)){ *idx_out=idx; return 1; }

    /* 撤廃: ソース側(.sファイル)からの.setsym/.clearsymは廃止した。
     * シンボル(レジスタ名等のエンコード値)はパターンファイル(.axx)側
     * でのみ定義するものとし、ソース側からの上書きは受け付けない。
     * ソース中に.setsym/.clearsymと書いても、以下のパターンマッチング
     * ループに委ねられ、該当パターンが無いため通常の
     * 未知命令/構文エラーとして報告される。 */

    if(!l[0]){ *idx_out=idx; return 0; }

    int se=0, oerr=0, pln=0;
    int idxs_val=0;
    int loopflag=1;
    PatEntry *oerr_entry=NULL;   /* pattern entry that caused oerr */
    int hit_sentinel=0;          /* 番兵エントリ f[0]=="" に到達したか */
    BestMatch best;
    best_init(&best);

    for(int pi=0;pi<st->pat.len;pi++){
        PatEntry *i=&st->pat.data[pi];
        pln++;
        for(int vi=0;vi<26;vi++) st->vars[vi]=u256_zero();

        if(dir_set_symbol(asmb,i)) continue;
        if(dir_clear_symbol(asmb,i)) continue;
        if(dir_padding(asmb,i)) continue;
        if(dir_bits(asmb,i)) continue;
        if(dir_symbolc(asmb,i)) continue;
        if(dir_epic(asmb,i)) continue;
        if(dir_vliwp(asmb,i)) continue;
        if(dir_check(asmb,i)) continue;
        if(dir_clrcheck(asmb,i)) continue;

        int lw=0; for(int fi=0;fi<PAT_FIELDS;fi++) if(i->f[fi][0]) lw++;
        if(lw==0) continue;

        /* Fix: l2(オペランド部)が空のとき "%s %s" は末尾に余分な空白を
         * 残してしまい、空白の有無を厳密に見るようになった pat_match() で
         * 「NOP」のようなオペランド無しパターンが不一致になってしまう。
         * l2が空の場合は区切りの空白を入れない(axx.py側と同期)。 */
        char lin[8192];
        if(l2[0]) snprintf(lin,sizeof(lin),"%s %s",l,l2);
        else      snprintf(lin,sizeof(lin),"%s",l);
        axx_reduce_spaces(lin);

        if(!i->f[0][0]){
            /* 番兵エントリ: パターン走査の終端。
             * f[3] にはVLIWスロットインデックス式が入っているため、
             * マッチが1つも無い場合はここで必ず評価する。
             * マッチ済み (best.valid) の場合は採用パターンの f[3] を
             * 生成ステージで評価するのでここでは評価しない。 */
            hit_sentinel=1;
            if(!best.valid){
                int io2;
                uint256_t idxv2=expr_expression_pat(asmb,i->f[3],0,&io2);
                idxs_val=(int)u256_to_i64(idxv2);
            }
            break;
        }

        /* 事前フィルタ: 先頭ニーモニック不一致のパターンはスキップする
         * （結果は変わらない・高速化のみ）。 */
        if(!pat_prefix_matches(i->f[0], lin)) continue;

        st->error_undefined_label=0;
        st->expmode=EXP_ASM;

        /* マッチ試行の副作用（キャプチャ変数・ELF追跡状態）を
         * 巻き戻せるよう保存する。 */
        uint256_t saved_vars[26];
        memcpy(saved_vars, st->vars, sizeof(saved_vars));
        int saved_refs_len = st->elf_refs_len;
        struct { int set; char *label_name; uint64_t label_val; } saved_vtl[26];
        for(int vi=0;vi<26;vi++){
            saved_vtl[vi].set        = st->elf_var_to_label[vi].set;
            saved_vtl[vi].label_val  = st->elf_var_to_label[vi].label_val;
            saved_vtl[vi].label_name = st->elf_var_to_label[vi].label_name
                                       ? strdup(st->elf_var_to_label[vi].label_name)
                                       : NULL;
        }

        /* パターンマッチ試行中はラベル未定義エラーの表示を抑制する。
         * (例: OUT (!n),A が OUT (C),E を試みると !n キャプチャで
         *  C がラベルとして評価され false-positive エラーが出る。) */
        st->in_match_attempt = 1;
        int _match_ok = pat_match0(asmb,lin,i->f[0]);
        st->in_match_attempt = 0;

        if(_match_ok){
            /* より具体的なマッチなら候補を更新する（同点は先出現優先）。 */
            if(!best.valid ||
               score_less(st->match_score_expr, st->match_score_sym,
                          st->match_score_lit,
                          best.score_expr, best.score_sym, best.score_lit)){
                best_capture(st, &best, i, pln, saved_refs_len);
            }
            /* 副作用を巻き戻して走査を継続する
             * （より具体的なパターンが後方にあるかもしれない）。 */
            memcpy(st->vars, saved_vars, sizeof(saved_vars));
            for(int ri2=saved_refs_len; ri2<st->elf_refs_len; ri2++)
                free(st->elf_refs[ri2].name);
            st->elf_refs_len = saved_refs_len;
            for(int vi=0;vi<26;vi++){
                free(st->elf_var_to_label[vi].label_name);
                st->elf_var_to_label[vi].set        = saved_vtl[vi].set;
                st->elf_var_to_label[vi].label_val  = saved_vtl[vi].label_val;
                st->elf_var_to_label[vi].label_name = saved_vtl[vi].label_name;
                saved_vtl[vi].label_name = NULL;   /* 所有権移動 */
            }
            st->error_undefined_label=0;

            /* 最適化: リテラルのみのマッチ (式・シンボルキャプチャ 0) は
             * これ以上具体的なパターンが存在し得ないため走査を打ち切る。
             * （同一行にマッチするリテラルのみのパターン同士は
             *   リテラル一致文字数も必ず等しいので、先出現優先も保たれる。）*/
            if(best.score_expr==0 && best.score_sym==0) break;
        } else {
            /* pat_match0 は失敗時に内部で状態を復元済み。
             * 保存用に複製した label_name を解放する。 */
            for(int vi=0;vi<26;vi++) free(saved_vtl[vi].label_name);
            st->error_undefined_label=0;
        }
    }

    /* ---- 採用パターンでのオブジェクト生成ステージ ---- */
    if(best.valid){
        PatEntry *i = best.pat;
        pln = best.pln;
        loopflag = 0;

        /* マッチ成功時点のディレクティブ状態・キャプチャ変数・
         * ELF追跡状態を復元する。 */
        best_restore_dirstate(st, &best);
        memcpy(st->vars, best.vars, sizeof(st->vars));
        for(int ri2=0; ri2<best.refs_len; ri2++)
            elf_refs_push_copy(st, best.refs[ri2].name,
                               best.refs[ri2].val, best.refs[ri2].word_idx);
        for(int vi=0;vi<26;vi++){
            free(st->elf_var_to_label[vi].label_name);
            st->elf_var_to_label[vi].set        = best.vtl[vi].set;
            st->elf_var_to_label[vi].label_val  = best.vtl[vi].label_val;
            st->elf_var_to_label[vi].label_name = best.vtl[vi].label_name
                                                  ? strdup(best.vtl[vi].label_name)
                                                  : NULL;
        }
        /* Bugfix (axx.py port): restore (not hard-reset) so a !x-captured
         * pattern variable's undefined-label status from the winning
         * trial match (saved on `best` above) survives into the probe/
         * real makeobj() calls below instead of being discarded here. */
        st->error_undefined_label = best.error_undefined_label;
        st->expmode = EXP_ASM;

        /* $$/$. のために命令先頭・末尾アドレスを事前確定する。
         * error条件式 i->f[1] でも $. を参照できるよう dir_error() より前に実施。 */
        st->pc_instr_start = st->pc;
        st->pc_instr_end   = st->pc_instr_start;  /* プローブ中の暫定値 */
        {
            int _probe_sm_saved  = st->pass1_size_mode;
            int _probe_refs_len  = st->elf_refs_len;
            int _probe_widx_saved = st->elf_current_word_idx;
            st->pass1_size_mode = 1;
            IntVec _probe_objl; iv_init(&_probe_objl);
            /* プローブ中はerror_undefined_labelが汚染しないよう保護 */
            int _probe_err_undef_saved = st->error_undefined_label;
            st->error_undefined_label = 0;
            makeobj(asmb, i->f[2], &_probe_objl);
            /* pc_instr_end = 命令先頭 + 命令バイト数 */
            uint256_t _probe_sz = u256_from_i64((int64_t)_probe_objl.len);
            st->pc_instr_end = u256_add(st->pc_instr_start, _probe_sz);
            iv_free(&_probe_objl);
            /* ELFトラッキング状態をプローブ前に巻き戻す */
            for(int ri2=_probe_refs_len; ri2<st->elf_refs_len; ri2++)
                free(st->elf_refs[ri2].name);
            st->elf_refs_len        = _probe_refs_len;
            st->elf_current_word_idx = _probe_widx_saved;
            st->pass1_size_mode     = _probe_sm_saved;
            st->error_undefined_label = _probe_err_undef_saved;
        }
        /* Fix 10 (axx.py): only call makeobj when dir_error did NOT trigger.
         * Previously makeobj always ran even if an .error condition fired. */
        int err_triggered = dir_error(asmb,i->f[1]);
        if(!err_triggered){
            /* pc_instr_start は上のプローブブロックで設定済み */
            makeobj(asmb,i->f[2],objl_out);
            /* Pass1ではmakeobj内でpass1_size_modeを使うため、
             * ここでのretryは不要。error_undefined_labelはmakeobj内でクリア済み。
             * Pass2: if makeobj produced undefined label, that's a hard error */
            if(st->pas==2 && st->error_undefined_label){
                oerr=1;
                oerr_entry=i;
            }
        } else {
            iv_clear(objl_out);
        }
        if(!oerr){
            int io;
            uint256_t idxv=expr_expression_pat(asmb,i->f[3],0,&io);
            idxs_val=(int)u256_to_i64(idxv);
        }
    } else if(hit_sentinel){
        /* 番兵に到達し、かつ何もマッチしなかった。
         * 従来通り構文エラーとはせず、番兵で評価した idxs を返す。 */
        loopflag=0;
    }
    best_free(&best);

    if(loopflag){ se=1; pln=0; }

    if(should_report_errors(st)){
        /* Bugfix (axx.py port): each of these three conditions must abort
         * this line (return 0) the same way `oerr` below already does.
         * Previously only `oerr` returned early; the undefined-label and
         * syntax-error branches printed their message but then fell through
         * to the success path at the bottom of this function, so the caller
         * (lineassemble()) treated the line as successfully assembled --
         * e.g. a genuinely undefined label reference (reachable in
         * interactive/pas==0 mode, where the pas==2-gated oerr conversion
         * below never triggers) printed "Undefined label" yet still
         * returned 1 with whatever bytes makeobj() happened to produce. */
        if(st->error_undefined_label){
            fprintf(stderr, " error - Undefined label in expression.  [%s:%d]\n",
                st->current_file, (int)st->ln);
            st->had_error=1;
            *idx_out=idx; return 0;
        }
        if(se){
            fprintf(stderr, " error - Syntax error.  [%s:%d]\n",
                st->current_file, (int)st->ln);
            st->had_error=1;
            *idx_out=idx; return 0;
        }
        if(oerr){
            /* Mirrors Python:
             *   print(f" ; pat {pln} {pl} error - Illegal syntax in assemble line or pattern line.")
             * pl is the PatEntry (list of 6 strings). */
            fprintf(stderr, " ; pat %d ['%s', '%s', '%s', '%s', '%s', '%s'] error - Illegal syntax in assemble line or pattern line.\n",
                   pln,
                   oerr_entry ? oerr_entry->f[0] : "",
                   oerr_entry ? oerr_entry->f[1] : "",
                   oerr_entry ? oerr_entry->f[2] : "",
                   oerr_entry ? oerr_entry->f[3] : "",
                   oerr_entry ? oerr_entry->f[4] : "",
                   oerr_entry ? oerr_entry->f[5] : "");
            st->had_error=1;
            *idx_out=idx; return 0;
        }
    }

    iv_clear(idxs_out);
    iv_push(idxs_out, u256_from_i64(idxs_val));
    *idx_out=idx;
    return 1;
}

/* =========================================================
 * ELF relocation reference type and comparator.
 *
 * Fix (new): the original code defined both the typedef and the comparator
 * as a GCC nested function inside lineassemble().  This is:
 *   (a) non-standard C (GCC extension only – Clang/MSVC reject it), and
 *   (b) using subtraction for comparison, which overflows when one word_idx
 *       is large-positive and the other is large-negative (same class of
 *       bug as the int_cmp() fix K).
 *
 * Fix: promote the typedef to file scope and provide a proper static
 * comparator using the branchless 3-way pattern already used by int_cmp().
 * ========================================================= */
typedef struct { const char *name; uint64_t val; int word_idx; } ElfRef;

static int elf_ref_cmp(const void *a, const void *b){
    int ia = ((const ElfRef *)a)->word_idx;
    int ib = ((const ElfRef *)b)->word_idx;
    return (ia > ib) - (ia < ib);   /* branchless 3-way; no overflow */
}

static int lineassemble(Assembler *asmb, const char *line_in){
    AsmState *st=&asmb->st;

    /* Fix P7c: replace fixed char line[4096] with a heap-allocated copy so
     * that source lines longer than 4095 bytes are not silently truncated.  */
    size_t lin_len = strlen(line_in);
    char *line = malloc(lin_len + 2);
    if(!line){ perror("malloc"); return 0; }
    memcpy(line, line_in, lin_len + 1);

    for(char*p=line;*p;p++){ if(*p=='\t') *p=' '; if(*p=='\n'||*p=='\r') *p=' '; }
    axx_reduce_spaces(line);
    axx_remove_comment_asm(line);
    if(!line[0]){ free(line); return 0; }

    /* アセンブリ行を1行処理するたびに .check 拘束条件を全解除する。
     * パターンファイルの .check ディレクティブはパターン走査ループ
     * (lineassemble2 内のパターン探索) の中で再登録される。行ごとに
     * ここでクリアしておくことで、パターン走査が当該行のために再登録した
     * .check 拘束のみが有効になり、前行の走査で蓄積された残留拘束が
     * 次行へ持ち越されない。 */
    for(int _ci = 0; _ci < 26; _ci++){
        sv_free(&asmb->st.check_constraints[_ci]);
        sv_init(&asmb->st.check_constraints[_ci]);
    }

    smap_clear(&asmb->st.symbols);
    for(int pi=0; pi<asmb->st.patsymbols.nb; pi++)
        for(SymEntry *se=asmb->st.patsymbols.buckets[pi]; se; se=se->next)
            smap_set(&asmb->st.symbols, se->key, se->val);

    /* Fix P7d: replace fixed char processed[4096] with a heap buffer.
     * adir_label_processing output is at most strlen(line)+1 bytes.          */
    char *processed = malloc(lin_len + 2);
    if(!processed){ perror("malloc"); free(line); return 0; }
    adir_label_processing(asmb, line, processed, lin_len + 2);
    free(line);

    /* Fix P10: warn when PC exceeds the uint64_t range used by BufMap.       */
    if(st->pc.w[1]||st->pc.w[2]||st->pc.w[3]){
        static int pc_warned = 0;
        if(!pc_warned){
            fprintf(stderr,"warning: program counter exceeds 64-bit range "
                           "(0x%llx…); binary output positions truncated to 64 bits.\n",
                           (unsigned long long)st->pc.w[1]);
            pc_warned = 1;
        }
    }

    /* Fix: vcnt !! counting must ignore !! inside double-quoted strings and
     * single-quote char literals. Mirrors axx.py lineassemble() Bugfix L/L2/L3. */
    {
        int _vcnt = 0;
        const char *_pp = processed;
        int _in_dq = 0;
        int _has_content = 0;
        while(*_pp){
            char _c = *_pp;
            /* backslash escape inside double-quoted string */
            if(_c == '\\' && _in_dq){
                _pp++;
                if(*_pp) _pp++;
                _has_content = 1;
                continue;
            }
            if(_c == '"'){
                _in_dq = !_in_dq;
                _pp++; _has_content = 1;
                continue;
            }
            /* single-quote char literal: consume without counting */
            if(_c == '\'' && !_in_dq){
                /* look-ahead: '\x' (4-chars) or 'x' (3-chars) */
                if(_pp[1] == '\\' && _pp[2] && _pp[3] == '\''){
                    _pp += 4; _has_content = 1; continue;
                } else if(_pp[1] && _pp[2] == '\''){
                    _pp += 3; _has_content = 1; continue;
                }
                _pp++; _has_content = 1;
                continue;
            }
            if(!_in_dq && _pp[0] == '!' && _pp[1] == '!'){
                if(_has_content){ _vcnt++; _has_content = 0; }
                _pp += 2;
                continue;
            }
            if(_c != ' ') _has_content = 1;
            _pp++;
        }
        if(_has_content) _vcnt++;
        st->vcnt = _vcnt ? _vcnt : 1;
    }

    if(st->elf_objfile[0] && st->pas==2){
        st->elf_tracking=1;
        for(int ri=0;ri<st->elf_refs_len;ri++) free(st->elf_refs[ri].name);
        st->elf_refs_len=0;
        st->elf_current_word_idx = -1;
        for(int _vi=0;_vi<26;_vi++){
            st->elf_var_to_label[_vi].set = 0;
            free(st->elf_var_to_label[_vi].label_name);
            st->elf_var_to_label[_vi].label_name = NULL;
            st->elf_var_to_label[_vi].label_val = 0;
        }
        st->elf_capturing_var = '\0';
    }

    IntVec idxs; iv_init(&idxs);
    IntVec objl; iv_init(&objl);
    int new_idx;
    int flag=lineassemble2(asmb,processed,0,&idxs,&objl,&new_idx);

    st->elf_tracking=0;

    if(!flag){ free(processed); iv_free(&idxs); iv_free(&objl); return 0; }

    const char *rest=processed+new_idx;
    while(*rest==' ') rest++;
    int is_vliw_cont=(st->vliwflag && rest[0]=='!'&&rest[1]=='!');

    if(!is_vliw_cont){
        /* ELF relocation detection (tracking method)
         * Use word_idx recorded during makeobj()/expr_factor1() to locate each
         * label reference precisely.  No binary scanning – no false positives.
         *
         * Architecture-specific default relocation type table (machine → nbytes → rtype):
         *   EM_X86_64(62) : 8→R_X86_64_64(1)   4→R_X86_64_PC32(2)   2→R_X86_64_16(12)  1→R_X86_64_8(14)
         *   EM_386(3)     : 4→R_386_PC32(2)     2→R_386_16(20)       1→R_386_8(22)
         *   EM_ARM(40)    : 4→R_ARM_REL32(3)    2→R_ARM_ABS16(4)     1→R_ARM_ABS8(8)
         *   EM_AARCH64(183): 8→R_AARCH64_ABS64(257) 4→R_AARCH64_PREL32(261) 2→R_AARCH64_PREL16(262)
         *   EM_RISCV(243) : 8→R_RISCV_64(2)    4→R_RISCV_32(1)      2→R_RISCV_ADD16(34) 1→R_RISCV_ADD8(33)
         *   EM_PPC(20)    : 4→R_PPC_REL32(26)  2→R_PPC_ADDR16(4)
         *   fallback      : 8→1  4→2  2→3  1→4
         *
         * 4-byte default is PC-relative for x86-64/i386/ARM/AArch64/PPC because
         * CALL/JMP/BL are the dominant 4-byte symbol references in code sections.
         * Use .EXTERN label::abs32 (or abs32s/abs64 etc.) to force absolute. */
        if(st->elf_objfile[0] && st->pas==2 && objl.len>0 && st->elf_refs_len>0){
            int bpw = (st->bts+7)/8; if(bpw<1) bpw=1;
            const char *sec_name = st->current_section;
            SecEntry *_rse = secmap_find(&st->sections, sec_name);
            /* 破綻点修正 (axx.py port): 以前は sec_start をこのセクションの
             * 「最初の訪問の開始pc」とし、sec_rel = pc - sec_start として
             * いた。これはセクションに複数回出入りする(.text→.data→.text等)
             * と、2回目以降の訪問のオフセットが正しく計算できない(間に
             * 挟まった他セクションのぶんだけずれる)。現在オープン中の訪問
             * より前に完了した訪問の累積ワード数(_rse->size、離脱時に
             * 加算済み)に、今回の訪問内でのオフセット(pc - entry_pc)を
             * 足すことで、断片を跨いだ正しいセクション内相対位置を計算する。 */
            uint64_t sec_completed_words = _rse ? u256_to_u64(_rse->size) : 0;
            uint64_t sec_entry_pc_cur    = _rse ? u256_to_u64(_rse->entry_pc) : 0;
            uint64_t cur_pc    = u256_to_u64(st->pc);

        /* Per-machine rtype lookup: ELF_MACHINES' width_guess (axx.py port,
         * see ELF_MACHINES' definition above -- single source of truth,
         * replacing what used to be a table hand-duplicated at this call
         * site). 4-byte is PC-relative (CALL/JMP主流) for most
         * architectures; absolute variants: use .EXTERN label::abs32 /
         * ::abs64 etc. to force. */
            const ElfMachineInfo *_mtbl_rm = elf_machine_find(st->elf_machine);
            #define RTYPE_FOR(nb) reloctype_for(st, _mtbl_rm, (nb))

            /* collect refs with valid word_idx (>= 0), sort by word_idx */
            ElfRef *_valid = (ElfRef*)malloc((size_t)st->elf_refs_len * sizeof(ElfRef));
            if(!_valid){perror("malloc");exit(1);}
            int _nvalid = 0;
            for(int _ri=0; _ri<st->elf_refs_len; _ri++){
                if(st->elf_refs[_ri].word_idx >= 0)
                    _valid[_nvalid++] = (ElfRef){st->elf_refs[_ri].name,
                                              st->elf_refs[_ri].val,
                                              st->elf_refs[_ri].word_idx};
            }
            /* sort by word_idx – use file-scope elf_ref_cmp (branchless, standard C) */
            qsort(_valid, (size_t)_nvalid, sizeof(ElfRef), elf_ref_cmp);

            /* Bugfix (axx.py port): the same label can be captured into the
             * same output word twice (e.g. two pattern variables both bound
             * to the same source operand, as in a hypothetical "DIFF L,L").
             * Left unchecked, both identical (name, word_idx) entries survive
             * here and the grouping loop below -- which only extends a group
             * when the NEXT entry's word_idx is exactly one past the
             * previous -- ends up forming two separate single-word groups
             * both anchored at the same word_idx, emitting a duplicate/
             * non-conformant .rela entry at the same offset. De-duplicate
             * exact (name, word_idx) repeats first, keeping only the first
             * occurrence (array is already sorted by word_idx, so repeats
             * for the same label are adjacent). */
            {
                int _w2 = 0;
                for(int _r2 = 0; _r2 < _nvalid; _r2++){
                    if(_w2 > 0
                       && _valid[_r2].word_idx == _valid[_w2-1].word_idx
                       && strcmp(_valid[_r2].name, _valid[_w2-1].name) == 0)
                        continue;
                    if(_w2 != _r2) _valid[_w2] = _valid[_r2];
                    _w2++;
                }
                _nvalid = _w2;
            }

            /* group consecutive same-label refs into one relocation entry */
            int _gi = 0;
            while(_gi < _nvalid){
                const char *_lname = _valid[_gi].name;
                int _widx = _valid[_gi].word_idx;
                int _gj = _gi + 1;
                while(_gj < _nvalid
                      && strcmp(_valid[_gj].name, _lname) == 0
                      && _valid[_gj].word_idx == _widx + (_gj - _gi))
                    _gj++;
                int _nwords = _gj - _gi;
                int _nbytes = _nwords * bpw;
                /* axx.py: check .EXTERN reloc_type_override first, then fall back to default */
                int _rtype = 0;
                int _rtype_is_default_guess = 0;
                {
                    LabelEntry *_le = lmap_find(&st->labels, _lname);
                    if(_le && _le->reloc_type_override >= 0){
                        int _rt_ov = _le->reloc_type_override;
                        /* reloc_type が要求するフィールド幅と実際のフィールド幅が
                         * 一致しなければ override を無視する。例: abs64(8バイト) を
                         * 4バイトの CALL フィールドに適用すると隣接バイトを破壊して
                         * セグフォルトを引き起こす。
                         * Bugfix (axx.py port): 以前は is_imported (.EXTERN で
                         * 宣言されたラベルは常にtrue) の場合このチェックを
                         * 無条件にスキップしていた。`.EXTERN foo`(型指定なし)は
                         * 常にマシンのデフォルトreloc型(例: x86_64なら4バイト幅の
                         * PC32)を記録するため、1バイト幅の短縮ジャンプ(Jcc rel8)
                         * のような狭いフィールドで参照されると、実際のフィールド幅
                         * と食い違ったまま常に適用されてしまい、リンク時に後続の
                         * 命令バイトまで巻き込んで破壊するrelocationが生成されて
                         * いた。is_imported かどうかに関わらず幅チェックを適用する
                         * (axx.pyのlineassemble()と同じ修正)。 */
                        int _expected = elf_machine_reloc_bytes(_mtbl_rm, _rt_ov);
                        if(_expected == 0 || _expected == _nbytes)
                            _rtype = _rt_ov;
                        else {
                            _rtype = RTYPE_FOR(_nbytes);  /* フィールド幅不一致 → デフォルト */
                            _rtype_is_default_guess = 1;
                        }
                    } else {
                        _rtype = RTYPE_FOR(_nbytes);
                        _rtype_is_default_guess = 1;
                    }
                }
                if(_rtype != 0 && _widx < objl.len){
                    int64_t _sec_rel = (int64_t)((sec_completed_words +
                                                   (cur_pc + (uint64_t)_widx - sec_entry_pc_cur))
                                                  * (uint64_t)bpw);
                    /* RELA addend computation:
                     *   addend = (value stored in objl word(s)) − (label absolute address)
                     *
                     * The old code fixed addend=0.  For a reference like "label+8" the
                     * assembled word holds label_value+8, but with addend=0 the linker
                     * writes S+0 (symbol address only) and loses the +8 offset.
                     *
                     * Fix: reconstruct the scalar stored in the word group using the
                     * assembler's current endianness and bts setting, then subtract the
                     * label's absolute value.  The result is the constant addend that
                     * must be preserved across relocation. */
                    int _bts = st->bts;
                    uint64_t _wmask = (_bts < 64)
                        ? (((uint64_t)1 << _bts) - 1)
                        : (uint64_t)-1;
                    uint64_t _raw_val = 0;
                    if(!st->endian_big){
                        /* little-endian: word[0] is least-significant */
                        for(int _k = 0; _k < _nwords; _k++){
                            int _wk = _widx + _k;
                            if(_wk < objl.len){
                                uint64_t _wv = u256_to_u64(objl.data[_wk]) & _wmask;
                                _raw_val |= _wv << (_bts * _k);
                            }
                        }
                    } else {
                        /* big-endian: word[0] is most-significant */
                        for(int _k = 0; _k < _nwords; _k++){
                            int _wk = _widx + _k;
                            if(_wk < objl.len){
                                uint64_t _wv = u256_to_u64(objl.data[_wk]) & _wmask;
                                _raw_val = (_raw_val << _bts) | _wv;
                            }
                        }
                    }
                    /* 破綻点修正 (axx.py port): _raw_valはフィールド幅の生の
                     * ビットパターンをuint64_tにそのまま集めただけで、一度も
                     * 符号拡張されていなかった。axx.py側は
                     * "if raw_val >= (1<<(field_bits-1)): raw_val -= (1<<field_bits)"
                     * でフィールド幅基準の符号付き値に変換してから
                     * addend計算(raw_val - abs_w_bytes)に使っているが、
                     * caxx.cはこの変換が無いままint64_tにキャストしていたため、
                     * 埋め込み済みフィールド値の最上位ビットが立っている場合
                     * (例: 1バイト幅で0xfc=符号付き-4)、符号なしの
                     * 大きな正数(252)としてそのままaddend計算に使われ、
                     * PC相対でない(絶対)リロケーションのaddendが誤って
                     * 計算されていた。uint64_t上で2の補数表現になるよう
                     * 減算しておけば、後続のint64_tへのキャストで正しく
                     * 符号付き値として解釈される。 */
                    {
                        /* Bugfix (axx.py port): this must be the TRUE encoded
                         * bit width (_nwords * _bts), not the byte-rounded
                         * _nbytes*8. _raw_val was built above using _wmask =
                         * (1<<_bts)-1, so for a word size that isn't a
                         * multiple of 8 (e.g. .bits::11), _nbytes*8 is larger
                         * than the actual field (16 vs. 11 bits); _raw_val
                         * (which never exceeds 2**_bts-1) could then never
                         * reach the byte-rounded halfway point, so negative
                         * values were never sign-extended -- corrupting the
                         * addend by exactly 2**_bts for every negative
                         * pc-relative/relocated value on such targets.
                         * Mirrors the identical fix applied to axx.py
                         * lineassemble(): _field_bits = num_words*state.bts. */
                        int _field_bits = _nwords * _bts;
                        if(_field_bits > 0 && _field_bits < 64
                           && _raw_val >= ((uint64_t)1 << (_field_bits - 1))){
                            _raw_val -= ((uint64_t)1 << _field_bits);
                        }
                    }
                    /* Bugfix (axx.py port): abs_w must be converted to BYTE
                     * units (abs_w * bpw) before comparing/subtracting
                     * against _raw_val (which is already a byte-field
                     * value once bts spans more than one byte's worth of
                     * addressing). `_valid[_gi].val` is the label's raw
                     * stored value in WORDS (mirrors axx.py's `abs_w`), so
                     * for any target where bpw != 1 (bts > 8), comparing/
                     * subtracting it directly against _raw_val without this
                     * scaling silently produced wrong results. This was
                     * masked in all prior byte-addressable (bts==8, bpw==1)
                     * test cases, where scaling by 1 is a no-op. */
                    int64_t _abs_w_bytes = (int64_t)_valid[_gi].val * (int64_t)bpw;

                    /* 破綻点修正 (axx.py port): _rtype がreloc_type明示指定なしに
                     * バイト幅だけから推測された場合(_rtype_is_default_guess)、
                     * その推測がたまたまPC相対型に landing しても、実際に
                     * エンコードされた値(_raw_val)がラベルの絶対アドレス
                     * そのもの(_abs_w_bytes)と厳密に一致するなら、それは
                     * 減算を伴わない絶対参照(例: "DD label")であることの
                     * 明確な証拠になる。真にPC相対な参照(call/jmp rel32等)
                     * ではraw_valが絶対アドレスとぴったり一致することは
                     * 実質あり得ないため、この場合だけ絶対型に読み替える
                     * (x86_64のデフォルト表でのみ確認済み: 4バイト幅は
                     * R_X86_64_PC32(2)ではなくR_X86_64_32(10)にすべき)。 */
                    /* axx.py port: kept x86_64-only after ELF_MACHINES
                     * consolidation (was already excluded for 3/40/183/20/
                     * 243 before; now explicit rather than an exclusion
                     * list, so newly-added architectures don't silently
                     * inherit a heuristic never validated for them --
                     * mirrors axx.py's `self.state.elf_machine == 62` guard). */
                    if(_rtype_is_default_guess && _rtype == 2 && _nbytes == 4
                       && st->elf_machine == 62
                       && (int64_t)_raw_val == _abs_w_bytes){
                        _rtype = 10; /* R_X86_64_32: absolute 32-bit */
                    }

                    /* addend の計算 (axx.py port bugfix):
                     * 旧コードはPC相対の場合を「フィールド = ターゲット -
                     * (命令アドレス+フィールドサイズ)」という特定の規約
                     * (x86のCALL/JMP rel32のような、命令末尾基準の相対
                     * アドレシング)に固定的に決め打ちし、addend=-num_bytes
                     * という定数式を使っていた。axxは任意のISA(Z80のJR等、
                     * 命令先頭基準で相対値を計算するパターンも含む)を
                     * パターンファイルだけでターゲットにできる汎用アセンブラ
                     * であり、この決め打ちはパターンが実際に採用している
                     * $$規約と食い違う場合(例: "JMP !d :: (d-$$)"のように
                     * 命令先頭基準の場合)、addendを誤って計算していた
                     * (x86のCALL rel32のような命令末尾基準の規約とたまたま
                     * 一致するケースでしか正しい値にならなかった)。
                     *
                     * axx.pyのlineassemble()と同じ、raw_val・ラベルの絶対値・
                     * 命令自身のアドレス(P)から汎用的に再構成する式に統一する:
                     *   PC相対: addend = raw_val - abs_w_bytes + P
                     *   絶対  : addend = raw_val - abs_w_bytes
                     * Pは「このリロケーション参照が実際に埋め込まれている
                     * ワードのセクション相対バイトアドレス」であり、これは
                     * 数バイト下で r_offset として使っている _sec_rel と
                     * 全く同じ値(同じ pc+_widx から計算される)なので、
                     * そのまま再利用する。 */
                    int64_t _addend;
                    {
                    /* PC相対リロケーション型はアーキテクチャ別に定義する。
                     * 全アーキテクチャ共通リストにすると番号衝突が発生する。
                     * 例: PPC R_PPC_REL24=10 と x86-64 R_X86_64_32=10(絶対) が衝突 →
                     *     x86-64 で abs32 が誤って PC相対と判定され addend=-4 になるバグ。
                     * Mirrors axx.py: _pc_rel_types_all はマシン別に分岐して定義。 */
                    /* Machine-specific PC-relative relocation-type set, from
                     * ELF_MACHINES (axx.py port: single source of truth). */
                    int _is_pcrel = elf_machine_is_pcrel(_mtbl_rm, _rtype);
                        if(_is_pcrel)
                            _addend = (int64_t)_raw_val - _abs_w_bytes + _sec_rel;
                        else
                            _addend = (int64_t)_raw_val - _abs_w_bytes;
                    }
                    if(st->reloc_count >= st->reloc_cap){
                        st->reloc_cap = st->reloc_cap ? st->reloc_cap*2 : 16;
                        st->relocations = realloc(st->relocations,
                            (size_t)st->reloc_cap * sizeof(st->relocations[0]));
                        if(!st->relocations){ perror("realloc"); exit(1); }
                    }
                    st->relocations[st->reloc_count].section   = strdup(sec_name);
                    st->relocations[st->reloc_count].sec_offset = _sec_rel;
                    st->relocations[st->reloc_count].sym        = strdup(_lname);
                    st->relocations[st->reloc_count].rtype      = _rtype;
                    st->relocations[st->reloc_count].addend     = _addend;
                    st->relocations[st->reloc_count].nbytes     = _nbytes;
                    st->reloc_count++;
                }
                _gi = _gj;
            }
            free(_valid);
            #undef RTYPE_FOR
        }

        /* DWARF .debug_line: record (section, word_pc, file, line) for every
         * byte-producing line during pass2. The VLIW branch below is excluded
         * (instruction/byte boundaries are not 1:1 there). st->ln is the line
         * currently being assembled (lineassemble0 increments it afterwards). */
        if(st->gen_debug && st->pas==2 && objl.len>0){
            if(st->line_map_len >= st->line_map_cap){
                st->line_map_cap = st->line_map_cap ? st->line_map_cap*2 : 64;
                st->line_map = realloc(st->line_map,
                    (size_t)st->line_map_cap * sizeof(st->line_map[0]));
                if(!st->line_map){ perror("realloc"); exit(1); }
            }
            st->line_map[st->line_map_len].section = strdup(st->current_section);
            st->line_map[st->line_map_len].word_pc = u256_to_u64(st->pc);
            st->line_map[st->line_map_len].file    = strdup(st->current_file);
            st->line_map[st->line_map_len].line    = (int)st->ln;
            st->line_map_len++;
        }

        for(int ci=0;ci<objl.len;ci++){
            outbin(st,st->pc,objl.data[ci]);
            st->pc=u256_add(st->pc,u256_one());
        }
    } else {
        int vi;
        int vok=vliwprocess(asmb,processed,&idxs,&objl,new_idx,&vi);
        free(processed);
        iv_free(&idxs); iv_free(&objl);
        return vok;
    }

    free(processed);
    iv_free(&idxs); iv_free(&objl);
    return 1;
}

static int lineassemble0(Assembler *asmb, const char *line){
    AsmState *st=&asmb->st;
    strncpy(st->cl,line,sizeof(st->cl)-1);
    int l=(int)strlen(st->cl);
    while(l>0&&(st->cl[l-1]=='\n'||st->cl[l-1]=='\r')) st->cl[--l]=0;

    /* -v (verbose) フラグが立っているときだけリスト出力する（axx.py の verbose）。
     * 対話モード (pas==0) は常に出力する。                         */
    int show = (st->pas==0) || ((st->pas==2) && st->verbose);
    if(show){
        printf("%016llx %s %d %s ",(unsigned long long)u256_to_u64(st->pc),
               st->current_file, st->ln, st->cl);
    }
    int f=lineassemble(asmb,st->cl);
    if(show) printf("\n");
    st->ln++;
    return f;
}

static char *file_input_from_stdin(void){
    size_t total=0, cap=4096;
    char *buf=malloc(cap);
    if(!buf){ perror("malloc"); exit(1); }
    char line[4096];
    while(fgets(line,sizeof(line),stdin)){
        size_t l=strlen(line);
        for(size_t i=0;i<l;i++) if(line[i]=='\r'){ memmove(line+i,line+i+1,l-i); l--; }
        while(total+l+1>cap){
            cap*=2;
            /* Fix #8: save old pointer so it can be freed if realloc fails */
            char *tmp=realloc(buf,cap);
            if(!tmp){ free(buf); perror("realloc"); exit(1); }
            buf=tmp;
        }
        memcpy(buf+total,line,l);
        total+=l;
    }
    buf[total]=0;
    return buf;
}


/* =========================================================
 * write_elf_obj: write FreeBSD ELF64 relocatable object file
 * Mirrors axx.py Assembler.write_elf_obj() exactly.
 *
 * File layout:
 *   ELF header (64 bytes)
 *   Content sections (16-byte aligned each)
 *   .rela.X sections (8-byte aligned, 24 bytes/entry)
 *   .symtab          (8-byte aligned, 24 bytes/entry)
 *   .strtab
 *   .shstrtab
 *   Section header table (8-byte aligned, 64 bytes/entry)
 * ========================================================= */

/* =====================================================================
 * ELF/DWARF writer helpers (file scope).
 *
 * These were previously GCC *nested functions* defined inside
 * write_elf_obj().  Nested functions are a GNU C extension and are NOT
 * supported by clang (the default `cc` on FreeBSD/macOS), so they are
 * lifted to file scope here, with the formerly-captured local variables
 * passed as explicit parameters.  This lets the file build with a plain
 * standard C compiler (cc/clang) as well as gcc.
 * ===================================================================== */

/* dynamic byte buffer (string tables start with a leading NUL byte) */
typedef struct { uint8_t*b; size_t len,cap; } WBB;
/* one content (output) section */
typedef struct { const char*name; uint64_t bs,bsz,fl; uint8_t*data; } WCS;
/* (section index, value-within-section) result of weo_shndx() */
typedef struct { uint16_t shndx; uint64_t sv; } WSR;
/* relocation entry / per-section list */
typedef struct { int64_t off; const char*sym; int rtype; int64_t addend; int nbytes; } WRE;
typedef struct { WRE*data; int len,cap; } WRL;
/* symbol-name -> symtab-index map entry */
typedef struct { const char*name; int idx; } WSNI;
/* label record used for sorting */
typedef struct { const char*name; uint64_t val; int is_equ; int is_imported; int reloc_type_override; const char*section; } WLK;
/* DWARF section descriptors */
typedef struct { const char *name; uint8_t *data; size_t len; } DSEC;
typedef struct { const char *name; int target; uint8_t *data; size_t len; } DREL;
/* DWARF raw byte buffer, relocation accumulator, and line-row */
typedef struct { uint8_t*b; size_t len,cap; } RB;
typedef struct { uint64_t off; int sym; int rtype; int64_t addend; } DRE;
typedef struct { DRE*d; int len,cap; } DRV;
typedef struct { uint64_t wpc; int file; int line; } LROW;

/* endian-aware integer writers (is_le: 1=little, 0=big) */
static void weo_w2(uint8_t*p,uint16_t v,int is_le){
    if(is_le){ p[0]=v&0xff; p[1]=(v>>8)&0xff; }
    else     { p[1]=v&0xff; p[0]=(v>>8)&0xff; }
}
static void weo_w4(uint8_t*p,uint32_t v,int is_le){
    if(is_le){ p[0]=v&0xff;p[1]=(v>>8)&0xff;p[2]=(v>>16)&0xff;p[3]=(v>>24)&0xff; }
    else     { p[3]=v&0xff;p[2]=(v>>8)&0xff;p[1]=(v>>16)&0xff;p[0]=(v>>24)&0xff; }
}
static void weo_w8(uint8_t*p,uint64_t v,int is_le){
    if(is_le){ for(int j=0;j<8;j++){p[j]=(uint8_t)(v&0xff);v>>=8;} }
    else     { for(int j=7;j>=0;j--){p[j]=(uint8_t)(v&0xff);v>>=8;} }
}
static void weo_w8s(uint8_t*p,int64_t v,int is_le){ weo_w8(p,(uint64_t)v,is_le); }

/* WBB dynamic byte buffer helpers */
static void wbb_init(WBB*w){ w->b=calloc(1,64); w->len=1; w->cap=64; }
static void wbb_grow(WBB*w, size_t need){
    while(w->len+need>w->cap){w->cap*=2;w->b=realloc(w->b,w->cap);if(!w->b){perror("realloc");exit(1);}}
}
static uint32_t wbb_str(WBB*w, const char*s){
    size_t l=strlen(s)+1; uint32_t off=(uint32_t)w->len;
    wbb_grow(w,l); memcpy(w->b+w->len,s,l); w->len+=l; return off;
}
static void wbb_app(WBB*w, const void*src, size_t n){
    wbb_grow(w,n); memcpy(w->b+w->len,src,n); w->len+=n;
}

/* extract word range [w0, w0+wn) of the binary image as a byte array */
static uint8_t *weo_extract(AsmState*st,int bpw,uint64_t w0,uint64_t wn){
    uint64_t nb=wn*(uint64_t)bpw;
    if(!nb) return calloc(1,1);
    uint8_t *d=calloc(1,(size_t)nb); if(!d){perror("calloc");exit(1);}
    uint64_t pad=u256_to_u64(st->padding);
    if(pad){
        uint64_t mask=(st->bts<64)?((uint64_t)1<<st->bts)-1:(uint64_t)-1; pad&=mask;
        for(uint64_t wp=0;wp<wn;wp++){
            uint64_t base=wp*(uint64_t)bpw,tmp=pad;
            if(!st->endian_big){for(int j=0;j<bpw;j++){d[base+j]=(uint8_t)(tmp&0xff);tmp>>=8;}}
            else               {for(int j=bpw-1;j>=0;j--){d[base+j]=(uint8_t)(tmp&0xff);tmp>>=8;}}
        }
    }
    for(int bi=0;bi<BUFMAP_NB;bi++)
        for(BufEntry*be=st->buf.buckets[bi];be;be=be->next){
            if(be->pos<w0||be->pos>=w0+wn) continue;
            uint64_t off=(be->pos-w0)*(uint64_t)bpw,tmp=be->val;
            if(!st->endian_big){for(int j=0;j<bpw;j++){if(off+(uint64_t)j<nb)d[off+j]=(uint8_t)(tmp&0xff);tmp>>=8;}}
            else               {for(int j=bpw-1;j>=0;j--){if(off+(uint64_t)j<nb)d[off+j]=(uint8_t)(tmp&0xff);tmp>>=8;}}
        }
    return d;
}

/* 破綻点修正 (axx.py port): セクションが複数回の出入り(.text→.data→.text等)
 * で複数の断片に分かれている場合、単一の(start,size)によるweo_extract()
 * だけでは真の内容を正しく取り出せない(2つ目以降の断片の位置に別
 * セクションのバイトが来てしまう)。st->section_ranges に記録された、この
 * セクションに属する全ての断片を訪問順に連結する。 */
static uint8_t *weo_extract_ranges(AsmState*st, int bpw, const char*name, uint64_t *out_nb){
    uint64_t total_words = 0;
    for(int i=0;i<st->section_ranges.len;i++)
        if(strcmp(st->section_ranges.data[i].name,name)==0)
            total_words += u256_to_u64(st->section_ranges.data[i].len);
    uint64_t nb = total_words*(uint64_t)bpw;
    if(!nb){ *out_nb=0; return calloc(1,1); }
    uint8_t *d = malloc((size_t)nb);
    if(!d){ perror("malloc"); exit(1); }
    uint64_t off=0;
    for(int i=0;i<st->section_ranges.len;i++){
        if(strcmp(st->section_ranges.data[i].name,name)!=0) continue;
        uint64_t rs = u256_to_u64(st->section_ranges.data[i].start);
        uint64_t rl = u256_to_u64(st->section_ranges.data[i].len);
        uint8_t *chunk = weo_extract(st,bpw,rs,rl);
        memcpy(d+off, chunk, (size_t)(rl*(uint64_t)bpw));
        free(chunk);
        off += rl*(uint64_t)bpw;
    }
    *out_nb = nb;
    return d;
}

/* byte-address -> (1-based content section index, in-section offset)
 *
 * axx.py の _find_shndx() (Fix 7) 相当のフォールバックを追加。
 * 旧実装は「start <= addr < start+size」の通常範囲にも
 * 「size==0 かつ addr==start」にも一致しないアドレスを即座に
 * SHN_ABS(0xfff1) としていた。これにより、ファイル末尾（セクション終端＝
 * start+size ちょうど）に置かれたラベル（サイズマーカーなど、よくあるパターン）が
 * axx.py では .text セクション相対シンボルとして出力されるのに対し、
 * caxx.c では誤って絶対シンボル扱いになっていた。
 * 修正: 通常範囲に一致しない場合、addr 以下で最も開始アドレスが近い
 * セクションに帰属させる（best-effort）。セクションが1つも無い場合のみ
 * SHN_ABS を返す。 */
/* 破綻点修正 (axx.py port): ラベルがセクション境界ちょうど(前セクションの
 * 終端 == 次セクションの先頭)にあると、アドレスだけからの逆引きでは
 * 半開区間 [start, start+size) の判定により誤って次のセクションに
 * 帰属してしまう(例: ".text"末尾の終端マーカーラベルが".data"の
 * シンボルとして出力される)。ラベル自身が保持する本来のセクション名
 * (sec_name)が分かっている場合はそれを最優先で使う。名前が一致する
 * セクションが無い場合のみ、従来通りアドレスからの逆引きにフォール
 * バックする。sec_name==NULLのときは従来通りアドレスのみで判定する。 */
static WSR weo_shndx(WCS*csecs,int ncs,uint64_t ba,const char*sec_name,
                      SecRangeVec*ranges,int bpw){
    /* 破綻点修正 (axx.py port): セクションの真の内容は複数回の出入り
     * (.text→.data→.text等)で複数の断片に分かれうるため、単純な
     * ba - csecs[i].bs では断片2つ目以降のアドレスが正しいオフセットに
     * ならない。addr_to_word_offset()で断片を跨いだ累積オフセットを
     * 計算する(戻り値-1は「このセクションに属さない」の意味)。 */
    uint64_t word_pc = bpw ? ba/(uint64_t)bpw : 0;
    if(sec_name){
        for(int i=0;i<ncs;i++){
            if(strcmp(csecs[i].name,sec_name)==0){
                int64_t woff = addr_to_word_offset(ranges, sec_name, word_pc);
                if(woff >= 0) return (WSR){(uint16_t)(i+1), (uint64_t)woff*(uint64_t)bpw};
            }
        }
    }
    for(int i=0;i<ncs;i++){
        int64_t woff = addr_to_word_offset(ranges, csecs[i].name, word_pc);
        if(woff >= 0) return (WSR){(uint16_t)(i+1), (uint64_t)woff*(uint64_t)bpw};
    }
    if(ncs>0){
        int best_i=0; uint64_t best_start=csecs[0].bs;
        for(int i=0;i<ncs;i++){
            if(csecs[i].bs<=ba && csecs[i].bs>=best_start){ best_i=i; best_start=csecs[i].bs; }
        }
        uint64_t sv = ba - csecs[best_i].bs;   /* ba < csecs[best_i].bs のときは 0 側に丸める */
        if(ba < csecs[best_i].bs) sv = 0;
        return (WSR){(uint16_t)(best_i+1), sv};
    }
    return (WSR){0xfff1,ba};   /* SHN_ABS（セクションが一切ない場合のみ） */
}

/* Append one Elf64_Sym (24 bytes) or Elf32_Sym (16 bytes) to the symtab
 * buffer. axx.py port note: Elf32_Sym's field ORDER (not just width)
 * differs from Elf64_Sym -- name/value/size/info/other/shndx instead of
 * name/info/other/shndx/value/size. */
static void weo_sym(WBB*symtab_bb,int*nsyms,int is_le,int is_elf64,
                    uint32_t nm,uint8_t info,uint8_t oth,uint16_t shndx,uint64_t val,uint64_t sz){
    if(is_elf64){
        uint8_t sp[24]={0};
        weo_w4(sp,nm,is_le); sp[4]=info; sp[5]=oth; weo_w2(sp+6,shndx,is_le);
        weo_w8(sp+8,val,is_le); weo_w8(sp+16,sz,is_le);
        wbb_app(symtab_bb,sp,24);
    } else {
        uint8_t sp[16]={0};
        weo_w4(sp,nm,is_le); weo_w4(sp+4,(uint32_t)val,is_le); weo_w4(sp+8,(uint32_t)sz,is_le);
        sp[12]=info; sp[13]=oth; weo_w2(sp+14,shndx,is_le);
        wbb_app(symtab_bb,sp,16);
    }
    (*nsyms)++;
}

/* qsort comparator for WLK label records (by name) */
static int cmp_wlk(const void*a,const void*b){ return strcmp(((const WLK*)a)->name,((const WLK*)b)->name); }

/* is name present in the export array? */
static int weo_isexp(WLK*earr,int ne,const char*nm){
    for(int i=0;i<ne;i++) if(!strcmp(earr[i].name,nm)) return 1;
    return 0;
}

/* symbol name -> symtab index */
static int weo_symof(WSNI*snimap,int snimap_len,const char*nm){
    for(int i=0;i<snimap_len;i++) if(!strcmp(snimap[i].name,nm)) return snimap[i].idx;
    return 0;
}

/* is content section i a .bss (SHT_NOBITS)? */
static int weo_isno(WCS*csecs,int i){
    char _n[64]; int _j=0;
    for(;csecs[i].name[_j]&&_j<63;_j++) _n[_j]=(char)axx_upper_char(csecs[i].name[_j]);
    _n[_j]=0;
    return strncmp(_n,".BSS",4)==0;
}

/* pad file with zero bytes up to absolute offset t */
static void weo_pad(FILE*f,uint64_t t){
    long c=ftell(f);
    if(c < 0){ fprintf(stderr,"weo_pad: ftell failed\n"); return; }
    while((uint64_t)c<t){fputc(0,f);c++;}
}

/* write one Elf64_Shdr (64 bytes) or Elf32_Shdr (40 bytes) */
static void weo_shdr(FILE*f,int is_le,int is_elf64,uint32_t nm,uint32_t ty,uint64_t fl,uint64_t addr,uint64_t off,
                     uint64_t sz,uint32_t lnk,uint32_t info,uint64_t align,uint64_t entsz){
    if(is_elf64){
        uint8_t sh[64]={0};
        weo_w4(sh,nm,is_le);weo_w4(sh+4,ty,is_le);weo_w8(sh+8,fl,is_le);weo_w8(sh+16,addr,is_le);
        weo_w8(sh+24,off,is_le);weo_w8(sh+32,sz,is_le);weo_w4(sh+40,lnk,is_le);weo_w4(sh+44,info,is_le);
        weo_w8(sh+48,align,is_le);weo_w8(sh+56,entsz,is_le);
        fwrite(sh,1,64,f);
    } else {
        uint8_t sh[40]={0};
        weo_w4(sh,nm,is_le);weo_w4(sh+4,ty,is_le);weo_w4(sh+8,(uint32_t)fl,is_le);weo_w4(sh+12,(uint32_t)addr,is_le);
        weo_w4(sh+16,(uint32_t)off,is_le);weo_w4(sh+20,(uint32_t)sz,is_le);weo_w4(sh+24,lnk,is_le);weo_w4(sh+28,info,is_le);
        weo_w4(sh+32,(uint32_t)align,is_le);weo_w4(sh+36,(uint32_t)entsz,is_le);
        fwrite(sh,1,40,f);
    }
}

/* ---- DWARF raw-buffer helpers ---- */
static void rb_init(RB*r){ r->b=malloc(64); r->len=0; r->cap=64; if(!r->b){perror("malloc");exit(1);} }
static void rb_need(RB*r,size_t n){ while(r->len+n>r->cap){ r->cap*=2; r->b=realloc(r->b,r->cap); if(!r->b){perror("realloc");exit(1);} } }
static void rb_u8(RB*r,uint8_t v){ rb_need(r,1); r->b[r->len++]=v; }
static void rb_app(RB*r,const void*s,size_t n){ rb_need(r,n); memcpy(r->b+r->len,s,n); r->len+=n; }
static void rb_cstr(RB*r,const char*s){ rb_app(r,s,strlen(s)+1); }
static void rb_uleb(RB*r,uint64_t v){ for(;;){ uint8_t b=(uint8_t)(v&0x7f); v>>=7; if(v) rb_u8(r,(uint8_t)(b|0x80)); else { rb_u8(r,b); break; } } }
static void rb_sleb(RB*r,int64_t v){ for(;;){ uint8_t b=(uint8_t)(v&0x7f); v>>=7; if((v==0&&!(b&0x40))||(v==-1&&(b&0x40))){ rb_u8(r,b); break; } else rb_u8(r,(uint8_t)(b|0x80)); } }
static void rb_w2(RB*r,uint16_t v,int is_le){ uint8_t t[2]; weo_w2(t,v,is_le); rb_app(r,t,2); }
static void rb_w4(RB*r,uint32_t v,int is_le){ uint8_t t[4]; weo_w4(t,v,is_le); rb_app(r,t,4); }
static void rb_w8(RB*r,uint64_t v,int is_le){ uint8_t t[8]; weo_w8(t,v,is_le); rb_app(r,t,8); }
static void drv_add(DRV*v,uint64_t off,int sym,int rtype,int64_t add){
    if(v->len>=v->cap){ v->cap=v->cap?v->cap*2:8; v->d=realloc(v->d,(size_t)v->cap*sizeof(DRE)); if(!v->d){perror("realloc");exit(1);} }
    v->d[v->len++]=(DRE){off,sym,rtype,add};
}
/* pack a DRV of relocations into Elf64_Rela payload bytes */
static uint8_t* dwarf_pack_relas(DRV*v,size_t*outlen,int is_le){
    size_t n=(size_t)v->len*24; uint8_t*b=calloc(1,n?n:1);
    for(int i=0;i<v->len;i++){
        uint8_t*p=b+(size_t)i*24;
        uint64_t rinfo=((uint64_t)v->d[i].sym<<32)|((uint32_t)v->d[i].rtype);
        weo_w8(p,v->d[i].off,is_le); weo_w8(p+8,rinfo,is_le); weo_w8s(p+16,v->d[i].addend,is_le);
    }
    *outlen=n; return b;
}
/* qsort comparator for DWARF line rows (by address) */
static int lrow_cmp(const void*a,const void*b){ uint64_t x=((const LROW*)a)->wpc,y=((const LROW*)b)->wpc; return x<y?-1:(x>y?1:0); }

static void write_elf_obj(AsmState *st, const char *path, int machine){
    int bpw = (st->bts+7)/8; if(bpw<1) bpw=1;

    /* Endianness: mirrors axx.py write_elf_obj():
     *   _is_le   = (self.state.endian != 'big')
     *   _ei_data = 1 if _is_le else 2   (ELFDATA2LSB / ELFDATA2MSB)
     *   _pk      = '<' if _is_le else '>'
     * The ELF structures (header, shdrs, symtab, rela) must use the same
     * byte order as the target architecture. */
    int _is_le  = !st->endian_big;
    int _ei_data = _is_le ? 1 : 2;   /* EI_DATA: 1=LE, 2=BE */

    /* axx.py port: ELF class (32/64-bit) and RELA-vs-REL convention both
     * come from ELF_MACHINES (single source of truth, see its definition
     * near the top of this file). Falls back to 64-bit/RELA if `machine`
     * somehow isn't in the table -- shouldn't happen since -m is validated
     * against it at CLI parse time, but write_elf_obj() has no other
     * caller-independent way to fail loudly here. */
    const ElfMachineInfo *_mtbl_w = elf_machine_find(machine);
    int _is_elf64 = !_mtbl_w || _mtbl_w->elfclass == 2;
    int _is_rela_w = !_mtbl_w || _mtbl_w->is_rela;

    /* Endian-aware field write helpers */
    #define WEO_W2(p,v) do{ uint16_t _v=(uint16_t)(v); \
        if(_is_le){ (p)[0]=_v&0xff; (p)[1]=(_v>>8)&0xff; } \
        else      { (p)[1]=_v&0xff; (p)[0]=(_v>>8)&0xff; } }while(0)
    #define WEO_W4(p,v) do{ uint32_t _v=(uint32_t)(v); \
        if(_is_le){ (p)[0]=_v&0xff;(p)[1]=(_v>>8)&0xff;(p)[2]=(_v>>16)&0xff;(p)[3]=(_v>>24)&0xff; } \
        else      { (p)[3]=_v&0xff;(p)[2]=(_v>>8)&0xff;(p)[1]=(_v>>16)&0xff;(p)[0]=(_v>>24)&0xff; } }while(0)
    #define WEO_W8(p,v) do{ uint64_t _v=(uint64_t)(v); \
        if(_is_le){ for(int _j=0;_j<8;_j++){(p)[_j]=(uint8_t)(_v&0xff);_v>>=8;} } \
        else      { for(int _j=7;_j>=0;_j--){(p)[_j]=(uint8_t)(_v&0xff);_v>>=8;} } }while(0)
    #define WEO_W8S(p,v) WEO_W8(p,(uint64_t)(int64_t)(v))
    #define WEO_ALIGN(x,a) (((uint64_t)(x)+((uint64_t)(a)-1))&~((uint64_t)(a)-1))
    /* Aliases used in symtab / rela / shdr write code */
    #define WEO_LE2(p,v)  WEO_W2(p,v)
    #define WEO_LE4(p,v)  WEO_W4(p,v)
    #define WEO_LE8(p,v)  WEO_W8(p,v)
    #define WEO_LE8S(p,v) WEO_W8S(p,v)

    /* dynamic byte buffer (starts with one NUL byte) */

    /* extract word range [w0, w0+wn) as byte array */

    /* ---- 1. collect content sections ---- */
    uint64_t max_w=0; int have_w=0;
    for(int i=0;i<BUFMAP_NB;i++)
        for(BufEntry*be=st->buf.buckets[i];be;be=be->next)
            if(!have_w||be->pos>max_w){max_w=be->pos;have_w=1;}

    int ncs=0; WCS *csecs=NULL;
    if(st->sections.count==0){
        ncs=1; csecs=calloc(1,sizeof(WCS));
        uint64_t wn=have_w?max_w+1:0;
        csecs[0]=(WCS){".text",0,wn*(uint64_t)bpw,0x2|0x4,weo_extract(st,bpw,0,wn)};
    } else {
        ncs=st->sections.count; csecs=calloc((size_t)ncs,sizeof(WCS));
        for(int i=0;i<ncs;i++){
            SecEntry *se=st->sections.order[i];
            uint64_t w0=u256_to_u64(se->start);
            /* 破綻点修正 (axx.py port): セクションの真のバイト数・内容は
             * section_ranges に記録された全断片から得る(旧来の「次の
             * セクションの開始位置から借用してサイズを推定する」フォール
             * バックは、複数回出入りする設計では単一連続領域を仮定してしまい
             * 誤りだったため廃止)。 */
            char un[64]; int ui=0;
            for(;se->name[ui]&&ui<63;ui++) un[ui]=(char)axx_upper_char(se->name[ui]);
            un[ui]=0;
            uint64_t fl;
            if     (strncmp(un,".TEXT",5)==0)   fl=0x2|0x4;
            else if(strncmp(un,".DATA",5)==0)   fl=0x2|0x1;
            else if(strncmp(un,".RODATA",7)==0) fl=0x2;
            else if(strncmp(un,".BSS",4)==0)    fl=0x2|0x1;
            else                                fl=0x2;
            uint64_t _nb;
            uint8_t *_data = weo_extract_ranges(st, bpw, se->name, &_nb);
            csecs[i]=(WCS){se->name,w0*(uint64_t)bpw,_nb,fl,_data};
        }
    }

    /* ---- 2. group relocations by content section ---- */
    WRL *rela_lists=calloc((size_t)ncs,sizeof(WRL));
    for(int ri=0;ri<st->reloc_count;ri++){
        int sidx=-1;
        for(int i=0;i<ncs;i++) if(strcmp(st->relocations[ri].section,csecs[i].name)==0){sidx=i;break;}
        if(sidx<0) continue;
        WRL *rl=&rela_lists[sidx];
        if(rl->len>=rl->cap){rl->cap=rl->cap?rl->cap*2:4;rl->data=realloc(rl->data,rl->cap*sizeof(WRE));if(!rl->data){perror("realloc");exit(1);}}
        rl->data[rl->len++]=(WRE){st->relocations[ri].sec_offset,st->relocations[ri].sym,
                                   st->relocations[ri].rtype,st->relocations[ri].addend,
                                   st->relocations[ri].nbytes};
    }

    /* axx.py port: REL-style target (ELF_MACHINES' is_rela==0, e.g. i386,
     * ARM(32)) has no addend field in the relocation entry at all -- the
     * addend must instead be baked directly into the relocated field's
     * bytes (a REL consumer reads it back as the implicit addend). The
     * bytes there right now hold the *originally encoded* field value, not
     * the RELA-style addend `pat_match`/the reloc-collection code above
     * computed; patch them here before the section data is written out. */
    if(!_is_rela_w){
        for(int i=0;i<ncs;i++){
            WRL *rl=&rela_lists[i];
            for(int ei=0;ei<rl->len;ei++){
                int64_t off = rl->data[ei].off;
                int nb = rl->data[ei].nbytes;
                if(nb<=0 || off<0 || (uint64_t)(off+nb) > csecs[i].bsz) continue;
                uint64_t field = (uint64_t)rl->data[ei].addend & ((nb>=8)?~(uint64_t)0:(((uint64_t)1<<(nb*8))-1));
                uint8_t *dp = csecs[i].data + off;
                if(_is_le){
                    for(int j=0;j<nb;j++){ dp[j]=(uint8_t)(field&0xff); field>>=8; }
                } else {
                    for(int j=nb-1;j>=0;j--){ dp[j]=(uint8_t)(field&0xff); field>>=8; }
                }
            }
        }
    }

    int nrela=0; for(int i=0;i<ncs;i++) if(rela_lists[i].len>0) nrela++;
    int *rs_idx=calloc((size_t)(nrela?nrela:1),sizeof(int));
    { int ri2=0; for(int i=0;i<ncs;i++) if(rela_lists[i].len>0) rs_idx[ri2++]=i; }

    /* ---- 3. build shstrtab and strtab ---- */
    WBB shstr; wbb_init(&shstr);
    WBB strtab_bb; wbb_init(&strtab_bb);

    uint32_t *sec_noff=calloc((size_t)ncs,sizeof(uint32_t));
    for(int i=0;i<ncs;i++) sec_noff[i]=wbb_str(&shstr,csecs[i].name);
    uint32_t *rela_noff=calloc((size_t)(nrela?nrela:1),sizeof(uint32_t));
    for(int ri2=0;ri2<nrela;ri2++){
        char rn[256]; snprintf(rn,sizeof(rn),"%s%s",_is_rela_w?".rela":".rel",csecs[rs_idx[ri2]].name);
        rela_noff[ri2]=wbb_str(&shstr,rn);
    }
    uint32_t sym_noff  =wbb_str(&shstr,".symtab");
    uint32_t str_noff  =wbb_str(&shstr,".strtab");
    uint32_t shstr_noff=wbb_str(&shstr,".shstrtab");

    /* ---- 4. build .symtab ---- */
    int WEO_SYMSZ = _is_elf64 ? 24 : 16;
    WBB symtab_bb; symtab_bb.b=calloc(32,(size_t)WEO_SYMSZ); symtab_bb.len=0; symtab_bb.cap=32*WEO_SYMSZ;
    int nsyms=0;
    WSNI *snimap=calloc((size_t)(st->labels.count+st->export_labels.count+8),sizeof(WSNI));
    int snimap_len=0;

    weo_sym(&symtab_bb,&nsyms,_is_le,_is_elf64,0,0,0,0,0,0);                             /* null */
    for(int i=0;i<ncs;i++) weo_sym(&symtab_bb,&nsyms,_is_le,_is_elf64,0,0x03,0,(uint16_t)(i+1),0,0); /* section syms */

    /* sort labels and export_labels by name */
    int nl=0;
    WLK *larr=calloc((size_t)(st->labels.count?st->labels.count:1),sizeof(WLK));
    {for(int bi=0;bi<st->labels.nbuckets;bi++)
        for(LabelEntry*e=st->labels.buckets[bi];e;e=e->next){
            if(u256_is_undef_derived(e->value)) continue;
            larr[nl++]=(WLK){e->key,u256_to_u64(e->value),e->is_equ,e->is_imported,e->reloc_type_override,e->section};}}
    qsort(larr,nl,sizeof(WLK),cmp_wlk);

    int ne=0;
    WLK *earr=calloc((size_t)(st->export_labels.count?st->export_labels.count:1),sizeof(WLK));
    {for(int bi=0;bi<st->export_labels.nbuckets;bi++)
        for(LabelEntry*e=st->export_labels.buckets[bi];e;e=e->next){
            if(u256_is_undef_derived(e->value)) continue;
            /* export_labels には reloc_type_override が保存されないため labels から引く */
            LabelEntry *_fl=lmap_find(&st->labels,e->key);
            int _rto = _fl ? _fl->reloc_type_override : -1;
            earr[ne++]=(WLK){e->key,u256_to_u64(e->value),e->is_equ,0,_rto,e->section};}}
    qsort(earr,ne,sizeof(WLK),cmp_wlk);


    /* (1) Local labels: not exported, not imported → STB_LOCAL (0x00) */
    for(int i=0;i<nl;i++){
        if(weo_isexp(earr,ne,larr[i].name)) continue;
        if(larr[i].is_imported) continue;   /* imported: emitted below as STB_GLOBAL/SHN_UNDEF */
        /* .equ+::reloctype のラベルはアドレスラベルとしてセクション相対シンボルで出力する。
         * reloc_type_override のない純粋な .equ 定数のみ SHN_ABS とする。 */
        int _equ_has_reloc = larr[i].is_equ && (larr[i].reloc_type_override >= 0);
        WSR sr = (larr[i].is_equ && !_equ_has_reloc)
                 ? (WSR){0xfff1, larr[i].val}
                 : weo_shndx(csecs,ncs,larr[i].val*(uint64_t)bpw,larr[i].section,&st->section_ranges,bpw);
        uint32_t noff=wbb_str(&strtab_bb,larr[i].name);
        snimap[snimap_len++]=(WSNI){larr[i].name,nsyms};
        weo_sym(&symtab_bb,&nsyms,_is_le,_is_elf64,noff,0x00,0,sr.shndx,sr.sv,0);
    }
    int first_global=nsyms;
    /* (2) Imported symbols (.EXTERN): STB_GLOBAL (0x10) / SHN_UNDEF (0)
     * Mirrors axx.py: syms.append(_pack_sym(name_off, 0x10, 0, 0, 0, 0)) */
    for(int i=0;i<nl;i++){
        if(!larr[i].is_imported) continue;
        if(weo_isexp(earr,ne,larr[i].name)) continue;
        uint32_t noff=wbb_str(&strtab_bb,larr[i].name);
        snimap[snimap_len++]=(WSNI){larr[i].name,nsyms};
        weo_sym(&symtab_bb,&nsyms,_is_le,_is_elf64,noff,0x10,0,0,0,0);   /* SHN_UNDEF=0, value=0 */
    }
    /* (3) Export labels → STB_GLOBAL (0x10) */
    for(int i=0;i<ne;i++){
        int _equ_has_reloc = earr[i].is_equ && (earr[i].reloc_type_override >= 0);
        WSR sr = (earr[i].is_equ && !_equ_has_reloc)
                 ? (WSR){0xfff1, earr[i].val}
                 : weo_shndx(csecs,ncs,earr[i].val*(uint64_t)bpw,earr[i].section,&st->section_ranges,bpw);
        uint32_t noff=wbb_str(&strtab_bb,earr[i].name);
        snimap[snimap_len++]=(WSNI){earr[i].name,nsyms};
        weo_sym(&symtab_bb,&nsyms,_is_le,_is_elf64,noff,0x10,0,sr.shndx,sr.sv,0);
    }


    /* ---- 5. build .rela/.rel data ----
     * axx.py port: entry size and layout depend on both ELF class and the
     * RELA-vs-REL convention --
     *   Elf64_Rela (24B): offset(8) info(8, sym<<32|type) addend(8)
     *   Elf32_Rela (12B): offset(4) info(4, sym<<8|type)  addend(4)
     *   Elf64_Rel  (16B): offset(8) info(8, sym<<32|type)  -- no addend
     *   Elf32_Rel  ( 8B): offset(4) info(4, sym<<8|type)   -- no addend
     * (REL's implicit addend was already patched into the section bytes
     * above; every relocation-type number used for a 32-bit-class machine
     * fits in 8 bits, so Elf32's info packing never truncates in practice.) */
    int _reloc_entsz = _is_elf64 ? (_is_rela_w?24:16) : (_is_rela_w?12:8);
    uint8_t **rela_bufs=calloc((size_t)(nrela?nrela:1),sizeof(uint8_t*));
    size_t   *rela_szs =calloc((size_t)(nrela?nrela:1),sizeof(size_t));
    for(int ri2=0;ri2<nrela;ri2++){
        WRL *rl=&rela_lists[rs_idx[ri2]];
        size_t rbs=(size_t)rl->len*(size_t)_reloc_entsz;
        uint8_t *rb=calloc(1,rbs?rbs:1);
        for(int ei=0;ei<rl->len;ei++){
            uint8_t *rp=rb+ei*_reloc_entsz;
            int sym = weo_symof(snimap,snimap_len,rl->data[ei].sym);
            if(_is_elf64){
                uint64_t rinfo=((uint64_t)sym<<32)|((uint32_t)rl->data[ei].rtype);
                WEO_LE8(rp,(uint64_t)rl->data[ei].off);
                WEO_LE8(rp+8,rinfo);
                if(_is_rela_w) WEO_LE8S(rp+16,rl->data[ei].addend);
            } else {
                uint32_t rinfo=((uint32_t)(sym&0xffffff)<<8)|((uint8_t)rl->data[ei].rtype);
                WEO_LE4(rp,(uint32_t)rl->data[ei].off);
                WEO_LE4(rp+4,rinfo);
                if(_is_rela_w) WEO_LE4(rp+8,(uint32_t)rl->data[ei].addend);
            }
        }
        rela_bufs[ri2]=rb; rela_szs[ri2]=rbs;
    }

    /* ---- 5b. build DWARF debug sections (-g) ----
     * Mirrors the axx.py _build_dwarf_sections() port:
     *   dbg_prog : SHT_PROGBITS  .debug_abbrev / .debug_info / .debug_line
     *   dbg_rela : SHT_RELA      .rela.debug_info / .rela.debug_line
     * Debug sections are appended AFTER .shstrtab so e_shstrndx / .symtab /
     * .strtab indices are unchanged. Addresses are 8 bytes and relocated
     * against the content section symbol (sym index == content index),
     * carrying the in-section byte offset as the addend. Single CU, so
     * DW_AT_stmt_list and abbrev_offset are 0 (no relocation needed).
     * Strings are inline (DW_FORM_string), so no .debug_str is required. */
    DSEC dbg_prog[3]; int n_dbg_prog=0;
    DREL dbg_rela[2]; int n_dbg_rela=0;
    for(int _i=0;_i<3;_i++){ dbg_prog[_i]=(DSEC){NULL,NULL,0}; }
    for(int _i=0;_i<2;_i++){ dbg_rela[_i]=(DREL){NULL,0,NULL,0}; }

    const ElfMachineInfo *_mtbl_dbg = elf_machine_find(machine);
    if(st->gen_debug && st->line_map_len>0 && (!_mtbl_dbg || _mtbl_dbg->elfclass != 2)){
        /* This DWARF builder hardcodes 8-byte (DW_FORM_addr) addresses
         * throughout, which is only correct for a 64-bit target -- mirrors
         * axx.py's _build_dwarf_sections() early-return for the same
         * reason. Emitting it for a 32-bit machine would produce
         * structurally-wrong-width DWARF instead of just incomplete DWARF,
         * so refuse rather than silently corrupt it. */
        fprintf(stderr," warning - DWARF debug info (-g) is not yet supported for "
                "32-bit targets (machine %d); skipping debug sections.\n", machine);
    }
    if(st->gen_debug && st->line_map_len>0 && _mtbl_dbg && _mtbl_dbg->elfclass == 2){
        /* growable raw byte buffer */

        /* relocation accumulator for debug sections */

        /* 64-bit absolute relocation type per arch, from ELF_MACHINES
         * (axx.py port: single source of truth). */
        int abs64 = _mtbl_dbg->dwarf_abs;

        /* ---- .debug_abbrev ---- */
        RB abv; rb_init(&abv);
        rb_uleb(&abv,1); rb_uleb(&abv,0x11); rb_u8(&abv,1);   /* compile_unit, children */
        rb_uleb(&abv,0x25);rb_uleb(&abv,0x08);  /* producer  DW_FORM_string  */
        rb_uleb(&abv,0x13);rb_uleb(&abv,0x05);  /* language  DW_FORM_data2   */
        rb_uleb(&abv,0x03);rb_uleb(&abv,0x08);  /* name      DW_FORM_string  */
        rb_uleb(&abv,0x1b);rb_uleb(&abv,0x08);  /* comp_dir  DW_FORM_string  */
        rb_uleb(&abv,0x11);rb_uleb(&abv,0x01);  /* low_pc    DW_FORM_addr    */
        rb_uleb(&abv,0x12);rb_uleb(&abv,0x07);  /* high_pc   DW_FORM_data8   */
        rb_uleb(&abv,0x10);rb_uleb(&abv,0x17);  /* stmt_list DW_FORM_sec_offset */
        rb_uleb(&abv,0);rb_uleb(&abv,0);
        rb_uleb(&abv,2); rb_uleb(&abv,0x0a); rb_u8(&abv,0);   /* label, no children */
        rb_uleb(&abv,0x03);rb_uleb(&abv,0x08);  /* name   DW_FORM_string */
        rb_uleb(&abv,0x11);rb_uleb(&abv,0x01);  /* low_pc DW_FORM_addr   */
        rb_uleb(&abv,0);rb_uleb(&abv,0);
        rb_uleb(&abv,0);                          /* end of abbrev table */

        /* ---- primary section for CU low_pc/high_pc ---- */
        int primary_idx=0; uint64_t primary_size=0;
        for(int i=0;i<ncs;i++) if(strcmp(csecs[i].name,st->line_map[0].section)==0){ primary_idx=i+1; break; }
        if(primary_idx==0 && ncs>0) primary_idx=1;
        if(primary_idx>0) primary_size=csecs[primary_idx-1].bsz;

        char cwd[1024]; if(!getcwd(cwd,sizeof(cwd))) strcpy(cwd,".");
        const char *cu_name = st->line_map[0].file[0]?st->line_map[0].file:"(source)";
        const char *producer = "axx general assembler (C, DWARF4)";

        /* ---- .debug_info ---- */
        DRV info_relas={0,0,0};
        RB die; rb_init(&die);
        rb_uleb(&die,1);
        rb_cstr(&die,producer);
        rb_w2(&die,0x8001,_is_le);            /* DW_LANG_Mips_Assembler */
        rb_cstr(&die,cu_name);
        rb_cstr(&die,cwd);
        if(primary_idx>0) drv_add(&info_relas,die.len,primary_idx,abs64,0);
        rb_w8(&die,0,_is_le);                 /* low_pc (relocated) */
        rb_w8(&die,primary_size,_is_le);      /* high_pc (data8)    */
        rb_w4(&die,0,_is_le);                 /* stmt_list = 0      */
        for(int i=0;i<nl;i++){
            if(larr[i].is_equ || larr[i].is_imported) continue;
            WSR sr = weo_shndx(csecs,ncs,larr[i].val*(uint64_t)bpw,larr[i].section,&st->section_ranges,bpw);
            if(sr.shndx==0xfff1) continue;           /* not in a content section */
            rb_uleb(&die,2);
            rb_cstr(&die,larr[i].name);
            drv_add(&info_relas,die.len,(int)sr.shndx,abs64,(int64_t)sr.sv);
            rb_w8(&die,0,_is_le);
        }
        rb_uleb(&die,0);               /* terminate CU children */
        RB info; rb_init(&info);
        rb_w4(&info,(uint32_t)(2+4+1+die.len),_is_le); /* unit_length */
        rb_w2(&info,4,_is_le);                          /* version */
        rb_w4(&info,0,_is_le);                          /* debug_abbrev_offset */
        rb_u8(&info,8);                          /* address_size */
        size_t info_prefix=info.len;             /* 4+2+4+1 = 11 */
        rb_app(&info,die.b,die.len);
        free(die.b);

        /* ---- .debug_line (DWARF v4) ---- */
        DRV line_relas={0,0,0};
        const char **files=calloc((size_t)st->line_map_len,sizeof(char*)); int nfiles=0;
        int *row_file=calloc((size_t)st->line_map_len,sizeof(int));
        for(int i=0;i<st->line_map_len;i++){
            const char *fn=st->line_map[i].file[0]?st->line_map[i].file:"(source)";
            int fi=0; for(;fi<nfiles;fi++) if(strcmp(files[fi],fn)==0) break;
            if(fi==nfiles) files[nfiles++]=fn;
            row_file[i]=fi+1; /* 1-based */
        }
        RB hb; rb_init(&hb);
        rb_u8(&hb,1);  /* minimum_instruction_length */
        rb_u8(&hb,1);  /* maximum_operations_per_instruction (v4) */
        rb_u8(&hb,1);  /* default_is_stmt */
        rb_u8(&hb,(uint8_t)(int8_t)-5); /* line_base */
        rb_u8(&hb,14); /* line_range */
        rb_u8(&hb,13); /* opcode_base */
        { static const uint8_t sol[12]={0,1,1,1,1,0,0,0,1,0,0,1}; rb_app(&hb,sol,12); }
        rb_u8(&hb,0);  /* include_directories: none + terminator */
        for(int fi=0;fi<nfiles;fi++){ rb_cstr(&hb,files[fi]); rb_uleb(&hb,0);rb_uleb(&hb,0);rb_uleb(&hb,0); }
        rb_u8(&hb,0);  /* end of file_names */

        RB prog; rb_init(&prog);
        size_t prog_base = 4+2+4+hb.len;   /* program offset within .debug_line */
        for(int s=0;s<ncs;s++){
            int cnt=0;
            for(int i=0;i<st->line_map_len;i++) if(strcmp(st->line_map[i].section,csecs[s].name)==0) cnt++;
            if(cnt==0) continue;
            LROW *rows=calloc((size_t)cnt,sizeof(LROW)); int k=0;
            for(int i=0;i<st->line_map_len;i++) if(strcmp(st->line_map[i].section,csecs[s].name)==0){
                rows[k].wpc=st->line_map[i].word_pc; rows[k].file=row_file[i]; rows[k].line=st->line_map[i].line; k++;
            }
            qsort(rows,(size_t)cnt,sizeof(LROW),lrow_cmp);
            /* 破綻点修正 (axx.py port): セクションが複数回の出入りで複数の
             * 断片に分かれている場合、単純な (wpc*bpw - secbase) では
             * 2つ目以降の断片のアドレスが正しいオフセットにならない。
             * addr_to_word_offset()で断片を跨いだ累積オフセットを使う
             * (該当する断片が見つからない場合は0にフォールバックする)。 */
            uint64_t first_off = dwarf_word_offset(st, csecs[s].name, rows[0].wpc, bpw);
            rb_u8(&prog,0); rb_uleb(&prog,1+8); rb_u8(&prog,2);   /* DW_LNE_set_address */
            drv_add(&line_relas, prog_base+prog.len, s+1, abs64, (int64_t)first_off);
            rb_w8(&prog,0,_is_le);
            uint64_t cur_off=first_off; int cur_line=1, cur_file=1;
            for(int i=0;i<cnt;i++){
                uint64_t boff = dwarf_word_offset(st, csecs[s].name, rows[i].wpc, bpw);
                if(rows[i].file!=cur_file){ rb_u8(&prog,4); rb_uleb(&prog,(uint64_t)rows[i].file); cur_file=rows[i].file; }
                if(rows[i].line!=cur_line){ rb_u8(&prog,3); rb_sleb(&prog,(int64_t)rows[i].line-cur_line); cur_line=rows[i].line; }
                if(boff>cur_off){ rb_u8(&prog,2); rb_uleb(&prog,boff-cur_off); cur_off=boff; }
                rb_u8(&prog,1); /* DW_LNS_copy */
            }
            uint64_t end_off=csecs[s].bsz;
            if(end_off>cur_off){ rb_u8(&prog,2); rb_uleb(&prog,end_off-cur_off); }
            rb_u8(&prog,0); rb_uleb(&prog,1); rb_u8(&prog,1); /* DW_LNE_end_sequence */
            free(rows);
        }
        free(files); free(row_file);

        RB line; rb_init(&line);
        rb_w4(&line,(uint32_t)(2+4+hb.len+prog.len),_is_le); /* unit_length */
        rb_w2(&line,4,_is_le);                                /* version */
        rb_w4(&line,(uint32_t)hb.len,_is_le);                 /* header_length */
        rb_app(&line,hb.b,hb.len);
        rb_app(&line,prog.b,prog.len);
        free(hb.b); free(prog.b);

        /* pack Elf64_Rela payloads */

        dbg_prog[n_dbg_prog++]=(DSEC){".debug_abbrev",abv.b,abv.len};
        int info_pi=n_dbg_prog; dbg_prog[n_dbg_prog++]=(DSEC){".debug_info",info.b,info.len};
        int line_pi=n_dbg_prog; dbg_prog[n_dbg_prog++]=(DSEC){".debug_line",line.b,line.len};
        for(int i=0;i<info_relas.len;i++) info_relas.d[i].off += info_prefix;
        if(info_relas.len>0){ size_t L; uint8_t*B=dwarf_pack_relas(&info_relas,&L,_is_le); dbg_rela[n_dbg_rela++]=(DREL){".rela.debug_info",info_pi,B,L}; }
        if(line_relas.len>0){ size_t L; uint8_t*B=dwarf_pack_relas(&line_relas,&L,_is_le); dbg_rela[n_dbg_rela++]=(DREL){".rela.debug_line",line_pi,B,L}; }
        free(info_relas.d); free(line_relas.d);
    }
    /* add debug section names to shstrtab (must be before offset computation) */
    uint32_t dbg_prog_noff[3]={0,0,0};
    uint32_t dbg_rela_noff[2]={0,0};
    for(int i=0;i<n_dbg_prog;i++) dbg_prog_noff[i]=wbb_str(&shstr,dbg_prog[i].name);
    for(int i=0;i<n_dbg_rela;i++) dbg_rela_noff[i]=wbb_str(&shstr,dbg_rela[i].name);

    /* ---- 6. compute file offsets ---- */
    /* Fix 1B: SHT_NOBITS (.bss) sections must NOT consume file space.
     * ELF spec: "A section of type SHT_NOBITS occupies no space in the file."
     * We record sh_offset = current foff (any valid offset is fine; linkers
     * ignore it for NOBITS) but do NOT advance foff past the section data.
     * weo_isno(csecs,) mirrors the same .bss test used in the section-header loop. */
    uint64_t foff=_is_elf64?64:52;
    uint64_t *sec_fo=calloc((size_t)ncs,sizeof(uint64_t));
    for(int i=0;i<ncs;i++){
        foff=WEO_ALIGN(foff,16); sec_fo[i]=foff;
        if(!weo_isno(csecs,i)) foff+=csecs[i].bsz;  /* NOBITS: offset recorded, no file bytes */
    }
    uint64_t *rela_fo=calloc((size_t)(nrela?nrela:1),sizeof(uint64_t));
    for(int ri2=0;ri2<nrela;ri2++){foff=WEO_ALIGN(foff,8);rela_fo[ri2]=foff;foff+=rela_szs[ri2];}
    uint64_t sym_fo=WEO_ALIGN(foff,8); foff=sym_fo+(uint64_t)nsyms*(uint64_t)WEO_SYMSZ;
    uint64_t str_fo=foff;     foff+=strtab_bb.len;
    uint64_t shstr_fo=foff;   foff+=shstr.len;
    /* DWARF debug section offsets (placed after .shstrtab) */
    uint64_t dbg_prog_fo[3]={0,0,0};
    for(int i=0;i<n_dbg_prog;i++){ foff=WEO_ALIGN(foff,1); dbg_prog_fo[i]=foff; foff+=dbg_prog[i].len; }
    uint64_t dbg_rela_fo[2]={0,0};
    for(int i=0;i<n_dbg_rela;i++){ foff=WEO_ALIGN(foff,8); dbg_rela_fo[i]=foff; foff+=dbg_rela[i].len; }
    uint64_t shdr_fo=WEO_ALIGN(foff,8);

    int ndbg=n_dbg_prog+n_dbg_rela;
    int tot_sh=1+ncs+nrela+3+ndbg;
    int shstrndx=ncs+nrela+3;          /* .shstrtab index is unchanged */
    int dbg_base=ncs+nrela+3;          /* debug sections follow .shstrtab */
    int sym_shidx=ncs+nrela+1;
    int str_shidx=ncs+nrela+2;

    /* ---- 7. write file ---- */
    FILE *fp=fopen(path,"wb");
    if(!fp){perror(path);goto weo_done;}

    /* ELF header: Elf64_Ehdr (64 bytes) or Elf32_Ehdr (52 bytes). Both share
     * the same 16-byte e_ident and the same e_type/e_machine/e_version
     * layout at offset 16, but diverge from e_entry onward -- Elf32 packs
     * e_entry/e_phoff/e_shoff as 4-byte fields instead of Elf64's 8-byte
     * ones, shifting every field after it. axx.py port: mirrors axx.py
     * write_elf_obj()'s _pack_ehdr(). */
    if(_is_elf64){
        uint8_t eh[64]={0};
        eh[0]=0x7f;eh[1]='E';eh[2]='L';eh[3]='F';
        eh[4]=2;eh[5]=(uint8_t)_ei_data;eh[6]=1;eh[7]=st->osabi; /* ELFCLASS64 EI_DATA EV_CURRENT ELFOSABI */
        WEO_LE2(eh+16,1); WEO_LE2(eh+18,(uint16_t)machine); WEO_LE4(eh+20,1);
        WEO_LE8(eh+40,shdr_fo);
        WEO_LE2(eh+52,64); WEO_LE2(eh+58,64);
        WEO_LE2(eh+60,(uint16_t)tot_sh); WEO_LE2(eh+62,(uint16_t)shstrndx);
        fwrite(eh,1,64,fp);
    } else {
        uint8_t eh[52]={0};
        eh[0]=0x7f;eh[1]='E';eh[2]='L';eh[3]='F';
        eh[4]=1;eh[5]=(uint8_t)_ei_data;eh[6]=1;eh[7]=st->osabi; /* ELFCLASS32 EI_DATA EV_CURRENT ELFOSABI */
        WEO_LE2(eh+16,1); WEO_LE2(eh+18,(uint16_t)machine); WEO_LE4(eh+20,1);
        WEO_LE4(eh+32,(uint32_t)shdr_fo);
        WEO_LE2(eh+40,52); WEO_LE2(eh+46,40);
        WEO_LE2(eh+48,(uint16_t)tot_sh); WEO_LE2(eh+50,(uint16_t)shstrndx);
        fwrite(eh,1,52,fp);
    }

    /* Fix J: if ftell() fails it returns -1 (a negative long).  The original
     * cast that to uint64_t, yielding UINT64_MAX, which is never < t so the
     * while-loop exited immediately — silently skipping the required padding
     * and corrupting the ELF file.  Now we detect the error and abort. */

    for(int i=0;i<ncs;i++){
        weo_pad(fp,sec_fo[i]);
        /* NOBITS sections (.bss) have no file bytes — skip fwrite. */
        if(!weo_isno(csecs,i) && csecs[i].bsz) fwrite(csecs[i].data,1,(size_t)csecs[i].bsz,fp);
    }
    for(int ri2=0;ri2<nrela;ri2++){weo_pad(fp,rela_fo[ri2]);if(rela_szs[ri2])fwrite(rela_bufs[ri2],1,rela_szs[ri2],fp);}
    weo_pad(fp,sym_fo); fwrite(symtab_bb.b,1,(size_t)nsyms*(size_t)WEO_SYMSZ,fp);
    fwrite(strtab_bb.b,1,strtab_bb.len,fp);
    fwrite(shstr.b,1,shstr.len,fp);
    /* DWARF debug section data (PROGBITS then RELA) */
    for(int i=0;i<n_dbg_prog;i++){ weo_pad(fp,dbg_prog_fo[i]); if(dbg_prog[i].len) fwrite(dbg_prog[i].data,1,dbg_prog[i].len,fp); }
    for(int i=0;i<n_dbg_rela;i++){ weo_pad(fp,dbg_rela_fo[i]); if(dbg_rela[i].len) fwrite(dbg_rela[i].data,1,dbg_rela[i].len,fp); }
    weo_pad(fp,shdr_fo);

    weo_shdr(fp,_is_le,_is_elf64,0,0,0,0,0,0,0,0,0,0); /* [0] NULL */
    for(int i=0;i<ncs;i++){
        /* Fix: .bss は SHT_NOBITS (8)、それ以外は SHT_PROGBITS (1)。
         * ELF 仕様上 SHT_NOBITS セクションはファイル領域を持たない（sh_size は
         * 実際のバイト数を保持するがファイルデータは書かれない）ため、
         * リンカ・ローダーが正しくゼロ初期化できる。 */
        char _un[64]; int _ui=0;
        for(;csecs[i].name[_ui]&&_ui<63;_ui++) _un[_ui]=(char)axx_upper_char(csecs[i].name[_ui]);
        _un[_ui]=0;
        uint32_t _sh_type = (strncmp(_un,".BSS",4)==0) ? 8 : 1;
        weo_shdr(fp,_is_le,_is_elf64,sec_noff[i],_sh_type,csecs[i].fl,0,sec_fo[i],csecs[i].bsz,0,0,16,0);
    }
    {
    uint32_t _word_align = _is_elf64?8:4;
    uint32_t _rel_sh_type = _is_rela_w?4:9;   /* SHT_RELA : SHT_REL */
    for(int ri2=0;ri2<nrela;ri2++)
        weo_shdr(fp,_is_le,_is_elf64,rela_noff[ri2],_rel_sh_type,0x40,0,rela_fo[ri2],rela_szs[ri2],
                 (uint32_t)sym_shidx,(uint32_t)(rs_idx[ri2]+1),_word_align,(uint64_t)_reloc_entsz);
    weo_shdr(fp,_is_le,_is_elf64,sym_noff,2,0,0,sym_fo,(uint64_t)nsyms*(uint64_t)WEO_SYMSZ,
             (uint32_t)str_shidx,(uint32_t)first_global,_word_align,(uint64_t)WEO_SYMSZ);
    }
    weo_shdr(fp,_is_le,_is_elf64,str_noff,3,0,0,str_fo,strtab_bb.len,0,0,1,0);
    weo_shdr(fp,_is_le,_is_elf64,shstr_noff,3,0,0,shstr_fo,shstr.len,0,0,1,0);
    /* DWARF debug section headers (PROGBITS then RELA). */
    for(int i=0;i<n_dbg_prog;i++)
        weo_shdr(fp,_is_le,_is_elf64,dbg_prog_noff[i],1,0,0,dbg_prog_fo[i],dbg_prog[i].len,0,0,1,0);
    for(int i=0;i<n_dbg_rela;i++)
        weo_shdr(fp,_is_le,_is_elf64,dbg_rela_noff[i],4,0x40,0,dbg_rela_fo[i],dbg_rela[i].len,
                 (uint32_t)sym_shidx,(uint32_t)(dbg_base+1+dbg_rela[i].target),8,24);
    fclose(fp);
    fprintf(stderr,"elf: wrote %s (%d section(s), %d %s section(s), %d symbol(s)%s)\n",
            path,ncs,nrela,_is_rela_w?"rela":"rel",nsyms, n_dbg_prog?", +DWARF debug":"");

weo_done:
    for(int i=0;i<ncs;i++) free(csecs[i].data);
    free(csecs);
    for(int i=0;i<nrela;i++) free(rela_bufs[i]);
    free(rela_bufs); free(rela_szs); free(rela_fo); free(rs_idx);
    for(int i=0;i<ncs;i++) free(rela_lists[i].data);
    free(rela_lists);
    free(sec_noff); free(rela_noff);
    free(shstr.b); free(strtab_bb.b); free(symtab_bb.b);
    free(sec_fo); free(larr); free(earr); free(snimap);
    for(int i=0;i<n_dbg_prog;i++) free(dbg_prog[i].data);
    for(int i=0;i<n_dbg_rela;i++) free(dbg_rela[i].data);
    #undef WEO_W2
    #undef WEO_W4
    #undef WEO_W8
    #undef WEO_W8S
    #undef WEO_LE2
    #undef WEO_LE4
    #undef WEO_LE8
    #undef WEO_LE8S
    #undef WEO_ALIGN
}

static void fileassemble(Assembler *asmb, const char *fn){
    AsmState *st=&asmb->st;

    /* Fix ③ (axx.py): circular .INCLUDE detection.
     * Compare absolute paths to catch relative-path aliases.
     * stdin / (stdin) are compared by name only (no realpath). */
    {
        int is_stdin_fn = (strcmp(fn,"stdin")==0 || strcmp(fn,"(stdin)")==0);
        for(int si=0; si<st->fnstack.len; si++){
            const char *already = st->fnstack.data[si];
            if(!already || !already[0]) continue;
            int is_stdin_already = (strcmp(already,"stdin")==0 || strcmp(already,"(stdin)")==0);
            if(is_stdin_fn && is_stdin_already){
                fprintf(stderr," error - circular .INCLUDE detected: '%s' is already being assembled.\n", fn);
                st->had_error=1;
                return;
            }
            if(!is_stdin_fn && !is_stdin_already){
                /* Compare by resolved absolute path */
                char abs_fn[4096]={0}, abs_al[4096]={0};
                if(realpath(fn,   abs_fn) && realpath(already, abs_al)
                   && strcmp(abs_fn, abs_al)==0){
                    fprintf(stderr," error - circular .INCLUDE detected: '%s' is already being assembled.\n", fn);
                    st->had_error=1;
                    return;
                }
            }
        }
    }

    /* Bugfix (axx.py port): push `fn` itself (the file about to be entered)
     * onto fnstack, not the caller's current_file. fnstack must contain the
     * exact stack of files currently open so the cycle check above can see
     * a file that re-includes ITSELF directly (`.INCLUDE` of its own name):
     * pushing the caller's file instead left `fn` absent from fnstack for
     * its first (direct) re-entry, so a self-including file got assembled
     * twice -- duplicating its emitted bytes at wrong addresses -- before
     * the cycle was finally caught one level deeper. current_file is saved
     * in a local and restored from there in `done:` below instead, so
     * fnstack purely tracks "files currently open" for cycle detection.
     *
     * Fix C-10 (still applies): push is always unconditional; pop must
     * therefore also be unconditional. */
    char _caller_file[512];
    strncpy(_caller_file, st->current_file, sizeof(_caller_file)-1);
    _caller_file[sizeof(_caller_file)-1] = '\0';
    sv_push(&st->fnstack, fn);
    is_push(&st->lnstack, st->ln);
    strncpy(st->current_file,fn,sizeof(st->current_file)-1);
    st->ln=1;

    FILE *f=NULL;
    char *stdin_buf=NULL;

    if(strcmp(fn,"stdin")==0){
        /* Fix C-6 / Fix C-N4: use a per-process unique temp file instead of
         * the fixed name "axx.tmp" to avoid races when multiple caxx instances
         * run concurrently.
         *
         * Fix C-N4: the old code set need_read=(st->pas==1), which caused stdin
         * to be read again on every relaxation iteration (pas is always 1 inside
         * the loop).  By the second iteration stdin is at EOF, so the temp file
         * was overwritten with an empty string and all subsequent passes assembled
         * nothing.
         *
         * Fix: read stdin exactly once – when stdin_tmp_path is first created.
         * All subsequent calls (relaxation iterations + pass2) reuse the file. */
        if(st->stdin_tmp_path[0] == '\0'){
            /* First call: create unique temp file AND read stdin into it. */
            char tmpl[] = "/tmp/axx_XXXXXX";
            int fd = mkstemp(tmpl);
            if(fd >= 0){
                close(fd);
                strncpy(st->stdin_tmp_path, tmpl, sizeof(st->stdin_tmp_path)-1);
            } else {
                /* fallback to fixed name if mkstemp fails */
                strncpy(st->stdin_tmp_path, "axx.tmp", sizeof(st->stdin_tmp_path)-1);
            }
            stdin_buf=file_input_from_stdin();
            FILE *tmpf=fopen(st->stdin_tmp_path,"wt");
            if(tmpf){ fwrite(stdin_buf,1,strlen(stdin_buf),tmpf); fclose(tmpf); }
        }
        /* All passes (including relaxation iterations) reuse the same file. */
        fn=st->stdin_tmp_path;
    }

    f=fopen(fn,"rt");
    if(!f){ fprintf(stderr,"Cannot open: %s\n",fn); goto done; }
    {
        char *line=NULL; size_t lcap=0;
        while(getline(&line,&lcap,f)!=-1) lineassemble0(asmb,line);
        free(line);
    }
    fclose(f);

done:
    free(stdin_buf);
    /* Fix C-10: pop unconditionally to mirror the unconditional push above.
     * The original guarded the pop with (fnstack.len>0) which could silently
     * leave current_file/ln unrestored if the stack was somehow empty.
     * Bugfix (axx.py port): restore current_file from `_caller_file` (saved
     * before the push above), not from fnstack's top -- fnstack now holds
     * `fn` itself (needed so the cycle check above can see direct
     * self-includes), not the caller's file, so reading it here would
     * incorrectly "restore" current_file back to `fn`. */
    strncpy(st->current_file, _caller_file, sizeof(st->current_file)-1);
    st->current_file[sizeof(st->current_file)-1] = '\0';
    sv_pop(&st->fnstack);
    st->ln = is_pop(&st->lnstack);
}

/* =========================================================
 * setpatsymbols
 * ========================================================= */
static void setpatsymbols(Assembler *asmb){
    /* Fix 8 (axx.py): process .setsym AND .clearsym in pattern-file order,
     * starting from an empty table.  The old code only called dir_set_symbol()
     * and ignored .clearsym, so a pattern sequence like:
     *   .setsym A 1
     *   .clearsym
     * would still leave A defined.  Also, calling dir_set_symbol() mutated
     * st->symbols directly and then copied to patsymbols; if .clearsym wiped
     * st->symbols before the copy, patsymbols ended up empty regardless of what
     * .setsym defined earlier.
     *
     * Fix: build a fresh map by processing entries in order, then assign to
     * both patsymbols and symbols (mirroring axx.py setpatsymbols()).         */
    SymMap fresh; smap_init(&fresh);

    for(int pi=0; pi<asmb->st.pat.len; pi++){
        PatEntry *e=&asmb->st.pat.data[pi];
        if(!e) continue;

        if(strcmp(e->f[0],".setsym")==0){
            /* Same readpat() 2-field-vs-3-field indexing quirk fixed in
             * dir_set_symbol() above: a name-only ".setsym::FOO" line puts
             * "FOO" in f[2], not f[1]. */
            const char *name_field = e->f[1][0] ? e->f[1] : e->f[2];
            const char *value_field = e->f[1][0] ? e->f[2] : "";
            char key[512]; axx_strupr_to(key,name_field,sizeof(key));
            int io;
            uint256_t v = value_field[0] ? expr_expression_pat(asmb,value_field,0,&io) : u256_zero();
            smap_set(&fresh, key, v);
            continue;
        }
        if(strcmp(e->f[0],".clearsym")==0){
            if(e->f[2][0]){
                char key[512]; axx_strupr_to(key,e->f[2],sizeof(key));
                smap_delete(&fresh, key);
            } else {
                smap_clear(&fresh);
            }
            continue;
        }
        /* Bugfix (axx.py port): apply `.bits` as soon as it's seen here, the
         * same way, so `st->bts`/`st->endian_big` already reflect the
         * pattern file's real word width by the time `main()` processes a
         * `-i` label-import file (which happens right after this call,
         * before any source line is assembled). `.bits` is normally only
         * applied lazily while scanning `st->pat` during actual line
         * assembly (inside lineassemble2()'s directive dispatch), which
         * would otherwise leave st->bts at its default (8) during import,
         * corrupting the bytes-per-word conversion imp_label() needs. */
        if(strcmp(e->f[0],".bits")==0){
            dir_bits(asmb, e);
            continue;
        }
    }

    /* Assign fresh to patsymbols and sync symbols */
    smap_free(&asmb->st.patsymbols); smap_init(&asmb->st.patsymbols);
    smap_clear(&asmb->st.symbols);
    for(int i=0; i<fresh.nb; i++)
        for(SymEntry *e=fresh.buckets[i]; e; e=e->next){
            smap_set(&asmb->st.patsymbols, e->key, e->val);
            smap_set(&asmb->st.symbols,    e->key, e->val);
        }
    smap_free(&fresh);
}

/* =========================================================
 * imp_label
 * ========================================================= */
static int imp_label(Assembler *asmb, const char *l){
    /* Parse TSV format produced by WRITE_EXPORT.
     *
     * Line formats (tab-separated):
     *   section_name\tstart_hex\tsize_hex\t[flag]  <- section line (>=3 fields)
     *   label_name\tvalue_hex                      <- label line  (2 fields)
     *
     * The old implementation used axx_skipspc() (space-only skip) together
     * with axx_get_label_word() and assumed a space-separated
     * "section label value" layout.  WRITE_EXPORT writes TAB-separated TSV
     * with section and label information on separate lines, so the old code
     * never parsed a single line correctly – imp_label always returned 0.
     *
     * Fix: split on '\t', distinguish line kind by field count, build a
     * running imp_sections table for label→section resolution.
     */

    /* strip trailing CR/LF */
    char buf[4096];
    strncpy(buf, l, sizeof(buf)-1); buf[sizeof(buf)-1] = '\0';
    int blen = (int)strlen(buf);
    while(blen > 0 && (buf[blen-1]=='\n'||buf[blen-1]=='\r')) buf[--blen] = '\0';
    if(!buf[0]) return 0;

    /* split on '\t' – at most 5 fields needed */
    char *fields[5]; int nfields = 0;
    char *p = buf;
    while(nfields < 5){
        fields[nfields++] = p;
        char *tab = strchr(p, '\t');
        if(!tab) break;
        *tab = '\0';
        p = tab + 1;
    }

    if(nfields >= 3){
        /* section line: record start/size for later label->section lookup */
        const char *sname = fields[0];
        char *endp;
        uint64_t start = strtoull(fields[1], &endp, 16);
        if(endp == fields[1]) return 0;
        uint64_t size  = strtoull(fields[2], &endp, 16);
        if(endp == fields[2]) return 0;
        secrangevec_push(&asmb->imp_sections, sname,
                          u256_from_u64(start), u256_from_u64(size));
        return 1;
    }

    if(nfields == 2){
        char labelbuf[512];
        strncpy(labelbuf, fields[0], sizeof(labelbuf)-1); labelbuf[sizeof(labelbuf)-1]='\0';
        const char *label = labelbuf;
        if(!label[0]) return 0;
        /* 破綻点修正 (axx.py port): WRITE_EXPORTはreloc_type付きラベルを
         * "labelname::reloctype" という1フィールドで書き出す(例:
         * "myconst::abs64")が、ここではその"::"を一切分離せず
         * フィールド全体をラベル名としてそのまま取り込んでいたため、
         * インポート後は本来の"myconst"とは無関係な、実体の無い
         * "myconst::abs64"という名前のグローバル未定義シンボルが
         * 紛れ込み、かつ肝心のreloc_type情報はインポート後に
         * 失われていた(常に-1固定で label_put_value に渡していた)。 */
        int reloc_type = -1;
        char *sep = strstr(labelbuf, "::");
        if(sep){
            *sep = '\0';
            const char *rt_str = sep + 2;
            reloc_type = elf_machine_named(elf_machine_find(asmb->st.elf_machine), rt_str);
            if(reloc_type < 0)
                fprintf(stderr," warning - unknown reloc type '%s' for imported label '%s'\n",
                        rt_str, label);
        }
        if(!label[0]) return 0;
        char *endp;
        uint64_t v = strtoull(fields[1], &endp, 16);
        if(endp == fields[1]) return 0;

        /* determine section by range lookup in previously parsed sections.
         * 破綻点修正 (axx.py port): imp_sectionsがSecRangeVec(断片ごと
         * 複数エントリ可)になったため、同名の全断片を単純に線形走査
         * すれば、再入セクションの2回目以降の断片も正しく拾える。 */
        const char *section = ".text";
        for(int i = 0; i < asmb->imp_sections.len; i++){
            SecRange *se = &asmb->imp_sections.data[i];
            uint64_t s0 = u256_to_u64(se->start);
            uint64_t sz = u256_to_u64(se->len);
            if(sz > 0 && v >= s0 && v < s0 + sz){ section = se->name; break; }
            if(sz == 0 && v == s0)               { section = se->name; break; }
        }
        /* 破綻点修正 (axx.py port): label_put_value() 経由(→lmap_set())
         * では is_imported が常に0にリセットされ、インポートしたラベルが
         * ELF出力上「このファイル内でローカルに実定義された値」として
         * 書き出されてしまい、本来リンク時に解決されるべき外部シンボルが
         * 誤ったローカル値のまま固定されるバグがあった(axx.py側は
         * self.state.labels[label] = [v, section, False, True] と直接
         * 代入しis_imported=Trueにしている)。.EXTERN と同じ経路である
         * lmap_set_imported() を使い、is_imported=1 として登録する。 */
        /* Bugfix (axx.py port): WRITE_EXPORT writes non-.EQU label addresses
         * in BYTES (word_value * bpw, matching the ELF st_value convention;
         * see the WRITE_EXPORT macro's byte_start/lbl_addr computation).
         * But every other consumer of a label's stored value (ELF st_value,
         * DWARF addresses, $$/$. pc-relative math, ...) treats it as a raw
         * WORD pc and multiplies by bpw itself. Storing `v` here unconverted
         * double-counted bpw for every reference to an imported label
         * whenever bpw != 1 (st->bts not a multiple of 8) -- e.g. a label
         * imported at byte offset 4 on a 16-bit-word target (bpw=2) was
         * silently treated as word offset 4 (byte 8) instead of the correct
         * word offset 2. The section-membership lookup just above
         * intentionally still compares the byte-scaled `v` against
         * imp_sections' byte-scaled ranges (both written by the same
         * WRITE_EXPORT, so mutually consistent); only the value finally
         * stored needs converting back to words. */
        {
            int _bpw = (asmb->st.bts+7)/8; if(_bpw<1) _bpw=1;
            v /= (uint64_t)_bpw;
        }
        lmap_set_imported(&asmb->st.labels, label, u256_from_u64(v), section, reloc_type);
        return 1;
    }

    return 0;
}

/* =========================================================
 * main
 * ========================================================= */
static void print_usage(const char *prog){
    printf("usage: %s patternfile [sourcefile] [--osabi OSNAME] [-b outfile] [-e export_tsv] [-E export_elf_tsv] [-i import_tsv] [-o elf_obj] [-m machine] [-v]\n",prog);
    printf("axx general assembler programmed and designed by Taisuke Maekawa\n");
}

/* 破綻点修正6 (axx.py port): Pass1リラクゼーションの振動検出。
 * 直前の1回とだけ比較していると、周期2以上で振動するレイアウト
 * (A→B→A→B→...)をMAX_RELAX回使い切るまで検出できない。過去に見た
 * 全レイアウトの履歴(history[])と比較し、以前に見たものへ戻ったら
 * その時点で振動として検出する。比較基準は既存の収束判定と同じ
 * (エントリ数が一致し、全ラベルの値・所属セクションが一致)。 */
static int label_maps_equal(LabelMap *a, LabelMap *b) {
    if (a->count != b->count) return 0;
    for (int bi = 0; bi < a->nbuckets; bi++)
        for (LabelEntry *e = a->buckets[bi]; e; e = e->next) {
            LabelEntry *p = lmap_find(b, e->key);
            if (!p || !u256_eq(p->value, e->value)
                   || strcmp(p->section ? p->section : "",
                             e->section ? e->section : "") != 0)
                return 0;
        }
    return 1;
}
static void label_map_copy_from(LabelMap *dst, LabelMap *src) {
    lmap_init(dst);
    for (int bi = 0; bi < src->nbuckets; bi++)
        for (LabelEntry *e = src->buckets[bi]; e; e = e->next)
            lmap_set_full(dst, e->key, e->value, e->section,
                          e->is_equ, e->is_imported, e->reloc_type_override);
}

typedef struct {
    char    s[16];
    int     nu;
} OSABIENT;

/* 破綻点修正 (axx.py port): 小文字表記("linux"/"freebsd")のエントリが
 * 無かったため、find_osabi()は大文字小文字完全一致のみで判定し、
 * 未知値扱いになった場合は警告も出さずに黙ってFreeBSD(デフォルトと
 * 同じ値)へフォールバックしていた。既定値がたまたまFreeBSDのため、
 * "--osabi linux"のように小文字でLinuxを明示指定したつもりが、
 * ユーザに一切気づかれないままFreeBSDとして出力される事故になっていた。 */
static OSABIENT osabitbl[]={{"Linux",0},{"linux",0},{"FreeBSD",9},{"freebsd",9},{"EOTBL",-1}};

int find_osabi( char *osname ) {
    int idx = 0;
    while (1) {
        if (strcmp(osabitbl[idx].s,"EOTBL")==0)
            return -1;
        if (strcmp(osabitbl[idx].s,osname)==0)
            return osabitbl[idx].nu;
        idx++;
    }
}

    
int main(int argc, char *argv[]){
    if(argc==1){ print_usage(argv[0]); return 0; }

    int exit_code = 0;
    Assembler *asmb=calloc(1,sizeof(Assembler));
    assembler_init(asmb);
    AsmState *st=&asmb->st;

    const char *patternfile=NULL, *sourcefile=NULL;
    char osabistr[16]="FreeBSD"; /* ELF_OSABI Default: FreeBSD */

    for(int i=1;i<argc;i++){
        if(strcmp(argv[i],"--osabi")==0&&i+1<argc){ strncpy(osabistr,argv[++i],sizeof(osabistr)-1); }
        else if(strcmp(argv[i],"-b")==0&&i+1<argc){ strncpy(st->outfile,argv[++i],sizeof(st->outfile)-1); }
        else if(strcmp(argv[i],"-e")==0&&i+1<argc){ strncpy(st->expfile,argv[++i],sizeof(st->expfile)-1); }
        else if(strcmp(argv[i],"-E")==0&&i+1<argc){ strncpy(st->expfile_elf,argv[++i],sizeof(st->expfile_elf)-1); }
        else if(strcmp(argv[i],"-i")==0&&i+1<argc){ strncpy(st->impfile,argv[++i],sizeof(st->impfile)-1); }
        else if(strcmp(argv[i],"-o")==0&&i+1<argc){ strncpy(st->elf_objfile,argv[++i],sizeof(st->elf_objfile)-1); }
        else if(strcmp(argv[i],"-m")==0&&i+1<argc){
            int _mval = atoi(argv[++i]);
            /* axx.py port: reject any machine number ELF_MACHINES doesn't
             * know correct relocation numbering for, rather than accepting
             * any 16-bit value and silently falling back to x86_64-shaped
             * relocations for an unrecognized one (that used to be this
             * check's only job -- range-only, no whitelist -- mirrors
             * axx.py's `args.elf_machine not in ELF_MACHINES` check). */
            if(!elf_machine_find(_mval)){
                char _known[512]; int _kn=0;
                for(int _mi=0; _mi<ELF_MACHINES_N && _kn < (int)sizeof(_known)-40; _mi++){
                    _kn += snprintf(_known+_kn, sizeof(_known)-(size_t)_kn, "%s%d (%s)",
                                     _mi?", ":"", ELF_MACHINES[_mi].machine, ELF_MACHINES[_mi].name);
                }
                fprintf(stderr, " error - -m/--machine value %d is not a supported ELF "
                        "e_machine number. axx only knows correct relocation-type "
                        "numbering for: %s. Refusing to guess/fall back to x86_64 "
                        "numbering for an unrecognized machine, since that would "
                        "silently mislabel every relocation in the output.\n",
                        _mval, _known);
                return 1;
            }
            st->elf_machine = _mval;
        }
        else if(strcmp(argv[i],"-v")==0||strcmp(argv[i],"--verbose")==0){ st->verbose=1; }
        else if(strcmp(argv[i],"-d")==0||strcmp(argv[i],"--debug")==0){ st->debug=1; }
        else if(strcmp(argv[i],"-g")==0||strcmp(argv[i],"--gen-debug")==0){ st->gen_debug=1; }
        else if(argv[i][0]!='-'){
            if(!patternfile) patternfile=argv[i];
            else if(!sourcefile) sourcefile=argv[i];
        }
    }

    int osa = find_osabi(osabistr);
    if (osa==-1) {
        fprintf(stderr, "warning: unknown --osabi value '%s'; "
                "valid choices are Linux/linux/FreeBSD/freebsd. Using 'FreeBSD'.\n",
                osabistr);
        osa = find_osabi("FreeBSD"); /* Fall back to Default FreeBSD */
    }
    st->osabi = osa;

    if(!patternfile){ print_usage(argv[0]); return 1; }

    readpat(asmb,patternfile);
    setpatsymbols(asmb);

    if(st->impfile[0]){
        FILE *lf=fopen(st->impfile,"rt");
        if(lf){ char *l=NULL; size_t lc=0; while(getline(&l,&lc,lf)!=-1) imp_label(asmb,l); free(l); fclose(lf); }
    }

    if(st->outfile[0]) remove(st->outfile);

    if(!sourcefile){
        st->pc=u256_zero(); st->pas=0; st->ln=1;
        strncpy(st->current_file,"(stdin)",sizeof(st->current_file)-1);
        char *line=NULL; size_t lcap=0;
        while(1){
            /* Mirrors Python printaddr() + input(">> "):
             *   print("%016x: " % pc, end='')
             *   line = input(">> ")                                  */
            printf("%016llx: >> ",(unsigned long long)u256_to_u64(st->pc));
            fflush(stdout);
            if(getline(&line,&lcap,stdin)==-1) break;
            int ll=(int)strlen(line);
            while(ll>0&&(line[ll-1]=='\n'||line[ll-1]=='\r')) line[--ll]=0;
            /* Bugfix (axx.py port): this used to also do an extra
             * "replace('\\\\','\\')" pass here, mirroring what was (also
             * buggily) in axx.py. That pre-collapsed backslash pairs
             * BEFORE the line ever reached the normal string-literal
             * escape processing (.ASCII/asciistr etc.), which already
             * correctly interprets '\\' as one escaped backslash --
             * double-processing it silently produced different bytes in
             * interactive/stdin mode than the identical line assembled
             * from a file would. Removed; both modes now agree. */
            /* Python: line = line.strip() */
            ll=(int)strlen(line);
            while(ll>0&&line[ll-1]==' ') line[--ll]=0;
            int start=0; while(line[start]==' ') start++;
            if(start) memmove(line,line+start,ll-start+1);
            if(!line[0]) continue;
            if(strcmp(line,"?")==0){ label_print_all(st); continue; }
            lineassemble0(asmb,line);
        }
        free(line);
    } else {
        /* Fix C-3: pass1 relaxation loop.
         *
         * For variable-length instruction architectures, a single pass1 may
         * estimate instruction sizes incorrectly when forward references force
         * label values to 0.  This shifts all subsequent label addresses, which
         * in turn may change instruction sizes again.
         *
         * Fix: repeat pass1 (up to MAX_RELAX times) until every label's PC
         * value is identical to the previous iteration ("converged").  Then
         * run pass2 once against the stable label table.
         *
         * For fixed-size ISAs the loop converges in one iteration (no change).
         *
         * Fix 5  (axx.py): imported labels (-i option) must be restored at the
         *   start of every iteration; a bare lmap_free+lmap_init discards them.
         * Fix ⑧ (axx.py): vars (a-z) must be reset to their pre-loop state at
         *   the start of every iteration.
         * Fix ⑤ (axx.py): if any label value is UNDEF (0xff…ff) do not consider
         *   the iteration converged; UNDEF == UNDEF is a false convergence.
         * Fix ⑥-2 (axx.py): convergence snapshot includes section membership,
         *   not just PC value.
         */
#define MAX_RELAX 16   /* A (axx.py port): relaxation now actually iterates; allow more headroom */
        /* Fix 5: snapshot imported labels before the relaxation loop so they
         * can be restored at the start of each iteration. */
        LabelMap imported_labels;
        lmap_init(&imported_labels);
        for(int bi=0; bi<st->labels.nbuckets; bi++)
            for(LabelEntry *e=st->labels.buckets[bi]; e; e=e->next)
                lmap_set_full(&imported_labels, e->key, e->value, e->section,
                              e->is_equ, e->is_imported, e->reloc_type_override);

        /* Fix ⑧: snapshot initial vars (a-z) */
        uint256_t initial_vars[26];
        memcpy(initial_vars, st->vars, sizeof(initial_vars));

        LabelMap prev_labels;
        lmap_init(&prev_labels);
        int converged = 0;

        /* 破綻点修正6: 振動検出用のレイアウト履歴(label_maps_equal参照)。 */
        LabelMap history[MAX_RELAX];
        int history_count = 0;

        /* A (axx.py port): expose the previous-iteration snapshot to
         * label_get_value() so pass1 forward references resolve to their prior
         * address. prev_labels is updated at the END of each iteration, so at
         * the START of iteration N it holds iteration N-1's values (empty on
         * the first iteration => forward refs fall back to 0/UNDEF, correct). */
        st->relax_prev = &prev_labels;

        for(int relax=0; relax<MAX_RELAX; relax++){
            st->pc=u256_zero(); st->pas=1; st->ln=1;
            /* Fix 5: restore imported labels instead of starting from empty */
            lmap_free(&st->labels); lmap_init(&st->labels);
            for(int bi=0; bi<imported_labels.nbuckets; bi++)
                for(LabelEntry *e=imported_labels.buckets[bi]; e; e=e->next)
                    lmap_set_full(&st->labels, e->key, e->value, e->section,
                                  e->is_equ, e->is_imported, e->reloc_type_override);
            /* reset sections and export_labels too (mirrors axx.py run()) */
            secmap_clear(&st->sections);
            secrangevec_clear(&st->section_ranges);
            /* Bug修正(axx.py port): reset current_section so that the previous
             * iteration's trailing section (.data etc.) does not become old_sec
             * at the next iteration's start and get wrongly registered at pc=0. */
            strcpy(st->current_section, ".text");
            lmap_free(&st->export_labels); lmap_init(&st->export_labels);
            /* Fix C-N6: reset symbols to the post-pattern-file baseline at the
             * start of every relaxation iteration (patsymbols is immutable
             * after the initial setpatsymbols() call now that source-level
             * .setsym/.clearsym has been removed; only symbols needs
             * resetting here, since the per-line pattern-file replay
             * mutates it during matching). */
            smap_clear(&st->symbols);
            for(int pi=0; pi<st->patsymbols.nb; pi++)
                for(SymEntry *se2=st->patsymbols.buckets[pi]; se2; se2=se2->next)
                    smap_set(&st->symbols, se2->key, se2->val);
            /* Fix ⑧: restore vars to pre-loop state */
            memcpy(st->vars, initial_vars, sizeof(st->vars));
            fileassemble(asmb,sourcefile);

            /* Bug修正(axx.py port): finalize the last section's size.
             * adir_section() only updates old_sec when switching sections, so the
             * final (trailing) section never gets its size updated.
             * Mirrors axx.py run(): _blk1 = pc - entry_pc; _e1[1] += _blk1 */
            secmap_finalize_current(st);

            /* Fix ⑤: if any label is UNDEF, do not treat this as converged.
             * Fix ⑥-2: convergence check includes section membership as well
             * as PC value (mirrors axx.py current_pcs = {k: (v[0], v[1]) ...}).
             * Fix ⑮ (axx.py port): values >= 2^128 are also treated as UNDEF-derived.
             *   UNDEF = 2^256-1; UNDEF+offset etc. produce huge but not all-ones values.
             *   In practice no real assembler PC exceeds 2^128, so treat anything
             *   that large as an unresolved forward-reference (mirrors axx.py
             *   _UNDEF_THRESHOLD = 1 << 128 logic).
             *   is_equ labels hold arbitrary integer constants and are excluded
             *   from this check (they may legitimately be large). */
            int has_undef = 0;
            for(int bi=0; bi<st->labels.nbuckets && !has_undef; bi++)
                for(LabelEntry *e=st->labels.buckets[bi]; e; e=e->next){
                    if(e->is_equ) continue;
                    if(u256_is_undef_derived(e->value)){ has_undef=1; break; }
                }

            /* 破綻点修正6: 直前の1回だけでなく、履歴中の全レイアウトと比較する。
             * cycle_len==1なら従来通りの単純収束、2以上なら振動として検出し、
             * MAX_RELAX回を待たずに明確なエラーで打ち切る(誤ったバイナリを
             * 黙って出力しないため)。 */
            converged = 0;
            if(!has_undef){
                int first_seen = -1;
                for(int hi=0; hi<history_count; hi++){
                    if(label_maps_equal(&st->labels, &history[hi])){ first_seen = hi; break; }
                }
                if(first_seen >= 0){
                    int cycle_len = history_count - first_seen;
                    if(cycle_len == 1){
                        converged = 1;
                    } else {
                        fprintf(stderr,
                            " error - Pass1 relaxation is oscillating with period %d "
                            "(the instruction layout at iteration %d is identical to "
                            "iteration %d); it will never converge by simple repetition.\n",
                            cycle_len, relax+1, first_seen+1);
                        fprintf(stderr,"         Aborting: no output file written.\n");
                        for(int hi=0; hi<history_count; hi++) lmap_free(&history[hi]);
                        lmap_free(&prev_labels);
                        lmap_free(&imported_labels);
                        st->relax_prev = NULL;
                        exit_code = 1;
                        goto cleanup;
                    }
                } else {
                    label_map_copy_from(&history[history_count], &st->labels);
                    history_count++;
                }
            }

            /* Update prev_labels snapshot (label_get_value()の前方参照推定用。
             * 振動検出のhistory[]とは別目的なので、こちらは従来通り毎回更新する)。 */
            lmap_free(&prev_labels); lmap_init(&prev_labels);
            for(int bi=0; bi<st->labels.nbuckets; bi++)
                for(LabelEntry *e=st->labels.buckets[bi]; e; e=e->next)
                    lmap_set_full(&prev_labels, e->key, e->value, e->section,
                                  e->is_equ, e->is_imported, e->reloc_type_override);

            if(converged){
                if(st->debug)
                    fprintf(stderr,"Pass1 relaxation converged after %d iteration(s)\n",
                            relax+1);
                break;
            }
        }
        for(int hi=0; hi<history_count; hi++) lmap_free(&history[hi]);
        /* A (axx.py port, 指摘3): snapshot pass1-final addresses (is_equ=0 only)
         * for the pass1<->pass2 consistency check performed after pass2. */
        LabelMap pass1_final;
        lmap_init(&pass1_final);
        for(int bi=0; bi<st->labels.nbuckets; bi++)
            for(LabelEntry *e=st->labels.buckets[bi]; e; e=e->next)
                if(!e->is_equ)
                    lmap_set_full(&pass1_final, e->key, e->value, e->section,
                                  e->is_equ, e->is_imported, e->reloc_type_override);

        lmap_free(&prev_labels);
        lmap_free(&imported_labels);
        /* A: relaxation is done; pass2 must NOT consult the (now-freed) snapshot. */
        st->relax_prev = NULL;

        if(!converged){
            /* Fix: 収束しなかった場合は単なる警告ではなく致命的エラーとする。
             * 収束前提のPass2アドレスは信頼できないため、Pass2実行・出力書き込み
             * を行わずここで打ち切る(誤ったバイナリを黙って出力しないため)。 */
            fprintf(stderr," error - Pass1 relaxation did not converge after %d iterations; "
                    "addresses would be incorrect for variable-length instructions "
                    "with forward references.\n", MAX_RELAX);
            fprintf(stderr,"         Aborting: no output file written.\n");
            lmap_free(&pass1_final);
            exit_code = 1;
            goto cleanup;
        }
#undef MAX_RELAX

        st->pc=u256_zero(); st->pas=2; st->ln=1;
        /* reset relocations before pass2 (mirrors axx.py run()) */
        for(int ri=0;ri<st->reloc_count;ri++){
            free(st->relocations[ri].section);
            free(st->relocations[ri].sym);
        }
        st->reloc_count=0;
        /* reset DWARF line map before pass2 (only pass2 fills it) */
        for(int _li=0;_li<st->line_map_len;_li++){
            free(st->line_map[_li].section);
            free(st->line_map[_li].file);
        }
        st->line_map_len=0;
        /* Fix 5 (new) (axx.py port): reset sections before pass2 so stale
         * provisional sizes from pass1 do not carry over.  labels and
         * patsymbols do NOT need resetting here (only sections): symbols
         * are only ever set by the pattern file (source-level .setsym/
         * .clearsym has been removed), so patsymbols is immutable after
         * the initial setpatsymbols() call and needs no per-pass reset. */
        secmap_clear(&st->sections);
        secrangevec_clear(&st->section_ranges);
        /* Bug修正(axx.py port): reset current_section before pass2 (mirrors
         * axx.py: self.state.current_section = '.text' before pass2 fileassemble). */
        strcpy(st->current_section, ".text");
        fileassemble(asmb,sourcefile);

        /* Bug修正(axx.py port): finalize the last section's size after pass2.
         * Mirrors axx.py run():
         *   _last_sec = self.state.current_section
         *   if not _confirmed: _e[1] += (pc - entry_pc) */
        secmap_finalize_current(st);

        /* A (axx.py port, 指摘3): pass1<->pass2 address consistency check (safety net).
         * If any non-.equ label's pass2 address differs from its pass1-final
         * address, the emitted binary's addresses are unreliable (relaxation did
         * not fully converge). The old code emitted such a binary silently.
         * Two passes: first count all drifts (so the header can include the
         * count, matching axx.py exactly), then print up to 10 details. */
        {
            int drift_count = 0;
            for(int bi=0; bi<st->labels.nbuckets; bi++)
                for(LabelEntry *e=st->labels.buckets[bi]; e; e=e->next){
                    if(e->is_equ) continue;
                    if(u256_is_undef_derived(e->value)) continue;
                    LabelEntry *p = lmap_find(&pass1_final, e->key);
                    if(p && !u256_eq(p->value, e->value)) drift_count++;
                }
            if(drift_count){
                fprintf(stderr," error - address mismatch between pass1 and pass2 "
                    "(%d label(s)); output addresses are UNRELIABLE.\n", drift_count);
                fprintf(stderr,"         This usually means pass1 relaxation did "
                    "not fully converge for variable-length forward references.\n");
                int shown = 0;
                for(int bi=0; bi<st->labels.nbuckets && shown<10; bi++)
                    for(LabelEntry *e=st->labels.buckets[bi]; e && shown<10; e=e->next){
                        if(e->is_equ) continue;
                        if(u256_is_undef_derived(e->value)) continue;
                        LabelEntry *p = lmap_find(&pass1_final, e->key);
                        if(p && !u256_eq(p->value, e->value)){
                            fprintf(stderr,"           %s: pass1=0x%llX pass2=0x%llX\n",
                                e->key,
                                (unsigned long long)u256_to_u64(p->value),
                                (unsigned long long)u256_to_u64(e->value));
                            shown++;
                        }
                    }
                if(drift_count > 10)
                    fprintf(stderr,"           ... and %d more.\n", drift_count - 10);
                /* Fix: 従来はエラー表示のみで出力を続けていたため、アドレスが
                 * 不正なオブジェクトファイルがそのまま生成されていた。ここで
                 * 中断し、出力ファイルを書かない。 */
                fprintf(stderr,"         Aborting: no output file written.\n");
                lmap_free(&pass1_final);
                exit_code = 1;
                goto cleanup;
            }
        }
        lmap_free(&pass1_final);

        /* Bugfix (axx.py port): a genuine per-line error during pass2
         * (undefined label, syntax error, illegal pattern match, label
         * conflict) must abort the build instead of silently writing a
         * shorter/wrong binary and exiting 0. Previously fileassemble()'s
         * per-line return values were discarded entirely and no run-wide
         * error state existed, so main() always reached this point and
         * wrote output regardless of errors printed above. */
        if(st->had_error){
            fprintf(stderr," error - one or more errors were reported during assembly; "
                    "output would be incomplete or wrong.\n");
            fprintf(stderr,"         Aborting: no output file written.\n");
            exit_code = 1;
            goto cleanup;
        }
    }

    binary_flush(st);

    /* ELF relocatable object output (-o option) */
    if(st->elf_objfile[0])
        write_elf_obj(st, st->elf_objfile, st->elf_machine);

    /* Fix #2: -e と -E が同時指定された場合、元のコードは expfile_elf で
     * st->expfile を上書きしてから一回だけ書き出していたため -e ファイルが
     * 消えていた。修正: write_export() を分離し、-e と -E をそれぞれ独立して
     * 書き出す。両方指定された場合は警告を表示する。             */
    if(st->expfile_elf[0] && st->expfile[0])
        fprintf(stderr,"warning: both -e '%s' and -E '%s' specified; "
                "exporting plain format to -e and ELF format to -E separately.\n",
                st->expfile, st->expfile_elf);

    /* Helper lambda (as a nested function via a local write) */
    /* Fix (axx.py port):
     *   1. Section start/size are stored in word units; imp_label() expects byte
     *      units.  Multiply by bytes-per-word (_bpw_export) before writing.
     *   2. Label addresses are also word-unit PCs; convert to bytes.
     *      Exception: is_equ=1 labels are absolute constants, not PCs – no conversion.
     *   Mirrors axx.py _write_export() / _bpw_export logic. */
    int _bpw_export = ((st->bts + 7) / 8);
    if(_bpw_export < 1) _bpw_export = 1;

    #define WRITE_EXPORT(path_, elf_) do { \
        FILE *lf=fopen((path_),"wt"); \
        if(lf){ \
            for(int i=0;i<st->sections.count;i++){ \
                SecEntry *e=st->sections.order[i]; \
                const char *flag=""; \
                if(elf_){ \
                    if(strcmp(e->name,".text")==0) flag="AX"; \
                    else if(strcmp(e->name,".data")==0) flag="WA"; \
                } \
                /* 破綻点修正 (axx.py port): セクションが複数回出入り \
                 * した場合(.text→.data→.text等)、真の訪問範囲は複数の \
                 * 断片に分かれる。以前はst->sections[i]の(最小開始pc, \
                 * 累積サイズ)を単一の範囲として書き出していたため、 \
                 * 2回目以降の断片の実際のpc位置を全くカバーしない \
                 * 不正な範囲になり、-iでインポートした際にラベルの \
                 * 所属セクションを誤判定する原因になっていた。 \
                 * st->section_rangesから断片ごとに個別の行を書き出す。 */ \
                int _wrote_any = 0; \
                for(int j=0;j<st->section_ranges.len;j++){ \
                    SecRange *sr=&st->section_ranges.data[j]; \
                    if(strcmp(sr->name,e->name)!=0) continue; \
                    unsigned long long byte_start = \
                        (unsigned long long)u256_to_u64(sr->start) * (unsigned long long)_bpw_export; \
                    unsigned long long byte_size  = \
                        (unsigned long long)u256_to_u64(sr->len)  * (unsigned long long)_bpw_export; \
                    fprintf(lf,"%s\t0x%llx\t0x%llx\t%s\n", \
                            e->name, byte_start, byte_size, flag); \
                    _wrote_any = 1; \
                } \
                if(!_wrote_any){ \
                    unsigned long long byte_start = \
                        (unsigned long long)u256_to_u64(e->start) * (unsigned long long)_bpw_export; \
                    unsigned long long byte_size  = \
                        (unsigned long long)u256_to_u64(e->size)  * (unsigned long long)_bpw_export; \
                    fprintf(lf,"%s\t0x%llx\t0x%llx\t%s\n", \
                            e->name, byte_start, byte_size, flag); \
                } \
            } \
            for(int i=0;i<st->export_labels.nbuckets;i++){ \
                for(LabelEntry*e=st->export_labels.buckets[i];e;e=e->next){ \
                    if(u256_is_undef_derived(e->value)) continue; \
                    unsigned long long lbl_addr; \
                    if(e->is_equ){ \
                        lbl_addr=(unsigned long long)u256_to_u64(e->value); \
                    } else { \
                        lbl_addr=(unsigned long long)u256_to_u64(e->value) \
                                 *(unsigned long long)_bpw_export; \
                    } \
                    /* axx.py: emit ::reloc_type suffix if reloc_type_override is set, \
                     * looking up the symbolic name from ELF_MACHINES (axx.py port: \
                     * single source of truth, was a hardcoded x86_64-only switch). */ \
                    char _rtype_sfx[80]=""; \
                    if(elf_){ \
                        LabelEntry *_full=lmap_find(&st->labels,e->key); \
                        if(_full && _full->reloc_type_override>=0){ \
                            const char *_nm=elf_machine_reverse(elf_machine_find(st->elf_machine), \
                                                                 _full->reloc_type_override); \
                            if(_nm) snprintf(_rtype_sfx,sizeof(_rtype_sfx),"::%s",_nm); \
                        } \
                    } \
                    fprintf(lf,"%s%s\t0x%llx\n",e->key,_rtype_sfx,lbl_addr); \
                } \
            } \
            fclose(lf); \
        } \
    } while(0)

    if(st->expfile[0])     WRITE_EXPORT(st->expfile,     0);
    if(st->expfile_elf[0]) WRITE_EXPORT(st->expfile_elf, 1);

    #undef WRITE_EXPORT

    /* Fix C-6: clean up the per-process stdin temp file if one was created. */
cleanup:
    if(st->stdin_tmp_path[0]){
        unlink(st->stdin_tmp_path);
        st->stdin_tmp_path[0] = '\0';
    }

    /* Free the DWARF line map (strdup'd section/file strings + array). */
    for(int _li=0;_li<st->line_map_len;_li++){
        free(st->line_map[_li].section);
        free(st->line_map[_li].file);
    }
    free(st->line_map);
    st->line_map=NULL; st->line_map_len=0; st->line_map_cap=0;

    return exit_code;
}
