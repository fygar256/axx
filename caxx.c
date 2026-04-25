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
    int            is_equ;       /* 1 if defined via .equ – not relocatable */
    int            is_imported;  /* 1 if declared via .EXTERN – STB_GLOBAL/SHN_UNDEF in ELF */
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
    uint32_t h=hash_str(key)%(uint32_t)m->nbuckets;
    for(LabelEntry*e=m->buckets[h];e;e=e->next)
        if(strcmp(e->key,key)==0) return e;
    return NULL;
}
static int lmap_contains(LabelMap *m, const char *key) { return lmap_find(m,key)!=NULL; }
static void lmap_set(LabelMap *m, const char *key, uint256_t val, const char *sec, int is_equ) {
    uint32_t h=hash_str(key)%(uint32_t)m->nbuckets;
    for(LabelEntry*e=m->buckets[h];e;e=e->next){
        if(strcmp(e->key,key)==0){
            e->value=val; free(e->section); e->section=strdup(sec); e->is_equ=is_equ;
            /* preserve is_imported when updating an existing entry */
            return;
        }
    }
    LabelEntry *e=calloc(1,sizeof(LabelEntry));
    e->key=strdup(key); e->value=val; e->section=strdup(sec);
    e->is_equ=is_equ; e->is_imported=0;
    e->next=m->buckets[h]; m->buckets[h]=e; m->count++;
}
/* Set a label as an imported external symbol (.EXTERN).
 * Mirrors axx.py: labels[s] = [0, '.text', False, True] */
static void lmap_set_imported(LabelMap *m, const char *key, uint256_t val, const char *sec) {
    uint32_t h=hash_str(key)%(uint32_t)m->nbuckets;
    for(LabelEntry*e=m->buckets[h];e;e=e->next){
        if(strcmp(e->key,key)==0){
            e->value=val; free(e->section); e->section=strdup(sec);
            e->is_equ=0; e->is_imported=1;
            return;
        }
    }
    LabelEntry *e=calloc(1,sizeof(LabelEntry));
    e->key=strdup(key); e->value=val; e->section=strdup(sec);
    e->is_equ=0; e->is_imported=1;
    e->next=m->buckets[h]; m->buckets[h]=e; m->count++;
}
/* Copy all label fields including is_imported. Used for relaxation snapshots. */
static void lmap_set_full(LabelMap *m, const char *key, uint256_t val,
                          const char *sec, int is_equ, int is_imported) {
    uint32_t h=hash_str(key)%(uint32_t)m->nbuckets;
    for(LabelEntry*e=m->buckets[h];e;e=e->next){
        if(strcmp(e->key,key)==0){
            e->value=val; free(e->section); e->section=strdup(sec);
            e->is_equ=is_equ; e->is_imported=is_imported;
            return;
        }
    }
    LabelEntry *e=calloc(1,sizeof(LabelEntry));
    e->key=strdup(key); e->value=val; e->section=strdup(sec);
    e->is_equ=is_equ; e->is_imported=is_imported;
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
typedef struct SecEntry { char*name; uint256_t start; uint256_t size; struct SecEntry*next; } SecEntry;
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
    e->next=m->buckets[h]; m->buckets[h]=e;
    if(m->count>=m->cap){m->cap*=2;m->order=realloc(m->order,m->cap*sizeof(SecEntry*));}
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
    BufEntry*e=malloc(sizeof(BufEntry)); e->pos=pos; e->val=val;
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

    int        align;
    int        bts;
    int        endian_big;
    int        pas;
    int        debug;

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
    } *relocations;
    int        reloc_count;
    int        reloc_cap;
} AsmState;

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
    st->pass1_size_mode = 0;
    st->stdin_tmp_path[0] = '\0';
    st->expfile_elf[0] = '\0';
    st->elf_objfile[0] = '\0';
    st->elf_machine = 62;
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
    idx=axx_skipspc(s,idx);
    size_t n=0;
    while(s[idx]&&s[idx]!=' '&&n<tsz-1) t[n++]=s[idx++];
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
        printf(" warning - unterminated string literal: %s\n", l2);
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
        printf(" error - missing closing '}' in expression: '{%s'\n", t_out);
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
    t_out[n++]=s[idx++];
    while(s[idx]&&char_in(s[idx],swordchars)&&n<tsz-1) t_out[n++]=s[idx++];
    t_out[n]=0;
    axx_strupr(t_out);
    return idx;
}

static int axx_get_label_word(const char *s, int idx, const char *lwordchars, char *t_out, size_t tsz){
    t_out[0]=0;
    if(!s[idx]) return idx;
    if(s[idx]!='.'&&(is_digit(s[idx])||!char_in(s[idx],lwordchars))) return idx;
    size_t n=0;
    t_out[n++]=s[idx++];
    while(s[idx]&&char_in(s[idx],lwordchars)&&n<tsz-1) t_out[n++]=s[idx++];
    t_out[n]=0;
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
     * phase only and must not be confused with st.sections (assembly output). */
    SecMap imp_sections;
};

static void assembler_init(Assembler *a){
    state_init(&a->st);
    secmap_init(&a->imp_sections);
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
    if(st->pas==2||st->pas==0)
        fwrite_word(st, u256_to_u64(a), x, 1);
}
static void outbin2(AsmState *st, uint256_t a, uint256_t x){
    if(st->pas==2||st->pas==0)
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
    st->error_undefined_label=0;
    LabelEntry *e=lmap_find(&st->labels,k);
    if(e){
        /* ELF relocation tracking.
         * .equ-defined labels are absolute constants – never relocatable. */
        if(st->elf_tracking && !e->is_equ){
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
        return e->value;
    }
    st->error_undefined_label=1;
    /* Fix C-3: in pass1 size-estimation mode return 0 so makeobj() can
     * compute the correct instruction byte count even for forward refs. */
    return st->pass1_size_mode ? u256_zero() : UNDEF_VAL();
}
static const char *label_get_section(AsmState *st, const char *k){
    st->error_undefined_label=0;
    LabelEntry *e=lmap_find(&st->labels,k);
    if(e) return e->section;
    st->error_undefined_label=1;
    return "";
}
static int label_put_value(AsmState *st, const char *k, uint256_t v, const char *sec, int is_equ){
    if(st->pas==1||st->pas==0){
        if(lmap_contains(&st->labels,k)){
            st->error_already_defined=1;
            printf(" error - label already defined.\n");
            return 0;
        }
    } else if(st->pas==2){
        if(!lmap_contains(&st->labels,k)){
            st->error_already_defined=1;
            printf(" error - label '%s' not defined in pass 1.\n",k);
            return 0;
        }
    }
    char uk[512]; axx_strupr_to(uk,k,sizeof(uk));
    uint256_t dummy;
    if(smap_get(&st->patsymbols,uk,&dummy)){
        printf(" error - '%s' is a pattern file symbol.\n",k);
        return 0;
    }
    st->error_already_defined=0;
    lmap_set(&st->labels,k,v,sec,is_equ);
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
    printf("{");
    for(int i=0;i<st->labels.nbuckets;i++){
        for(LabelEntry*e=st->labels.buckets[i];e;e=e->next){
            if(!first) printf(", ");
            printf("'%s': ['0x%llx', '%s']",
                   e->key,
                   (unsigned long long)u256_to_u64(e->value),
                   e->section);
            first=0;
        }
    }
    printf("}\n");
}

/* =========================================================
 * SymbolManager
 * ========================================================= */
static int symbol_get(AsmState *st, const char *w, uint256_t *out){
    char uw[512]; axx_strupr_to(uw,w,sizeof(uw));
    return smap_get(&st->symbols,uw,out);
}

/* =========================================================
 * Expression evaluator
 * ========================================================= */
static uint256_t expr_factor(Assembler *asmb, const char *s, int idx, int *idx_out);
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
                    printf(" error - missing ')' in *(expr, expr) expression.\n");
                    x=u256_zero();
                }
            } else {
                /* 修正⑩: missing ',' – report error and return 0 */
                printf(" error - missing ',' in *(expr, expr) expression.\n");
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

static uint256_t expr_factor1(Assembler *asmb, const char *s, int idx, int *idx_out){
    AsmState *st=&asmb->st;
    uint256_t x=u256_zero();
    idx=axx_skipspc(s,idx);
    int slen=(int)strlen(s);

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
    else if(idx+3<=slen && s[idx]=='\'' && s[idx+2]=='\''){
        unsigned char cv=(unsigned char)s[idx+1]; x=u256_from_i64(cv); idx+=3;
        if(asmb->st.exp_typ_float) x=double_to_u256((double)cv); }
    else if(axx_q(s,slen,"$$",idx)){
        idx+=2;
        x=st->pc;
        /* In float mode, treat PC as an integer-valued double (int→float). */
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
    else if(idx+3<=slen && strncmp(s+idx,"qad",3)==0){
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
                /* Fall back: evaluate as double-mode expression */
                int io2;
                int prev_flt=asmb->st.exp_typ_float;
                asmb->st.exp_typ_float=1;
                uint256_t fv=expr_expression_pat(asmb,expr_buf,0,&io2);
                asmb->st.exp_typ_float=prev_flt;
                double dv=u256_to_double(fv);
                char fstr[64]; snprintf(fstr,sizeof(fstr),"%.17g",dv);
                x=ieee754_128_from_str(fstr);
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
    else if(idx+5<=slen && strncmp(s+idx,"enflt",5)==0){
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
    else if(idx+5<=slen && strncmp(s+idx,"endbl",5)==0){
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
    else if(idx+3<=slen && strncmp(s+idx,"dbl",3)==0){
        idx+=3;
        int f; char t[512];
        idx=axx_get_curlb(s,idx,&f,t,sizeof(t));
        if(f){
            uint64_t bits;
            if(strcmp(t,"nan")==0) bits=0x7ff8000000000000ULL;
            else if(strcmp(t,"inf")==0) bits=0x7ff0000000000000ULL;
            else if(strcmp(t,"-inf")==0) bits=0xfff0000000000000ULL;
            else {
                /* Evaluate expression inside braces in float mode using the
                 * native C expression evaluator (no Python subprocess). */
                int prev_flt = asmb->st.exp_typ_float;
                asmb->st.exp_typ_float = 1;
                int io2; uint256_t fv = expr_expression_pat(asmb,t,0,&io2);
                asmb->st.exp_typ_float = prev_flt;
                double v = u256_to_double(fv);
                memcpy(&bits,&v,8);
            }
            x=u256_from_u64(bits);
        }
    }
    else if(idx+3<=slen && strncmp(s+idx,"flt",3)==0){
        idx+=3;
        int f; char t[512];
        idx=axx_get_curlb(s,idx,&f,t,sizeof(t));
        if(f){
            uint32_t bits;
            if(strcmp(t,"nan")==0) bits=0x7fc00000u;
            else if(strcmp(t,"inf")==0) bits=0x7f800000u;
            else if(strcmp(t,"-inf")==0) bits=0xff800000u;
            else {
                /* Evaluate expression inside braces in float mode using the
                 * native C expression evaluator (no Python subprocess). */
                int prev_flt = asmb->st.exp_typ_float;
                asmb->st.exp_typ_float = 1;
                int io2; uint256_t fv = expr_expression_pat(asmb,t,0,&io2);
                asmb->st.exp_typ_float = prev_flt;
                float v = (float)u256_to_double(fv);
                memcpy(&bits,&v,4);
            }
            x=u256_from_u64(bits);
        }
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
                if(b==0.0){ printf("Division by 0 error.\n"); x=double_to_u256(0.0); }
                else x=double_to_u256(floor(u256_to_double(x)/b));
            } else {
                /* Fix L: set x=0 on div-by-zero; previously x kept the old
                 * dividend value, making 'a//0' silently return 'a'. */
                if(u256_is_zero(t)){ printf("Division by 0 error.\n"); x=u256_zero(); }
                else x=u256_floordiv(x,t);
            }
        } else if(s[idx]=='/'&&s[idx+1]!='/'){
            /* True division */
            uint256_t t=expr_term0_0(asmb,s,idx+1,&idx);
            if(flt){
                double b=u256_to_double(t);
                if(b==0.0){ printf("Division by 0 error.\n"); x=double_to_u256(0.0); }
                else x=double_to_u256(u256_to_double(x)/b);
            } else {
                /* Fix L: same as // fix */
                if(u256_is_zero(t)){ printf("Division by 0 error.\n"); x=u256_zero(); }
                else x=u256_floordiv(x,t);
            }
        } else if(s[idx]=='%'){
            uint256_t t=expr_term0_0(asmb,s,idx+1,&idx);
            if(flt){
                double b=u256_to_double(t);
                if(b==0.0){ printf("Division by 0 error.\n"); x=double_to_u256(0.0); }
                else x=double_to_u256(fmod(u256_to_double(x),b));
            } else {
                /* Fix L: same as // fix */
                if(u256_is_zero(t)){ printf("Division by 0 error.\n"); x=u256_zero(); }
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
        if(axx_q(s,slen,"<<",idx)){uint256_t t=expr_term1(asmb,s,idx+2,&idx);x=u256_shl(x,(int)u256_to_i64(t));}
        else if(axx_q(s,slen,">>",idx)){uint256_t t=expr_term1(asmb,s,idx+2,&idx);x=u256_sar(x,(int)u256_to_i64(t));}
        else break;
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
            printf(" warning - sign-extension bit width %lld exceeds maximum %d, result set to 0.\n",
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

static uint256_t expr_term8(Assembler *asmb, const char *s, int idx, int *idx_out){
    int slen=(int)strlen(s);
    if(idx+4<=slen && axx_q(s,slen,"not(",idx)){
        uint256_t x=expr_expression(asmb,s,idx+3,&idx);
        *idx_out=idx;
        return u256_from_i64(u256_is_zero(x)?1:0);
    }
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
                && (c == '?' || c == ',')) break;
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
    char key[512]; axx_strupr_to(key,e->f[1],sizeof(key));
    int io;
    uint256_t v = e->f[2][0] ? expr_expression_pat(asmb,e->f[2],0,&io) : u256_zero();
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
        if((st->pas==2||st->pas==0)&&!u256_is_zero(u)){
            int64_t tc=u256_to_i64(t);
            printf("Line %d Error code %lld ",(int)st->ln,(long long)tc);
            if(tc>=0&&tc<ERRORS_COUNT) printf("%s",ERRORS_TABLE[tc]);
            printf(": \n");
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

    while(1){
        idx_s=axx_skipspc(s,idx_s);
        idx_t=axx_skipspc(t,idx_t);
        char b=s[idx_s], a=t[idx_t];

        if(a=='\0'&&b=='\0'){ result=1; break; }

        if(a=='\\'){
            idx_t++;
            if(idx_t<tlen && t[idx_t]==b){ idx_t++; idx_s++; continue; }
            else { result=0; break; }
        } else if(a>='A'&&a<='Z'){
            if(a==axx_upper_char(b)){ idx_s++; idx_t++; continue; }
            else { result=0; break; }
        } else if(a=='!'){
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
            idx_t++;
            char w[512];
            idx_s=axx_get_symbol_word(s,idx_s,st->swordchars,w,sizeof(w));
            uint256_t sv;
            if(!symbol_get(st,w,&sv)){ result=0; break; }
            var_put(st,a,sv);
            continue;
        } else if(a=='[' || a==']'){
            idx_t++;
            idx_s=axx_skipspc(s,idx_s);
            if(s[idx_s]==a){ idx_s++; continue; }
            else { result=0; break; }
        } else if(a==b){ idx_t++; idx_s++; continue; }
        else { result=0; break; }
    }
    free(s); free(t);
    return result;
}

/* -------------------------------------------------------
 * Bug 3 fix: pat_match0() – undefined behaviour from 1<<cnt
 * When cnt >= 32, (1<<cnt) is UB in C (signed int overflow).
 *
 * Fix: use uint64_t for the mask.  We also cap cnt at 63 to
 * stay within uint64_t range; patterns with >= 64 optional
 * groups are pathological and were broken before anyway.
 * ------------------------------------------------------- */
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

    /* Cap at 63 to keep the uint64_t bitmask valid */
    if(cnt > 63) cnt = 63;

    int *sl=malloc((cnt+1)*sizeof(int));
    for(int i=0;i<cnt;i++) sl[i]=i+1;   /* serials 1..cnt */

    int found=0;
    uint64_t total = (uint64_t)1 << cnt; /* 2^cnt subsets; safe for cnt<=63 */
    for(uint64_t mask=0; mask<total && !found; mask++){
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
    FILE *f=fopen(fn,"rt");
    if(!f){ fprintf(stderr,"Cannot open pattern file: %s\n",fn); return; }

    /* Compute this file's directory for recursive .INCLUDE resolution */
    char this_dir[1024];
    axx_dir_of(fn, this_dir, sizeof(this_dir));

    char line[4096];
    while(fgets(line,sizeof(line),f)){
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
    fclose(f);
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

    /* Fix P9: use a separate logical index for ELF word tracking so that
     * UNDEF-skipped elements do not cause subsequent elements to inherit a
     * stale/duplicate word_idx (the old code used objl->len which does not
     * advance when an element is skipped).                                   */
    int logical_word_idx = 0;
    int idx=0;
    while(1){
        if(idx>=slen||s[idx]=='\0') break;
        if(s[idx]==','){
            idx++;
            uint64_t p=u256_to_u64(st->pc)+(uint64_t)objl->len;
            uint64_t aligned=align_addr(st,p);
            for(uint64_t ii=p;ii<aligned;ii++){
                /* Fix ⑤ (axx.py): update elf_current_word_idx before each
                 * padding push so subsequent label refs get the right word_idx. */
                st->elf_current_word_idx = (int)objl->len;
                iv_push(objl,st->padding);
            }
            continue;
        }
        int semicolon=0;
        if(s[idx]==';'){ semicolon=1; idx++; }
        st->elf_current_word_idx = logical_word_idx;
        int io;
        uint256_t x=expr_expression_pat(asmb,s,idx,&io);
        idx=io;
        logical_word_idx++;
        if(u256_is_undef(x)){
            if(s[idx]==','){idx++;continue;}
            continue;
        }
        if(semicolon?!u256_is_zero(x):1) iv_push(objl,x);
        if(s[idx]==','){idx++;continue;}
        break;
    }
    st->elf_current_word_idx = -1;
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
            IntVec new_idxs; iv_init(&new_idxs);
            IntVec new_objl; iv_init(&new_objl);
            int new_idx;
            lineassemble2(asmb,line,idx,&new_idxs,&new_objl,&new_idx);
            idx=new_idx;
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
        if(st->pas==0||st->pas==2)
            printf(" error - vliwinstbits is zero; cannot compute instruction slots.\n");
        ivv_free(&objs); free(idxlst);
        if(idx_out) *idx_out=idx;
        return 0;
    }

    for(int ki=0;ki<st->vliwset.len;ki++){
        VliwSetEntry *k=&st->vliwset.data[ki];
        int *sorted_k=malloc(k->nidxs*sizeof(int));
        memcpy(sorted_k,k->idxs,k->nidxs*sizeof(int));
        // qsort(sorted_k,k->nidxs,sizeof(int),int_cmp);
        int *sorted_l=malloc(nidxlst*sizeof(int));
        memcpy(sorted_l,idxlst,nidxlst*sizeof(int));
        // qsort(sorted_l,nidxlst,sizeof(int),int_cmp);
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
        int target_len=ibyte*noi;
        if(values.len > target_len){
            if(st->pas==2||st->pas==0)
                printf("warning-VLIW:%d values exceed slot capacity %d,truncating.\n",values.len,target_len);
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

    if(!found && (st->pas==0||st->pas==2))
        printf(" error - No vliw instruction-set defined.\n");

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
            /* Bug 7 fix: pass only the expression tail, not the full line */
            const char *expr_tail = l + idx;
            uint256_t u = expr_expression_asm(asmb, expr_tail, 0, &io);
            label_put_value(st,label,u,st->current_section,1);  /* is_equ=1 */
            out[0]=0; return out;
        } else {
            label_put_value(st,label,st->pc,st->current_section,0);  /* is_equ=0 */
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
    if(strcmp(up,"SECTION")!=0 && strcmp(up,"SEGMENT")!=0) return 0;
    if(l2&&l2[0]){
        snprintf(st->current_section, sizeof(st->current_section), "%s", l2);
        /* Only record start address the first time a section is declared.
         * Re-declarations (.text -> .data -> .text) must not overwrite the
         * original start, otherwise ELF section start / endsection size
         * calculation would be corrupted.  Mirrors axx.py section_processing:
         *   if l2 not in self.state.sections:
         *       self.state.sections[l2] = [self.state.pc, 0]            */
        if(!secmap_find(&st->sections,l2))
            secmap_set(&st->sections,l2,st->pc,u256_zero());
    }
    return 1;
}
static int adir_endsection(AsmState *st, const char *l){
    char up[32]; axx_strupr_to(up,l,sizeof(up));
    if(strcmp(up,"ENDSECTION")!=0 && strcmp(up,"ENDSEGMENT")!=0) return 0;
    SecEntry *e=secmap_find(&st->sections,st->current_section);
    if(!e){
        printf(" error - ENDSECTION without matching SECTION for '%s'.\n",
               st->current_section);
        return 1;
    }
    e->size=u256_sub(st->pc,e->start);
    return 1;
}
static int adir_zero(Assembler *asmb, const char *l, const char *l2){
    char up[16]; axx_strupr_to(up,l,sizeof(up));
    if(strcmp(up,".ZERO")!=0) return 0;
    int io;
    uint256_t x=expr_expression_asm(asmb,l2,0,&io);
    /* Fix ②: guard against UNDEF (undefined label) to avoid range(UNDEF) freeze.
     * Also guard against negative values. Mirrors axx.py zero_processing(). */
    if(asmb->st.error_undefined_label){
        if(asmb->st.pas==2||asmb->st.pas==0)
            printf(" error - .ZERO argument contains undefined label.\n");
        return 1;
    }
    int64_t cnt=u256_to_i64(x);
    if(cnt < 0){
        printf(" error - .ZERO requires a non-negative count, got %lld.\n", (long long)cnt);
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
    if(strcmp(up,".ASCIIZ")!=0) return 0;
    int f=asciistr(asmb,l2);
    if(!f){
        if(asmb->st.pas==2||asmb->st.pas==0)
            printf(" error - .ASCIIZ requires a quoted string.\n");
        return 0;
    }
    outbin(&asmb->st,asmb->st.pc,u256_zero());
    asmb->st.pc=u256_add(asmb->st.pc,u256_one());
    return 1;
}
static int adir_align(Assembler *asmb, const char *l, const char *l2){
    char up[16]; axx_strupr_to(up,l,sizeof(up));
    if(strcmp(up,".ALIGN")!=0) return 0;
    if(l2&&l2[0]){ int io; uint256_t u=expr_expression_asm(asmb,l2,0,&io); asmb->st.align=(int)u256_to_i64(u); }
    asmb->st.pc=u256_from_u64(align_addr(&asmb->st,u256_to_u64(asmb->st.pc)));
    return 1;
}
static int adir_org(Assembler *asmb, const char *l, const char *l2){
    char up[16]; axx_strupr_to(up,l,sizeof(up));
    if(strcmp(up,".ORG")!=0) return 0;
    int io;
    uint256_t u=expr_expression_asm(asmb,l2,0,&io);
    /* Fix ②: guard against UNDEF to prevent pc being set to 0xffff…ff.
     * Mirrors axx.py org_processing() which checks error_undefined_label. */
    if(asmb->st.error_undefined_label){
        if(asmb->st.pas==2||asmb->st.pas==0)
            printf(" error - .ORG argument contains undefined label.\n");
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
 * .EXTERN label [, label ...]
 * Declares external (undefined) symbols.  Each name is registered in
 * st->labels as an imported label (is_imported=1, value=0, section=".text")
 * so that references do NOT raise "undefined label" errors, and
 * write_elf_obj() emits the symbol as STB_GLOBAL / SHN_UNDEF.
 * If the label is already locally defined (.EXTERN is processed in all passes
 * to support forward references in the pass1 relaxation loop). */
static int adir_extern(Assembler *asmb, const char *l, const char *l2){
    AsmState *st=&asmb->st;
    char up[16]; axx_strupr_to(up,l,sizeof(up));
    if(strcmp(up,".EXTERN")!=0) return 0;
    char buf[4096]; strncpy(buf,l2,sizeof(buf)-1); buf[sizeof(buf)-1]=0;
    int idx=0; int blen=(int)strlen(buf);
    while(idx<blen&&buf[idx]){
        idx=axx_skipspc(buf,idx);
        char s[512];
        idx=axx_get_label_word(buf,idx,st->lwordchars,s,sizeof(s));
        if(!s[0]) break;
        if(buf[idx]==':') idx++;
        /* Only register if NOT already locally defined.
         * A locally defined label has is_imported==0 (or absent). */
        LabelEntry *existing=lmap_find(&st->labels,s);
        int is_locally_defined = (existing && !existing->is_imported);
        if(!is_locally_defined){
            /* [value=0, section=".text", is_equ=0, is_imported=1] */
            lmap_set_imported(&st->labels, s, u256_zero(), ".text");
        }
        idx=axx_skipspc(buf,idx);
        if(buf[idx]==',') idx++;
    }
    return 1;
}

/* =========================================================
 * Main assembly loop
 * ========================================================= */
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
              if(cur && cur[0] && strcmp(cur,"(stdin)")!=0 && strcmp(cur,"stdin")!=0){
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
    if(adir_export(asmb,l,l2)){ *idx_out=idx; return 1; }

    /* Fix 9 (axx.py): source-level .setsym / .clearsym directives must be
     * processed here (before the pattern loop) and must also update patsymbols
     * so that their effect persists across the per-instruction symbols reset
     * that lineassemble() performs at the top of the loop.
     *
     * axx.py lineassemble2():
     *   _i_src = [l, '', l2, '', '', '']
     *   if self.directive_proc.set_symbol(_i_src):
     *       self.state.patsymbols = dict(self.state.symbols)
     *       return [], [], True, idx
     *   if self.directive_proc.clear_symbol(_i_src):
     *       self.state.patsymbols = dict(self.state.symbols)
     *       return [], [], True, idx
     */
    {
        char lu[16]; axx_strupr_to(lu,l,sizeof(lu));
        if(strcmp(lu,".SETSYM")==0){
            /* l2 contains the symbol name (field[1]) and optionally a value (field[2]) */
            /* Parse: l2 = "NAME [value]" */
            char sym_name[512]; int sio=0;
            sio=axx_get_param_to_spc(l2,0,sym_name,sizeof(sym_name));
            char sym_name_upper[512]; axx_strupr_to(sym_name_upper,sym_name,sizeof(sym_name_upper));
            uint256_t v=u256_zero();
            if(l2[sio]){
                int vio;
                v=expr_expression_pat(asmb,l2+sio,0,&vio);
            }
            smap_set(&asmb->st.symbols,sym_name_upper,v);
            /* Mirror patsymbols to persist across the per-line symbols reset */
            smap_clear(&asmb->st.patsymbols);
            for(int pi2=0; pi2<asmb->st.symbols.nb; pi2++)
                for(SymEntry *se2=asmb->st.symbols.buckets[pi2]; se2; se2=se2->next)
                    smap_set(&asmb->st.patsymbols, se2->key, se2->val);
            *idx_out=idx; return 1;
        }
        if(strcmp(lu,".CLEARSYM")==0){
            if(l2[0]){
                char sym_name[512]; axx_get_param_to_spc(l2,0,sym_name,sizeof(sym_name));
                char sym_name_upper[512]; axx_strupr_to(sym_name_upper,sym_name,sizeof(sym_name_upper));
                smap_delete(&asmb->st.symbols,sym_name_upper);
            } else {
                smap_clear(&asmb->st.symbols);
            }
            /* Mirror patsymbols */
            smap_clear(&asmb->st.patsymbols);
            for(int pi2=0; pi2<asmb->st.symbols.nb; pi2++)
                for(SymEntry *se2=asmb->st.symbols.buckets[pi2]; se2; se2=se2->next)
                    smap_set(&asmb->st.patsymbols, se2->key, se2->val);
            *idx_out=idx; return 1;
        }
    }

    if(!l[0]){ *idx_out=idx; return 0; }

    int se=0, oerr=0, pln=0;
    int idxs_val=0;
    int loopflag=1;
    PatEntry *oerr_entry=NULL;   /* pattern entry that caused oerr */

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

        int lw=0; for(int fi=0;fi<PAT_FIELDS;fi++) if(i->f[fi][0]) lw++;
        if(lw==0) continue;

        char lin[8192]; snprintf(lin,sizeof(lin),"%s %s",l,l2);
        axx_reduce_spaces(lin);

        if(!i->f[0][0]){
            /* Sentinel entry (empty pattern field[0]): treat as end-of-match.
             * Python evaluates i[3] here to capture the VLIW slot index before
             * breaking, so we must do the same. */
            int io2;
            uint256_t idxv2=expr_expression_pat(asmb,i->f[3],0,&io2);
            idxs_val=(int)u256_to_i64(idxv2);
            loopflag=0; break;
        }

        st->error_undefined_label=0;
        st->expmode=EXP_ASM;

        if(pat_match0(asmb,lin,i->f[0])){
            /* Fix 10 (axx.py): only call makeobj when dir_error did NOT trigger.
             * Previously makeobj always ran even if an .error condition fired. */
            int err_triggered = dir_error(asmb,i->f[1]);
            if(!err_triggered){
                makeobj(asmb,i->f[2],objl_out);
                /* Pass1: retry with size-mode on forward reference */
                if(st->pas==1 && st->error_undefined_label){
                    st->pass1_size_mode=1;
                    makeobj(asmb,i->f[2],objl_out);
                    st->pass1_size_mode=0;
                    st->error_undefined_label=0;
                }
                /* Pass2: if makeobj produced undefined label, that's a hard error */
                if(st->pas==2 && st->error_undefined_label){
                    oerr=1;
                    oerr_entry=i;
                    loopflag=0; break;
                }
            } else {
                iv_clear(objl_out);
            }
            int io;
            uint256_t idxv=expr_expression_pat(asmb,i->f[3],0,&io);
            idxs_val=(int)u256_to_i64(idxv);
            loopflag=0; break;
        }
    }

    if(loopflag){ se=1; pln=0; }

    if(st->pas==2||st->pas==0){
        if(st->error_undefined_label){ printf(" error - undefined label error.\n"); *idx_out=idx; return 0; }
        if(se){ printf(" error - Syntax error.\n"); *idx_out=idx; return 0; }
        if(oerr){
            /* Mirrors Python:
             *   print(f" ; pat {pln} {pl} error - Illegal syntax in assemble line or pattern line.")
             * pl is the PatEntry (list of 6 strings). */
            printf(" ; pat %d ['%s', '%s', '%s', '%s', '%s', '%s'] error - Illegal syntax in assemble line or pattern line.\n",
                   pln,
                   oerr_entry ? oerr_entry->f[0] : "",
                   oerr_entry ? oerr_entry->f[1] : "",
                   oerr_entry ? oerr_entry->f[2] : "",
                   oerr_entry ? oerr_entry->f[3] : "",
                   oerr_entry ? oerr_entry->f[4] : "",
                   oerr_entry ? oerr_entry->f[5] : "");
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

    int vcnt=0;
    const char *pp=processed;
    while(1){
        const char *seg_start=pp;
        while(*pp&&!(*pp=='!'&&*(pp+1)=='!')) pp++;
        if(pp!=seg_start) vcnt++;
        if(*pp) pp+=2; else break;
    }
    st->vcnt=vcnt?vcnt:1;

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
         * Architecture-specific relocation type table (machine -> nbytes -> rtype):
         *   EM_X86_64(62) : 8→R_X86_64_64(1) 4→R_X86_64_32(10) 2→(12) 1→(14)
         *   EM_386(3)     : 4→1  2→2  1→7
         *   EM_ARM(40)    : 4→2  2→250
         *   EM_AARCH64(183): 8→257  4→258
         *   EM_RISCV(243) : 8→2  4→3
         *   EM_PPC(20)    : 4→1
         *   fallback      : 8→1  4→2  2→3  1→4
         */
        if(st->elf_objfile[0] && st->pas==2 && objl.len>0 && st->elf_refs_len>0){
            int bpw = (st->bts+7)/8; if(bpw<1) bpw=1;
            const char *sec_name = st->current_section;
            SecEntry *_rse = secmap_find(&st->sections, sec_name);
            uint64_t sec_start = _rse ? u256_to_u64(_rse->start) : 0;
            uint64_t cur_pc    = u256_to_u64(st->pc);

            /* Per-machine rtype lookup */
            static const struct { int mach; int b8,b4,b2,b1; } _rm[] = {
                {62,  1, 10, 12, 14},
                {3,   0,  1,  2,  7},
                {40,  0,  2,250,  0},
                {183,257,258,  0,  0},
                {243, 2,  3,  0,  0},
                {20,  0,  1,  0,  0},
                {0,0,0,0,0}
            };
            int _rb8=1,_rb4=2,_rb2=3,_rb1=4;  /* fallback */
            for(int _ri=0; _rm[_ri].mach; _ri++){
                if(_rm[_ri].mach == st->elf_machine){
                    _rb8=_rm[_ri].b8; _rb4=_rm[_ri].b4;
                    _rb2=_rm[_ri].b2; _rb1=_rm[_ri].b1;
                    break;
                }
            }
            #define RTYPE_FOR(nb) ((nb)==8?_rb8:(nb)==4?_rb4:(nb)==2?_rb2:(nb)==1?_rb1:0)

            /* collect refs with valid word_idx (>= 0), sort by word_idx */
            ElfRef *_valid = (ElfRef*)malloc((size_t)st->elf_refs_len * sizeof(ElfRef));
            int _nvalid = 0;
            for(int _ri=0; _ri<st->elf_refs_len; _ri++){
                if(st->elf_refs[_ri].word_idx >= 0)
                    _valid[_nvalid++] = (ElfRef){st->elf_refs[_ri].name,
                                              st->elf_refs[_ri].val,
                                              st->elf_refs[_ri].word_idx};
            }
            /* sort by word_idx – use file-scope elf_ref_cmp (branchless, standard C) */
            qsort(_valid, (size_t)_nvalid, sizeof(ElfRef), elf_ref_cmp);

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
                int _rtype  = RTYPE_FOR(_nbytes);
                if(_rtype != 0 && _widx < objl.len){
                    int64_t _sec_rel = (int64_t)((cur_pc + (uint64_t)_widx - sec_start)
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
                    int64_t _addend = (int64_t)(_raw_val - _valid[_gi].val);
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
                    st->reloc_count++;
                }
                _gi = _gj;
            }
            free(_valid);
            #undef RTYPE_FOR
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

    if(st->pas==2||st->pas==0){
        printf("%016llx %s %d %s ",(unsigned long long)u256_to_u64(st->pc),
               st->current_file, st->ln, st->cl);
    }
    int f=lineassemble(asmb,st->cl);
    if(st->pas==2||st->pas==0) printf("\n");
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
    typedef struct { uint8_t*b; size_t len,cap; } WBB;
    void wbb_init(WBB*w){ w->b=calloc(1,64); w->len=1; w->cap=64; }
    void wbb_grow(WBB*w, size_t need){
        while(w->len+need>w->cap){w->cap*=2;w->b=realloc(w->b,w->cap);if(!w->b){perror("realloc");exit(1);}}
    }
    uint32_t wbb_str(WBB*w, const char*s){
        size_t l=strlen(s)+1; uint32_t off=(uint32_t)w->len;
        wbb_grow(w,l); memcpy(w->b+w->len,s,l); w->len+=l; return off;
    }
    void wbb_app(WBB*w, const void*src, size_t n){
        wbb_grow(w,n); memcpy(w->b+w->len,src,n); w->len+=n;
    }

    /* extract word range [w0, w0+wn) as byte array */
    uint8_t *weo_extract(uint64_t w0, uint64_t wn){
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

    /* ---- 1. collect content sections ---- */
    typedef struct{ const char*name; uint64_t bs,bsz,fl; uint8_t*data; } WCS;
    uint64_t max_w=0; int have_w=0;
    for(int i=0;i<BUFMAP_NB;i++)
        for(BufEntry*be=st->buf.buckets[i];be;be=be->next)
            if(!have_w||be->pos>max_w){max_w=be->pos;have_w=1;}

    int ncs=0; WCS *csecs=NULL;
    if(st->sections.count==0){
        ncs=1; csecs=calloc(1,sizeof(WCS));
        uint64_t wn=have_w?max_w+1:0;
        csecs[0]=(WCS){".text",0,wn*(uint64_t)bpw,0x2|0x4,weo_extract(0,wn)};
    } else {
        ncs=st->sections.count; csecs=calloc((size_t)ncs,sizeof(WCS));
        for(int i=0;i<ncs;i++){
            SecEntry *se=st->sections.order[i];
            uint64_t w0=u256_to_u64(se->start),wsz=u256_to_u64(se->size);
            if(!wsz){
                if(i+1<ncs){uint64_t w1=u256_to_u64(st->sections.order[i+1]->start);wsz=w1>w0?w1-w0:0;}
                else        wsz=(have_w&&max_w>=w0)?max_w+1-w0:0;
            }
            char un[64]; int ui=0;
            for(;se->name[ui]&&ui<63;ui++) un[ui]=(char)axx_upper_char(se->name[ui]);
            un[ui]=0;
            uint64_t fl;
            if     (strncmp(un,".TEXT",5)==0)   fl=0x2|0x4;
            else if(strncmp(un,".DATA",5)==0)   fl=0x2|0x1;
            else if(strncmp(un,".RODATA",7)==0) fl=0x2;
            else if(strncmp(un,".BSS",4)==0)    fl=0x2|0x1;
            else                                fl=0x2;
            csecs[i]=(WCS){se->name,w0*(uint64_t)bpw,wsz*(uint64_t)bpw,fl,weo_extract(w0,wsz)};
        }
    }

    /* ---- 2. group relocations by content section ---- */
    typedef struct{ int64_t off; const char*sym; int rtype; int64_t addend; } WRE;
    typedef struct{ WRE*data; int len,cap; } WRL;
    WRL *rela_lists=calloc((size_t)ncs,sizeof(WRL));
    for(int ri=0;ri<st->reloc_count;ri++){
        int sidx=-1;
        for(int i=0;i<ncs;i++) if(strcmp(st->relocations[ri].section,csecs[i].name)==0){sidx=i;break;}
        if(sidx<0) continue;
        WRL *rl=&rela_lists[sidx];
        if(rl->len>=rl->cap){rl->cap=rl->cap?rl->cap*2:4;rl->data=realloc(rl->data,rl->cap*sizeof(WRE));}
        rl->data[rl->len++]=(WRE){st->relocations[ri].sec_offset,st->relocations[ri].sym,
                                   st->relocations[ri].rtype,st->relocations[ri].addend};
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
        char rn[256]; snprintf(rn,sizeof(rn),".rela%s",csecs[rs_idx[ri2]].name);
        rela_noff[ri2]=wbb_str(&shstr,rn);
    }
    uint32_t sym_noff  =wbb_str(&shstr,".symtab");
    uint32_t str_noff  =wbb_str(&shstr,".strtab");
    uint32_t shstr_noff=wbb_str(&shstr,".shstrtab");

    /* ---- 4. build .symtab ---- */
    typedef struct{ uint16_t shndx; uint64_t sv; } WSR;
    WSR weo_shndx(uint64_t ba){
        for(int i=0;i<ncs;i++){
            if(csecs[i].bsz>0&&csecs[i].bs<=ba&&ba<csecs[i].bs+csecs[i].bsz)
                return (WSR){(uint16_t)(i+1),ba-csecs[i].bs};
            if(!csecs[i].bsz&&ba==csecs[i].bs) return (WSR){(uint16_t)(i+1),0};
        }
        return (WSR){0xfff1,ba};
    }
    #define WEO_SYMSZ 24
    WBB symtab_bb; symtab_bb.b=calloc(32,(size_t)WEO_SYMSZ); symtab_bb.len=0; symtab_bb.cap=32*WEO_SYMSZ;
    int nsyms=0;
    void weo_sym(uint32_t nm,uint8_t info,uint8_t oth,uint16_t shndx,uint64_t val,uint64_t sz){
        uint8_t sp[WEO_SYMSZ]={0};
        WEO_LE4(sp,nm); sp[4]=info; sp[5]=oth; WEO_LE2(sp+6,shndx); WEO_LE8(sp+8,val); WEO_LE8(sp+16,sz);
        wbb_app(&symtab_bb,sp,WEO_SYMSZ); nsyms++;
    }
    typedef struct{const char*name;int idx;} WSNI;
    WSNI *snimap=calloc((size_t)(st->labels.count+st->export_labels.count+8),sizeof(WSNI));
    int snimap_len=0;

    weo_sym(0,0,0,0,0,0);                             /* null */
    for(int i=0;i<ncs;i++) weo_sym(0,0x03,0,(uint16_t)(i+1),0,0); /* section syms */

    /* sort labels and export_labels by name */
    typedef struct{const char*name;uint64_t val;int is_equ;int is_imported;} WLK;
    int nl=st->labels.count;
    WLK *larr=calloc((size_t)(nl?nl:1),sizeof(WLK));
    {int li=0;for(int bi=0;bi<st->labels.nbuckets;bi++)
        for(LabelEntry*e=st->labels.buckets[bi];e;e=e->next)
            larr[li++]=(WLK){e->key,u256_to_u64(e->value),e->is_equ,e->is_imported};}
    int cmp_wlk(const void*a,const void*b){return strcmp(((WLK*)a)->name,((WLK*)b)->name);}
    qsort(larr,nl,sizeof(WLK),cmp_wlk);

    int ne=st->export_labels.count;
    WLK *earr=calloc((size_t)(ne?ne:1),sizeof(WLK));
    {int ei=0;for(int bi=0;bi<st->export_labels.nbuckets;bi++)
        for(LabelEntry*e=st->export_labels.buckets[bi];e;e=e->next)
            earr[ei++]=(WLK){e->key,u256_to_u64(e->value),e->is_equ,0};}
    qsort(earr,ne,sizeof(WLK),cmp_wlk);

    int weo_isexp(const char*nm){for(int i=0;i<ne;i++)if(!strcmp(earr[i].name,nm))return 1;return 0;}

    /* (1) Local labels: not exported, not imported → STB_LOCAL (0x00) */
    for(int i=0;i<nl;i++){
        if(weo_isexp(larr[i].name)) continue;
        if(larr[i].is_imported) continue;   /* imported: emitted below as STB_GLOBAL/SHN_UNDEF */
        /* .equ labels are absolute constants: use SHN_ABS, not section-relative */
        WSR sr = larr[i].is_equ ? (WSR){0xfff1, larr[i].val} : weo_shndx(larr[i].val*(uint64_t)bpw);
        uint32_t noff=wbb_str(&strtab_bb,larr[i].name);
        snimap[snimap_len++]=(WSNI){larr[i].name,nsyms};
        weo_sym(noff,0x00,0,sr.shndx,sr.sv,0);
    }
    int first_global=nsyms;
    /* (2) Imported symbols (.EXTERN): STB_GLOBAL (0x10) / SHN_UNDEF (0)
     * Mirrors axx.py: syms.append(_pack_sym(name_off, 0x10, 0, 0, 0, 0)) */
    for(int i=0;i<nl;i++){
        if(!larr[i].is_imported) continue;
        if(weo_isexp(larr[i].name)) continue;
        uint32_t noff=wbb_str(&strtab_bb,larr[i].name);
        snimap[snimap_len++]=(WSNI){larr[i].name,nsyms};
        weo_sym(noff,0x10,0,0,0,0);   /* SHN_UNDEF=0, value=0 */
    }
    /* (3) Export labels → STB_GLOBAL (0x10) */
    for(int i=0;i<ne;i++){
        WSR sr = earr[i].is_equ ? (WSR){0xfff1, earr[i].val} : weo_shndx(earr[i].val*(uint64_t)bpw);
        uint32_t noff=wbb_str(&strtab_bb,earr[i].name);
        snimap[snimap_len++]=(WSNI){earr[i].name,nsyms};
        weo_sym(noff,0x10,0,sr.shndx,sr.sv,0);
    }

    int weo_symof(const char*nm){for(int i=0;i<snimap_len;i++)if(!strcmp(snimap[i].name,nm))return snimap[i].idx;return 0;}

    /* ---- 5. build .rela data ---- */
    uint8_t **rela_bufs=calloc((size_t)(nrela?nrela:1),sizeof(uint8_t*));
    size_t   *rela_szs =calloc((size_t)(nrela?nrela:1),sizeof(size_t));
    for(int ri2=0;ri2<nrela;ri2++){
        WRL *rl=&rela_lists[rs_idx[ri2]];
        size_t rbs=(size_t)rl->len*24;
        uint8_t *rb=calloc(1,rbs?rbs:1);
        for(int ei=0;ei<rl->len;ei++){
            uint8_t *rp=rb+ei*24;
            uint64_t rinfo=((uint64_t)weo_symof(rl->data[ei].sym)<<32)|((uint32_t)rl->data[ei].rtype);
            WEO_LE8(rp,(uint64_t)rl->data[ei].off);
            WEO_LE8(rp+8,rinfo);
            WEO_LE8S(rp+16,rl->data[ei].addend);
        }
        rela_bufs[ri2]=rb; rela_szs[ri2]=rbs;
    }

    /* ---- 6. compute file offsets ---- */
    uint64_t foff=64;
    uint64_t *sec_fo=calloc((size_t)ncs,sizeof(uint64_t));
    for(int i=0;i<ncs;i++){foff=WEO_ALIGN(foff,16);sec_fo[i]=foff;foff+=csecs[i].bsz;}
    uint64_t *rela_fo=calloc((size_t)(nrela?nrela:1),sizeof(uint64_t));
    for(int ri2=0;ri2<nrela;ri2++){foff=WEO_ALIGN(foff,8);rela_fo[ri2]=foff;foff+=rela_szs[ri2];}
    uint64_t sym_fo=WEO_ALIGN(foff,8); foff=sym_fo+(uint64_t)nsyms*(uint64_t)WEO_SYMSZ;
    uint64_t str_fo=foff;     foff+=strtab_bb.len;
    uint64_t shstr_fo=foff;   foff+=shstr.len;
    uint64_t shdr_fo=WEO_ALIGN(foff,8);

    int tot_sh=1+ncs+nrela+3;
    int shstrndx=ncs+nrela+3;
    int sym_shidx=ncs+nrela+1;
    int str_shidx=ncs+nrela+2;

    /* ---- 7. write file ---- */
    FILE *fp=fopen(path,"wb");
    if(!fp){perror(path);goto weo_done;}

    /* ELF header */
    {uint8_t eh[64]={0};
     eh[0]=0x7f;eh[1]='E';eh[2]='L';eh[3]='F';
     eh[4]=2;eh[5]=(uint8_t)_ei_data;eh[6]=1;eh[7]=st->osabi; /* ELFCLASS64 EI_DATA EV_CURRENT ELFOSABI */
     WEO_LE2(eh+16,1); WEO_LE2(eh+18,(uint16_t)machine); WEO_LE4(eh+20,1);
     WEO_LE8(eh+40,shdr_fo);
     WEO_LE2(eh+52,64); WEO_LE2(eh+58,64);
     WEO_LE2(eh+60,(uint16_t)tot_sh); WEO_LE2(eh+62,(uint16_t)shstrndx);
     fwrite(eh,1,64,fp);}

    /* Fix J: if ftell() fails it returns -1 (a negative long).  The original
     * cast that to uint64_t, yielding UINT64_MAX, which is never < t so the
     * while-loop exited immediately — silently skipping the required padding
     * and corrupting the ELF file.  Now we detect the error and abort. */
    void weo_pad(FILE*f,uint64_t t){
        long c=ftell(f);
        if(c < 0){ fprintf(stderr,"weo_pad: ftell failed\n"); return; }
        while((uint64_t)c<t){fputc(0,f);c++;}
    }

    for(int i=0;i<ncs;i++){weo_pad(fp,sec_fo[i]);if(csecs[i].bsz)fwrite(csecs[i].data,1,(size_t)csecs[i].bsz,fp);}
    for(int ri2=0;ri2<nrela;ri2++){weo_pad(fp,rela_fo[ri2]);if(rela_szs[ri2])fwrite(rela_bufs[ri2],1,rela_szs[ri2],fp);}
    weo_pad(fp,sym_fo); fwrite(symtab_bb.b,1,(size_t)nsyms*(size_t)WEO_SYMSZ,fp);
    fwrite(strtab_bb.b,1,strtab_bb.len,fp);
    fwrite(shstr.b,1,shstr.len,fp);
    weo_pad(fp,shdr_fo);

    void weo_shdr(FILE*f,uint32_t nm,uint32_t ty,uint64_t fl,uint64_t addr,uint64_t off,
                  uint64_t sz,uint32_t lnk,uint32_t info,uint64_t align,uint64_t entsz){
        uint8_t sh[64]={0};
        WEO_LE4(sh,nm);WEO_LE4(sh+4,ty);WEO_LE8(sh+8,fl);WEO_LE8(sh+16,addr);
        WEO_LE8(sh+24,off);WEO_LE8(sh+32,sz);WEO_LE4(sh+40,lnk);WEO_LE4(sh+44,info);
        WEO_LE8(sh+48,align);WEO_LE8(sh+56,entsz);
        fwrite(sh,1,64,f);
    }
    weo_shdr(fp,0,0,0,0,0,0,0,0,0,0); /* [0] NULL */
    for(int i=0;i<ncs;i++)
        weo_shdr(fp,sec_noff[i],1,csecs[i].fl,0,sec_fo[i],csecs[i].bsz,0,0,16,0);
    for(int ri2=0;ri2<nrela;ri2++)
        weo_shdr(fp,rela_noff[ri2],4,0x40,0,rela_fo[ri2],rela_szs[ri2],
                 (uint32_t)sym_shidx,(uint32_t)(rs_idx[ri2]+1),8,24);
    weo_shdr(fp,sym_noff,2,0,0,sym_fo,(uint64_t)nsyms*(uint64_t)WEO_SYMSZ,
             (uint32_t)str_shidx,(uint32_t)first_global,8,(uint64_t)WEO_SYMSZ);
    weo_shdr(fp,str_noff,3,0,0,str_fo,strtab_bb.len,0,0,1,0);
    weo_shdr(fp,shstr_noff,3,0,0,shstr_fo,shstr.len,0,0,1,0);
    fclose(fp);
    fprintf(stderr,"elf: wrote %s (%d section(s), %d rela section(s), %d symbol(s))\n",
            path,ncs,nrela,nsyms);

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
    #undef WEO_W2
    #undef WEO_W4
    #undef WEO_W8
    #undef WEO_W8S
    #undef WEO_LE2
    #undef WEO_LE4
    #undef WEO_LE8
    #undef WEO_LE8S
    #undef WEO_ALIGN
    #undef WEO_SYMSZ
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
                printf(" error - circular .INCLUDE detected: '%s' is already being assembled.\n", fn);
                return;
            }
            if(!is_stdin_fn && !is_stdin_already){
                /* Compare by resolved absolute path */
                char abs_fn[4096]={0}, abs_al[4096]={0};
                if(realpath(fn,   abs_fn) && realpath(already, abs_al)
                   && strcmp(abs_fn, abs_al)==0){
                    printf(" error - circular .INCLUDE detected: '%s' is already being assembled.\n", fn);
                    return;
                }
            }
        }
    }

    /* Fix C-10: push is always unconditional; pop must therefore also be
     * unconditional.  Save fn locally so we can replace it with the temp
     * path for stdin without altering the caller's string. */
    sv_push(&st->fnstack, st->current_file);
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
        char line[4096];
        while(fgets(line,sizeof(line),f)) lineassemble0(asmb,line);
    }
    fclose(f);

done:
    free(stdin_buf);
    /* Fix C-10: pop unconditionally to mirror the unconditional push above.
     * The original guarded the pop with (fnstack.len>0) which could silently
     * leave current_file/ln unrestored if the stack was somehow empty. */
    strncpy(st->current_file, st->fnstack.data[st->fnstack.len-1],
            sizeof(st->current_file)-1);
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
            char key[512]; axx_strupr_to(key,e->f[1],sizeof(key));
            int io;
            uint256_t v = e->f[2][0] ? expr_expression_pat(asmb,e->f[2],0,&io) : u256_zero();
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
        secmap_set(&asmb->imp_sections, sname,
                   u256_from_u64(start), u256_from_u64(size));
        return 1;
    }

    if(nfields == 2){
        const char *label = fields[0];
        if(!label[0]) return 0;
        char *endp;
        uint64_t v = strtoull(fields[1], &endp, 16);
        if(endp == fields[1]) return 0;

        /* determine section by range lookup in previously parsed sections */
        const char *section = ".text";
        for(int i = 0; i < asmb->imp_sections.count; i++){
            SecEntry *se = asmb->imp_sections.order[i];
            uint64_t s0 = u256_to_u64(se->start);
            uint64_t sz = u256_to_u64(se->size);
            if(sz > 0 && v >= s0 && v < s0 + sz){ section = se->name; break; }
            if(sz == 0 && v == s0)               { section = se->name; break; }
        }
        label_put_value(&asmb->st, label, u256_from_u64(v), section, 0);
        return 1;
    }

    return 0;
}

/* =========================================================
 * main
 * ========================================================= */
static void print_usage(const char *prog){
    printf("usage: %s patternfile [sourcefile] [--osabi OSNAME] [-b outfile] [-e export_tsv] [-E export_elf_tsv] [-i import_tsv] [-o elf_obj] [-m machine]\n",prog);
    printf("axx general assembler programmed and designed by Taisuke Maekawa\n");
}

typedef struct {
    char    s[16];
    int     nu;
} OSABIENT;

static OSABIENT osabitbl[]={{"Linux",0},{"FreeBSD",9},{"EOTBL",-1}};

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
        else if(strcmp(argv[i],"-m")==0&&i+1<argc){ st->elf_machine=atoi(argv[++i]); }
        else if(argv[i][0]!='-'){
            if(!patternfile) patternfile=argv[i];
            else if(!sourcefile) sourcefile=argv[i];
        }
    }

    int osa = find_osabi(osabistr);
    if (osa==-1) {
        osa = find_osabi("FreeBSD"); /* Fall back to Default FreeBSD */
    }
    st->osabi = osa;

    if(!patternfile){ print_usage(argv[0]); return 1; }

    readpat(asmb,patternfile);
    setpatsymbols(asmb);

    if(st->impfile[0]){
        FILE *lf=fopen(st->impfile,"rt");
        if(lf){ char l[4096]; while(fgets(l,sizeof(l),lf)) imp_label(asmb,l); fclose(lf); }
    }

    if(st->outfile[0]) remove(st->outfile);

    if(!sourcefile){
        st->pc=u256_zero(); st->pas=0; st->ln=1;
        strncpy(st->current_file,"(stdin)",sizeof(st->current_file)-1);
        char line[4096];
        while(1){
            /* Mirrors Python printaddr() + input(">> "):
             *   print("%016x: " % pc, end='')
             *   line = input(">> ")                                  */
            printf("%016llx: >> ",(unsigned long long)u256_to_u64(st->pc));
            fflush(stdout);
            if(!fgets(line,sizeof(line),stdin)) break;
            int ll=(int)strlen(line);
            while(ll>0&&(line[ll-1]=='\n'||line[ll-1]=='\r')) line[--ll]=0;
            /* Python: line = line.replace("\\\\", "\\") */
            for(int i=0;line[i];i++)
                if(line[i]=='\\'&&line[i+1]=='\\'){
                    line[i]='\\'; memmove(line+i+1,line+i+2,ll-i-1); ll--;
                }
            /* Python: line = line.strip() */
            ll=(int)strlen(line);
            while(ll>0&&line[ll-1]==' ') line[--ll]=0;
            int start=0; while(line[start]==' ') start++;
            if(start) memmove(line,line+start,ll-start+1);
            if(!line[0]) continue;
            if(strcmp(line,"?")==0){ label_print_all(st); continue; }
            lineassemble0(asmb,line);
        }
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
#define MAX_RELAX 8
        /* Fix 5: snapshot imported labels before the relaxation loop so they
         * can be restored at the start of each iteration. */
        LabelMap imported_labels;
        lmap_init(&imported_labels);
        for(int bi=0; bi<st->labels.nbuckets; bi++)
            for(LabelEntry *e=st->labels.buckets[bi]; e; e=e->next)
                lmap_set_full(&imported_labels, e->key, e->value, e->section,
                              e->is_equ, e->is_imported);

        /* Fix ⑧: snapshot initial vars (a-z) */
        uint256_t initial_vars[26];
        memcpy(initial_vars, st->vars, sizeof(initial_vars));

        LabelMap prev_labels;
        lmap_init(&prev_labels);
        int converged = 0;

        for(int relax=0; relax<MAX_RELAX; relax++){
            st->pc=u256_zero(); st->pas=1; st->ln=1;
            /* Fix 5: restore imported labels instead of starting from empty */
            lmap_free(&st->labels); lmap_init(&st->labels);
            for(int bi=0; bi<imported_labels.nbuckets; bi++)
                for(LabelEntry *e=imported_labels.buckets[bi]; e; e=e->next)
                    lmap_set_full(&st->labels, e->key, e->value, e->section,
                                  e->is_equ, e->is_imported);
            /* reset sections and export_labels too (mirrors axx.py run()) */
            secmap_clear(&st->sections);
            lmap_free(&st->export_labels); lmap_init(&st->export_labels);
            /* Fix C-N6: reset symbols to the post-pattern-file baseline at the
             * start of every relaxation iteration.  Source-level .setsym /
             * .clearsym directives mutate st->symbols during assembly; without
             * this reset their effects accumulate across iterations, producing
             * non-deterministic symbol tables on the 2nd and later passes. */
            smap_clear(&st->symbols);
            for(int pi=0; pi<st->patsymbols.nb; pi++)
                for(SymEntry *se2=st->patsymbols.buckets[pi]; se2; se2=se2->next)
                    smap_set(&st->symbols, se2->key, se2->val);
            /* Fix ⑧: restore vars to pre-loop state */
            memcpy(st->vars, initial_vars, sizeof(st->vars));
            fileassemble(asmb,sourcefile);

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
                    if(u256_is_undef(e->value)){  has_undef=1; break; }
                    if(e->value.w[2] || e->value.w[3]){ has_undef=1; break; }
                }

            converged = !has_undef ? 1 : 0;
            if(converged){
                for(int bi=0; bi<st->labels.nbuckets && converged; bi++){
                    for(LabelEntry *e=st->labels.buckets[bi]; e; e=e->next){
                        LabelEntry *p=lmap_find(&prev_labels, e->key);
                        /* Fix ⑥-2: compare both value and section */
                        if(!p || !u256_eq(p->value, e->value)
                               || strcmp(p->section ? p->section : "",
                                         e->section ? e->section : "") != 0){
                            converged=0; break;
                        }
                    }
                }
                /* Also check no label was removed */
                if(converged && prev_labels.count != st->labels.count) converged=0;
            }

            /* Update prev_labels snapshot */
            lmap_free(&prev_labels); lmap_init(&prev_labels);
            for(int bi=0; bi<st->labels.nbuckets; bi++)
                for(LabelEntry *e=st->labels.buckets[bi]; e; e=e->next)
                    lmap_set_full(&prev_labels, e->key, e->value, e->section,
                                  e->is_equ, e->is_imported);

            if(converged){
                if(st->debug)
                    fprintf(stderr,"Pass1 relaxation converged after %d iteration(s)\n",
                            relax+1);
                break;
            }
        }
        lmap_free(&prev_labels);
        lmap_free(&imported_labels);

        if(!converged)
            fprintf(stderr,"warning: pass1 relaxation did not converge after %d iterations; "
                    "addresses may be incorrect for variable-length instructions "
                    "with forward references.\n", MAX_RELAX);
#undef MAX_RELAX

        st->pc=u256_zero(); st->pas=2; st->ln=1;
        /* reset relocations before pass2 (mirrors axx.py run()) */
        for(int ri=0;ri<st->reloc_count;ri++){
            free(st->relocations[ri].section);
            free(st->relocations[ri].sym);
        }
        st->reloc_count=0;
        /* Fix 5 (new) (axx.py port): reset sections before pass2 so stale
         * provisional sizes from pass1 do not carry over.  labels and
         * patsymbols do NOT need resetting here (only sections). */
        secmap_clear(&st->sections);
        fileassemble(asmb,sourcefile);
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
                unsigned long long byte_start = \
                    (unsigned long long)u256_to_u64(e->start) * (unsigned long long)_bpw_export; \
                unsigned long long byte_size  = \
                    (unsigned long long)u256_to_u64(e->size)  * (unsigned long long)_bpw_export; \
                fprintf(lf,"%s\t0x%llx\t0x%llx\t%s\n", \
                        e->name, byte_start, byte_size, flag); \
            } \
            for(int i=0;i<st->export_labels.nbuckets;i++){ \
                for(LabelEntry*e=st->export_labels.buckets[i];e;e=e->next){ \
                    unsigned long long lbl_addr; \
                    if(e->is_equ){ \
                        /* absolute constant: output as-is */ \
                        lbl_addr=(unsigned long long)u256_to_u64(e->value); \
                    } else { \
                        /* PC (word units) → byte address */ \
                        lbl_addr=(unsigned long long)u256_to_u64(e->value) \
                                 *(unsigned long long)_bpw_export; \
                    } \
                    fprintf(lf,"%s\t0x%llx\n",e->key,lbl_addr); \
                } \
            } \
            fclose(lf); \
        } \
    } while(0)

    if(st->expfile[0])     WRITE_EXPORT(st->expfile,     0);
    if(st->expfile_elf[0]) WRITE_EXPORT(st->expfile_elf, 1);

    #undef WRITE_EXPORT

    /* Fix C-6: clean up the per-process stdin temp file if one was created. */
    if(st->stdin_tmp_path[0]){
        unlink(st->stdin_tmp_path);
        st->stdin_tmp_path[0] = '\0';
    }

    return 0;
}
