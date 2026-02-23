/*
 * axx general assembler designed and programmed by Taisuke Maekawa
 * C translation (complete, behavior-compatible)
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
/* signed compare: treat as two's-complement 256-bit */
static int u256_lt_signed(uint256_t a, uint256_t b) {
    /* compare word by word from MSW */
    /* sign bit in w[3] bit63 */
    int sa = (int)(a.w[3] >> 63);
    int sb = (int)(b.w[3] >> 63);
    if (sa != sb) return sa > sb; /* negative < positive */
    /* same sign: magnitude compare */
    if (a.w[3] != b.w[3]) return (sa ? a.w[3] > b.w[3] : a.w[3] < b.w[3]);
    if (a.w[2] != b.w[2]) return (sa ? a.w[2] > b.w[2] : a.w[2] < b.w[2]);
    if (a.w[1] != b.w[1]) return (sa ? a.w[1] > b.w[1] : a.w[1] < b.w[1]);
    return (sa ? a.w[0] > b.w[0] : a.w[0] < b.w[0]);
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
    /* two's complement negation */
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
    /* for Python big-int semantics: just use unsigned mul (lower bits same) */
    return u256_mul(a,b);
}
/* unsigned divide: a // b */
static uint256_t u256_udiv(uint256_t a, uint256_t b) {
    /* Simple bit-by-bit division */
    if (u256_is_zero(b)) return u256_zero();
    uint256_t q = u256_zero();
    uint256_t r = u256_zero();
    for (int i=255; i>=0; i--) {
        r = u256_shl(r,1);
        /* set bit i of r's lsb from a */
        int wi = i/64, bi = i%64;
        r.w[0] |= ((a.w[wi]>>bi)&1);
        /* unsigned compare: r >= b? */
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
    /* adjust for signs (Python floor division) */
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
/* power: a**b (capped at reasonable size) */
static uint256_t u256_pow(uint256_t base, uint256_t exp) {
    uint256_t r = u256_one();
    /* only use low 16 bits of exp to avoid infinite loops */
    uint64_t e = exp.w[0] & 0xffff;
    while(e){
        if(e&1) r=u256_mul(r,base);
        base=u256_mul(base,base);
        e>>=1;
    }
    return r;
}

/* Convert to int64 (sign-extended from lower 64 bits for printing etc.) */
static int64_t u256_to_i64(uint256_t a) { return (int64_t)a.w[0]; }
static uint64_t u256_to_u64(uint256_t a) { return a.w[0]; }

/* nbit: number of bits needed */
static int u256_nbit(uint256_t v) {
    /* if negative, treat as positive for bit counting */
    if ((v.w[3]>>63)) v = u256_neg(v);
    int b=0;
    uint256_t r=v;
    while(!u256_is_zero(r)){ r=u256_sar(r,1); b++; }
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
static void ds_free(DynStr *d) { free(d->buf); ds_init(d); }
static void ds_ensure(DynStr *d, size_t need) {
    if (d->cap >= need+1) return;
    size_t nc = (need+1)*2;
    if(nc<32)nc=32;
    d->buf = realloc(d->buf, nc);
    if(!d->buf){perror("realloc");exit(1);}
    d->cap = nc;
}
static void ds_set(DynStr *d, const char *s) {
    size_t l = strlen(s);
    ds_ensure(d, l);
    memcpy(d->buf, s, l+1);
    d->len = l;
}
static void ds_setc(DynStr *d, char c) {
    ds_ensure(d,1);
    d->buf[0]=c; d->buf[1]=0; d->len=1;
}
static void ds_append(DynStr *d, const char *s) {
    size_t l=strlen(s);
    ds_ensure(d, d->len+l);
    memcpy(d->buf+d->len, s, l+1);
    d->len+=l;
}
static void ds_appendc(DynStr *d, char c) {
    ds_ensure(d, d->len+1);
    d->buf[d->len++]=c;
    d->buf[d->len]=0;
}
static const char *ds_get(const DynStr *d) { return d->buf ? d->buf : ""; }

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
static void iv_append(IntVec *dst, const IntVec *src) {
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
static void sv_free(StrVec *v){
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
static void lmap_free(LabelMap *m) {
    for(int i=0;i<m->nbuckets;i++){
        LabelEntry *e=m->buckets[i];
        while(e){ LabelEntry*n=e->next; free(e->key); free(e->section); free(e); e=n;}
    }
    free(m->buckets); m->buckets=NULL; m->count=0;
}
static LabelEntry *lmap_find(LabelMap *m, const char *key) {
    uint32_t h=hash_str(key)%(uint32_t)m->nbuckets;
    for(LabelEntry*e=m->buckets[h];e;e=e->next)
        if(strcmp(e->key,key)==0) return e;
    return NULL;
}
static int lmap_contains(LabelMap *m, const char *key) { return lmap_find(m,key)!=NULL; }
static void lmap_set(LabelMap *m, const char *key, uint256_t val, const char *sec) {
    uint32_t h=hash_str(key)%(uint32_t)m->nbuckets;
    for(LabelEntry*e=m->buckets[h];e;e=e->next){
        if(strcmp(e->key,key)==0){
            e->value=val; free(e->section); e->section=strdup(sec); return;
        }
    }
    LabelEntry *e=calloc(1,sizeof(LabelEntry));
    e->key=strdup(key); e->value=val; e->section=strdup(sec);
    e->next=m->buckets[h]; m->buckets[h]=e; m->count++;
}
static void lmap_delete(LabelMap *m, const char *key) {
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
/* iterate all entries */
typedef void (*lmap_iter_fn)(const char*key, uint256_t val, const char*sec, void*user);
static void lmap_iter(LabelMap *m, lmap_iter_fn fn, void*user){
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
static void pv_free(PatVec*v){
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
static void vset_free(VliwSet*v){
    for(int i=0;i<v->len;i++){free(v->data[i].idxs);free(v->data[i].templ);}
    free(v->data);vset_init(v);
}
static void vset_clear(VliwSet*v){
    for(int i=0;i<v->len;i++){free(v->data[i].idxs);free(v->data[i].templ);}
    v->len=0;
}
static void vset_add(VliwSet*v,int*idxs,int n,const char*templ){
    /* check duplicate */
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
static uint64_t bufmap_max_key(BufMap*m){
    uint64_t mx=0; int found=0;
    for(int i=0;i<BUFMAP_NB;i++) for(BufEntry*e=m->buckets[i];e;e=e->next){
        if(!found||e->pos>mx){mx=e->pos;found=1;}
    }
    return found?mx:0;
}
static void bufmap_free(BufMap*m){
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
    "Value out of range.",
    "Invalid syntax.",
    "Address out of range.",
    "",
    "",
    "Register out of range.",
    "Port number out of range."
};
#define ERRORS_COUNT 7

typedef struct {
    /* file paths */
    char outfile[512];
    char expfile[512];
    char impfile[512];

    /* program counter, padding */
    uint256_t pc;
    uint256_t padding;

    /* character sets */
    char lwordchars[256];   /* dynamic, null-terminated */
    char swordchars[256];

    /* current context */
    char current_section[512];
    char current_file[512];

    /* data structures */
    LabelMap   labels;
    SecMap     sections;
    SymMap     symbols;
    SymMap     patsymbols;
    LabelMap   export_labels;
    PatVec     pat;

    /* VLIW */
    int        vliwinstbits;
    IntVec     vliwnop;
    int        vliwbits;
    VliwSet    vliwset;
    int        vliwflag;
    int        vliwtemplatebits;
    int        vliwstop;
    int        vcnt;

    /* expression mode & errors */
    int        expmode;
    int        error_undefined_label;
    int        error_already_defined;

    /* assembly config */
    int        align;
    int        bts;
    int        endian_big;   /* 0=little, 1=big */
    int        pas;
    int        debug;

    /* current line info */
    char       cl[4096];
    int        ln;
    StrVec     fnstack;
    IStack     lnstack;

    /* variables a-z (26) */
    uint256_t  vars[26];

    /* debug */
    char deb1[4096];
    char deb2[4096];

    /* binary buffer */
    BufMap     buf;
} AsmState;

static void state_init(AsmState *st) {
    memset(st, 0, sizeof(*st));
    /* character sets */
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
    st->align = 16;
    st->bts = 8;
    st->endian_big = 0;
    st->pas = 0;
    st->debug = 0;
    st->ln = 0;
    sv_init(&st->fnstack);
    is_init(&st->lnstack);
    for(int i=0;i<26;i++) st->vars[i]=u256_zero();
    bufmap_init(&st->buf);
    st->pc = u256_zero();
    st->padding = u256_zero();
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
static int is_alpha(char c){ return (c>='A'&&c<='Z')||(c>='a'&&c<='z'); }

/* convert string to uppercase in-place, return s */
static char *axx_strupr(char *s) {
    for(char*p=s;*p;p++) *p=axx_upper_char(*p);
    return s;
}
/* uppercased copy into dst */
static void axx_strupr_to(char *dst, const char *src, size_t maxlen) {
    size_t i=0;
    for(;src[i]&&i<maxlen-1;i++) dst[i]=axx_upper_char(src[i]);
    dst[i]=0;
}

static int axx_q(const char *s, int slen, const char *t, int idx) {
    /* case-insensitive prefix match of t at s[idx] */
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

/* reduce_spaces: collapse whitespace runs to single space */
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

/* remove_comment: /* style */
static void axx_remove_comment(char *l) {
    for(int i=0;l[i];i++){
        if(l[i]=='/'&&l[i+1]=='*'){
            l[i]=0; return;
        }
    }
}

/* remove_comment_asm: ; style, preserve inside " */
static void axx_remove_comment_asm(char *l) {
    int in_str=0;
    for(int i=0;l[i];i++){
        if(l[i]=='"') in_str=!in_str;
        else if(l[i]==';'&&!in_str){
            /* rstrip before cut */
            int j=i-1;
            while(j>=0&&(l[j]==' '||l[j]=='\t')) j--;
            l[j+1]=0; return;
        }
    }
    /* rstrip */
    int j=(int)strlen(l)-1;
    while(j>=0&&(l[j]==' '||l[j]=='\t'||l[j]=='\n'||l[j]=='\r')) l[j--]=0;
}

/* get_param_to_spc: fill t, return new idx */
static int axx_get_param_to_spc(const char *s, int idx, char *t, size_t tsz) {
    idx=axx_skipspc(s,idx);
    size_t n=0;
    while(s[idx]&&s[idx]!=' '&&n<tsz-1) t[n++]=s[idx++];
    t[n]=0;
    return idx;
}

/* get_param_to_eon: up to !! or end */
static int axx_get_param_to_eon(const char *s, int idx, char *t, size_t tsz) {
    idx=axx_skipspc(s,idx);
    size_t n=0;
    while(s[idx]&&!(s[idx]=='!'&&s[idx+1]=='!')&&n<tsz-1) t[n++]=s[idx++];
    /* rstrip */
    while(n>0&&(t[n-1]==' '||t[n-1]=='\t')) n--;
    t[n]=0;
    return idx;
}

/* get_string: extract quoted string */
static void axx_get_string(const char *l2, char *out, size_t osz) {
    int idx=axx_skipspc(l2,0);
    out[0]=0;
    if(!l2[idx]||l2[idx]!='"') return;
    idx++;
    size_t n=0;
    while(l2[idx]&&l2[idx]!='"'&&n<osz-1) out[n++]=l2[idx++];
    out[n]=0;
}

/* =========================================================
 * Parser helpers (stateful: need lwordchars/swordchars)
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
    if(strncmp(s+idx,"inf",3)==0){strcpy(fs,"inf");return idx+3;}
    if(strncmp(s+idx,"-inf",4)==0){strcpy(fs,"-inf");return idx+4;}
    if(strncmp(s+idx,"nan",3)==0){strcpy(fs,"nan");return idx+3;}
    size_t n=0;
    if(s[idx]=='-'){fs[n++]='-';idx++;}
    while(s[idx]&&(is_digit(s[idx])||s[idx]=='.')&&n<fsz-1) fs[n++]=s[idx++];
    if(s[idx]=='e'||s[idx]=='E'){
        fs[n++]=s[idx++];
        if((s[idx]=='+'||s[idx]=='-')&&n<fsz-1) fs[n++]=s[idx++];
        while(s[idx]&&is_digit(s[idx])&&n<fsz-1) fs[n++]=s[idx++];
    }
    fs[n]=0;
    return idx;
}

static int axx_get_curlb(const char *s, int idx, int *f_out, char *t_out, size_t tsz){
    idx=axx_skipspc(s,idx);
    *f_out=0; t_out[0]=0;
    if(s[idx]!='{') return idx;
    idx++;
    *f_out=1;
    idx=axx_skipspc(s,idx);
    size_t n=0;
    while(s[idx]&&s[idx]!='}'&&n<tsz-1) t_out[n++]=s[idx++];
    /* rstrip */
    while(n>0&&t_out[n-1]==' ') n--;
    t_out[n]=0;
    idx=axx_skipspc(s,idx);
    if(s[idx]=='}') idx++;
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
    /* consume ':' only if not followed by '=' */
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
    /* rstrip */
    while(n>0&&(s_out[n-1]==' '||s_out[n-1]=='\t')) n--;
    s_out[n]=0;
    return idx;
}

/* =========================================================
 * IEEE754 conversion
 * ========================================================= */
static uint32_t ieee754_32_from_str(const char *a){
    if(strcmp(a,"inf")==0) return 0x7F800000u;
    if(strcmp(a,"-inf")==0) return 0xFF800000u;
    if(strcmp(a,"nan")==0) return 0x7FC00000u;
    float f=(float)strtod(a,NULL);
    uint32_t r; memcpy(&r,&f,4); return r;
}
static uint64_t ieee754_64_from_str(const char *a){
    if(strcmp(a,"inf")==0) return 0x7FF0000000000000ULL;
    if(strcmp(a,"-inf")==0) return 0xFFF0000000000000ULL;
    if(strcmp(a,"nan")==0) return 0x7FF8000000000000ULL;
    double d=strtod(a,NULL);
    uint64_t r; memcpy(&r,&d,8); return r;
}

/* IEEE754 binary128 from string via Python/mpmath for full 112-bit mantissa precision.
 *
 * long double (x86-64 extended) has only 64 bits of mantissa, which is far
 * less than the 112 bits binary128 requires.  Repeating decimals like 3.14
 * would have their lower ~48 mantissa bits all-zero with a pure C approach.
 * We therefore delegate to Python mpmath which supports arbitrary precision.
 *
 * The Python script prints 16 hex bytes (little-endian) representing the
 * binary128 bit pattern, which we parse back into a uint256_t.
 *
 * Special values (inf, -inf, nan) are handled directly in C.
 */
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

    /* Escape the expression string for embedding in a Python string literal */
    size_t alen = strlen(a);
    char *esc = malloc(alen * 2 + 4);
    size_t ei = 0;
    for(size_t k = 0; k < alen; k++){
        if(a[k]=='\\'||a[k]=='"'||a[k]=='\'') esc[ei++]='\\';
        esc[ei++] = a[k];
    }
    esc[ei] = '\0';

    /* Build python3 command:
     *   from mpmath import mp, mpf
     *   mp.prec = 128
     *   x = mpf('<value>')
     *   ... encode as binary128 little-endian hex bytes ...
     *   print(16 space-separated hex bytes)
     */
    size_t cmdcap = ei + 1024;
    char *cmd = malloc(cmdcap);
    snprintf(cmd, cmdcap,
        "python3 -c \""
        "from mpmath import mp,mpf\n"
        "mp.prec=128\n"
        "x=mpf('%s')\n"
        "sign=1 if x<0 else 0\n"
        "x=abs(x)\n"
        "if x==0:\n"
        "  print(' '.join(['0x00']*16))\n"
        "else:\n"
        "  import math\n"
        "  e=int(math.floor(float(mp.log(x,2))))\n"
        "  from mpmath import log,floor,power\n"
        "  e=int(floor(log(x,2)))\n"
        "  norm=x/power(2,e)\n"
        "  if norm>=2: e+=1; norm/=2\n"
        "  if norm<1:  e-=1; norm*=2\n"
        "  biased=e+16383\n"
        "  frac=norm-1\n"
        "  hi=0\n"
        "  for i in range(47,-1,-1):\n"
        "    frac*=2\n"
        "    if frac>=1: hi|=(1<<i); frac-=1\n"
        "  lo=0\n"
        "  for i in range(63,-1,-1):\n"
        "    frac*=2\n"
        "    if frac>=1: lo|=(1<<i); frac-=1\n"
        "  w1=(biased<<48)|hi\n"
        "  w0=lo\n"
        "  if sign: w1|=(1<<63)\n"
        "  bs=[]\n"
        "  for i in range(8): bs.append(w0&0xff); w0>>=8\n"
        "  for i in range(8): bs.append(w1&0xff); w1>>=8\n"
        "  print(' '.join('0x%%02X'%%b for b in bs))\n"
        "\"",
        esc);

    uint256_t result = u256_zero();
    FILE *fp = popen(cmd, "r");
    if(fp){
        char buf[256] = {0};
        if(fgets(buf, sizeof(buf), fp)){
            /* Parse 16 space-separated hex bytes (little-endian) */
            unsigned char bytes[16] = {0};
            int nb = 0;
            char *p = buf;
            while(nb < 16 && *p){
                while(*p==' '||*p=='\t') p++;
                if(!*p||*p=='\n') break;
                bytes[nb++] = (unsigned char)strtol(p, &p, 16);
            }
            if(nb == 16){
                /* little-endian: bytes[0..7]=w[0] LSB first, bytes[8..15]=w[1] LSB first */
                for(int wi=0; wi<2; wi++){
                    uint64_t w = 0;
                    for(int bi=7; bi>=0; bi--)
                        w = (w<<8) | bytes[wi*8 + bi];
                    result.w[wi] = w;
                }
            }
        }
        pclose(fp);
    } else {
        fprintf(stderr, "ieee754_128_from_str: popen failed for '%s'\n", a);
        /* fallback: use long double (reduced precision) */
        long double ld = strtold(a, NULL);
        int sign2 = (ld < 0.0L) ? 1 : 0;
        if(ld < 0.0L) ld = -ld;
        int fe; frexpl(ld, &fe);
        int exp_unbiased = fe - 1;
        long double norm = ld / powl(2.0L,(long double)exp_unbiased);
        int biased_exp = exp_unbiased + 16383;
        long double frac_part = norm - 1.0L;
        uint64_t hi=0, lo=0;
        for(int b=47;b>=0;b--){ frac_part*=2.0L; if(frac_part>=1.0L){hi|=((uint64_t)1<<b);frac_part-=1.0L;} }
        for(int b=63;b>=0;b--){ frac_part*=2.0L; if(frac_part>=1.0L){lo|=((uint64_t)1<<b);frac_part-=1.0L;} }
        result.w[0]=lo; result.w[1]=(hi&0x0000FFFFFFFFFFFFull)|((uint64_t)biased_exp<<48);
        if(sign2) result.w[1]|=0x8000000000000000ULL;
    }

    free(esc);
    free(cmd);
    return result;
}

/* enfloat / endouble: reinterpret bits as float/double */
static double enfloat_bits(uint64_t a){
    uint32_t u=(uint32_t)a; float f; memcpy(&f,&u,4); return (double)f;
}
static double endouble_bits(uint64_t a){
    double d; memcpy(&d,&a,8); return d;
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
 * Assembler struct (all sub-objects are just pointers into state)
 * ========================================================= */
struct Assembler {
    AsmState st;
};

static void assembler_init(Assembler *a){
    state_init(&a->st);
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
    uint64_t max_pos = bufmap_max_key(&st->buf);
    int word_bits = st->bts;
    int bytes_per_word = (word_bits+7)/8;
    uint64_t total_size = (max_pos+1)*(uint64_t)bytes_per_word;
    if(total_size==0) return;
    unsigned char *data = calloc(1, (size_t)total_size);
    if(!data){perror("calloc");return;}
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
    if(e) return e->value;
    st->error_undefined_label=1;
    return UNDEF_VAL();
}
static const char *label_get_section(AsmState *st, const char *k){
    st->error_undefined_label=0;
    LabelEntry *e=lmap_find(&st->labels,k);
    if(e) return e->section;
    st->error_undefined_label=1;
    return "";
}
static int label_put_value(AsmState *st, const char *k, uint256_t v, const char *sec){
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
    /* check patsymbols */
    char uk[512]; axx_strupr_to(uk,k,sizeof(uk));
    uint256_t dummy;
    if(smap_get(&st->patsymbols,uk,&dummy)){
        printf(" error - '%s' is a pattern file symbol.\n",k);
        return 0;
    }
    st->error_already_defined=0;
    lmap_set(&st->labels,k,v,sec);
    return 1;
}
static void label_print_all(AsmState *st){
    for(int i=0;i<st->labels.nbuckets;i++){
        for(LabelEntry*e=st->labels.buckets[i];e;e=e->next){
            /* print hex of value (lower 64 bits) */
            printf("'%s': [0x%llx, '%s']\n",
                   e->key,(unsigned long long)u256_to_u64(e->value),e->section);
        }
    }
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

/* terminate: append NUL if not already present */
static char *expr_terminate(const char *s){
    /* return malloced copy with NUL appended */
    size_t l=strlen(s);
    if(l>0&&s[l-1]=='\0') return strdup(s);
    char *r=malloc(l+2); memcpy(r,s,l); r[l]='\0'; r[l+1]=0;
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
static uint256_t expr_expression_esc(Assembler *asmb, const char *s, int idx, char stopchar, int *idx_out){
    /* Replace stopchar at bracket/paren depth==0 with NUL so the expression
       evaluator stops there.
       IMPORTANT: bracket depth must be counted starting from `idx`, not from
       the beginning of `s`.  The caller (pat_match) passes the full `lin`
       string but positions `idx` already past an opening '['.  Counting from
       i=0 would see that '[' and mistakenly increment bracket_depth, causing
       the matching ']' to be treated as an inner bracket instead of the
       stopchar. */
    size_t l = strlen(s);
    char *buf = malloc(l + 2);
    /* Copy the prefix [0..idx) verbatim -- no stopchar processing needed there */
    memcpy(buf, s, idx);
    int depth = 0;
    int bracket_depth = 0;
    for(size_t i = (size_t)idx; i < l; i++){
        if(s[i]=='(') { depth++; buf[i]=s[i]; }
        else if(s[i]==')') { if(depth>0) depth--; buf[i]=s[i]; }
        else if(s[i]=='[') { bracket_depth++; buf[i]=s[i]; }
        else if(s[i]==']') {
            if(bracket_depth>0){ bracket_depth--; buf[i]=s[i]; }
            else if(depth==0 && stopchar==']') buf[i]='\0';
            else buf[i]=s[i];
        }
        else if(depth==0 && bracket_depth==0 && s[i]==stopchar) buf[i]='\0';
        else buf[i]=s[i];
    }
    buf[l] = '\0';
    char *ts = expr_terminate(buf);
    free(buf);
    uint256_t r = expr_expression(asmb, ts, idx, idx_out);
    free(ts);
    return r;
}

/* =========================================================
 * xeval: evaluate flt{}/dbl{} expression via Python's eval().
 *
 * Before calling Python, :labelname tokens are replaced with
 * their numeric values (as decimal integers) so that Python
 * sees a plain arithmetic expression.
 *
 * enfloat() and endouble() are injected as Python helper
 * functions in the exec context so Python can evaluate them.
 *
 * Example transformations before Python eval():
 *   "3.14"                  -> "3.14"
 *   "enfloat(:label)*2"     -> "enfloat(12345)*2"
 *   "endouble(0x4008000000000000)" -> kept as-is (Python handles 0x)
 * ========================================================= */
static double xeval(Assembler *asmb, const char *expr_str){
    /* --- Step 1: replace :label tokens with their decimal values --- */
    /* Result buffer: at most 64 chars per label replacement */
    size_t elen = strlen(expr_str);
    size_t bufcap = elen * 24 + 256;
    char *expanded = malloc(bufcap);
    size_t out = 0;
    size_t i = 0;
    while(i < elen && out < bufcap - 32){
        if(expr_str[i] == ':'){
            /* read label name: alphanumeric, '_', '.' */
            size_t ns = ++i;
            while(expr_str[i] &&
                  (isalnum((unsigned char)expr_str[i]) ||
                   expr_str[i]=='_' || expr_str[i]=='.')){
                i++;
            }
            size_t nlen = i - ns;
            if(nlen > 0){
                char name[512];
                if(nlen >= sizeof(name)) nlen = sizeof(name)-1;
                memcpy(name, expr_str+ns, nlen); name[nlen] = '\0';
                uint256_t lv = label_get_value(&asmb->st, name);
                int64_t lvi = (int64_t)u256_to_i64(lv);
                int written = snprintf(expanded+out, bufcap-out, "%lld", (long long)lvi);
                if(written > 0) out += (size_t)written;
            }
        } else {
            expanded[out++] = expr_str[i++];
        }
    }
    expanded[out] = '\0';

    /* --- Step 2: build Python one-liner and call via popen --- */
    /*
     * Python script:
     *   import struct
     *   def enfloat(x): return struct.unpack('f', struct.pack('I', x & 0xFFFFFFFF))[0]
     *   def endouble(x): return struct.unpack('d', struct.pack('Q', x & 0xFFFFFFFFFFFFFFFF))[0]
     *   print(repr(float(eval("<expr>"))))
     */

    /* Escape backslashes and double-quotes in the expression */
    size_t ecap = out * 2 + 32;
    char *escaped = malloc(ecap);
    size_t ei = 0;
    for(size_t k = 0; k < out && ei < ecap-2; k++){
        char c = expanded[k];
        if(c == '\\' || c == '"'){ escaped[ei++] = '\\'; }
        escaped[ei++] = c;
    }
    escaped[ei] = '\0';

    /* Build the full Python command */
    size_t cmdcap = ei + 512;
    char *cmd = malloc(cmdcap);
    snprintf(cmd, cmdcap,
        "python3 -c \""
        "import struct\n"
        "def enfloat(x):\n"
        "  return struct.unpack('f',struct.pack('I',int(x)&0xFFFFFFFF))[0]\n"
        "def endouble(x):\n"
        "  return struct.unpack('d',struct.pack('Q',int(x)&0xFFFFFFFFFFFFFFFF))[0]\n"
        "print(repr(float(eval(\\\"" "%s" "\\\"))))"
        "\"",
        escaped);

    double result = 0.0;
    FILE *fp = popen(cmd, "r");
    if(fp){
        char buf[128] = {0};
        if(fgets(buf, sizeof(buf), fp)){
            result = strtod(buf, NULL);
        }
        pclose(fp);
    } else {
        fprintf(stderr, "xeval: popen failed for expr: %s\n", expr_str);
    }

    free(expanded);
    free(escaped);
    free(cmd);
    return result;
}

static uint256_t expr_factor(Assembler *asmb, const char *s, int idx, int *idx_out){
    AsmState *st=&asmb->st;
    idx=axx_skipspc(s,idx);
    uint256_t x=u256_zero();
    int slen=(int)strlen(s);

    if(idx+4<=slen && strncmp(s+idx,"!!!!",4)==0 && st->expmode==EXP_PAT){
        x=u256_from_i64(st->vliwstop); idx+=4;
    } else if(idx+3<=slen && strncmp(s+idx,"!!!",3)==0 && st->expmode==EXP_PAT){
        x=u256_from_i64(st->vcnt); idx+=3;
    } else if(s[idx]=='-'){
        x=expr_factor(asmb,s,idx+1,&idx);
        x=u256_neg(x);
    } else if(s[idx]=='~'){
        x=expr_factor(asmb,s,idx+1,&idx);
        x=u256_not(x);
    } else if(s[idx]=='@'){
        x=expr_factor(asmb,s,idx+1,&idx);
        x=u256_from_i64(u256_nbit(x));
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
                } else x=u256_zero();
            } else x=u256_zero();
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
    /* character literals */
    else if(idx+4<=slen && strncmp(s+idx,"'\\t'",4)==0){ x=u256_from_i64(0x09); idx+=4; }
    else if(idx+4<=slen && strncmp(s+idx,"'\\''",4)==0){ x=u256_from_i64('\''); idx+=4; }
    else if(idx+4<=slen && strncmp(s+idx,"'\\\\'",4)==0){ x=u256_from_i64('\\'); idx+=4; }
    else if(idx+4<=slen && strncmp(s+idx,"'\\n'",4)==0){ x=u256_from_i64(0x0a); idx+=4; }
    else if(idx+3<=slen && s[idx]=='\'' && s[idx+2]=='\''){ x=u256_from_i64((unsigned char)s[idx+1]); idx+=3; }
    /* $$ = pc */
    else if(axx_q(s,slen,"$$",idx)){ idx+=2; x=st->pc; }
    /* # = symbol */
    else if(axx_q(s,slen,"#",idx)){
        idx++;
        char t[512];
        idx=axx_get_symbol_word(s,idx,st->swordchars,t,sizeof(t));
        uint256_t sv;
        if(symbol_get(st,t,&sv)) x=sv; else x=u256_zero();
    }
    /* 0b binary */
    else if(axx_q(s,slen,"0b",idx)){
        idx+=2;
        while(s[idx]=='0'||s[idx]=='1'){
            x=u256_add(u256_mul(x,u256_from_u64(2)), u256_from_u64(s[idx]-'0'));
            idx++;
        }
    }
    /* 0x hex */
    else if(axx_q(s,slen,"0x",idx)){
        idx+=2;
        while(s[idx]&&is_xdigit_upper(axx_upper_char(s[idx]))){
            int d; char c=axx_upper_char(s[idx]);
            d=(c>='A')?(c-'A'+10):(c-'0');
            x=u256_add(u256_mul(x,u256_from_u64(16)), u256_from_u64((uint64_t)d));
            idx++;
        }
    }
    /* qad{} - quad float */
    else if(idx+3<=slen && strncmp(s+idx,"qad",3)==0){
        idx+=3;
        idx=axx_skipspc(s,idx);
        if(s[idx]=='{'){
            char fs[256];
            idx=axx_get_floatstr(s,idx+1,fs,sizeof(fs));
            x=ieee754_128_from_str(fs);
            if(s[idx]=='}') idx++;
        }
    }
    /* dbl{} */
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
                double v=xeval(asmb,t);
                memcpy(&bits,&v,8);
            }
            x=u256_from_u64(bits);
        }
    }
    /* flt{} */
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
                float v=(float)xeval(asmb,t);
                memcpy(&bits,&v,4);
            }
            x=u256_from_u64(bits);
        }
    }
    /* decimal integer - parse with u256 arithmetic to support >64-bit values */
    else if(is_digit(s[idx])){
        char fs[64];
        idx=axx_get_intstr(s,idx,fs,sizeof(fs));
        x=u256_zero();
        uint256_t ten=u256_from_u64(10);
        for(int di=0;fs[di];di++) x=u256_add(u256_mul(x,ten),u256_from_u64((uint64_t)(fs[di]-'0')));
    }
    /* single lowercase letter variable (EXP_PAT mode) */
    else if(st->expmode==EXP_PAT && is_lower(s[idx]) && (s[idx+1]=='\0'||!is_lower(s[idx+1]))){
        char ch=s[idx];
        if(idx+3<=slen && s[idx+1]==':'&&s[idx+2]=='='){
            x=expr_expression(asmb,s,idx+3,&idx);
            var_put(st,ch,x);
        } else {
            x=var_get(st,ch);
            idx++;
        }
    }
    /* label word */
    else if(s[idx]&&char_in(s[idx],st->lwordchars)){
        char w[512];
        int new_idx=axx_get_label_word(s,idx,st->lwordchars,w,sizeof(w));
        if(new_idx!=idx){
            idx=new_idx;
            x=label_get_value(st,w);
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
        x=u256_pow(x,t);
    }
    *idx_out=idx; return x;
}

static uint256_t expr_term0(Assembler *asmb, const char *s, int idx, int *idx_out){
    uint256_t x=expr_term0_0(asmb,s,idx,&idx);
    int slen=(int)strlen(s);
    while(idx<slen){
        if(s[idx]=='*'&&s[idx+1]!='*'){
            uint256_t t=expr_term0_0(asmb,s,idx+1,&idx);
            x=u256_mul_signed(x,t);
        } else if(axx_q(s,slen,"//",idx)){
            uint256_t t=expr_term0_0(asmb,s,idx+2,&idx);
            if(u256_is_zero(t)) printf("Division by 0 error.\n");
            else x=u256_floordiv(x,t);
        } else if(s[idx]=='%'){
            uint256_t t=expr_term0_0(asmb,s,idx+1,&idx);
            if(u256_is_zero(t)) printf("Division by 0 error.\n");
            else x=u256_mod(x,t);
        } else break;
    }
    *idx_out=idx; return x;
}

static uint256_t expr_term1(Assembler *asmb, const char *s, int idx, int *idx_out){
    uint256_t x=expr_term0(asmb,s,idx,&idx);
    int slen=(int)strlen(s);
    while(idx<slen){
        if(s[idx]=='+'){uint256_t t=expr_term0(asmb,s,idx+1,&idx);x=u256_add(x,t);}
        else if(s[idx]=='-'){uint256_t t=expr_term0(asmb,s,idx+1,&idx);x=u256_sub(x,t);}
        else break;
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

static uint256_t expr_term6(Assembler *asmb, const char *s, int idx, int *idx_out){
    /* sign extension operator: x'n */
    uint256_t x=expr_term5(asmb,s,idx,&idx);
    int slen=(int)strlen(s);
    while(idx<slen && s[idx]=='\''){
        int ni=idx+1; ni=axx_skipspc(s,ni);
        if(ni>=slen||((s[ni]<'0'||s[ni]>'9')&&s[ni]!='(')) break;
        uint256_t t=expr_term5(asmb,s,idx+1,&idx);
        int64_t tv=u256_to_i64(t);
        if(tv<=0){ x=u256_zero(); }
        else {
            /* x = (x & ~(~0<<t)) | (~0<<t if (x>>(t-1))&1 else 0) */
            uint256_t mask=u256_not(u256_shl(u256_not(u256_zero()),(int)tv));
            x=u256_and(x,mask);
            uint256_t sign_bit=u256_sar(x,(int)(tv-1));
            sign_bit=u256_and(sign_bit,u256_one());
            if(!u256_is_zero(sign_bit)){
                uint256_t ext=u256_shl(u256_not(u256_zero()),(int)tv);
                x=u256_or(x,ext);
            }
        }
    }
    *idx_out=idx; return x;
}

static uint256_t expr_term7(Assembler *asmb, const char *s, int idx, int *idx_out){
    uint256_t x=expr_term6(asmb,s,idx,&idx);
    int slen=(int)strlen(s);
    while(idx<slen){
        if(axx_q(s,slen,"<=",idx)){uint256_t t=expr_term6(asmb,s,idx+2,&idx);x=u256_from_i64(u256_le_signed(x,t)?1:0);}
        else if(s[idx]=='<'&&s[idx+1]!='<'){uint256_t t=expr_term6(asmb,s,idx+1,&idx);x=u256_from_i64(u256_lt_signed(x,t)?1:0);}
        else if(axx_q(s,slen,">=",idx)){uint256_t t=expr_term6(asmb,s,idx+2,&idx);x=u256_from_i64(u256_ge_signed(x,t)?1:0);}
        else if(s[idx]=='>'&&s[idx+1]!='>'){uint256_t t=expr_term6(asmb,s,idx+1,&idx);x=u256_from_i64(u256_gt_signed(x,t)?1:0);}
        else if(axx_q(s,slen,"==",idx)){uint256_t t=expr_term6(asmb,s,idx+2,&idx);x=u256_from_i64(u256_eq(x,t)?1:0);}
        else if(axx_q(s,slen,"!=",idx)){uint256_t t=expr_term6(asmb,s,idx+2,&idx);x=u256_from_i64(!u256_eq(x,t)?1:0);}
        else break;
    }
    *idx_out=idx; return x;
}

static uint256_t expr_term8(Assembler *asmb, const char *s, int idx, int *idx_out){
    int slen=(int)strlen(s);
    if(idx+4<=slen && strncmp(s+idx,"not(",4)==0){
        uint256_t x=expr_expression(asmb,s,idx+3,&idx);
        *idx_out=idx;
        return u256_from_i64(u256_is_zero(x)?1:0);
    }
    return expr_term7(asmb,s,idx,idx_out);
}

static uint256_t expr_term9(Assembler *asmb, const char *s, int idx, int *idx_out){
    uint256_t x=expr_term8(asmb,s,idx,&idx);
    int slen=(int)strlen(s);
    while(idx<slen && axx_q(s,slen,"&&",idx)){
        uint256_t t=expr_term8(asmb,s,idx+2,&idx);
        x=u256_from_i64((!u256_is_zero(x)&&!u256_is_zero(t))?1:0);
    }
    *idx_out=idx; return x;
}

static uint256_t expr_term10(Assembler *asmb, const char *s, int idx, int *idx_out){
    uint256_t x=expr_term9(asmb,s,idx,&idx);
    int slen=(int)strlen(s);
    while(idx<slen && axx_q(s,slen,"||",idx)){
        uint256_t t=expr_term9(asmb,s,idx+2,&idx);
        x=u256_from_i64((!u256_is_zero(x)||!u256_is_zero(t))?1:0);
    }
    *idx_out=idx; return x;
}

static uint256_t expr_term11(Assembler *asmb, const char *s, int idx, int *idx_out){
    uint256_t x=expr_term10(asmb,s,idx,&idx);
    int slen=(int)strlen(s);
    while(idx<slen && axx_q(s,slen,"?",idx)){
        uint256_t t=expr_term10(asmb,s,idx+1,&idx);
        if(axx_q(s,slen,":",idx)){
            uint256_t u=expr_term10(asmb,s,idx+1,&idx);
            x=u256_is_zero(x)?u:t;
        }
    }
    *idx_out=idx; return x;
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
        /* field[2] = specific key to clear */
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
        char buf[256];
        snprintf(buf,sizeof(buf),"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789%s",e->f[2]);
        strncpy(asmb->st.swordchars,buf,sizeof(asmb->st.swordchars)-1);
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

static void dir_error(Assembler *asmb, const char *s){
    AsmState *st=&asmb->st;
    /* strip spaces */
    int has_content=0;
    for(const char*p=s;*p;p++) if(*p!=' '){has_content=1;break;}
    if(!has_content) return;

    char buf[4096];
    size_t l=strlen(s);
    if(l>=sizeof(buf)) l=sizeof(buf)-1;
    memcpy(buf,s,l); buf[l]='\0';
    /* append NUL sentinel */
    buf[l]='\0';

    int idx=0;
    while(1){
        if(!buf[idx]) break;
        if(buf[idx]==','){idx++;continue;}
        int io;
        uint256_t u=expr_expression_pat(asmb,buf,idx,&io);
        idx=io;
        if(buf[idx]==';') idx++;
        uint256_t t=expr_expression_pat(asmb,buf,idx,&io);
        idx=io;
        if((st->pas==2||st->pas==0)&&!u256_is_zero(u)){
            int64_t tc=u256_to_i64(t);
            printf("Line %d Error code %lld ",(int)st->ln,(long long)tc);
            if(tc>=0&&tc<ERRORS_COUNT) printf("%s",ERRORS_TABLE[tc]);
            printf(": \n");
        }
    }
}

/* =========================================================
 * PatternMatcher
 * ========================================================= */
/* remove_brackets: remove OB..CB pairs at given 1-based indices */
static char *remove_brackets_str(const char *s, int *remove_idx, int nr){
    int len=(int)strlen(s);
    /* find bracket positions */
    typedef struct { int level; int pos; int is_open; } BP;
    BP *bps=calloc(len,sizeof(BP)); int nbps=0;
    int open_count=0;
    for(int i=0;i<len;i++){
        if(s[i]==OB_CHAR){ open_count++; bps[nbps++]=(BP){open_count,i,1}; }
        else if(s[i]==CB_CHAR){ bps[nbps++]=(BP){open_count,i,0}; open_count--; }
    }
    /* build set of positions to remove */
    char *result=malloc(len+1);
    memcpy(result,s,len+1);
    /* for each index in remove_idx, find matching open/close and blank them */
    for(int ri=0;ri<nr;ri++){
        int ridx=remove_idx[ri];
        int start_pos=-1, end_pos=-1;
        for(int b=0;b<nbps;b++){
            if(bps[b].level==ridx && bps[b].is_open && start_pos<0) start_pos=bps[b].pos;
            else if(bps[b].level==ridx && !bps[b].is_open && start_pos>=0){ end_pos=bps[b].pos; break; }
        }
        if(start_pos>=0&&end_pos>=0)
            for(int j=start_pos;j<=end_pos;j++) result[j]='\x01'; /* mark for removal */
    }
    /* compact */
    char *out=malloc(len+1); int n=0;
    for(int i=0;i<len;i++) if(result[i]!='\x01') out[n++]=result[i];
    out[n]=0;
    free(result); free(bps);
    return out;
}

/* match: match assembly line s against pattern t */
static int pat_match(Assembler *asmb, const char *s_orig, const char *t_orig){
    AsmState *st=&asmb->st;
    strncpy(st->deb1,s_orig,sizeof(st->deb1)-1);
    strncpy(st->deb2,t_orig,sizeof(st->deb2)-1);

    /* remove OB/CB from t */
    char *t_nobr=strdup(t_orig);
    for(char*p=t_nobr;*p;p++) if(*p==OB_CHAR||*p==CB_CHAR) *p=' ';
    /* Actually per Python: t.replace(OB,'').replace(CB,'') */
    char *t_clean=malloc(strlen(t_nobr)+1); int n2=0;
    for(int i=0;t_nobr[i];i++) if(t_nobr[i]!=OB_CHAR&&t_nobr[i]!=CB_CHAR) t_clean[n2++]=t_nobr[i];
    t_clean[n2]=0; free(t_nobr);

    /* NUL-terminate both */
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
            if(a=='!'){
                a=t[idx_t]; idx_t++;
                uint256_t v=expr_factor(asmb,s,idx_s,&idx_s);
                var_put(st,a,v);
                continue;
            } else {
                idx_t=axx_skipspc(t,idx_t);
                char stopchar='\0';
                if(idx_t<tlen && t[idx_t]=='\\'){
                    idx_t++;                          /* skip '\' in pattern   */
                    idx_t=axx_skipspc(t,idx_t);
                    stopchar=t[idx_t];
                    idx_t++;                          /* skip stopchar in pattern */
                }
                uint256_t v=expr_expression_esc(asmb,s,idx_s,stopchar,&idx_s);
                var_put(st,a,v);
                /* stopchar was used as the NUL sentinel in the buffer, so
                   idx_s now points AT the stopchar in s (or past end).
                   Consume it from s so the next pattern char can match
                   whatever follows the stopchar. */
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
            /* Brackets are significant delimiters in x86-style patterns like [rbx+rcx*2+d].
               Match them literally, skipping surrounding spaces in both s and t. */
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

static int pat_match0(Assembler *asmb, const char *s, const char *t_orig){
    /* Replace [[ ]] with OB CB */
    char *t=malloc(strlen(t_orig)+1);
    strcpy(t,t_orig);
    /* replace [[ -> OB, ]] -> CB */
    char *out=malloc(strlen(t)*2+4);
    int n=0;
    for(int i=0;t[i];){
        if(t[i]=='['&&t[i+1]=='['){ out[n++]=OB_CHAR; i+=2; }
        else if(t[i]==']'&&t[i+1]==']'){ out[n++]=CB_CHAR; i+=2; }
        else out[n++]=t[i++];
    }
    out[n]=0; free(t); t=out;

    /* count OB chars */
    int cnt=0; for(const char*p=t;*p;p++) if(*p==OB_CHAR) cnt++;
    int *sl=malloc((cnt+1)*sizeof(int));
    for(int i=0;i<cnt;i++) sl[i]=i+1;

    /* iterate all subsets */
    int found=0;
    /* 2^cnt subsets */
    for(int mask=0;mask<(1<<cnt)&&!found;mask++){
        int ri[64]; int nr=0;
        for(int i=0;i<cnt;i++) if(mask&(1<<i)) ri[nr++]=sl[i];
        char *lt=remove_brackets_str(t,ri,nr);
        if(pat_match(asmb,s,lt)) found=1;
        free(lt);
    }
    free(sl); free(t);
    return found;
}

/* =========================================================
 * PatternFileReader
 * ========================================================= */
static void readpat(Assembler *asmb, const char *fn);
static void include_pat(Assembler *asmb, const char *l);

static void include_pat(Assembler *asmb, const char *l){
    int idx=axx_skipspc(l,0);
    char upper8[16]={0};
    for(int i=0;i<8&&l[idx+i];i++) upper8[i]=axx_upper_char(l[idx+i]);
    if(strcmp(upper8,".INCLUDE")!=0) return;
    char s[512];
    axx_get_string(l+8,s,sizeof(s));
    if(s[0]) readpat(asmb,s);
}

static void readpat(Assembler *asmb, const char *fn){
    if(!fn||!fn[0]) return;
    FILE *f=fopen(fn,"rt");
    if(!f){ fprintf(stderr,"Cannot open pattern file: %s\n",fn); return; }
    char line[4096];
    while(fgets(line,sizeof(line),f)){
        axx_remove_comment(line);
        /* replace tab with space, strip CR */
        for(char*p=line;*p;p++){ if(*p=='\t') *p=' '; if(*p=='\r') *p=' '; }
        /* strip newline */
        int l=(int)strlen(line);
        while(l>0&&(line[l-1]=='\n'||line[l-1]=='\r')) line[--l]=0;
        axx_reduce_spaces(line);

        /* check .include */
        char uline[16]={0};
        int si=axx_skipspc(line,0);
        for(int i=0;i<8&&line[si+i];i++) uline[i]=axx_upper_char(line[si+i]);
        if(strcmp(uline,".INCLUDE")==0){ include_pat(asmb,line+si); continue; }

        /* split by :: */
        char fields[8][1024]; int nf=0;
        int idx=0;
        while(1){
            char f_out[1024];
            idx=axx_get_params1(line,idx,f_out,sizeof(f_out));
            fields[nf][0]=0; strncpy(fields[nf],f_out,sizeof(fields[nf])-1);
            nf++;
            if(idx>=(int)strlen(line)||nf>=8) break;
        }

        PatEntry *pe=pv_push_blank(&asmb->st.pat);
        /* map fields to [0..5] per Python logic */
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

/* e_p: expand @@[n,pattern] syntax */
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
                i++; /* skip ] */
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

    char ep_buf[8192]={0}; int is_empty;
    e_p(s_in,ep_buf,sizeof(ep_buf),&is_empty,asmb);
    if(is_empty) return;

    char s[8192]={0};
    replace_percent_with_index(ep_buf,s,sizeof(s));
    int slen=(int)strlen(s); s[slen]='\0';

    int idx=0;
    while(1){
        if(idx>=(int)strlen(s)||s[idx]=='\0') break;
        if(s[idx]==','){
            idx++;
            uint64_t p=u256_to_u64(st->pc)+(uint64_t)objl->len;
            uint64_t aligned=align_addr(st,p);
            for(uint64_t ii=p;ii<aligned;ii++) iv_push(objl,st->padding);
            continue;
        }
        int semicolon=0;
        if(s[idx]==';'){ semicolon=1; idx++; }
        int io;
        uint256_t x=expr_expression_pat(asmb,s,idx,&io);
        idx=io;
        if(semicolon?!u256_is_zero(x):1) iv_push(objl,x);
        if(s[idx]==','){idx++;continue;}
        break;
    }
}

/* =========================================================
 * VLIWProcessor
 * ========================================================= */
typedef struct { IntVec *data; int len; int cap; } IVVec;
static void ivv_init(IVVec*v){v->data=NULL;v->len=0;v->cap=0;}
static void ivv_push(IVVec*v,IntVec*iv){
    if(v->len>=v->cap){v->cap=v->cap?v->cap*2:8;v->data=realloc(v->data,v->cap*sizeof(IntVec));}
    IntVec *dst=&v->data[v->len++]; iv_init(dst); iv_copy(dst,iv);
}
static void ivv_free(IVVec*v){
    for(int i=0;i<v->len;i++) iv_free(&v->data[i]);
    free(v->data); ivv_init(v);
}

static int int_cmp(const void*a,const void*b){ return *(int*)a-*(int*)b; }

static int vliwprocess(Assembler *asmb, const char *line, IntVec *idxs_in, IntVec *objl_in,
                       int idx, int *idx_out){
    AsmState *st=&asmb->st;
    IVVec objs; ivv_init(&objs);
    ivv_push(&objs,objl_in);

    int *idxlst=malloc(256*sizeof(int)); int nidxlst=0;
    for(int i=0;i<idxs_in->len;i++) idxlst[nidxlst++]=(int)u256_to_i64(idxs_in->data[i]);

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
            if(nidxlst<256) for(int i=0;i<new_idxs.len;i++) idxlst[nidxlst++]=(int)u256_to_i64(new_idxs.data[i]);
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

    for(int ki=0;ki<st->vliwset.len;ki++){
        VliwSetEntry *k=&st->vliwset.data[ki];
        /* sorted compare */
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

        /* collect values */
        IntVec values; iv_init(&values);
        for(int oi=0;oi<objs.len;oi++) for(int mi=0;mi<objs.data[oi].len;mi++) iv_push(&values,objs.data[oi].data[mi]);

        int ibyte=st->vliwinstbits/8+(st->vliwinstbits%8?1:0);
        int noi=(vbits-at)/st->vliwinstbits;
        int target_len=ibyte*noi;
        /* pad with nop, or warn+truncate on overflow */
        if(values.len > target_len){
            if(st->pas==2||st->pas==0)
                printf("warning-VLIW:%d values exceed slot capacity %d,truncating.\n",values.len,target_len);
            values.len=target_len;
        } else {
            int needed=target_len-values.len;
            for(int pi=0;pi<needed;pi++) for(int ni=0;ni<st->vliwnop.len;ni++) iv_push(&values,st->vliwnop.data[ni]);
        }

        /* build v1: noi instruction words */
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

        /* r = concat v1 */
        uint256_t pm=u256_sub(u256_shl(u256_one(),vbits),u256_one());
        uint256_t r=u256_zero();
        for(int vi=0;vi<v1.len;vi++){ r=u256_shl(r,st->vliwinstbits); r=u256_or(r,v1.data[vi]); }
        r=u256_and(r,pm);

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
        char buf[256];
        snprintf(buf,sizeof(buf),"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789%s",ll);
        strncpy(st->lwordchars,buf,sizeof(st->lwordchars)-1);
    }
    return 1;
}

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
            uint256_t u=expr_expression_asm(asmb,l,idx,&io);
            label_put_value(st,label,u,st->current_section);
            out[0]=0; return out;
        } else {
            label_put_value(st,label,st->pc,st->current_section);
            strncpy(out,l+lidx,osz-1); out[osz-1]=0; return out;
        }
    }
    strncpy(out,l,osz-1); out[osz-1]=0; return out;
}

static void asciistr(Assembler *asmb, const char *l2){
    AsmState *st=&asmb->st;
    if(!l2[0]||l2[0]!='"') return;
    int idx=1;
    while(l2[idx]&&l2[idx]!='"'){
        unsigned char ch;
        if(l2[idx]=='\\'&&l2[idx+1]=='0'){ ch=0; idx+=2; }
        else if(l2[idx]=='\\'&&l2[idx+1]=='t'){ ch='\t'; idx+=2; }
        else if(l2[idx]=='\\'&&l2[idx+1]=='n'){ ch='\n'; idx+=2; }
        else { ch=(unsigned char)l2[idx]; idx++; }
        outbin(st,st->pc,u256_from_u64(ch));
        st->pc=u256_add(st->pc,u256_one());
    }
}

static int adir_section(AsmState *st, const char *l, const char *l2){
    char up[32]; axx_strupr_to(up,l,sizeof(up));
    if(strcmp(up,"SECTION")!=0 && strcmp(up,"SEGMENT")!=0) return 0;
    if(l2&&l2[0]){
        strncpy(st->current_section,l2,sizeof(st->current_section)-1);
        secmap_set(&st->sections,l2,st->pc,u256_zero());
    }
    return 1;
}
static int adir_endsection(AsmState *st, const char *l){
    char up[32]; axx_strupr_to(up,l,sizeof(up));
    if(strcmp(up,"ENDSECTION")!=0 && strcmp(up,"ENDSEGMENT")!=0) return 0;
    SecEntry *e=secmap_find(&st->sections,st->current_section);
    if(e){ e->size=u256_sub(st->pc,e->start); }
    return 1;
}
static int adir_zero(Assembler *asmb, const char *l, const char *l2){
    char up[16]; axx_strupr_to(up,l,sizeof(up));
    if(strcmp(up,".ZERO")!=0) return 0;
    int io;
    uint256_t x=expr_expression_asm(asmb,l2,0,&io);
    int64_t cnt=u256_to_i64(x);
    for(int64_t i=0;i<cnt;i++){
        outbin2(&asmb->st,asmb->st.pc,u256_from_u64(0));
        asmb->st.pc=u256_add(asmb->st.pc,u256_one());
    }
    return 1;
}
static int adir_ascii(Assembler *asmb, const char *l, const char *l2){
    char up[16]; axx_strupr_to(up,l,sizeof(up));
    if(strcmp(up,".ASCII")!=0) return 0;
    asciistr(asmb,l2); return 1;
}
static int adir_asciiz(Assembler *asmb, const char *l, const char *l2){
    char up[16]; axx_strupr_to(up,l,sizeof(up));
    if(strcmp(up,".ASCIIZ")!=0) return 0;
    asciistr(asmb,l2);
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
    /* check ,P suffix */
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
    if(strcmp(up,".EXPORT")!=0) return 0;
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
        lmap_set(&st->export_labels,s,v,sec);
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
    /* rstrip l */
    int ll=(int)strlen(l); while(ll>0&&(l[ll-1]==' '||l[ll-1]=='\t')) l[--ll]=0;
    /* l2 already rstripped by get_param_to_eon */
    /* remove spaces from l */
    char l_nospace[1024]={0}; int nn=0;
    for(int i=0;l[i];i++) if(l[i]!=' ') l_nospace[nn++]=l[i];
    l_nospace[nn]=0;
    strncpy(l,l_nospace,sizeof(l)-1);

    if(adir_section(st,l,l2)){ *idx_out=idx; return 1; }
    if(adir_endsection(st,l)){ *idx_out=idx; return 1; }
    if(adir_zero(asmb,l,l2)){ *idx_out=idx; return 1; }
    if(adir_ascii(asmb,l,l2)){ *idx_out=idx; return 1; }
    if(adir_asciiz(asmb,l,l2)){ *idx_out=idx; return 1; }
    /* .include */
    { char up[16]; axx_strupr_to(up,l,sizeof(up));
      if(strcmp(up,".INCLUDE")==0){ char s[512]; axx_get_string(l2,s,sizeof(s)); if(s[0]) fileassemble(asmb,s); *idx_out=idx; return 1; } }
    if(adir_align(asmb,l,l2)){ *idx_out=idx; return 1; }
    if(adir_org(asmb,l,l2)){ *idx_out=idx; return 1; }
    if(adir_labelc(st,l,l2)){ *idx_out=idx; return 1; }
    if(adir_export(asmb,l,l2)){ *idx_out=idx; return 1; }
    if(!l[0]){ *idx_out=idx; return 0; }

    int se=0, oerr=0, pln=0;
    int idxs_val=0;
    int loopflag=1;

    for(int pi=0;pi<st->pat.len;pi++){
        PatEntry *i=&st->pat.data[pi];
        pln++;
        /* reset vars */
        for(int vi=0;vi<26;vi++) st->vars[vi]=u256_zero();

        /* check pattern directives */
        if(dir_set_symbol(asmb,i)) continue;
        if(dir_clear_symbol(asmb,i)) continue;
        if(dir_padding(asmb,i)) continue;
        if(dir_bits(asmb,i)) continue;
        if(dir_symbolc(asmb,i)) continue;
        if(dir_epic(asmb,i)) continue;
        if(dir_vliwp(asmb,i)) continue;

        /* count non-empty fields */
        int lw=0; for(int fi=0;fi<PAT_FIELDS;fi++) if(i->f[fi][0]) lw++;
        if(lw==0) continue;

        char lin[8192]; snprintf(lin,sizeof(lin),"%s %s",l,l2);
        axx_reduce_spaces(lin);

        if(!i->f[0][0]){ loopflag=0; break; }

        st->error_undefined_label=0;
        st->expmode=EXP_ASM;

        if(!st->debug){
            /* try/catch equivalent: use setjmp or just proceed */
            /* In C we just call directly */
            if(pat_match0(asmb,lin,i->f[0])){
                dir_error(asmb,i->f[1]);
                makeobj(asmb,i->f[2],objl_out);
                int io;
                uint256_t idxv=expr_expression_pat(asmb,i->f[3],0,&io);
                idxs_val=(int)u256_to_i64(idxv);
                loopflag=0; break;
            }
        } else {
            if(pat_match0(asmb,lin,i->f[0])){
                dir_error(asmb,i->f[1]);
                makeobj(asmb,i->f[2],objl_out);
                int io;
                uint256_t idxv=expr_expression_pat(asmb,i->f[3],0,&io);
                idxs_val=(int)u256_to_i64(idxv);
                loopflag=0; break;
            }
        }
    }

    if(loopflag){ se=1; pln=0; }

    if(st->pas==2||st->pas==0){
        if(st->error_undefined_label){ printf(" error - undefined label error.\n"); *idx_out=idx; return 0; }
        if(se){ printf(" error - Syntax error.\n"); *idx_out=idx; return 0; }
        if(oerr){ printf(" ; pat %d error - Illegal syntax in assemble line or pattern line.\n",pln); *idx_out=idx; return 0; }
    }

    /* populate idxs_out as single-element IntVec */
    iv_clear(idxs_out);
    iv_push(idxs_out, u256_from_i64(idxs_val));
    *idx_out=idx;
    return 1;
}

static int lineassemble(Assembler *asmb, const char *line_in){
    AsmState *st=&asmb->st;
    char line[4096];
    strncpy(line,line_in,sizeof(line)-1);
    /* replace tab with space, strip newline */
    for(char*p=line;*p;p++){ if(*p=='\t') *p=' '; if(*p=='\n'||*p=='\r') *p=' '; }
    axx_reduce_spaces(line);
    axx_remove_comment_asm(line);
    if(!line[0]) return 0;

    char processed[4096];
    adir_label_processing(asmb,line,processed,sizeof(processed));
    /* clear_symbol with ".clearsym" */
    {
        PatEntry ce;
        ce.f[0]=strdup(".clearsym"); ce.f[1]=strdup(""); ce.f[2]=strdup("");
        for(int i=3;i<PAT_FIELDS;i++) ce.f[i]=strdup("");
        dir_clear_symbol(asmb,&ce);
        for(int i=0;i<PAT_FIELDS;i++) free(ce.f[i]);
    }

    /* count vcnt from !! split */
    int vcnt=0;
    const char *pp=processed;
    while(1){
        /* count non-empty parts */
        int has=0;
        while(*pp&&!(*pp=='!'&&*(pp+1)=='!')){ if(*pp!=' ') has=1; pp++; }
        if(has) vcnt++;
        if(*pp) pp+=2; else break;
    }
    st->vcnt=vcnt?vcnt:1;

    IntVec idxs; iv_init(&idxs);
    IntVec objl; iv_init(&objl);
    int new_idx;
    int flag=lineassemble2(asmb,processed,0,&idxs,&objl,&new_idx);
    if(!flag){ iv_free(&idxs); iv_free(&objl); return 0; }

    /* check if VLIW continues */
    const char *rest=processed+new_idx;
    while(*rest==' ') rest++;
    int is_vliw_cont=(st->vliwflag && rest[0]=='!'&&rest[1]=='!');

    if(!is_vliw_cont){
        for(int ci=0;ci<objl.len;ci++){
            outbin(st,st->pc,objl.data[ci]);
            st->pc=u256_add(st->pc,u256_one());
        }
    } else {
        int vi;
        int vok=vliwprocess(asmb,processed,&idxs,&objl,new_idx,&vi);
        iv_free(&idxs); iv_free(&objl);
        return vok;
    }

    iv_free(&idxs); iv_free(&objl);
    return 1;
}

static int lineassemble0(Assembler *asmb, const char *line){
    AsmState *st=&asmb->st;
    strncpy(st->cl,line,sizeof(st->cl)-1);
    /* strip trailing newline */
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
    /* read all stdin into malloced string */
    size_t total=0, cap=4096;
    char *buf=malloc(cap);
    char line[4096];
    while(fgets(line,sizeof(line),stdin)){
        size_t l=strlen(line);
        /* remove \r */
        for(size_t i=0;i<l;i++) if(line[i]=='\r'){ memmove(line+i,line+i+1,l-i); l--; }
        while(total+l+1>cap){ cap*=2; buf=realloc(buf,cap); }
        memcpy(buf+total,line,l);
        total+=l;
    }
    buf[total]=0;
    return buf;
}

static void fileassemble(Assembler *asmb, const char *fn){
    AsmState *st=&asmb->st;
    sv_push(&st->fnstack, st->current_file);
    is_push(&st->lnstack, st->ln);
    strncpy(st->current_file,fn,sizeof(st->current_file)-1);
    st->ln=1;

    FILE *f=NULL;
    char *stdin_buf=NULL;

    if(strcmp(fn,"stdin")==0){
        char tmp_path[]="axx.tmp";
        int need_read=(st->pas==1);
        if(!need_read){ FILE*test=fopen(tmp_path,"rt"); if(test)fclose(test); else need_read=1; }
        if(need_read){
            stdin_buf=file_input_from_stdin();
            FILE*tmpf=fopen(tmp_path,"wt");
            if(tmpf){ fwrite(stdin_buf,1,strlen(stdin_buf),tmpf); fclose(tmpf); }
        }
        fn=tmp_path;
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
    if(st->fnstack.len>0){
        strncpy(st->current_file,st->fnstack.data[st->fnstack.len-1],sizeof(st->current_file)-1);
        sv_pop(&st->fnstack);
        st->ln=is_pop(&st->lnstack);
    }
}

/* =========================================================
 * setpatsymbols
 * ========================================================= */
static void setpatsymbols(Assembler *asmb){
    for(int pi=0;pi<asmb->st.pat.len;pi++){
        PatEntry *e=&asmb->st.pat.data[pi];
        dir_set_symbol(asmb,e);
    }
    /* copy symbols -> patsymbols */
    smap_free(&asmb->st.patsymbols);
    smap_init(&asmb->st.patsymbols);
    for(int i=0;i<asmb->st.symbols.nb;i++){
        for(SymEntry*e=asmb->st.symbols.buckets[i];e;e=e->next)
            smap_set(&asmb->st.patsymbols,e->key,e->val);
    }
}

/* =========================================================
 * imp_label
 * ========================================================= */
static int imp_label(Assembler *asmb, const char *l){
    AsmState *st=&asmb->st;
    int idx=axx_skipspc(l,0);
    char section[512];
    idx=axx_get_label_word(l,idx,st->lwordchars,section,sizeof(section));
    idx=axx_skipspc(l,idx);
    char label[512];
    idx=axx_get_label_word(l,idx,st->lwordchars,label,sizeof(label));
    if(!label[0]) return 0;
    idx=axx_skipspc(l,idx);
    int io;
    uint256_t v=expr_expression_asm(asmb,l,idx,&io);
    if(io==idx) return 0;
    label_put_value(st,label,v,section);
    return 1;
}

/* =========================================================
 * main
 * ========================================================= */
static void print_usage(const char *prog){
    printf("usage: %s patternfile [sourcefile] [-o outfile] [-e export_tsv] [-E export_elf_tsv] [-i import_tsv]\n",prog);
    printf("axx general assembler programmed and designed by Taisuke Maekawa\n");
}

int main(int argc, char *argv[]){
    if(argc==1){ print_usage(argv[0]); return 0; }

    Assembler *asmb=calloc(1,sizeof(Assembler));
    assembler_init(asmb);
    AsmState *st=&asmb->st;

    const char *patternfile=NULL, *sourcefile=NULL;
    const char *expfile_elf=NULL;

    for(int i=1;i<argc;i++){
        if(strcmp(argv[i],"-o")==0&&i+1<argc){ strncpy(st->outfile,argv[++i],sizeof(st->outfile)-1); }
        else if(strcmp(argv[i],"-e")==0&&i+1<argc){ strncpy(st->expfile,argv[++i],sizeof(st->expfile)-1); }
        else if(strcmp(argv[i],"-E")==0&&i+1<argc){ expfile_elf=argv[++i]; }
        else if(strcmp(argv[i],"-i")==0&&i+1<argc){ strncpy(st->impfile,argv[++i],sizeof(st->impfile)-1); }
        else if(argv[i][0]!='-'){
            if(!patternfile) patternfile=argv[i];
            else if(!sourcefile) sourcefile=argv[i];
        }
    }

    if(!patternfile){ print_usage(argv[0]); return 1; }

    /* load pattern */
    readpat(asmb,patternfile);
    setpatsymbols(asmb);

    /* import labels */
    if(st->impfile[0]){
        FILE *lf=fopen(st->impfile,"rt");
        if(lf){ char l[4096]; while(fgets(l,sizeof(l),lf)) imp_label(asmb,l); fclose(lf); }
    }

    /* remove stale outfile */
    if(st->outfile[0]) remove(st->outfile);

    if(!sourcefile){
        /* interactive / stdin mode */
        st->pc=u256_zero(); st->pas=0; st->ln=1;
        strncpy(st->current_file,"(stdin)",sizeof(st->current_file)-1);
        char line[4096];
        while(1){
            printf("%016llx >> ",(unsigned long long)u256_to_u64(st->pc));
            fflush(stdout);
            if(!fgets(line,sizeof(line),stdin)) break;
            /* strip newline */
            int ll=(int)strlen(line);
            while(ll>0&&(line[ll-1]=='\n'||line[ll-1]=='\r')) line[--ll]=0;
            /* replace \\ -> \ */
            for(int i=0;line[i];i++) if(line[i]=='\\'&&line[i+1]=='\\') { line[i]='\\'; memmove(line+i+1,line+i+2,ll-i-1); ll--; }
            /* trim */
            ll=(int)strlen(line);
            while(ll>0&&line[ll-1]==' ') line[--ll]=0;
            if(!line[0]) continue;
            if(strcmp(line,"?")==0){ label_print_all(st); continue; }
            lineassemble0(asmb,line);
        }
    } else {
        /* two-pass */
        st->pc=u256_zero(); st->pas=1; st->ln=1;
        fileassemble(asmb,sourcefile);
        st->pc=u256_zero(); st->pas=2; st->ln=1;
        fileassemble(asmb,sourcefile);
    }

    binary_flush(st);

    /* export labels */
    int elf=0;
    if(expfile_elf){ strncpy(st->expfile,expfile_elf,sizeof(st->expfile)-1); elf=1; }

    if(st->expfile[0]){
        FILE *lf=fopen(st->expfile,"wt");
        if(lf){
            /* sections */
            for(int i=0;i<st->sections.count;i++){
                SecEntry *e=st->sections.order[i];
                const char *flag="";
                if(elf){
                    if(strcmp(e->name,".text")==0) flag="AX";
                    else if(strcmp(e->name,".data")==0) flag="WA";
                }
                fprintf(lf,"%s\t0x%llx\t0x%llx\t%s\n",
                        e->name,
                        (unsigned long long)u256_to_u64(e->start),
                        (unsigned long long)u256_to_u64(e->size),
                        flag);
            }
            /* export labels */
            for(int i=0;i<st->export_labels.nbuckets;i++){
                for(LabelEntry*e=st->export_labels.buckets[i];e;e=e->next){
                    fprintf(lf,"%s\t0x%llx\n",e->key,(unsigned long long)u256_to_u64(e->value));
                }
            }
            fclose(lf);
        }
    }

    /* cleanup (optional) */
    return 0;
}
