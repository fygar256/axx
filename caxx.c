
/*
 * caxx — axx 汎用アセンブラの C 実装
 *
 * 同じディレクトリの axx.py（Python 版・こちらが原典）の移植であり、
 * 同一の入力に対して同一のバイト列を出すことを目標に保守されている。
 * 仕様・設計の説明は axx.py 冒頭のコメントを参照。
 *
 * axx は命令セットをコードに埋め込まず、外部のパターンファイル（.axx）から
 * 「ニーモニックの書式 → バイナリエンコーディング」の対応を読み込む。
 * パターンファイルを差し替えるだけで任意の ISA を扱える。
 *
 *     caxx <パターンファイル.axx> <ソース.s> -o <出力.o>
 *
 * 処理の流れ:
 *   1. パターンファイル読み込み（readpat / .INCLUDE を再帰展開）
 *   2. マクロ展開（macro_expand）
 *   3. パス1: サイズ収束。可変長命令の長さが前方参照ラベルの値に依存するため、
 *      全ラベルのアドレスが前回反復と一致するまで繰り返す（リラクゼーション）
 *   4. パス2: 確定アドレスで実バイト列と ELF リロケーションを生成
 *   5. 出力: ELF オブジェクト / 生バイナリ / ラベル TSV
 *
 * このファイルの大まかな構成（上から順に）:
 *   - uint256_t          256bit 整数演算（アドレスと即値の内部表現）
 *   - 各種コンテナ       ラベル表・シンボル表・セクション表・出力バッファ
 *   - AsmState           アセンブル中の全状態
 *   - axx_*              行の前処理（コメント除去・エスケープ・トークン切り出し）
 *   - IEEE754 変換       32/64/128bit 浮動小数点のビットパターン生成
 *   - expr_*             式評価器（優先順位ごとの再帰下降）
 *   - pat_*              パターン照合
 *   - dir_* / adir_*     パターン側 / ソース側のディレクティブ処理
 *   - makeobj            エンコーディング欄からワード列を作る
 *   - vliwprocess        VLIW/EPIC パケット組み立て
 *   - lineassemble       1行を処理する主ループ
 *   - write_elf_obj      ELF オブジェクト出力
 *   - macro_*            行指向マクロ層（!if / !while / !def）
 *   - main               コマンドライン処理と全体の駆動
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

static void axx_diagf(int set_error, int force, const char *fmt, ...);
static void m_pyrepr(const char *s, char *out, size_t outsz);
#include <unistd.h>
#include <sys/stat.h>
#include <libgen.h>
#include <limits.h>
#include <sys/wait.h>

#ifdef __GNUC__
#  define AXX_UNUSED __attribute__((unused))
#else
#  define AXX_UNUSED
#endif

/* =========================================================
 * uint256_t — 256bit 整数
 *
 * アドレス・即値・ラベル値の内部表現。w[0] が最下位ワード。
 * 256bit も必要なのは、axx が 128bit 浮動小数点（四倍精度）のビットパターンを
 * 整数として扱うことと、未定義ラベルを巨大な番兵値で表現するため。
 * 符号付きとして解釈する場合は最上位ビット（w[3] の bit63）が符号になる。
 *
 * 浮動小数点モード（st.exp_typ_float）では、同じ uint256_t を「C の double の
 * ビットを w[0] にコピーしたもの」として使う。数値変換ではなくビット再解釈
 * である点に注意（u256_to_double / double_to_u256 は memcpy で実装されている）。
 * ========================================================= */
typedef struct { uint64_t w[4]; } uint256_t;
static void u256_to_pydec(uint256_t a, char *out, size_t outsz);

/* パターン変数（a〜z）1個ぶんの束縛。is_undef は「まだ束縛されていない」印。 */
typedef struct { uint256_t val; int is_undef; } PatVar;

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
static int u256_lt_signed(uint256_t a, uint256_t b) {
    int sa = (int)(a.w[3] >> 63);
    int sb = (int)(b.w[3] >> 63);
    if (sa != sb) return sa > sb;
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
static uint256_t u256_mul_signed(uint256_t a, uint256_t b) {
    return u256_mul(a,b);
}
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
static uint256_t u256_truncdiv(uint256_t a, uint256_t b) {
    if (u256_is_zero(b)) { fprintf(stderr,"Division by zero\n"); return u256_zero(); }
    int sa = (int)(a.w[3]>>63);
    int sb = (int)(b.w[3]>>63);
    uint256_t ua = sa ? u256_neg(a) : a;
    uint256_t ub = sb ? u256_neg(b) : b;
    uint256_t q = u256_udiv(ua, ub);
    if (sa != sb) q = u256_neg(q);
    return q;
}
static uint256_t u256_mod(uint256_t a, uint256_t b) {
    if (u256_is_zero(b)) { fprintf(stderr,"Division by zero\n"); return u256_zero(); }
    uint256_t q = u256_floordiv(a,b);
    return u256_sub(a, u256_mul(q,b));
}

static uint256_t u256_pow(uint256_t base, uint256_t exp) {
    uint256_t r = u256_one();
    for (int wi = 0; wi < 4; wi++) {
        uint64_t word = exp.w[wi];
        if (!word) {
            int all_zero = 1;
            for (int k = wi + 1; k < 4; k++) if (exp.w[k]) { all_zero = 0; break; }
            if (all_zero) break;
        }
        for (int bi = 0; bi < 64; bi++) {
            if (word & ((uint64_t)1 << bi))
                r = u256_mul(r, base);
            int last_bit = (wi == 3 && bi == 63);
            if (!last_bit)
                base = u256_mul(base, base);
        }
    }
    return r;
}

static int64_t u256_to_i64(uint256_t a) { return (int64_t)a.w[0]; }
static uint64_t u256_to_u64(uint256_t a) { return a.w[0]; }

static int u256_nbit(uint256_t v) {
    int sign = (int)(v.w[3] >> 63);
    if(sign){
        uint256_t av = u256_neg(v);
        if((int)(av.w[3] >> 63)){
            return 256;
        }
        v = av;
    }
    int b = 0;
    for (int wi = 3; wi >= 0; wi--) {
        if (v.w[wi]) {
            uint64_t word = v.w[wi];
            int bits = 0;
            while (word) { word >>= 1; bits++; }
            b = wi * 64 + bits;
            break;
        }
    }
    return b;
}

static uint256_t UNDEF_VAL(void) { return u256_not(u256_zero()); }
static int u256_is_undef(uint256_t a) { return u256_eq(a, UNDEF_VAL()); }
static int u256_is_undef_derived(uint256_t a) {
    if (u256_is_undef(a)) return 1;
    int sign = (int)(a.w[3] >> 63);
    uint256_t av = sign ? u256_neg(a) : a;
    if (av.w[3] != 0) {
        static int warned = 0;
        if (!warned) {
            warned = 1;
            axx_diagf(0, 0, " warning - a value whose signed absolute magnitude is >= 2**192 was "
                       "computed and is being treated as UNDEF-derived; this heuristic cannot "
                       "distinguish it from a genuine large 256-bit constant (e.g. an all-ones "
                       "bitmask) because uint256_t has no headroom beyond 256 bits for a true "
                       "out-of-band sentinel.\n");
        }
    }
    return av.w[3] != 0;
}

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

typedef struct { int *data; int len; int cap; } IStack;
static void is_init(IStack*v){v->data=NULL;v->len=0;v->cap=0;}
static void is_push(IStack*v,int x){
    if(v->len>=v->cap){v->cap=v->cap?v->cap*2:8;v->data=realloc(v->data,v->cap*sizeof(int));if(!v->data){perror("realloc");exit(1);}}
    v->data[v->len++]=x;
}
static int is_pop(IStack*v){return v->len>0?v->data[--v->len]:0;}

#define HASH_INIT_CAP 64

/* ラベル1個ぶんの定義。ハッシュ表 LabelMap のチェイン要素でもある。 */
typedef struct LabelEntry {
    char          *key;                 /* ラベル名 */
    uint256_t      value;               /* 値（.EQU なら定数、通常はアドレス） */
    char          *section;             /* 属するセクション名 */
    int            is_equ;              /* .EQU 由来か（アドレスではなく定数） */
    int            is_imported;         /* .extern の仮登録。実定義で上書き可 */
    int            reloc_type_override; /* `::型名` で明示指定されたリロケーション型 */
    int            is_undef;            /* 参照されたが未定義 */
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
static void lmap_set(LabelMap *m, const char *key, uint256_t val, const char *sec, int is_equ, int is_undef) {
    if(!m->nbuckets) return;
    uint32_t h=hash_str(key)%(uint32_t)m->nbuckets;
    for(LabelEntry*e=m->buckets[h];e;e=e->next){
        if(strcmp(e->key,key)==0){
            e->value=val; free(e->section); e->section=strdup(sec); e->is_equ=is_equ; e->is_undef=is_undef;
            e->is_imported = 0;
            e->reloc_type_override = -1;
            return;
        }
    }
    LabelEntry *e=calloc(1,sizeof(LabelEntry));
    e->key=strdup(key); e->value=val; e->section=strdup(sec);
    e->is_equ=is_equ; e->is_imported=0; e->reloc_type_override=-1; e->is_undef=is_undef;
    e->next=m->buckets[h]; m->buckets[h]=e; m->count++;
}
static void lmap_set_reloc_type(LabelMap *m, const char *key, int reloc_type) {
    LabelEntry *e = lmap_find(m, key);
    if(e) e->reloc_type_override = reloc_type;
}
static void lmap_set_imported(LabelMap *m, const char *key, uint256_t val, const char *sec, int reloc_type) {
    uint32_t h=hash_str(key)%(uint32_t)m->nbuckets;
    for(LabelEntry*e=m->buckets[h];e;e=e->next){
        if(strcmp(e->key,key)==0){
            e->value=val; free(e->section); e->section=strdup(sec);
            e->is_equ=0; e->is_imported=1; e->is_undef=0;
            if(reloc_type >= 0) e->reloc_type_override=reloc_type;
            return;
        }
    }
    LabelEntry *e=calloc(1,sizeof(LabelEntry));
    e->key=strdup(key); e->value=val; e->section=strdup(sec);
    e->is_equ=0; e->is_imported=1; e->reloc_type_override=reloc_type; e->is_undef=0;
    e->next=m->buckets[h]; m->buckets[h]=e; m->count++;
}
static void lmap_set_full(LabelMap *m, const char *key, uint256_t val,
                          const char *sec, int is_equ, int is_imported, int reloc_type_override,
                          int is_undef) {
    uint32_t h=hash_str(key)%(uint32_t)m->nbuckets;
    for(LabelEntry*e=m->buckets[h];e;e=e->next){
        if(strcmp(e->key,key)==0){
            e->value=val; free(e->section); e->section=strdup(sec);
            e->is_equ=is_equ; e->is_imported=is_imported;
            e->reloc_type_override=reloc_type_override;
            e->is_undef=is_undef;
            return;
        }
    }
    LabelEntry *e=calloc(1,sizeof(LabelEntry));
    e->key=strdup(key); e->value=val; e->section=strdup(sec);
    e->is_equ=is_equ; e->is_imported=is_imported;
    e->reloc_type_override=reloc_type_override;
    e->is_undef=is_undef;
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

/* セクション1個ぶん。.section / .endsection の出入りで複数回訪れうる。 */
typedef struct SecEntry {
    char       *name;
    uint256_t   start;      /* 開始アドレス（ワード単位） */
    uint256_t   size;       /* 累計ワード数 */
    uint256_t   entry_pc;   /* 今回このセクションに入ったときの pc */
    int         confirmed;  /* パス1で確定済みか */
    struct SecEntry *next;
} SecEntry;
typedef struct { SecEntry**buckets; int nb; SecEntry**order; int count; int cap; } SecMap;
static void secmap_init(SecMap*m){m->nb=16;m->buckets=calloc(m->nb,sizeof(SecEntry*));m->count=0;m->cap=16;m->order=calloc(m->cap,sizeof(SecEntry*));}
static SecEntry *secmap_find(SecMap*m,const char*name){
    uint32_t h=hash_str(name)%(uint32_t)m->nb;
    for(SecEntry*e=m->buckets[h];e;e=e->next) if(strcmp(e->name,name)==0)return e;
    return NULL;
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
static void secmap_clear(SecMap*m){
    for(int i=0;i<m->nb;i++){
        SecEntry*e=m->buckets[i];
        while(e){SecEntry*n=e->next;free(e->name);free(e);e=n;}
        m->buckets[i]=NULL;
    }
    for(int i=0;i<m->count;i++) m->order[i]=NULL;
    m->count=0;
}

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


/* パターンファイル1行ぶん。"::" 区切りで最大6フィールドに分解して持つ。
 *   f[0] 照合パターン（ニーモニックの書式）
 *   f[1] エラー条件（`条件;番号` 形式。ERRORS_TABLE の番号を返す）
 *   f[2] エンコーディング（カンマ区切りの式。ここを評価してバイト列を作る）
 *   f[3] サイズ / VLIW スロット番号
 *   f[4..5] 予備
 * 注意: 2フィールドしか書かれていない行は f[1] ではなく f[2] に入る。 */
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

/* 出力バッファ。アドレス→ワード値の疎なハッシュ表として持つので、
 * .ORG でアドレスが大きく飛んでもその間を埋めずに済む。 */
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

#define OB_CHAR  ((char)0x90)
#define CB_CHAR  ((char)0x91)
#define VLIW_SEP_CHAR  ((char)0x92)
#define VLIW_STOP_CHAR ((char)0x93)
#define EXP_PAT  0
#define EXP_ASM  1

static const char *ERRORS_TABLE[] = {
    "",
    "Invalid syntax.",
    "Address out of range.",
    "Value out of range.",
    "",
    "Register out of range.",
    "Port number out of range."
};
#define ERRORS_COUNT 7

/* =========================================================
 * AsmState — アセンブル中の全状態
 *
 * 式評価・パターン照合・ディレクティブ処理・出力生成の各関数は自前の状態を
 * 持たず、全てこの構造体を共有して読み書きする（axx.py の AssemblerState に対応）。
 * ========================================================= */
typedef struct {
    /* --- 出力先 --- */
    char outfile[512];       /* -b 生バイナリ */
    char expfile[512];       /* -e ラベル TSV */
    char expfile_elf[512];   /* -E ラベル TSV（ELF フラグ付き） */
    char impfile[512];       /* -i ラベル TSV の取り込み */
    uint256_t pc_overflow_max;  /* pc が 64bit を超えた場合の記録（警告用） */
    int       pc_overflow_set;
    int  osabi;              /* ELF ヘッダの OSABI（9=FreeBSD） */

    /* --- 位置カウンタ --- */
    uint256_t pc;            /* 現在のプログラムカウンタ（ワード単位） */
    uint256_t padding;       /* .padding の詰め物値 */

    /* 識別子に使える文字集合（.labelc 等で変更可能） */
    char lwordchars[256];    /* ラベル名 */
    char swordchars[256];    /* .setsym シンボル名 */

    char current_section[512];
    char current_file[512];

    /* --- 記号表 --- */
    LabelMap   labels;         /* ソース側ラベル */
    SecMap     sections;       /* セクション */
    SymMap     symbols;        /* 現在有効なシンボル */
    SymMap     patsymbols;     /* パターンファイルの .setsym 由来 */
    LabelMap   export_labels;  /* .global 等で外部公開するラベル */
    StrVec     export_order;   /* 公開順（出力の再現性のため） */
    PatVec     pat;            /* 読み込んだパターン表 */

    /* --- VLIW / EPIC --- */
    int        vliwinstbits;     /* 命令スロット1個のビット幅 */
    IntVec     vliwnop;          /* 余ったスロットを埋める NOP バイト列 */
    int        vliwbits;         /* パケット全体のビット幅 */
    VliwSet    vliwset;          /* EPIC: スロット組み合わせ→テンプレート値 */
    int        vliwflag;         /* .vliw が宣言済みか */
    int        vliwtemplatebits; /* テンプレート幅（負なら上位側に配置） */
    int        vliwstop;         /* この行が `!!!!` で終わったか */
    int        vcnt;             /* この行のスロット数 */

    /* --- 式評価とエラー状態 --- */
    int        expmode;        /* EXP_PAT=パターン側 / EXP_ASM=ソース側 */
    int        exp_typ_float;  /* 浮動小数点モードか */

    /* 直近の式評価で未定義ラベルを踏んだか。「失敗時に立てる」だけで
     * 成功しても降ろさない（1つの式が複数ラベルを引くため、途中で降ろすと
     * 先に起きた失敗が消える）。降ろすのは .ORG/.RESB/.ZERO/.ALIGN/.EQU 等、
     * 新規に判定したい側が評価直前に自分で行う。 */
    int        error_undefined_label;
    int        error_already_defined;

    /* ユーザ向けの " error - ..." を1度でも表示したら立ち、以後降ろさない。
     * 最後にこれを見て、立っていれば出力を書かず終了コード1で終わる
     * （不完全・誤ったバイナリを黙って残さないため）。 */
    int        had_error;

    /* パターン照合の試行中か。試行中のエラーは本物の失敗とは限らないので
     * 表示を抑制する。 */
    int        in_match_attempt;

    int        match_score_expr;
    int        match_score_sym;
    int        match_score_lit;

    uint256_t  pc_instr_start;
    uint256_t  pc_instr_end;
    int        in_binary_list;

    uint256_t  align;
    int        bts;
    int        endian_big;
    int        pas;
    int        debug;
    int        verbose;

    char       cl[4096];
    int        ln;
    StrVec     fnstack;
    IStack     lnstack;

    PatVar     vars[26];

    char deb1[4096];
    char deb2[4096];

    BufMap     buf;

    int        pass1_size_mode;

    char       stdin_tmp_path[512];

    char       elf_objfile[512];
    int        elf_machine;
    int        elf_class;

    /* --- DWARF デバッグ情報（-g） --- */
    int        gen_debug;
    /* pc とソース行の対応表。.debug_line の生成に使う */
    struct { char *section; uint64_t word_pc; char *file; int line; } *line_map;
    int        line_map_len;
    int        line_map_cap;

    /* --- パス2でのリロケーション収集 ---
     * 式評価中にラベル参照を見つけるたび elf_refs へ (名前, 生値, 何ワード目か)
     * を積む。1命令ぶん組み立て終わった時点でこれをまとめ、同じラベルへの
     * 連続した参照を1つのリロケーションに束ねて relocations へ確定させる。 */
    int        elf_tracking;
    struct { char *name; uint64_t val; int word_idx; } *elf_refs;
    int        elf_refs_len;
    int        elf_refs_cap;
    int        elf_current_word_idx;
    struct {
        int      set;
        char    *label_name;
        uint64_t label_val;
    }          elf_var_to_label[26];
    char       elf_capturing_var;
    struct {
        char   *section;
        int64_t sec_offset;
        char   *sym;
        int     rtype;
        int64_t addend;
        int     nbytes;
    } *relocations;
    int        reloc_count;
    int        reloc_cap;

    int        reloctype_override[4];

    /* .check で登録された「変数 a〜z が満たすべき条件」 */
    StrVec     check_constraints[26];

    /* 式の再帰深度。深すぎる入れ子でネイティブスタックを溢れさせない番人 */
    int        expr_depth;

    /* --- パス1のリラクゼーション（サイズ収束） ---
     * relax_prev は前回反復での「ラベル→アドレス」。今回と一致したら収束。
     * relax_optimistic は未確定の前方参照を「近い」と仮定して収束を早めるモード。 */
    LabelMap  *relax_prev;

    int        relax_optimistic;

    char      *pat_include_chain[64];
    int        pat_include_depth;

    char       combo_budget_warned_file[64][512];
    int        combo_budget_warned_line[64];
    int        combo_budget_warned_count;

    SecRangeVec section_ranges;

    int        equ_section_tracking;
    char       equ_first_section[64];
    int        equ_multi_section;

    /* パターン照合の試行中に出た診断を溜める箱。
     * そのパターンが最終的に採用されたときだけ再生して表示する。 */
    char     **diag_pending;
    int       *diag_pending_seterr;
    int        diag_pending_len;
    int        diag_pending_cap;
    int        diag_capturing;
} AsmState;

/* ユーザ向けエラーを今表示してよいパスか。
 * パス2（最終）と対話モード(0)のみ。パス1のリラクゼーション中は同じエラーが
 * 反復回数だけ重複するうえ、前方参照が未解決なだけの偽エラーも多い。 */
static inline int should_report_errors(const AsmState *st) {
    return st->pas == 2 || st->pas == 0;
}


static AsmState *g_active_state = NULL;

static void diag_pending_push(AsmState *st, const char *text, int set_error){
    if(st->diag_pending_len >= st->diag_pending_cap){
        int nc = st->diag_pending_cap ? st->diag_pending_cap*2 : 8;
        char **nt = realloc(st->diag_pending, (size_t)nc*sizeof(char*));
        int   *ns = realloc(st->diag_pending_seterr, (size_t)nc*sizeof(int));
        if(!nt || !ns){ free(nt); free(ns); return; }
        st->diag_pending = nt; st->diag_pending_seterr = ns;
        st->diag_pending_cap = nc;
    }
    char *cp = strdup(text);
    if(!cp) return;
    st->diag_pending[st->diag_pending_len]        = cp;
    st->diag_pending_seterr[st->diag_pending_len] = set_error;
    st->diag_pending_len++;
}

static void diag_capture_begin(AsmState *st){
    for(int i=0;i<st->diag_pending_len;i++) free(st->diag_pending[i]);
    st->diag_pending_len = 0;
    st->diag_capturing   = 1;
}

static void diag_capture_take(AsmState *st, char ***texts, int **seterr, int *n){
    *texts  = st->diag_pending;
    *seterr = st->diag_pending_seterr;
    *n      = st->diag_pending_len;
    st->diag_pending        = NULL;
    st->diag_pending_seterr = NULL;
    st->diag_pending_len    = 0;
    st->diag_pending_cap    = 0;
    st->diag_capturing      = 0;
}

static void diag_replay(AsmState *st, char **texts, int *seterr, int n){
    for(int i=0;i<n;i++){
        if(should_report_errors(st)){
            fputs(texts[i], stderr);
            if(seterr[i]) st->had_error = 1;
        }
    }
}

static void axx_diagf(int set_error, int force, const char *fmt, ...){
    AsmState *st = g_active_state;
    char buf[2048];
    va_list ap;
    va_start(ap, fmt);
    vsnprintf(buf, sizeof(buf), fmt, ap);
    va_end(ap);

    if(st && !force){
        if(st->in_match_attempt){
            if(st->diag_capturing) diag_pending_push(st, buf, set_error);
            return;
        }
        if(!should_report_errors(st)) return;
    }
    fputs(buf, stderr);
    if(st && set_error) st->had_error = 1;
}

static void axx_oserr_str(const char *fn, int err, char *out, size_t osz){
    char q[1024]; m_pyrepr(fn ? fn : "", q, sizeof(q));
    snprintf(out, osz, "[Errno %d] %s: %s", err, strerror(err), q);
}

static FILE *axx_open_input(const char *fn, const char *what){
    char eb[1200];
    struct stat sb;
    if(stat(fn, &sb)==0 && S_ISDIR(sb.st_mode)){
        axx_oserr_str(fn, EISDIR, eb, sizeof(eb));
        axx_diagf(1, 0, " error - cannot open %s '%s': %s\n", what, fn, eb);
        return NULL;
    }
    FILE *f = fopen(fn, "rt");
    if(!f){
        axx_oserr_str(fn, errno, eb, sizeof(eb));
        axx_diagf(1, 0, " error - cannot open %s '%s': %s\n", what, fn, eb);
        return NULL;
    }
    return f;
}

typedef struct { const char *name; int rtype; int width; } ElfNamedReloc;

typedef struct {
    int         machine;
    const char *name;
    int         elfclass;
    int         is_rela;
    int         extern_default;
    int         dwarf_abs;
    int         wg8, wg4, wg2, wg1;
    const int  *pc_rel;
    int         pc_rel_n;
    const ElfNamedReloc *named;
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
    {"abs64", 2, 8}, {"abs32", 1, 4}, {"abs16", 34, 2}, {"abs8", 33, 1},
    {NULL, 0, 0},
};

/* アーキテクチャ別 ELF 情報表（axx.py の ELF_MACHINES に対応）。
 * 列の意味は左から:
 *   e_machine, 名前, elfclass(1=32/2=64), is_rela(1=RELA/0=REL),
 *   外部シンボルの既定型, 幅4の既定型, 幅8の既定型, 幅2の既定型, 幅1の既定型,
 *   PC相対型の一覧, DWARF絶対参照の型, 記号名テーブル
 * REL（加数を命令バイト列に埋め込む形式）を使うのは i386 と ARM(32) だけで、
 * 他は全て RELA（加数を専用フィールドに持つ）。 */
static const ElfMachineInfo ELF_MACHINES[] = {
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

static int elf_machine_named(const ElfMachineInfo *m, const char *name){
    if(!m) return -1;
    for(int i=0; m->named[i].name; i++)
        if(strcasecmp(m->named[i].name, name)==0) return m->named[i].rtype;
    return -1;
}

static const char *elf_machine_reverse(const ElfMachineInfo *m, int rtype){
    if(!m) return NULL;
    for(int i=0; m->named[i].name; i++)
        if(m->named[i].rtype == rtype) return m->named[i].name;
    return NULL;
}

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

static void secmap_finalize_current(AsmState *st){
    SecEntry *e = secmap_find(&st->sections, st->current_section);
    if(!e) return;
    uint256_t delta = u256_sub(st->pc, e->entry_pc);
    if(u256_lt_signed(delta, u256_zero())) return;
    e->size = u256_add(e->size, delta);
    if(!u256_is_zero(delta))
        secrangevec_push(&st->section_ranges, st->current_section, e->entry_pc, delta);
    e->entry_pc = st->pc;
}

static uint64_t dwarf_word_offset(AsmState *st, const char *sec_name, uint64_t word_pc, int bpw){
    if(st->sections.count == 0) return word_pc * (uint64_t)bpw;
    int64_t o = addr_to_word_offset(&st->section_ranges, sec_name, word_pc);
    return (uint64_t)(o >= 0 ? o : 0) * (uint64_t)bpw;
}

static int64_t equ_section_relative_offset(AsmState *st, const char *sec_name, uint64_t word_pc){
    int64_t o = addr_to_word_offset(&st->section_ranges, sec_name, word_pc);
    if(o >= 0) return o;
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
    g_active_state = st;
    strcpy(st->lwordchars, "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz_.");
    strcpy(st->swordchars, "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz_%$-~&|");
    strcpy(st->current_section, ".text");
    lmap_init(&st->labels);
    secmap_init(&st->sections);
    smap_init(&st->symbols);
    smap_init(&st->patsymbols);
    lmap_init(&st->export_labels);
    sv_init(&st->export_order);
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
    st->align = u256_from_u64(16);
    st->bts = 8;
    st->endian_big = 0;
    st->pas = 0;
    st->debug = 0;
    st->osabi = 9;
    st->ln = 0;
    sv_init(&st->fnstack);
    is_init(&st->lnstack);
    for(int i=0;i<26;i++){ st->vars[i].val=u256_zero(); st->vars[i].is_undef=0; }
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
    st->elf_class = 2;
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
    for(int _ci=0; _ci<26; _ci++) sv_init(&st->check_constraints[_ci]);
}

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

/* パターンファイルのコメント（スラッシュ＋アスタリスク以降）を落とす。
 * 行単位で扱うので閉じ記号は不要。 */
static void axx_remove_comment(char *l) {
    for(int i=0;l[i];i++){
        if(l[i]=='/'&&l[i+1]=='*'){
            l[i]=0; return;
        }
    }
}

/* アセンブリソースの `;` コメントを落とす。
 * 文字列 "..." や文字リテラル 'x' の中の `;` は本物のデータなので残す。
 * 引用符の外の `\;` はエスケープとして扱い、バックスラッシュを外した
 * リテラルな `;` に変える（コメントを開始させない）。
 * 文字列が縮むので、読み位置 i と書き位置 w を分けた in-place 詰め直しで行う
 * （常に w <= i なので同じバッファを上書きしても安全）。 */
static void axx_remove_comment_asm(char *l) {
    char *orig = strdup(l);
    int in_str=0;
    int i=0, w=0;
    while(l[i]){
        if(in_str && l[i]=='\\'){
            l[w++]=l[i++];
            if(l[i]) l[w++]=l[i++];
            continue;
        }
        if(!in_str && l[i]=='\\' && l[i+1]==';'){
            l[w++]=';';
            i+=2;
            continue;
        }
        if(l[i]=='"'){ in_str=!in_str; l[w++]=l[i++]; continue; }
        if(l[i]=='\'' && !in_str){
            int j=i+1;
            if(l[j]=='\\' && l[j+1] && l[j+2]=='\''){
                while(i<j+3) l[w++]=l[i++];
                continue;
            } else if(l[j] && l[j+1]=='\''){
                while(i<j+2) l[w++]=l[i++];
                continue;
            }
            l[w++]=l[i++]; continue;
        }
        if(l[i]==';'&&!in_str){
            int j=w-1;
            while(j>=0&&(l[j]==' '||l[j]=='\t')) j--;
            l[j+1]=0; free(orig); return;
        }
        l[w++]=l[i++];
    }
    l[w]=0;
    int j=w-1;
    while(j>=0&&(l[j]==' '||l[j]=='\t'||l[j]=='\n'||l[j]=='\r')) l[j--]=0;
    if(in_str){
        char r[1024]; m_pyrepr(orig?orig:"", r, sizeof(r));
        axx_diagf(0, 0, " warning - unterminated string literal in line: %s\n", r);
    }
    free(orig);
}

/* ソース行の `\!` を解決し、本物の VLIW 区切りを番兵に置き換える。
 *
 * 2つの処理を必ず1回の左→右走査で同時に行う:
 *   `\!`   → リテラルな `!`（バックスラッシュを外す）
 *   `!!`   → VLIW_SEP_CHAR   （本物のスロット区切り）
 *   `!!!!` → VLIW_STOP_CHAR  （本物のストップビット）
 *
 * 同時でなければならない理由: 先に `\!\!` を `!!` へ戻してしまうと、後から
 * 区切りを探す別の走査からは「エスケープ由来のただの !!」と「本物の区切り」を
 * 区別できない。後続の走査はどの !! がエスケープだったかを覚えていないからである。
 * ここで一度だけ判定して本物だけを番兵にしておけば、以降の全ての箇所
 * （lineassemble() の後処理、vliwprocess() のスロット走査、
 * axx_get_param_to_spc()/axx_get_param_to_eon()）は番兵だけを見ればよい。
 *
 * 文字列 "..." と文字リテラル 'x' の中身はそのまま素通しする。
 * 呼ぶのは axx_remove_comment_asm() が `\;` を解決した後なので、ここで面倒を
 * 見るのは `\!` だけでよい。 */
static void axx_resolve_vliw_escapes(char *l) {
    int in_str=0;
    int i=0, w=0;
    while(l[i]){
        if(in_str && l[i]=='\\'){
            l[w++]=l[i++];
            if(l[i]) l[w++]=l[i++];
            continue;
        }
        if(!in_str && l[i]=='\\' && l[i+1]=='!'){
            l[w++]='!';
            i+=2;
            continue;
        }
        if(l[i]=='"'){ in_str=!in_str; l[w++]=l[i++]; continue; }
        if(l[i]=='\'' && !in_str){
            int j=i+1;
            if(l[j]=='\\' && l[j+1] && l[j+2]=='\''){
                while(i<j+3) l[w++]=l[i++];
                continue;
            } else if(l[j] && l[j+1]=='\''){
                while(i<j+2) l[w++]=l[i++];
                continue;
            }
            l[w++]=l[i++]; continue;
        }
        if(!in_str && l[i]=='!'&&l[i+1]=='!'&&l[i+2]=='!'&&l[i+3]=='!'){
            l[w++]=VLIW_STOP_CHAR;
            i+=4;
            continue;
        }
        if(!in_str && l[i]=='!'&&l[i+1]=='!'){
            l[w++]=VLIW_SEP_CHAR;
            i+=2;
            continue;
        }
        l[w++]=l[i++];
    }
    l[w]=0;
}

/* 空白区切りで1語（ニーモニック部分）を切り出す。
 * VLIW 区切りの番兵でも切る（`NOP!!NOP` のように空白なしで次スロットが続く
 * 書き方で、ニーモニックが隣のスロットを飲み込まないように）。
 *
 * 番兵の判定は引用符の外だけで行う。番兵を「挿入」する
 * axx_resolve_vliw_escapes() が引用符の中を素通ししている以上、「探す」側も
 * 引用符の中を見てはいけない。番兵の値 0x92/0x93 は UTF-8 の継続バイトでもあり、
 * .ascii "..." の中の多バイト文字（例: 日本語）に生の 0x92/0x93 が正当に現れる
 * ため、引用符内で判定すると文字列の途中で切れてしまう。 */
static int axx_get_param_to_spc(const char *s, int idx, char *t, size_t tsz) {
    idx=axx_skipspc(s,idx);
    size_t n=0;
    int in_str=0;
    while(s[idx]&&n<tsz-1){
        if(!in_str&&(s[idx]==' '||s[idx]==VLIW_SEP_CHAR||s[idx]==VLIW_STOP_CHAR)) break;
        if(s[idx]=='"') in_str=!in_str;
        else if(in_str&&s[idx]=='\\'&&s[idx+1]){ t[n++]=s[idx++]; if(n>=tsz-1) break; }
        t[n++]=s[idx++];
    }
    t[n]=0;
    return idx;
}

/* 行の残り（空白を含む＝オペランド部分）を VLIW 区切りの手前まで取る。
 * 番兵の判定を引用符の外だけで行う理由は axx_get_param_to_spc() を参照。 */
static int axx_get_param_to_eon(const char *s, int idx, char *t, size_t tsz) {
    idx=axx_skipspc(s,idx);
    size_t n=0;
    int in_str=0;
    while(s[idx]&&n<tsz-1){
        if(!in_str&&(s[idx]==VLIW_SEP_CHAR||s[idx]==VLIW_STOP_CHAR)) break;
        if(s[idx]=='"') in_str=!in_str;
        else if(in_str&&s[idx]=='\\'&&s[idx+1]){ t[n++]=s[idx++]; if(n>=tsz-1) break; }
        t[n++]=s[idx++];
    }
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
                idx+=2;
                char hex[3]; int hn=0;
                while(l2[idx]&&is_xdigit_upper(axx_upper_char(l2[idx]))&&hn<2)
                    hex[hn++]=l2[idx++];
                hex[hn]=0;
                if(hn>0){
                    out[n++]=(char)(int)strtol(hex,NULL,16);
                } else {
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
        axx_diagf(0, 0, " warning - unterminated string literal: %s\n", l2);
}

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
    if(strncmp(s+idx,"-inf",4)==0){strcpy(fs,"-inf");return idx+4;}
    if(strncmp(s+idx,"inf",3)==0){strcpy(fs,"inf");return idx+3;}
    if(strncmp(s+idx,"nan",3)==0){strcpy(fs,"nan");return idx+3;}
    size_t n=0;
    while(s[idx]&&(is_digit(s[idx])||s[idx]=='.')&&n<fsz-1) fs[n++]=s[idx++];
    if((s[idx]=='e'||s[idx]=='E') && n<fsz-1){
        int saved_idx = idx;
        size_t saved_n = n;
        fs[n++]=s[idx++];
        if((s[idx]=='+'||s[idx]=='-')&&n<fsz-1) fs[n++]=s[idx++];
        int digits_start = idx;
        while(s[idx]&&is_digit(s[idx])&&n<fsz-1) fs[n++]=s[idx++];
        if(idx == digits_start){
            idx = saved_idx;
            n   = saved_n;
        }
    }
    fs[n]=0;
    return idx;
}

static int axx_get_curlb(AsmState *st, const char *s, int idx, int *f_out, char *t_out, size_t tsz){
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
        if(should_report_errors(st)){
            axx_diagf(1, 0, " error - missing closing '}' in expression: '{%s'\n", t_out);
        }
        return (int)strlen(s);
    }
    idx++;
    *f_out=1;
    return idx;
}

static int axx_get_symbol_word(const char *s, int idx, const char *swordchars, char *t_out, size_t tsz){
    t_out[0]=0;
    if(!s[idx]||is_digit(s[idx])||!char_in(s[idx],swordchars)) return idx;
    size_t n=0;
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



#if defined(__GNUC__) && !defined(__STRICT_ANSI__) && \
    (defined(__x86_64__) || defined(__i386__) || defined(__aarch64__) || \
     defined(__arm__) || defined(__riscv))

static __float128 f128_from_decimal(const char *s)
{
    const __float128 ten  = (__float128)10;
    const __float128 one  = (__float128)1;

    int sign = 0;
    if(*s == '-'){ sign = 1; s++; }
    else if(*s == '+'){ s++; }

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

    __float128 denom = one;
    for(int i = 0; i < frac_digits; i++) denom *= ten;
    __float128 result = int_val / denom;

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

typedef struct { __float128 val; const char *end; int ok; } F128R;

static F128R f128_expr_fn(const char *s);

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
            if(r2.val!=(__float128)0){ r.val/=r2.val; r.end=r2.end; }
            else {
                r.ok=0;
                return r;
            }
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

static uint256_t f128_eval_text(const char *text, int *ok_out)
{
    F128R r = f128_expr_fn(text);
    if(r.ok){
        double dcheck = (double)r.val;
        if(!isfinite(dcheck)) r.ok = 0;
    }
    if(ok_out) *ok_out = r.ok;
    if(!r.ok)  return u256_zero();
    return f128_to_u256(r.val);
}

#endif

static uint256_t ieee754_128_from_str(const char *a){
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
    int ok = 0;
    uint256_t r = f128_eval_text(a, &ok);
    if(ok) return r;
#endif

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
    long double sig = frexpl(ld, &fe);
    sig *= 2.0L;
    int exp_unbiased = fe - 1;
    int biased_exp = exp_unbiased + 16383;
    if(biased_exp <= 0)  biased_exp = 0;
    if(biased_exp >= 32767) {
        uint256_t r=u256_zero();
        r.w[1] = (uint64_t)(sign?1ULL:0ULL)<<63 | 0x7FFF000000000000ULL;
        return r;
    }
    long double frac_part = sig - 1.0L;
    uint64_t hi = 0;
    for(int b=47;b>=0;b--){
        frac_part *= 2.0L;
        if(frac_part >= 1.0L){ hi |= ((uint64_t)1<<b); frac_part -= 1.0L; }
    }
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

static inline double u256_to_double(uint256_t v){
    double d; memcpy(&d, &v.w[0], 8); return d;
}
static inline uint256_t double_to_u256(double d){
    uint256_t r = u256_zero(); memcpy(&r.w[0], &d, 8); return r;
}
static int axx_isfloatstr(const char *s, int idx){
    if(!s[idx]) return 0;
    if(strncmp(s+idx,"-inf",4)==0) return 1;
    if(strncmp(s+idx,"inf",3)==0) return 1;
    if(strncmp(s+idx,"nan",3)==0) return 1;
    if(is_digit(s[idx])) return 1;
    if(s[idx]=='.' && is_digit((unsigned char)s[idx+1])) return 1;
    return 0;
}

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

struct Assembler {
    AsmState st;
    SecRangeVec imp_sections;
};

static void assembler_init(Assembler *a){
    state_init(&a->st);
    secrangevec_init(&a->imp_sections);
}

static uint256_t align_addr256(AsmState *st, uint256_t addr){
    if(u256_is_zero(st->align)) return addr;
    uint256_t q = u256_udiv(addr, st->align);
    uint256_t a = u256_sub(addr, u256_mul(q, st->align));
    if(u256_is_zero(a)) return addr;
    return u256_add(addr, u256_sub(st->align, a));
}
static uint64_t align_addr(AsmState *st, uint64_t addr){
    return u256_to_u64(align_addr256(st, u256_from_u64(addr)));
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
    if(!buf_found) return;
    int word_bits = st->bts;
    int bytes_per_word = (word_bits+7)/8;
    if(st->pc_overflow_set){
        uint256_t _tot = u256_mul(u256_add(st->pc_overflow_max, u256_from_u64(1)),
                                  u256_from_u64((uint64_t)bytes_per_word));
        char _tb[96]; u256_to_pydec(_tot, _tb, sizeof(_tb));
        axx_diagf(1, 1, " error - output size %s bytes exceeds maximum %llu."
                        " Check for incorrect .ORG or address values.\n",
                  _tb, (unsigned long long)((uint64_t)1<<30));
        return;
    }
    if(max_pos == (uint64_t)-1){
        uint256_t _tot = u256_mul(u256_shl(u256_from_u64(1), 64),
                                  u256_from_u64((uint64_t)bytes_per_word));
        char _tb[96]; u256_to_pydec(_tot, _tb, sizeof(_tb));
        axx_diagf(1, 1, " error - output size %s bytes exceeds maximum %llu."
                        " Check for incorrect .ORG or address values.\n",
                  _tb, (unsigned long long)((uint64_t)1<<30));
        return;
    }
    uint64_t total_size = (max_pos+1)*(uint64_t)bytes_per_word;
    if(total_size==0) return;
    {
        const uint64_t MAX_OUTPUT_BYTES = (uint64_t)1<<30;
        if(total_size > MAX_OUTPUT_BYTES){
            axx_diagf(1, 1, " error - output size %llu bytes exceeds maximum %llu."
                            " Check for incorrect .ORG or address values.\n",
                      (unsigned long long)total_size,
                      (unsigned long long)MAX_OUTPUT_BYTES);
            return;
        }
    }
    if(total_size > (uint64_t)(size_t)-1){
        fprintf(stderr,"binary_flush: output too large (%llu bytes) for this platform's size_t.\n",
                (unsigned long long)total_size);
        return;
    }
    unsigned char *data = calloc(1, (size_t)total_size);
    if(!data){perror("calloc");return;}

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

static uint256_t var_get(AsmState *st, char ch){
    ch=(char)axx_upper_char(ch);
    if(ch>='A'&&ch<='Z') return st->vars[ch-'A'].val;
    return u256_zero();
}
static int var_get_is_undef(AsmState *st, char ch){
    ch=(char)axx_upper_char(ch);
    if(ch>='A'&&ch<='Z') return st->vars[ch-'A'].is_undef;
    return 0;
}
static void var_put(AsmState *st, char ch, uint256_t v){
    ch=(char)axx_upper_char(ch);
    if(ch>='A'&&ch<='Z'){ st->vars[ch-'A'].val=v; st->vars[ch-'A'].is_undef=0; }
}
static void var_put_tagged(AsmState *st, char ch, uint256_t v, int is_undef){
    ch=(char)axx_upper_char(ch);
    if(ch>='A'&&ch<='Z'){ st->vars[ch-'A'].val=v; st->vars[ch-'A'].is_undef=is_undef; }
}

/* ラベルの値を引く。
 * 見つからなければ st->error_undefined_label を「立てる」。成功しても降ろさない
 * のが重要な約束で、1つの式が複数のラベルを引くため、途中で降ろすと先に起きた
 * 失敗の情報が消えてしまう。新規に判定したい側が評価直前に自分で降ろす。 */
static uint256_t label_get_value(AsmState *st, const char *k){
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
            int64_t _adj = equ_section_relative_offset(st, sec, u256_to_u64(e->value));
            if(_adj >= 0) ret_val = u256_from_u64((uint64_t)_adj);
        }
        int _equ_has_reloc = e->is_equ && (e->reloc_type_override >= 0);
        if(st->elf_tracking && (!e->is_equ || _equ_has_reloc)){
            if(st->elf_capturing_var != '\0'){
                int vi = (unsigned char)st->elf_capturing_var - 'a';
                if(vi >= 0 && vi < 26){
                    if(st->elf_var_to_label[vi].set == 0){
                        st->elf_var_to_label[vi].set = 1;
                        free(st->elf_var_to_label[vi].label_name);
                        st->elf_var_to_label[vi].label_name = strdup(k);
                        st->elf_var_to_label[vi].label_val = u256_to_u64(e->value);
                    } else {
                        st->elf_var_to_label[vi].set = -1;
                        free(st->elf_var_to_label[vi].label_name);
                        st->elf_var_to_label[vi].label_name = NULL;
                    }
                }
            } else if(st->elf_current_word_idx >= 0){
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
    if(st->pas == 1 && st->relax_prev){
        LabelEntry *pe = lmap_find(st->relax_prev, k);
        if(pe && !pe->is_undef){
            return pe->value;
        }
    }
    if(st->pas == 1 && st->relax_optimistic){
        st->error_undefined_label = 1;
        return st->pc;
    }
    st->error_undefined_label = 1;
    if(st->pass1_size_mode) return u256_zero();
    if(!st->in_match_attempt && should_report_errors(st)){
        axx_diagf(0, 0, " error - Label undefined: '%s'  [%s:%d]\n",
                   k, st->current_file, (int)st->ln);
    }
    return UNDEF_VAL();
}
static const char *label_get_section(AsmState *st, const char *k){
    LabelEntry *e=lmap_find(&st->labels,k);
    if(e) return e->section;
    st->error_undefined_label=1;
    return "";
}
/* ラベルを定義する。パスによって意味が変わる:
 *   パス1/対話 … 新規定義。既に在れば二重定義エラー。ただし .extern による
 *                 仮登録(is_imported)は実体を持たないので上書きを許す。
 *   パス2      … パス1で既に在るはず。無ければ両パスで見た入力が違うという異常。
 * パターンファイルの .setsym と同名なら衝突として拒否する。 */
static int label_put_value(AsmState *st, const char *k, uint256_t v, const char *sec, int is_equ, int reloc_type, int is_undef){
    if(st->pas==1||st->pas==0){
        LabelEntry *_existing = lmap_find(&st->labels,k);
        if(_existing && !_existing->is_imported){
            st->error_already_defined=1;
            st->had_error=1;
            axx_diagf(0, 0, " error - label already defined.\n");
            return 0;
        }
    } else if(st->pas==2){
        if(!lmap_contains(&st->labels,k)){
            st->error_already_defined=1;
            st->had_error=1;
            if(should_report_errors(st))
                axx_diagf(0, 0, " error - label '%s' not defined in pass 1.\n",k);
            return 0;
        }
    }
    char uk[512]; axx_strupr_to(uk,k,sizeof(uk));
    uint256_t dummy;
    if(smap_get(&st->patsymbols,uk,&dummy)){
        st->had_error=1;
        if(should_report_errors(st))
            axx_diagf(0, 0, " error - '%s' is a pattern file symbol.\n",k);
        return 0;
    }
    st->error_already_defined=0;
    lmap_set(&st->labels,k,v,sec,is_equ,is_undef);
    if(reloc_type >= 0)
        lmap_set_reloc_type(&st->labels, k, reloc_type);
    return 1;
}
static void u256_to_pyhex(uint256_t a, char *out, size_t outsz){
    char buf[80]; size_t n=0; int neg=0;
    if((a.w[3]>>63)&1ULL){ neg=1; a=u256_neg(a); }
    int hi=3; while(hi>0 && a.w[hi]==0) hi--;
    n += (size_t)snprintf(buf+n,sizeof(buf)-n,"%llx",(unsigned long long)a.w[hi]);
    for(int i=hi-1;i>=0;i--)
        n += (size_t)snprintf(buf+n,sizeof(buf)-n,"%016llx",(unsigned long long)a.w[i]);
    snprintf(out,outsz,"%s0x%s",neg?"-":"",buf);
}

static void u256_to_pydec(uint256_t a, char *out, size_t outsz){
    char buf[96]; int n=0; int neg=0;
    if((a.w[3]>>63)&1ULL){ neg=1; a=u256_neg(a); }
    if(u256_is_zero(a)){ snprintf(out,outsz,"0"); return; }
    uint256_t ten = u256_from_u64(10);
    while(!u256_is_zero(a) && n < (int)sizeof(buf)-1){
        uint256_t q = u256_udiv(a, ten);
        uint256_t r = u256_sub(a, u256_mul(q, ten));
        buf[n++] = (char)('0' + (int)(r.w[0] & 0xf));
        a = q;
    }
    char rev[96]; int m=0;
    if(neg) rev[m++]='-';
    while(n>0 && m < (int)sizeof(rev)-1) rev[m++] = buf[--n];
    rev[m]='\0';
    snprintf(out,outsz,"%s",rev);
}

static int label_key_cmp(const void *pa, const void *pb){
    const LabelEntry *a = *(const LabelEntry *const *)pa;
    const LabelEntry *b = *(const LabelEntry *const *)pb;
    return strcmp(a->key, b->key);
}

static void label_print_all(AsmState *st){
    int n=0;
    for(int i=0;i<st->labels.nbuckets;i++)
        for(LabelEntry*e=st->labels.buckets[i];e;e=e->next) n++;
    if(n==0) return;
    LabelEntry **v=(LabelEntry**)malloc(sizeof(LabelEntry*)*(size_t)n);
    if(!v) return;
    int k=0;
    for(int i=0;i<st->labels.nbuckets;i++)
        for(LabelEntry*e=st->labels.buckets[i];e;e=e->next) v[k++]=e;
    qsort(v,(size_t)n,sizeof(LabelEntry*),label_key_cmp);
    for(int i=0;i<n;i++){
        char val[80];
        if(v[i]->is_undef) snprintf(val,sizeof(val),"UNDEF");
        else u256_to_pyhex(v[i]->value,val,sizeof(val));
        fprintf(stderr,"  %-40s  %s  (%s)\n",v[i]->key,val,v[i]->section);
    }
    free(v);
}

static int symbol_get(AsmState *st, const char *w, uint256_t *out){
    char uw[512]; axx_strupr_to(uw,w,sizeof(uw));
    return smap_get(&st->symbols,uw,out);
}

static long double u256_to_long_double(uint256_t v){
    int neg = (int)((v.w[3] >> 63) & 1);
    uint256_t m = v;
    if(neg){
        uint64_t carry = 1;
        for(int i=0;i<4;i++){
            uint64_t inv = ~m.w[i];
            uint64_t sum = inv + carry;
            carry = (sum < inv) ? 1u : 0u;
            m.w[i] = sum;
        }
    }
    long double r = 0.0L;
    for(int i=3;i>=0;i--){
        r = r * 18446744073709551616.0L + (long double)m.w[i];
    }
    return neg ? -r : r;
}

typedef struct { const char *s; int i; int len; int ok; Assembler *asmb; } XEP;

static long double xeval_expr(XEP *p);

static void xeval_skip(XEP *p){
    while(p->i<p->len && (p->s[p->i]==' '||p->s[p->i]=='\t')) p->i++;
}

static long double xeval_primary(XEP *p){
    xeval_skip(p);
    if(!p->ok || p->i>=p->len){ p->ok=0; return 0; }
    char c = p->s[p->i];
    if(c=='('){
        p->i++;
        long double v = xeval_expr(p);
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
        AsmState *st=&p->asmb->st;
        LabelEntry *e = lmap_find(&st->labels, name);
        if(!e || e->is_undef){
            st->error_undefined_label = 1;
            return 0;
        }
        return u256_to_long_double(e->value);
    }
    if(isalpha((unsigned char)c) || c=='_'){
        int start=p->i;
        while(p->i<p->len && (isalnum((unsigned char)p->s[p->i])||p->s[p->i]=='_')) p->i++;
        char name[64]; int n=p->i-start; if(n>(int)sizeof(name)-1) n=(int)sizeof(name)-1;
        memcpy(name,p->s+start,(size_t)n); name[n]='\0';
        xeval_skip(p);
        if(p->i>=p->len || p->s[p->i]!='('){
            p->ok=0; return 0;
        }
        p->i++;
        long double arg = xeval_expr(p);
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

static long double xeval_unary(XEP *p);

static long double xeval_power(XEP *p){
    long double base = xeval_primary(p);
    xeval_skip(p);
    if(p->ok && p->i+1<p->len && p->s[p->i]=='*' && p->s[p->i+1]=='*'){
        p->i+=2;
        long double e = xeval_unary(p);
        return pow(base, e);
    }
    return base;
}

static long double xeval_unary(XEP *p){
    xeval_skip(p);
    if(p->ok && p->i<p->len && p->s[p->i]=='+'){ p->i++; return xeval_unary(p); }
    if(p->ok && p->i<p->len && p->s[p->i]=='-'){ p->i++; return -xeval_unary(p); }
    if(p->ok && p->i<p->len && p->s[p->i]=='~'){
        p->i++;
        long double v = xeval_unary(p);
        return (long double)(~(int64_t)v);
    }
    return xeval_power(p);
}

static long double xeval_term(XEP *p){
    long double v = xeval_unary(p);
    while(p->ok){
        xeval_skip(p);
        if(p->i+1<p->len && p->s[p->i]=='/' && p->s[p->i+1]=='/'){
            p->i+=2; long double t=xeval_unary(p);
            if(t==0){ p->ok=0; break; }
            v = floor(v/t);
        } else if(p->i<p->len && p->s[p->i]=='/'){
            p->i++; long double t=xeval_unary(p);
            if(t==0){ p->ok=0; break; }
            v /= t;
        } else if(p->i<p->len && p->s[p->i]=='%'){
            p->i++; long double t=xeval_unary(p);
            if(t==0){ p->ok=0; break; }
            v = v - floor(v/t)*t;
        } else if(p->i<p->len && p->s[p->i]=='*'
                  && !(p->i+1<p->len && p->s[p->i+1]=='*')){
            p->i++; v *= xeval_unary(p);
        } else break;
    }
    return v;
}

static long double xeval_addsub(XEP *p){
    long double v = xeval_term(p);
    while(p->ok){
        xeval_skip(p);
        if(p->i<p->len && p->s[p->i]=='+'){ p->i++; v += xeval_term(p); }
        else if(p->i<p->len && p->s[p->i]=='-'){ p->i++; v -= xeval_term(p); }
        else break;
    }
    return v;
}

static long double xeval_shift(XEP *p){
    long double v = xeval_addsub(p);
    while(p->ok){
        xeval_skip(p);
        if(p->i+1<p->len && p->s[p->i]=='<' && p->s[p->i+1]=='<'){
            p->i+=2; long double t=xeval_addsub(p);
            v = (long double)((int64_t)v << (int64_t)t);
        } else if(p->i+1<p->len && p->s[p->i]=='>' && p->s[p->i+1]=='>'){
            p->i+=2; long double t=xeval_addsub(p);
            v = (long double)((int64_t)v >> (int64_t)t);
        } else break;
    }
    return v;
}

static long double xeval_band(XEP *p){
    long double v = xeval_shift(p);
    while(p->ok){
        xeval_skip(p);
        if(p->i<p->len && p->s[p->i]=='&'){ p->i++; v = (long double)((int64_t)v & (int64_t)xeval_shift(p)); }
        else break;
    }
    return v;
}

static long double xeval_bxor(XEP *p){
    long double v = xeval_band(p);
    while(p->ok){
        xeval_skip(p);
        if(p->i<p->len && p->s[p->i]=='^'){ p->i++; v = (long double)((int64_t)v ^ (int64_t)xeval_band(p)); }
        else break;
    }
    return v;
}

static long double xeval_expr(XEP *p){
    long double v = xeval_bxor(p);
    while(p->ok){
        xeval_skip(p);
        if(p->i<p->len && p->s[p->i]=='|'){ p->i++; v = (long double)((int64_t)v | (int64_t)xeval_bxor(p)); }
        else break;
    }
    return v;
}

static int xeval_eval(Assembler *asmb, const char *text, double *out){
    XEP p; p.s=text; p.i=0; p.len=(int)strlen(text); p.ok=1; p.asmb=asmb;
    long double v = xeval_expr(&p);
    xeval_skip(&p);
    if(!p.ok || p.i<p.len) return 0;
    *out = (double)v;
    return 1;
}

#define EXPR_MAX_DEPTH 500
static uint256_t expr_factor(Assembler *asmb, const char *s, int idx, int *idx_out);
static uint256_t expr_factor_impl(Assembler *asmb, const char *s, int idx, int *idx_out);
static uint256_t expr_factor1(Assembler *asmb, const char *s, int idx, int *idx_out);
static uint256_t expr_term0_0(Assembler *asmb, const char *s, int idx, int *idx_out);
static uint256_t expr_term0(Assembler *asmb, const char *s, int idx, int *idx_out);
static uint256_t expr_term1(Assembler *asmb, const char *s, int idx, int *idx_out);
static uint256_t expr_safe_bitwise_operand(Assembler *asmb, uint256_t v, const char *op_name);
static uint256_t expr_bitwise_result(Assembler *asmb, uint256_t v);
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
static uint256_t expr_expression_esc(Assembler *asmb, const char *s, int idx, char stopchar, int *idx_out){
    size_t l = strlen(s);
    char *buf = malloc(l + 2);
    if(!buf){ perror("malloc"); exit(1); }
    memcpy(buf, s, idx);

    char stk[256];
    int  stkp = 0;

    for(size_t i = (size_t)idx; i < l; i++){
        char c = s[i];
        if(stkp == 0 && c == stopchar){
            buf[i] = '\0';
        } else if(c == '(' || c == '[' || c == OB_CHAR){
            if(stkp < (int)(sizeof(stk)-1)) stk[stkp++] = c;
            buf[i] = c;
        } else if(c == ')' || c == ']' || c == CB_CHAR){
            char expected = (c == ')') ? '(' : (c == ']') ? '[' : OB_CHAR;
            if(stkp > 0 && stk[stkp-1] == expected){
                stkp--;
                buf[i] = c;
            } else if(stkp == 0 && c == stopchar){
                buf[i] = '\0';
            } else {
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


static uint256_t expr_factor(Assembler *asmb, const char *s, int idx, int *idx_out){
    AsmState *st=&asmb->st;
    if(st->expr_depth >= EXPR_MAX_DEPTH){
        if(should_report_errors(st)){
            axx_diagf(1, 0, " error - expression nesting too deep.\n");
        }
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
        x=u256_not(x);
    } else if(s[idx]=='@'){
        x=expr_factor(asmb,s,idx+1,&idx);
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
                    int64_t offset=u256_to_i64(x2);
                    if(offset<0){
                        if(should_report_errors(st)){
                            axx_diagf(1, 0, " error - negative byte-extract offset in *(expr, expr).\n");
                        }
                        x=u256_zero();
                    } else {
                        int shift=(int)(offset*8);
                        x=u256_sar(x,shift);
                    }
                } else {
                    if(should_report_errors(st)){
                        axx_diagf(1, 0, " error - missing ')' in *(expr, expr) expression.\n");
                    }
                    x=u256_zero();
                }
            } else {
                if(should_report_errors(st)){
                    axx_diagf(1, 0, " error - missing ',' in *(expr, expr) expression.\n");
                }
                x=u256_zero();
            }
        } else {
            if(should_report_errors(st)){
                axx_diagf(1, 0, " error - expected '(' after '*' in *(expr,expr) expression.\n");
            }
            x=u256_zero();
        }
    } else {
        x=expr_factor1(asmb,s,idx,&idx);
    }
    idx=axx_skipspc(s,idx);
    *idx_out=idx;
    return x;
}

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
        else {
            if(should_report_errors(st)){
                axx_diagf(1, 0, " error - missing closing ')' in expression.\n");
            }
        }
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
    else if(idx+3<=slen && s[idx]=='\'' && s[idx+1] != '\\' && s[idx+2]=='\''){
        unsigned char cv=(unsigned char)s[idx+1]; x=u256_from_i64(cv); idx+=3;
        if(asmb->st.exp_typ_float) x=double_to_u256((double)cv); }
    else if(axx_q(s,slen,"$$",idx)){
        idx+=2;
        x = st->in_binary_list ? st->pc_instr_start : st->pc;
        if(st->in_binary_list || st->equ_section_tracking){
            int64_t _adj = equ_section_relative_offset(st, st->current_section, u256_to_u64(x));
            if(_adj >= 0) x = u256_from_u64((uint64_t)_adj);
        }
        if(asmb->st.exp_typ_float)
            x=double_to_u256((double)(int64_t)u256_to_u64(x));
    }
    else if(axx_q(s,slen,"$.",idx)){
        idx+=2;
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
        if(symbol_get(st,t,&sv)) x=sv;
        else {
            if(should_report_errors(st)){
                axx_diagf(1, 0, " error - undefined symbol: '#%s'\n", t);
            }
            x=u256_zero();
        }
        if(asmb->st.exp_typ_float)
            x=double_to_u256((double)(int64_t)u256_to_u64(x));
    }
    else if(axx_q(s,slen,"0b",idx)){
        idx+=2;
        while(s[idx]=='0'||s[idx]=='1'){
            x=u256_add(u256_mul(x,u256_from_u64(2)), u256_from_u64(s[idx]-'0'));
            idx++;
        }
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
        if(asmb->st.exp_typ_float)
            x=double_to_u256((double)(int64_t)u256_to_i64(x));
    }
    else if(idx+3<=slen && strncmp(s+idx,"qad",3)==0 &&
            ({ int _j=axx_skipspc(s,idx+3); _j<slen && s[_j]=='{'; })){
        idx+=3;
        idx=axx_skipspc(s,idx);
        if(s[idx]=='{'){
            idx++;
            char expr_buf[1024]; size_t en=0; int depth=0;
            while(s[idx] && en<sizeof(expr_buf)-1){
                if(s[idx]=='('||s[idx]=='[') depth++;
                else if((s[idx]==')'||s[idx]==']')&&depth>0) depth--;
                else if(s[idx]=='}'&&depth==0) break;
                expr_buf[en++]=s[idx++];
            }
            expr_buf[en]='\0';
            if(s[idx]=='}') idx++;
            if(strcmp(expr_buf,"inf")==0 || strcmp(expr_buf,"-inf")==0 ||
               strcmp(expr_buf,"nan")==0){
                x=ieee754_128_from_str(expr_buf);
            }
            else
            {
#if defined(__GNUC__) && !defined(__STRICT_ANSI__) && \
    (defined(__x86_64__) || defined(__i386__) || defined(__aarch64__) || \
     defined(__arm__) || defined(__riscv))
            int q_ok=0;
            uint256_t qbits = f128_eval_text(expr_buf, &q_ok);
            if(q_ok){ x=qbits; }
            else
#endif
            {
                double xv;
                if(xeval_eval(asmb, expr_buf, &xv)){
                    char fstr[64]; snprintf(fstr,sizeof(fstr),"%.17g",xv);
                    x=ieee754_128_from_str(fstr);
                } else {
                    int io2;
                    int prev_flt=asmb->st.exp_typ_float;
                    int _prior_had_error=asmb->st.had_error;
                    asmb->st.exp_typ_float=1;
                    uint256_t fv=expr_expression_pat(asmb,expr_buf,0,&io2);
                    asmb->st.exp_typ_float=prev_flt;
                    int _fallback_errored = asmb->st.had_error && !_prior_had_error;
                    asmb->st.had_error=_prior_had_error;
                    if(_fallback_errored){
                        if(should_report_errors(&asmb->st)){
                            axx_diagf(1, 0, " error - qad{}: cannot evaluate expression '%s'; using 0.\n", expr_buf);
                        }
                        x=u256_zero();
                    } else {
                        double dv=u256_to_double(fv);
                        char fstr[64]; snprintf(fstr,sizeof(fstr),"%.17g",dv);
                        x=ieee754_128_from_str(fstr);
                    }
                }
            }
            }
        }
    }
    else if(idx+5<=slen && strncmp(s+idx,"enflt",5)==0 &&
            ({ int _j=axx_skipspc(s,idx+5); _j<slen && s[_j]=='{'; })){
        idx+=5;
        int f; char t[512];
        idx=axx_get_curlb(&asmb->st,s,idx,&f,t,sizeof(t));
        if(f){
            int prev_flt=asmb->st.exp_typ_float;
            asmb->st.exp_typ_float=0;
            int io2; uint256_t iv=expr_expression_pat(asmb,t,0,&io2);
            asmb->st.exp_typ_float=prev_flt;
            double fval=enfloat_bits(u256_to_u64(iv));
            x=double_to_u256(fval);
        }
    }
    else if(idx+5<=slen && strncmp(s+idx,"endbl",5)==0 &&
            ({ int _j=axx_skipspc(s,idx+5); _j<slen && s[_j]=='{'; })){
        idx+=5;
        int f; char t[512];
        idx=axx_get_curlb(&asmb->st,s,idx,&f,t,sizeof(t));
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
        idx=axx_get_curlb(&asmb->st,s,idx,&f,t,sizeof(t));
        if(f){
            uint64_t bits;
            if(strcmp(t,"nan")==0) bits=0x7ff8000000000000ULL;
            else if(strcmp(t,"inf")==0) bits=0x7ff0000000000000ULL;
            else if(strcmp(t,"-inf")==0) bits=0xfff0000000000000ULL;
            else {
                double xv;
                if(xeval_eval(asmb, t, &xv)){
                    memcpy(&bits,&xv,8);
                } else {
                    int prev_flt = asmb->st.exp_typ_float;
                    int _prior_had_error = asmb->st.had_error;
                    asmb->st.exp_typ_float = 1;
                    int io2; uint256_t fv = expr_expression_pat(asmb,t,0,&io2);
                    asmb->st.exp_typ_float = prev_flt;
                    int _fallback_errored = asmb->st.had_error && !_prior_had_error;
                    asmb->st.had_error = _prior_had_error;
                    if(_fallback_errored){
                        if(should_report_errors(&asmb->st)){
                            axx_diagf(1, 0, " error - dbl{}: cannot convert expression to float64; using 0.\n");
                        }
                        bits = 0;
                    } else {
                        double v = u256_to_double(fv);
                        memcpy(&bits,&v,8);
                    }
                }
            }
            x = asmb->st.exp_typ_float ? double_to_u256((double)bits) : u256_from_u64(bits);
        }
    }
    else if(idx+3<=slen && strncmp(s+idx,"flt",3)==0 &&
            ({ int _j=axx_skipspc(s,idx+3); _j<slen && s[_j]=='{'; })){
        idx+=3;
        int f; char t[512];
        idx=axx_get_curlb(&asmb->st,s,idx,&f,t,sizeof(t));
        if(f){
            uint32_t bits;
            if(strcmp(t,"nan")==0) bits=0x7fc00000u;
            else if(strcmp(t,"inf")==0) bits=0x7f800000u;
            else if(strcmp(t,"-inf")==0) bits=0xff800000u;
            else {
                double xv;
                if(xeval_eval(asmb, t, &xv)){
                    float v = (float)xv;
                    memcpy(&bits,&v,4);
                } else {
                    int prev_flt = asmb->st.exp_typ_float;
                    int _prior_had_error = asmb->st.had_error;
                    asmb->st.exp_typ_float = 1;
                    int io2; uint256_t fv = expr_expression_pat(asmb,t,0,&io2);
                    asmb->st.exp_typ_float = prev_flt;
                    int _fallback_errored = asmb->st.had_error && !_prior_had_error;
                    asmb->st.had_error = _prior_had_error;
                    if(_fallback_errored){
                        if(should_report_errors(&asmb->st)){
                            axx_diagf(1, 0, " error - flt{}: cannot convert expression to float32; using 0.\n");
                        }
                        bits = 0;
                    } else {
                        float v = (float)u256_to_double(fv);
                        memcpy(&bits,&v,4);
                    }
                }
            }
            x = asmb->st.exp_typ_float ? double_to_u256((double)bits) : u256_from_u64(bits);
        }
    }
    else if(idx+4<=slen && axx_q(s,slen,"not(",idx)){
        x=expr_expression(asmb,s,idx+4,&idx);
        idx=axx_skipspc(s,idx);
        if(idx<slen && s[idx]==')') idx++;
        else {
            if(should_report_errors(st)){
                axx_diagf(1, 0, " error - missing closing ')' in not(...) expression.\n");
            }
        }
        x=u256_from_i64(u256_is_zero(x)?1:0);
    }
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
            int _assign_prior_eul = st->error_undefined_label;
            st->error_undefined_label = 0;
            x=expr_expression(asmb,s,idx+3,&idx);
            int _assign_this_undef = st->error_undefined_label;
            st->error_undefined_label = _assign_prior_eul || _assign_this_undef;
            var_put_tagged(st,ch,x,_assign_this_undef);
        } else {
            x=var_get(st,ch);
            idx++;
            if(!st->in_match_attempt
               && !st->pass1_size_mode
               && should_report_errors(st)){
                if(var_get_is_undef(st, ch)){
                    st->error_undefined_label = 1;
                    axx_diagf(0, 0, " error - Label undefined: variable '%c' contains undefined value"
                               "  [%s:%d]\n",
                               ch, st->current_file, (int)st->ln);
                }
            }
            if(asmb->st.exp_typ_float)
                x=double_to_u256((double)(int64_t)u256_to_i64(x));
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
            const int64_t EXP_MAX = 1024;
            const int64_t EXP_RESULT_MAX_BITS = 1 << 20;
            int64_t t_int = u256_to_i64(t);
            if(t_int < 0){
                if(should_report_errors(&asmb->st)){
                    axx_diagf(1, 0, " error - Negative exponent in ** expression; result set to 0.\n");
                }
                x = u256_zero();
                break;
            }
            if(t_int > EXP_MAX){
                if(should_report_errors(&asmb->st)){
                    axx_diagf(1, 0, " error - Exponent %lld exceeds maximum %lld in ** expression; result set to 0.\n",(long long)t_int,(long long)EXP_MAX);
                }
                x = u256_zero();
                break;
            }
            int64_t base_bits = u256_nbit(x);
            int64_t exp_factor = t_int > 1 ? t_int : 1;
            if(base_bits * exp_factor > EXP_RESULT_MAX_BITS){
                if(should_report_errors(&asmb->st)){
                    axx_diagf(1, 0, " error - ** result would exceed %lld bits (chained exponentiation); result set to 0.\n",(long long)EXP_RESULT_MAX_BITS);
                }
                x = u256_zero();
                break;
            }
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
            uint256_t t=expr_term0_0(asmb,s,idx+2,&idx);
            if(flt){
                double b=u256_to_double(t);
                if(b==0.0){
                    if(should_report_errors(&asmb->st)){
                        axx_diagf(1, 0, " error - Division by 0 error.\n");
                    }
                    x=double_to_u256(0.0);
                }
                else x=double_to_u256(floor(u256_to_double(x)/b));
            } else {
                if(u256_is_zero(t)){
                    if(should_report_errors(&asmb->st)){
                        axx_diagf(1, 0, " error - Division by 0 error.\n");
                    }
                    x=u256_zero();
                }
                else x=u256_floordiv(x,t);
            }
        } else if(s[idx]=='/'&&s[idx+1]!='/'){
            uint256_t t=expr_term0_0(asmb,s,idx+1,&idx);
            if(flt){
                double b=u256_to_double(t);
                if(b==0.0){
                    if(should_report_errors(&asmb->st)){
                        axx_diagf(1, 0, " error - Division by 0 error.\n");
                    }
                    x=double_to_u256(0.0);
                }
                else x=double_to_u256(u256_to_double(x)/b);
            } else {
                if(u256_is_zero(t)){
                    if(should_report_errors(&asmb->st)){
                        axx_diagf(1, 0, " error - Division by 0 error.\n");
                    }
                    x=u256_zero();
                }
                else x=u256_truncdiv(x,t);
            }
        } else if(s[idx]=='%'){
            uint256_t t=expr_term0_0(asmb,s,idx+1,&idx);
            if(flt){
                double b=u256_to_double(t);
                if(b==0.0){
                    if(should_report_errors(&asmb->st)){
                        axx_diagf(1, 0, " error - Division by 0 error.\n");
                    }
                    x=double_to_u256(0.0);
                }
                else {
                    double r=fmod(u256_to_double(x),b);
                    if(r!=0.0 && ((r<0.0)!=(b<0.0))) r+=b;
                    x=double_to_u256(r);
                }
            } else {
                if(u256_is_zero(t)){
                    if(should_report_errors(&asmb->st)){
                        axx_diagf(1, 0, " error - Division by 0 error.\n");
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
    const int64_t SHIFT_MAX = 65536;
    while(idx<slen){
        if(axx_q(s,slen,"<<",idx)){
            uint256_t t=expr_term1(asmb,s,idx+2,&idx);
            int64_t sv=u256_to_i64(expr_safe_bitwise_operand(asmb,t,"<<"));
            if(sv<0){
                if(should_report_errors(&asmb->st)){
                    axx_diagf(1, 0, " error - negative shift count (%lld) in << expression.\n",(long long)sv);
                }
                x=u256_zero();
            } else if(sv>SHIFT_MAX){
                if(should_report_errors(&asmb->st)){
                    axx_diagf(1, 0, " error - shift count %lld exceeds maximum %lld in << expression.\n",(long long)sv,(long long)SHIFT_MAX);
                }
                x=u256_zero();
            } else x=expr_bitwise_result(asmb,u256_shl(expr_safe_bitwise_operand(asmb,x,"<<"),(int)sv));
        } else if(axx_q(s,slen,">>",idx)){
            uint256_t t=expr_term1(asmb,s,idx+2,&idx);
            int64_t sv=u256_to_i64(expr_safe_bitwise_operand(asmb,t,">>"));
            if(sv<0){
                if(should_report_errors(&asmb->st)){
                    axx_diagf(1, 0, " error - negative shift count (%lld) in >> expression.\n",(long long)sv);
                }
                x=u256_zero();
            } else if(sv>SHIFT_MAX){
                if(should_report_errors(&asmb->st)){
                    axx_diagf(1, 0, " error - shift count %lld exceeds maximum %lld in >> expression.\n",(long long)sv,(long long)SHIFT_MAX);
                }
                x=u256_zero();
            } else x=expr_bitwise_result(asmb,u256_sar(expr_safe_bitwise_operand(asmb,x,">>"),(int)sv));
        } else break;
    }
    *idx_out=idx; return x;
}


static uint256_t double_trunc_to_u256(double d){
    const double LIMB = 18446744073709551616.0;
    int neg = (d < 0.0);
    double a = neg ? -d : d;
    a = floor(a);
    uint256_t r = u256_zero();
    for(int i = 0; i < 4 && a >= 1.0; i++){
        r.w[i] = (uint64_t)fmod(a, LIMB);
        a = floor(a / LIMB);
    }
    return neg ? u256_neg(r) : r;
}

static double u256_int_to_double(uint256_t v){
    const double LIMB = 18446744073709551616.0;
    int neg = (int)((v.w[3] >> 63) & 1u);
    uint256_t m = neg ? u256_neg(v) : v;
    double d = 0.0;
    for(int i = 3; i >= 0; i--) d = d * LIMB + (double)m.w[i];
    return neg ? -d : d;
}

static uint256_t expr_safe_bitwise_operand(Assembler *asmb, uint256_t v, const char *op_name){
    if(asmb->st.exp_typ_float){
        double d = u256_to_double(v);
        if(!isfinite(d)){
            if(should_report_errors(&asmb->st)){
                axx_diagf(1, 0, " error - non-finite value %g in bitwise '%s' operation; treated as 0.\n", d, op_name);
            }
            return u256_zero();
        }
        return double_trunc_to_u256(d);
    }
    return v;
}

static uint256_t expr_bitwise_result(Assembler *asmb, uint256_t v){
    if(asmb->st.exp_typ_float) return double_to_u256(u256_int_to_double(v));
    return v;
}

static uint256_t expr_term3(Assembler *asmb, const char *s, int idx, int *idx_out){
    uint256_t x=expr_term2(asmb,s,idx,&idx);
    int slen=(int)strlen(s);
    while(idx<slen && s[idx]=='&' && s[idx+1]!='&'){
        uint256_t t=expr_term2(asmb,s,idx+1,&idx);
        x=expr_bitwise_result(asmb,u256_and(expr_safe_bitwise_operand(asmb,x,"&"),expr_safe_bitwise_operand(asmb,t,"&")));
    }
    *idx_out=idx; return x;
}

static uint256_t expr_term4(Assembler *asmb, const char *s, int idx, int *idx_out){
    uint256_t x=expr_term3(asmb,s,idx,&idx);
    int slen=(int)strlen(s);
    while(idx<slen && s[idx]=='|' && s[idx+1]!='|'){
        uint256_t t=expr_term3(asmb,s,idx+1,&idx);
        x=expr_bitwise_result(asmb,u256_or(expr_safe_bitwise_operand(asmb,x,"|"),expr_safe_bitwise_operand(asmb,t,"|")));
    }
    *idx_out=idx; return x;
}

static uint256_t expr_term5(Assembler *asmb, const char *s, int idx, int *idx_out){
    uint256_t x=expr_term4(asmb,s,idx,&idx);
    int slen=(int)strlen(s);
    while(idx<slen && s[idx]=='^'){
        uint256_t t=expr_term4(asmb,s,idx+1,&idx);
        x=expr_bitwise_result(asmb,u256_xor(expr_safe_bitwise_operand(asmb,x,"^"),expr_safe_bitwise_operand(asmb,t,"^")));
    }
    *idx_out=idx; return x;
}

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
            if(should_report_errors(&asmb->st)){
                axx_diagf(0, 0, " warning - sign-extension bit width %lld exceeds maximum %d, result set to 0.\n",
                           (long long)tv, SEXT_MAX_BITS);
            }
            x=u256_zero();
        } else {
            uint256_t mask = u256_not(u256_shl(u256_not(u256_zero()), (int)tv));
            x = u256_and(x, mask);
            uint256_t sign_bit = u256_sar(x, (int)(tv - 1));
            sign_bit = u256_and(sign_bit, u256_one());
            if(!u256_is_zero(sign_bit)){
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
    return expr_term7(asmb,s,idx,idx_out);
}

static int skip_subexpr(const char *s, int idx);

static uint256_t expr_term9(Assembler *asmb, const char *s, int idx, int *idx_out){
    uint256_t x=expr_term8(asmb,s,idx,&idx);
    int slen=(int)strlen(s);
    while(idx<slen && axx_q(s,slen,"&&",idx)){
        idx+=2;
        if(u256_is_zero(x)){
            idx = skip_subexpr(s, axx_skipspc(s, idx));
        } else {
            uint256_t t=expr_term8(asmb,s,idx,&idx);
            x=u256_from_i64((!u256_is_zero(t))?1:0);
        }
    }
    *idx_out=idx; return x;
}

static uint256_t expr_term10(Assembler *asmb, const char *s, int idx, int *idx_out){
    uint256_t x=expr_term9(asmb,s,idx,&idx);
    int slen=(int)strlen(s);
    while(idx<slen && axx_q(s,slen,"||",idx)){
        idx+=2;
        if(!u256_is_zero(x)){
            idx = skip_subexpr(s, axx_skipspc(s, idx));
            x = u256_one();
        } else {
            uint256_t t=expr_term9(asmb,s,idx,&idx);
            x=u256_from_i64((!u256_is_zero(t))?1:0);
        }
    }
    *idx_out=idx; return x;
}


static int skip_subexpr(const char *s, int idx) {
    int slen = (int)strlen(s);
    int paren_depth = 0;
    int brack_depth = 0;
    int ob_depth    = 0;
    while(idx < slen && s[idx]){
        char c = s[idx];
        if(c == '(') { paren_depth++; idx++; }
        else if(c == ')') {
            if(paren_depth > 0){ paren_depth--; idx++; }
            else break;
        }
        else if(c == '[') { brack_depth++; idx++; }
        else if(c == ']') {
            if(brack_depth > 0){ brack_depth--; idx++; }
            else break;
        }
        else if(c == OB_CHAR) { ob_depth++; idx++; }
        else if(c == CB_CHAR) {
            if(ob_depth > 0){ ob_depth--; idx++; }
            else break;
        }
        else if(paren_depth == 0 && brack_depth == 0 && ob_depth == 0
                && (c == '?' || c == ',' || c == ';')) break;
        else if(paren_depth == 0 && brack_depth == 0 && ob_depth == 0
                && c == ':' && s[idx+1] != '=') break;
        else idx++;
    }
    return idx;
}

static int skip_ternary_expr(const char *s, int idx) {
    int slen = (int)strlen(s);
    idx = skip_subexpr(s, idx);
    if(idx < slen && s[idx] == '?' && s[idx+1] != '='){
        idx++;
        idx = axx_skipspc(s, idx);
        idx = skip_ternary_expr(s, idx);
        idx = axx_skipspc(s, idx);
        if(idx < slen && s[idx] == ':' && s[idx+1] != '='){
            idx++;
            idx = axx_skipspc(s, idx);
            idx = skip_ternary_expr(s, idx);
        }
    }
    return idx;
}

static uint256_t expr_term11(Assembler *asmb, const char *s, int idx, int *idx_out){
    uint256_t x = expr_term10(asmb, s, idx, &idx);
    int slen = (int)strlen(s);
    if(idx < slen && axx_q(s, slen, "?", idx)){
        idx++;
        idx = axx_skipspc(s, idx);
        if(u256_is_zero(x)){
            int skip_end = skip_subexpr(s, idx);
            if(axx_q(s, slen, ":", skip_end) && s[skip_end+1] != '='){
                int false_start = axx_skipspc(s, skip_end + 1);
                x = expr_term11(asmb, s, false_start, &idx);
            } else {
                idx = skip_end;
                x = u256_zero();
            }
        } else {
            PatVar    saved_vars[26];
            memcpy(saved_vars, asmb->st.vars, sizeof(saved_vars));

            x = expr_term10(asmb, s, idx, &idx);
            PatVar    vars_after_true[26];
            memcpy(vars_after_true, asmb->st.vars, sizeof(vars_after_true));
            int err_after_true = asmb->st.error_undefined_label;

            idx = axx_skipspc(s, idx);
            if(axx_q(s, slen, ":", idx) && s[idx+1] != '='){
                idx++;
                memcpy(asmb->st.vars, saved_vars, sizeof(saved_vars));
                idx = skip_ternary_expr(s, axx_skipspc(s, idx));
            }
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

static int dir_set_symbol(Assembler *asmb, PatEntry *e){
    if(!e||strcmp(e->f[0],".setsym")!=0) return 0;
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
    asmb->st.endian_big=(strcasecmp(e->f[1],"big")==0);
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
    if(asmb->st.vliwinstbits < 0 || asmb->st.vliwinstbits > 8192){
        axx_diagf(1, 0, " error - .vliw: vliwinstbits %d is out of range (must be 0-8192).\n",
                   asmb->st.vliwinstbits);
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

static int dir_check(Assembler *asmb, PatEntry *e){
    if(!e || strcmp(e->f[0], ".check") != 0) return 0;
    const char *var_str  = e->f[1][0] ? e->f[1] : e->f[2];
    const char *syms_str = e->f[1][0] ? e->f[2] : "";
    if(!var_str[0]){
        axx_diagf(1, 0, " error - .check: variable name is not specified.\n");
        return 1;
    }
    char var = (char)tolower((unsigned char)var_str[0]);
    if(var < 'a' || var > 'z' || var_str[1] != '\0'){
        axx_diagf(1, 0, " error - .check: variable should be a lower case letter ('%s').\n",
                   var_str);
        return 1;
    }
    int idx = var - 'a';
    sv_free(&asmb->st.check_constraints[idx]);
    sv_init(&asmb->st.check_constraints[idx]);
    const char *p = syms_str;
    while(*p){
        while(*p == ' ' || *p == '\t') p++;
        if(!*p) break;
        char buf[512]; int j = 0;
        while(*p && *p != ',' && j < (int)sizeof(buf)-1)
            buf[j++] = (char)toupper((unsigned char)*p++);
        buf[j] = '\0';
        while(j > 0 && (buf[j-1] == ' ' || buf[j-1] == '\t')) buf[--j] = '\0';
        if(j == 2 && ((buf[0]=='"' && buf[1]=='"') || (buf[0]=='\'' && buf[1]=='\''))){
            /* 空文字リテラルは「このオペランドは省略可」の印。
               省略時、変数には 0 が入る。長さ0の要素として積む。 */
            int dup = 0;
            for(int si = 0; si < asmb->st.check_constraints[idx].len; si++)
                if(asmb->st.check_constraints[idx].data[si][0] == '\0'){ dup = 1; break; }
            if(!dup) sv_push(&asmb->st.check_constraints[idx], "");
        } else if(j > 0){
            sv_push(&asmb->st.check_constraints[idx], buf);
        }
        if(*p == ',') p++;
    }
    return 1;
}

static int dir_clrcheck(Assembler *asmb, PatEntry *e){
    if(!e || strcmp(e->f[0], ".clrcheck") != 0) return 0;
    const char *var_str = e->f[2];
    if(var_str[0]){
        char var = (char)tolower((unsigned char)var_str[0]);
        if(var < 'a' || var > 'z' || var_str[1] != '\0'){
            axx_diagf(1, 0, " error - .clrcheck: variable should be a lower case letter ('%s').\n",
                       var_str);
            return 1;
        }
        int idx = var - 'a';
        sv_free(&asmb->st.check_constraints[idx]);
        sv_init(&asmb->st.check_constraints[idx]);
    } else {
        for(int i = 0; i < 26; i++){
            sv_free(&asmb->st.check_constraints[i]);
            sv_init(&asmb->st.check_constraints[i]);
        }
    }
    return 1;
}

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
            st->had_error=1;
        }
    }
    return triggered;
}

static uint256_t expr_expression_esc_float(Assembler *asmb, const char *s,
                                            int idx, char stopchar, int *idx_out)
{
    int prev = asmb->st.exp_typ_float;
    asmb->st.exp_typ_float = 1;
    uint256_t r = expr_expression_esc(asmb, s, idx, stopchar, idx_out);
    asmb->st.exp_typ_float = prev;
    return r;
}


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

    char *del = calloc(len + 1, 1);
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


static int pat_expects_expr(const char *t, int idx){
    while(t[idx]==' '||t[idx]=='\t') idx++;
    return t[idx]=='!';
}
/* ソース行 s_orig をパターン t_orig と照合する（字句解析なしの1文字ずつ突き合わせ）。
 * パターン側の文字の意味:
 *   大文字      大小無視でリテラル一致（ニーモニック）
 *   小文字1文字 .setsym のシンボル（レジスタ名等）を取る
 *   !x          任意の式を読んで変数 x に束縛
 *   !!x         式ではなく factor 1個だけを束縛
 *   !Fx/!Dx/!Qx 浮動小数点式を IEEE754 の 32/64/128bit として束縛
 *   \c          次の1文字をリテラル扱い（エスケープ）
 * 成功時は具体度スコア (式の数, リテラル文字数, シンボル数) を st に残す。
 * 呼び出し側はこれが最も「具体的」なパターンを採用するので、パターンファイル内の
 * 記述順に依存しない。末尾まで両方使い切ったときだけ成功とする。 */
static int pat_match(Assembler *asmb, const char *s_orig, const char *t_orig){
    AsmState *st=&asmb->st;
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

    int n_expr=0, n_sym=0, n_lit=0;

    int prev_alnum=0;

    while(1){
        int s_sp = (s[idx_s]==' '||s[idx_s]=='\t');
        int t_sp = (t[idx_t]==' '||t[idx_t]=='\t');
        idx_s=axx_skipspc(s,idx_s);
        idx_t=axx_skipspc(t,idx_t);
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
            if(a=='F' || a=='D' || a=='Q'){
                char ftype = a;
                a = t[idx_t]; idx_t++;
                idx_t = axx_skipspc(t, idx_t);
                char stopchar = '\0';
                if(idx_t < tlen && t[idx_t] == '\\'){
                    idx_t++;
                    idx_t = axx_skipspc(t, idx_t);
                    stopchar = t[idx_t]; idx_t++;
                }
                int idx_s_q_start = idx_s;
                uint256_t fv = expr_expression_esc_float(asmb, s, idx_s, stopchar, &idx_s);
                double dv = u256_to_double(fv);
                if(stopchar != '\0' && idx_s < (int)strlen(s) && s[idx_s] == stopchar)
                    idx_s++;
                if(ftype == 'F'){
                    float fval = (float)dv;
                    if(isfinite(dv) && !isfinite(fval)){
                        if(should_report_errors(st)){
                            axx_diagf(1, 0, " error - !F: cannot convert value to float32; using 0.\n");
                        }
                        fval = 0.0f;
                    }
                    uint32_t bits; memcpy(&bits, &fval, 4);
                    var_put(st, a, u256_from_u64((uint64_t)bits));
                } else if(ftype == 'D'){
                    uint64_t bits; memcpy(&bits, &dv, 8);
                    var_put(st, a, u256_from_u64(bits));
                } else {
                    int raw_len = idx_s - idx_s_q_start;
                    if(stopchar && raw_len > 0 &&
                       s[idx_s_q_start + raw_len - 1] == stopchar)
                        raw_len--;
                    uint256_t qbits;
#if defined(__GNUC__) && !defined(__STRICT_ANSI__) && \
    (defined(__x86_64__) || defined(__i386__) || defined(__aarch64__) || \
     defined(__arm__) || defined(__riscv))
                    if(raw_len > 0 && raw_len < 1024){
                        char expr_text[1024];
                        memcpy(expr_text, s + idx_s_q_start, (size_t)raw_len);
                        expr_text[raw_len] = '\0';
                        const char *f128_text = expr_text;
                        char stripped[1024];
                        if(raw_len > 4 &&
                           strncmp(expr_text, "qad{", 4) == 0 &&
                           expr_text[raw_len-1] == '}'){
                            int inner = raw_len - 5;
                            memcpy(stripped, expr_text + 4, (size_t)inner);
                            stripped[inner] = '\0';
                            f128_text = stripped;
                        }
                        int q_ok = 0;
                        qbits = f128_eval_text(f128_text, &q_ok);
                        if(!q_ok){
                            if(strcmp(f128_text,"inf")==0 || strcmp(f128_text,"-inf")==0 ||
                               strcmp(f128_text,"nan")==0){
                                qbits = ieee754_128_from_str(f128_text);
                            } else {
                                char fstr[64];
                                snprintf(fstr, sizeof(fstr), "%.17g", dv);
                                qbits = ieee754_128_from_str(fstr);
                            }
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
                st->elf_capturing_var = a;
                int _cap_prior_eul = st->error_undefined_label;
                st->error_undefined_label = 0;
                uint256_t v=expr_factor(asmb,s,idx_s,&idx_s);
                int _cap_this_undef = st->error_undefined_label;
                st->error_undefined_label = _cap_prior_eul || _cap_this_undef;
                st->elf_capturing_var = '\0';
                var_put_tagged(st,a,v,_cap_this_undef);
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
                st->elf_capturing_var = a;
                int _cap_prior_eul2 = st->error_undefined_label;
                st->error_undefined_label = 0;
                uint256_t v=expr_expression_esc(asmb,s,idx_s,stopchar,&idx_s);
                int _cap_this_undef2 = st->error_undefined_label;
                st->error_undefined_label = _cap_prior_eul2 || _cap_this_undef2;
                st->elf_capturing_var = '\0';
                var_put_tagged(st,a,v,_cap_this_undef2);
                if(stopchar && s[idx_s]==stopchar) idx_s++;
                continue;
            }
        } else if(a>='a'&&a<='z'){
            prev_alnum=0;
            idx_t++;
            int prev_idx_s = idx_s;
            int vi = a - 'a';
            StrVec *cv = &st->check_constraints[vi];
            int allow_omit = 0, n_named = 0;
            for(int si = 0; si < cv->len; si++){
                if(cv->data[si][0] == '\0') allow_omit = 1;
                else                        n_named++;
            }

            char w[512];
            idx_s=axx_get_symbol_word(s,idx_s,st->swordchars,w,sizeof(w));
            uint256_t sv = u256_zero();
            int ok = 1;
            if(!symbol_get(st,w,&sv)){
                int _wl = (int)strlen(w), _hit = 0;
                for(int _cut = _wl - 1; _cut > 0; _cut--){
                    unsigned char _ch = (unsigned char)w[_cut];
                    if(isalnum(_ch) || _ch=='_') continue;
                    char _save = w[_cut];
                    w[_cut] = '\0';
                    if(symbol_get(st,w,&sv)){ idx_s = prev_idx_s + _cut; _hit = 1; break; }
                    w[_cut] = _save;
                }
                if(!_hit) ok = 0;
            }
            if(ok && idx_s == prev_idx_s) ok = 0;

            if(ok && cv->len > 0){
                int hit = 0;
                for(int si = 0; si < cv->len; si++){
                    if(cv->data[si][0] != '\0' && strcmp(cv->data[si], w) == 0){
                        hit = 1;
                        break;
                    }
                }
                if(!hit) ok = 0;
            }

            if(!ok && n_named > 0){
                /* 語として切り出せなかった／許可リストに無かった場合、
                   許可リストの名前そのものを前方一致で取り直す。
                   `MOVa1c3` のように区切り文字なしで連結された書き方を通すため。 */
                int best_len = 0, best_si = -1;
                for(int si = 0; si < cv->len; si++){
                    const char *nm = cv->data[si];
                    int nl = (int)strlen(nm);
                    if(nl <= best_len) continue;
                    int k = 0;
                    while(k < nl && s[prev_idx_s + k]
                          && axx_upper_char(s[prev_idx_s + k]) == nm[k]) k++;
                    if(k == nl){ best_len = nl; best_si = si; }
                }
                if(best_si >= 0 && (int)strlen(cv->data[best_si]) < (int)sizeof(w)
                   && symbol_get(st, cv->data[best_si], &sv)){
                    snprintf(w, sizeof(w), "%s", cv->data[best_si]);
                    idx_s = prev_idx_s + best_len;
                    ok = 1;
                }
            }

            if(!ok){
                if(!allow_omit){ result=0; break; }
                /* 省略とみなす。ソースは1文字も消費せず、変数は未代入(0)。 */
                idx_s = prev_idx_s;
                var_put(st, a, u256_zero());
                n_sym++;
                continue;
            }

            var_put(st,a,sv);
            n_sym++;
            continue;
        } else if(a=='[' || a==']'){
            prev_alnum=0;
            idx_t++;
            idx_s=axx_skipspc(s,idx_s);
            if(s[idx_s]==a){ idx_s++; n_lit++; continue; }
            else { result=0; break; }
        } else if(a=='+' && b=='-' && pat_expects_expr(t, idx_t + 1)){
            idx_t++; n_lit++;
            prev_alnum = 0;
            continue;
        } else if(a==b){
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

    enum { MAX_OPT_GROUPS = 20 };
    if(cnt > MAX_OPT_GROUPS){
        axx_diagf(0, 0, " warning - pattern has %d optional groups (max %d); "
                   "first %d are treated as optional, remainder are always included.\n",
                   cnt, MAX_OPT_GROUPS, MAX_OPT_GROUPS);
        cnt = MAX_OPT_GROUPS;
    }

    int *sl=malloc((cnt+1)*sizeof(int));
    for(int i=0;i<cnt;i++) sl[i]=i+1;

    const uint64_t MAX_COMBINATIONS = (uint64_t)1 << 16;
    uint64_t tried = 0;

    int found=0;
    uint64_t total = (uint64_t)1 << cnt;
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
                    snprintf(asmb->st.combo_budget_warned_file[_wi],
                             sizeof(asmb->st.combo_budget_warned_file[_wi]),
                             "%s", asmb->st.current_file);
                    asmb->st.combo_budget_warned_line[_wi] = asmb->st.ln;
                }
                axx_diagf(0, 0, " warning - a pattern with %d optional group(s) exceeded the "
                           "%llu-combination match budget and was treated as non-matching; "
                           "consider splitting it into multiple explicit pattern entries.\n",
                           cnt, (unsigned long long)MAX_COMBINATIONS);
            }
            break;
        }
        int ri[64]; int nr=0;
        for(int i=0;i<cnt;i++) if(mask & ((uint64_t)1<<i)) ri[nr++]=sl[i];
        char *lt=remove_brackets_str(t,ri,nr);

        PatVar    saved_vars[26];
        memcpy(saved_vars, asmb->st.vars, sizeof(saved_vars));

        int saved_elf_refs_len = asmb->st.elf_refs_len;
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
            for(int vi=0;vi<26;vi++) free(saved_vtl[vi].label_name);
        } else {
            memcpy(asmb->st.vars, saved_vars, sizeof(saved_vars));
            for(int ri2=saved_elf_refs_len; ri2<asmb->st.elf_refs_len; ri2++)
                free(asmb->st.elf_refs[ri2].name);
            asmb->st.elf_refs_len = saved_elf_refs_len;
            for(int vi=0;vi<26;vi++){
                free(asmb->st.elf_var_to_label[vi].label_name);
                asmb->st.elf_var_to_label[vi].set       = saved_vtl[vi].set;
                asmb->st.elf_var_to_label[vi].label_val = saved_vtl[vi].label_val;
                asmb->st.elf_var_to_label[vi].label_name = saved_vtl[vi].label_name;
                saved_vtl[vi].label_name = NULL;
            }
        }
        free(lt);
    }
    free(sl); free(t);
    return found;
}

static void axx_resolve_path(const char *base_dir, const char *fn,
                              char *out, size_t osz)
{
    if(!fn || !fn[0]){ out[0]='\0'; return; }
    if(fn[0]=='/' || !base_dir || !base_dir[0]){
        strncpy(out, fn, osz-1); out[osz-1]='\0'; return;
    }
    snprintf(out, osz, "%s/%s", base_dir, fn);
}

static void axx_dir_of(const char *path, char *out, size_t osz)
{
    strncpy(out, path, osz-1); out[osz-1]='\0';
    char *d = dirname(out);
    if(d != out) strncpy(out, d, osz-1);
}

static void readpat(Assembler *asmb, const char *fn);
static void include_pat(Assembler *asmb, const char *l, const char *base_dir);

static char **pat_macro_expand(FILE *f, const char *display, int *nlines);
static void pat_macro_expand_free(char **v, int n);
static void macro_reset_pass_pattern(void);

static void include_pat(Assembler *asmb, const char *l, const char *base_dir){
    int idx=axx_skipspc(l,0);
    char upper8[16]={0};
    for(int i=0;i<8&&l[idx+i];i++) upper8[i]=axx_upper_char(l[idx+i]);
    if(strcmp(upper8,".INCLUDE")!=0) return;
    const char *after_kw = l + idx + 8;
    char raw[512]; axx_get_string(after_kw,raw,sizeof(raw));
    if(!raw[0]){
        char trimmed[512];
        int ti=axx_skipspc(after_kw,0);
        int tn=0;
        while(after_kw[ti]&&after_kw[ti]!=' '&&after_kw[ti]!='\t'&&tn<(int)sizeof(trimmed)-1)
            trimmed[tn++]=after_kw[ti++];
        trimmed[tn]=0;
        if(trimmed[0]){
            axx_diagf(0, 0, " warning - .INCLUDE filename not quoted: '%s'. "
                       "Please use double quotes.\n", trimmed);
            strncpy(raw, trimmed, sizeof(raw)-1); raw[sizeof(raw)-1]='\0';
        } else {
            axx_diagf(0, 0, " error - .INCLUDE directive has no filename: %s\n", l);
            return;
        }
    }
    char resolved[1024];
    axx_resolve_path(base_dir, raw, resolved, sizeof(resolved));
    readpat(asmb, resolved);
}

static void readpat(Assembler *asmb, const char *fn){
    if(!fn||!fn[0]) return;

    enum { MAX_PAT_DEPTH = 50 };
    if(asmb->st.pat_include_depth > MAX_PAT_DEPTH){
        axx_diagf(0, 0, " error - pattern .INCLUDE nesting exceeds %d: '%s'\n",
                   MAX_PAT_DEPTH, fn);
        return;
    }
    char real[PATH_MAX];
    if(!realpath(fn, real)){
        strncpy(real, fn, sizeof(real)-1); real[sizeof(real)-1]='\0';
    }
    for(int i=0;i<asmb->st.pat_include_depth;i++){
        if(asmb->st.pat_include_chain[i]
           && strcmp(asmb->st.pat_include_chain[i], real)==0){
            axx_diagf(0, 0, " error - circular pattern .INCLUDE detected: '%s' "
                       "(already in include chain). Skipped.\n", fn);
            return;
        }
    }

    FILE *f=axx_open_input(fn, "pattern file");
    if(!f) return;

    if(asmb->st.pat_include_depth < (int)(sizeof(asmb->st.pat_include_chain)
                                          / sizeof(asmb->st.pat_include_chain[0]))){
        asmb->st.pat_include_chain[asmb->st.pat_include_depth] = strdup(real);
    }
    asmb->st.pat_include_depth++;

    char this_dir[1024];
    axx_dir_of(fn, this_dir, sizeof(this_dir));

    if(asmb->st.pat_include_depth == 1) macro_reset_pass_pattern();

    int nexp = 0;
    char **exp = pat_macro_expand(f, fn, &nexp);
    fclose(f);
    f = NULL;

    char *line = NULL; size_t lcap = 0;
    for(int li = 0; li < nexp; li++){
        size_t need = strlen(exp[li]) + 1;
        if(need > lcap){
            char *nl = realloc(line, need);
            if(!nl){ perror("realloc"); exit(1); }
            line = nl; lcap = need;
        }
        memcpy(line, exp[li], need);
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
    pat_macro_expand_free(exp, nexp);
    asmb->st.pat_include_depth--;
    if(asmb->st.pat_include_depth >= 0
       && asmb->st.pat_include_depth < (int)(sizeof(asmb->st.pat_include_chain)
                                             / sizeof(asmb->st.pat_include_chain[0]))){
        free(asmb->st.pat_include_chain[asmb->st.pat_include_depth]);
        asmb->st.pat_include_chain[asmb->st.pat_include_depth] = NULL;
    }
}

static int replace_percent_with_index(const char *s, char *out, size_t osz){
    int count=0,i=0; size_t n=0; int truncated=0;
    while(s[i]){
        if(s[i]=='%'&&s[i+1]=='%'){
            char num[16]; snprintf(num,sizeof(num),"%d",count++);
            for(const char*p=num;*p;p++){
                if(n<osz-1) out[n++]=*p; else truncated=1;
            }
            i+=2;
        } else if(s[i]=='%'&&s[i+1]=='0'){ count=0; i+=2; }
        else {
            if(n<osz-1) out[n++]=s[i]; else truncated=1;
            i++;
        }
    }
    if(n<osz) out[n]=0; else if(osz>0) out[osz-1]=0;
    return truncated;
}

/* エンコーディング欄の `@@[個数, 式]` を個数分だけ展開する。
 * 例: `0xe8,@@[4,*(e-$.,%%)]` は 4 バイトのリトルエンディアン展開になる。
 * is_empty には「展開の結果ワードが1つも無い」ことを返す（`;` 条件付き出力で
 * 何も出さない命令を、長さ0として扱うため）。 */
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
                if(should_report_errors(&asmb->st)){
                    axx_diagf(1, 0, " error - @@[...]: missing ',' separating count and pattern.\n");
                }
                if(n+3<osz){ out[n++]='@'; out[n++]='@'; out[n++]='['; has_content=1; }
            }
        } else { out[n++]=pattern[i++]; has_content=1; }
    }
    out[n]=0;
    *is_empty=!has_content;
}

/* パターンのエンコーディング欄を評価して、出力ワード列 objl を作る。
 * s_in はカンマ区切りの式の並び。`%%`(連番) と `@@[]`(反復) は呼び出し前に
 * 展開済み。要素が `;` で始まるものは条件付き出力で、値が 0 なら何も出さない
 * （x86 の REX プレフィックスの有無のような分岐に使う）。 */
static void makeobj(Assembler *asmb, const char *s_in, IntVec *objl){
    AsmState *st=&asmb->st;
    iv_clear(objl);

    size_t ep_cap = 8192;
    char *ep_buf = NULL;
    int is_empty = 0;
    while(1){
        ep_buf = realloc(ep_buf, ep_cap);
        if(!ep_buf){ perror("realloc"); exit(1); }
        memset(ep_buf, 0, ep_cap);
        e_p(s_in, ep_buf, ep_cap, &is_empty, asmb);
        size_t used = strlen(ep_buf);
        if(used < ep_cap - 16) break;
        ep_cap *= 2;
        if(ep_cap > (size_t)256*1024*1024){
            fprintf(stderr,"makeobj: expanded pattern too large (>256 MB), truncating.\n");
            break;
        }
    }
    if(is_empty){ free(ep_buf); return; }

    size_t s_cap = strlen(ep_buf) + 64;
    char *s = NULL;
    while(1){
        s = realloc(s, s_cap);
        if(!s){ perror("malloc"); free(ep_buf); return; }
        int truncated = replace_percent_with_index(ep_buf, s, s_cap);
        if(!truncated) break;
        s_cap *= 2;
        if(s_cap > (size_t)256*1024*1024){
            fprintf(stderr,"makeobj: expanded %%%% index text too large (>256 MB), truncating.\n");
            break;
        }
    }
    free(ep_buf);

    int slen = (int)strlen(s);

    st->in_binary_list = 1;
    int _prior_undef = st->error_undefined_label;
    st->error_undefined_label = 0;
    int any_undef = 0;

    int logical_word_idx = 0;
    int idx=0;
    while(1){
        if(idx>=slen||s[idx]=='\0') break;
        if(s[idx]==','){
            idx++;
            continue;
        }
        int semicolon=0;
        if(s[idx]==';'){ semicolon=1; idx++; }
        st->elf_current_word_idx = logical_word_idx;
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
            int cur_widx = logical_word_idx - 1;
            int wi2 = 0;
            for(int ri2 = 0; ri2 < st->elf_refs_len; ri2++){
                if(st->elf_refs[ri2].word_idx != cur_widx)
                    st->elf_refs[wi2++] = st->elf_refs[ri2];
                else
                    free(st->elf_refs[ri2].name);
            }
            st->elf_refs_len = wi2;
            logical_word_idx--;
        }
        if(s[idx]==','){idx++;continue;}
        break;
    }
    st->elf_current_word_idx = -1;
    st->in_binary_list = 0;
    st->error_undefined_label = any_undef || _prior_undef;
    free(s);
}

typedef struct { IntVec *data; int len; int cap; } IVVec;
static void ivv_init(IVVec*v){v->data=NULL;v->len=0;v->cap=0;}
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

static int int_cmp(const void*a,const void*b){
    int ia=*(const int*)a, ib=*(const int*)b;
    return (ia > ib) - (ia < ib);
}

/* `!!` 区切りで並んだ複数命令を1つの VLIW パケットに詰めて出力する。
 *
 * 各スロットを lineassemble2() で個別に組み立て、vliwinstbits 幅のフィールドへ
 * 順に詰め、余ったスロットは vliwnop で埋める。EPIC ならスロットの組み合わせに
 * 対応するテンプレート値を合成する（テンプレート幅が負ならパケットの上位側に置く）。
 * 最後にパケット幅ぶんのバイト列として書き出し、pc をパケット1個分進める。
 *
 * 注意: パケット全体を書き終えるまで pc は進まないので、スロットの中身が
 * .section 等のディレクティブだと誤った pc を基準に副作用が起きる。
 * そのためスロット内のディレクティブは明確なエラーとして弾く。 */
static int vliwprocess(Assembler *asmb, const char *line, IntVec *idxs_in, IntVec *objl_in,
                       int idx, int *idx_out){
    AsmState *st=&asmb->st;
    IVVec objs; ivv_init(&objs);
    ivv_push(&objs,objl_in);

    int *idxlst=malloc(256*sizeof(int)); int nidxlst=0;
    for(int i=0;i<idxs_in->len;i++) if(nidxlst<256) idxlst[nidxlst++]=(int)u256_to_i64(idxs_in->data[i]);

    st->vliwstop=0;
    int slen=(int)strlen(line);
    while(1){
        idx=axx_skipspc(line,idx);
        if(idx<slen && line[idx]==VLIW_STOP_CHAR){ idx+=1; st->vliwstop=1; continue; }
        else if(idx<slen && line[idx]==VLIW_SEP_CHAR){
            idx+=1;
            { int _peek=idx; while(_peek<slen && (line[_peek]==' '||line[_peek]=='\t')) _peek++;
              if(_peek<slen && line[_peek]=='.'){
                  if(should_report_errors(st)){
                      axx_diagf(1, 0, " error - directives (e.g. .section/.endsection/.INCLUDE) "
                                 "are not allowed inside VLIW slots (the packet's PC has not "
                                 "advanced yet at this point in the packet).\n");
                  }
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

    if(st->vliwinstbits == 0){
        if(should_report_errors(st)){
            axx_diagf(1, 0, " error - vliwinstbits is zero; cannot compute instruction slots.\n");
        }
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
        if(noi <= 0){
            if(should_report_errors(st)){
                axx_diagf(1, 0, " error - .vliw: vliwtemplatebits (%d) leaves no room for "
                           "instruction slots in a %d-bit packet (vliwinstbits=%d).\n",
                           st->vliwtemplatebits, vbits, st->vliwinstbits);
            }
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
            if(!st->endian_big){
                for(int ii=0;ii<ibyte;ii++){
                    if(values.len>cnt2)
                        vv=u256_or(vv,u256_shl(u256_and(values.data[cnt2],u256_from_u64(0xff)),8*ii));
                    cnt2++;
                }
            } else {
                for(int ii=0;ii<ibyte;ii++){
                    vv=u256_shl(vv,8);
                    if(values.len>cnt2) vv=u256_or(vv,u256_and(values.data[cnt2],u256_from_u64(0xff)));
                    cnt2++;
                }
            }
            iv_push(&v1,u256_and(vv,im));
        }

        uint256_t pm=u256_sub(u256_shl(u256_one(),vbits),u256_one());
        uint256_t r=u256_zero();
        for(int vi=0;vi<v1.len;vi++){ r=u256_shl(r,st->vliwinstbits); r=u256_or(r,v1.data[vi]); }
        r=u256_and(r,pm);

        uint256_t res;
        if(st->vliwtemplatebits<0) res=u256_or(r,u256_shl(templ,(int)(vbits-at)));
        else res=u256_or(u256_shl(r,at),templ);

        int q=0;
        uint64_t pc64=u256_to_u64(st->pc);
        if(vbits<8){
            uint256_t vmask=u256_sub(u256_shl(u256_one(),vbits),u256_one());
            outbin(st,u256_from_u64(pc64),u256_and(res,vmask));
            q=1;
        } else {
            int total_bytes=(vbits+7)/8;
            for(int c2=0;c2<total_bytes;c2++){
                int shift = st->endian_big ? (total_bytes-1-c2)*8 : c2*8;
                uint256_t byte_v=u256_and(u256_sar(res,shift),u256_from_u64(0xff));
                outbin(st,u256_from_u64(pc64+(uint64_t)c2),byte_v);
                q++;
            }
        }
        st->pc=u256_add(st->pc,u256_from_u64((uint64_t)q));
        iv_free(&values); iv_free(&v1);
        found=1; break;
    }

    if(!found && (should_report_errors(st))){
        axx_diagf(1, 0, " error - No vliw instruction-set defined.\n");
    }

    ivv_free(&objs); free(idxlst);
    *idx_out=idx;
    return found;
}

static int adir_labelc(AsmState *st, const char *l, const char *ll){
    char up[32]; axx_strupr_to(up,l,sizeof(up));
    if(strcmp(up,".LABELC")!=0) return 0;
    if(ll&&ll[0]){
        snprintf(st->lwordchars, sizeof(st->lwordchars),
                 "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789%s", ll);
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
            const char *expr_tail = l + idx;
            int reloc_type = -1;
            const char *dcolon = strstr(expr_tail, "::");
            char expr_buf[1024];
            if(dcolon){
                size_t elen = (size_t)(dcolon - expr_tail);
                if(elen >= sizeof(expr_buf)) elen = sizeof(expr_buf)-1;
                memcpy(expr_buf, expr_tail, elen); expr_buf[elen] = '\0';
                expr_tail = expr_buf;
                const char *rt_str = dcolon + 2;
                char rt_lc[64]; int ri=0;
                while(rt_str[ri] && ri < 63){ rt_lc[ri]=(char)tolower((unsigned char)rt_str[ri]); ri++; }
                rt_lc[ri]='\0';
                reloc_type = elf_machine_named(elf_machine_find(st->elf_machine), rt_lc);
                if(reloc_type < 0)
                    axx_diagf(0, 0, " warning - unknown reloctype '%s' in .EQU for machine %d\n",
                               rt_lc, st->elf_machine);
            }

            uint256_t u;
            st->error_undefined_label = 0;
            int saved_mode = st->pass1_size_mode;
            if(st->pas == 1)
                st->pass1_size_mode = 1;
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
                    axx_diagf(0, 0, " warning - .EQU '%s': expression combines labels from "
                               "multiple sections without an explicit ::reloctype; the resulting "
                               "constant assumes a specific section layout and will NOT be "
                               "relocated by the linker.\n", label);
                }
            }
            if(st->error_undefined_label && should_report_errors(st)){
                axx_diagf(1, 0, " error - .EQU '%s': expression contains undefined label.\n",
                           label);
            }

            label_put_value(st,label,u,st->current_section,1,reloc_type,st->error_undefined_label);
            out[0]=0; return out;
        } else {
            label_put_value(st,label,st->pc,st->current_section,0,-1,0);
            strncpy(out,l+lidx,osz-1); out[osz-1]=0; return out;
        }
    }
    strncpy(out,l,osz-1); out[osz-1]=0; return out;
}

static int asciistr(Assembler *asmb, const char *l2){
    AsmState *st=&asmb->st;
    if(!l2[0]||l2[0]!='"') return 0;
    int idx=1;
    uint64_t word_mask = (st->bts > 0)
                       ? ((st->bts < 64) ? (((uint64_t)1 << st->bts) - 1) : (uint64_t)-1)
                       : 0xFFu;
    int truncated = 0;
    while(l2[idx]&&l2[idx]!='"'){
        uint32_t ch;
        if(l2[idx]=='\\'&&l2[idx+1]=='0'){ ch=0; idx+=2; }
        else if(l2[idx]=='\\'&&l2[idx+1]=='t'){ ch='\t'; idx+=2; }
        else if(l2[idx]=='\\'&&l2[idx+1]=='n'){ ch='\n'; idx+=2; }
        else if(l2[idx]=='\\'&&l2[idx+1]=='r'){ ch='\r'; idx+=2; }
        else if(l2[idx]=='\\'&&l2[idx+1]=='\\'){ ch='\\'; idx+=2; }
        else if(l2[idx]=='\\'&&l2[idx+1]=='"'){ ch='"'; idx+=2; }
        else if(l2[idx]=='\\'&&(l2[idx+1]=='x'||l2[idx+1]=='X')){
            idx+=2;
            char hx[3]; int hn=0;
            while(l2[idx]&&is_xdigit_upper(axx_upper_char(l2[idx]))&&hn<2)
                hx[hn++]=l2[idx++];
            hx[hn]=0;
            if(hn==0){
                char r[1024]; m_pyrepr(l2, r, sizeof(r));
                axx_diagf(0, 0, " error - '\\x' escape requires at least one hex digit in string: %s\n", r);
                return 0;
            }
            ch=(uint32_t)strtoul(hx,NULL,16);
        }
        else if(l2[idx]=='\\'&&(l2[idx+1]=='u'||l2[idx+1]=='U')){
            int want = (l2[idx+1]=='u') ? 4 : 8;
            char uc = l2[idx+1];
            idx+=2;
            char hx[9]; int hn=0;
            while(l2[idx]&&is_xdigit_upper(axx_upper_char(l2[idx]))&&hn<want)
                hx[hn++]=l2[idx++];
            hx[hn]=0;
            if(hn!=want){
                char r[1024]; m_pyrepr(l2, r, sizeof(r));
                axx_diagf(0, 0, " error - '\\%c' escape requires %d hex digits in string: %s\n",
                          uc, want, r);
                return 0;
            }
            unsigned long cp = strtoul(hx,NULL,16);
            if(cp > 0x10FFFFul){
                char r[1024]; m_pyrepr(l2, r, sizeof(r));
                axx_diagf(0, 0, " error - invalid \\u/\\U escape in string: %s\n", r);
                return 0;
            }
            ch=(uint32_t)cp;
        }
        else { ch=(uint32_t)(unsigned char)l2[idx]; idx++; }
        if((uint64_t)ch > word_mask) truncated = 1;
        outbin(st,st->pc,u256_from_u64((uint64_t)ch));
        st->pc=u256_add(st->pc,u256_one());
    }
    if(!l2[idx]){
        char r[1024]; m_pyrepr(l2, r, sizeof(r));
        axx_diagf(0, 0, " warning - unterminated string literal in .ASCII/.ASCIZ: %s\n", r);
    }
    if(truncated && should_report_errors(st)){
        char r[1024]; m_pyrepr(l2, r, sizeof(r));
        axx_diagf(0, 0, " warning - .ASCII/.ASCIZ: one or more characters exceed the output word "
                        "width (%d bit(s)) and were truncated (high bits discarded): %s\n",
                  st->bts, r);
    }
    return 1;
}

static int adir_section(AsmState *st, const char *l, const char *l2){
    char up[32]; axx_strupr_to(up,l,sizeof(up));
    if(strcmp(up,".SECTION")!=0 && strcmp(up,".SEGMENT")!=0) return 0;
    if(l2&&l2[0]){
        const char *old_sec = st->current_section;

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
        {
            SecEntry *oe = secmap_find(&st->sections, old_sec);
            if(oe){
                uint256_t delta = u256_sub(st->pc, oe->entry_pc);
                if(!u256_lt_signed(delta, u256_zero())){
                    oe->size = u256_add(oe->size, delta);
                    if(!u256_is_zero(delta))
                        secrangevec_push(&st->section_ranges, old_sec, oe->entry_pc, delta);
                }
            }
        }

        snprintf(st->current_section, sizeof(st->current_section), "%s", l2);

        SecEntry *ne = secmap_find(&st->sections, l2);
        if(!ne){
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

            if(u256_is_zero(ne->size) && !ne->confirmed){
                ne->start = st->pc;
            } else if(!ne->confirmed){
                if(u256_lt_signed(st->pc, ne->start)) ne->start = st->pc;
            }
            ne->entry_pc = st->pc;
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
        axx_diagf(1, 0, " error - .ENDSECTION without matching .SECTION for '%s'.\n",
                   st->current_section);
        return 1;
    }
    uint256_t delta = u256_sub(st->pc, e->entry_pc);
    if(!u256_lt_signed(delta, u256_zero())){
        e->size = u256_add(e->size, delta);
        if(!u256_is_zero(delta))
            secrangevec_push(&st->section_ranges, st->current_section, e->entry_pc, delta);
    }
    e->entry_pc = st->pc;
    e->confirmed = 1;
    return 1;
}
static int adir_resX(Assembler *asmb, const char *l, const char *l2,
                     const char *directive, uint64_t mul){
    char up[16]; axx_strupr_to(up,l,sizeof(up));
    if(strcmp(up,directive)!=0) return 0;
    asmb->st.error_undefined_label = 0;
    int io;
    uint256_t x=expr_expression_asm(asmb,l2,0,&io);
    if(asmb->st.error_undefined_label){
        if(should_report_errors(&asmb->st)){
            axx_diagf(1, 0, " error - %s argument contains undefined label.\n",directive);
        }
        return 1;
    }
    int64_t cnt=u256_to_i64(x);
    if(cnt < 0){
        if(should_report_errors(&asmb->st)){
            axx_diagf(1, 0, " error - %s requires a non-negative count, got %lld.\n",
                       directive,(long long)cnt);
        }
        return 1;
    }
    if(cnt > (int64_t)(1 << 28) / (int64_t)mul){
        if(should_report_errors(&asmb->st)){
            axx_diagf(1, 0, " error - %s count %lld (x%llu) exceeds maximum %d words.\n",
                       directive,(long long)cnt,(unsigned long long)mul,1<<28);
        }
        return 1;
    }
    int64_t total = cnt * (int64_t)mul;
    asmb->st.pc = u256_add(asmb->st.pc, u256_from_u64((uint64_t)total));
    return 1;
}

static int adir_resb(Assembler *asmb, const char *l, const char *l2){
    return adir_resX(asmb,l,l2,".RESB",1);
}
static int adir_resw(Assembler *asmb, const char *l, const char *l2){
    return adir_resX(asmb,l,l2,".RESW",2);
}
static int adir_resd(Assembler *asmb, const char *l, const char *l2){
    return adir_resX(asmb,l,l2,".RESD",4);
}
static int adir_resq(Assembler *asmb, const char *l, const char *l2){
    return adir_resX(asmb,l,l2,".RESQ",8);
}
static int adir_zero(Assembler *asmb, const char *l, const char *l2){
    char up[16]; axx_strupr_to(up,l,sizeof(up));
    if(strcmp(up,".ZERO")!=0) return 0;
    asmb->st.error_undefined_label = 0;
    int io;
    uint256_t x=expr_expression_asm(asmb,l2,0,&io);
    if(asmb->st.error_undefined_label){
        if(should_report_errors(&asmb->st)){
            axx_diagf(1, 0, " error - .ZERO argument contains undefined label.\n");
        }
        return 1;
    }
    int64_t cnt=u256_to_i64(x);
    if(cnt < 0){
        if(should_report_errors(&asmb->st)){
            axx_diagf(1, 0, " error - .ZERO requires a non-negative count, got %lld.\n", (long long)cnt);
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
    return asciistr(asmb,l2);
}
static int adir_asciiz(Assembler *asmb, const char *l, const char *l2){
    char up[16]; axx_strupr_to(up,l,sizeof(up));
    if(strcmp(up,".ASCIZ")!=0) return 0;
    int f=asciistr(asmb,l2);
    if(!f){
        if(should_report_errors(&asmb->st)){
            axx_diagf(1, 0, " error - .ASCIZ requires a quoted string.\n");
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
        asmb->st.error_undefined_label = 0;
        int io; uint256_t u=expr_expression_asm(asmb,l2,0,&io);
        if(asmb->st.error_undefined_label){
            if(should_report_errors(&asmb->st)){
                axx_diagf(1, 0, " error - .ALIGN argument contains undefined label.\n");
            }
            return 1;
        }

        if(u256_is_zero(u) || ((u.w[3]>>63)&1ULL)){
            if(should_report_errors(&asmb->st)){
                char _ab[96]; u256_to_pydec(u, _ab, sizeof(_ab));
                axx_diagf(1, 0, " error - .ALIGN requires a positive value, got %s.\n", _ab);
            }
            return 1;
        }
        asmb->st.align=u;
    }
    {
        uint64_t _raw = u256_to_u64(asmb->st.pc);
        int64_t _adj = equ_section_relative_offset(&asmb->st, asmb->st.current_section, _raw);
        uint64_t _base = (_adj >= 0) ? (uint64_t)_adj : _raw;
        uint256_t _aligned_base = align_addr256(&asmb->st, u256_from_u64(_base));
        uint256_t _padding = u256_sub(_aligned_base, u256_from_u64(_base));
        asmb->st.pc = u256_add(u256_from_u64(_raw), _padding);
    }
    return 1;
}
static int adir_org(Assembler *asmb, const char *l, const char *l2){
    char up[16]; axx_strupr_to(up,l,sizeof(up));
    if(strcmp(up,".ORG")!=0) return 0;
    const uint64_t ORG_FILL_MAX = (uint64_t)1<<28;
    asmb->st.error_undefined_label = 0;
    int io;
    uint256_t u=expr_expression_asm(asmb,l2,0,&io);
    if(asmb->st.error_undefined_label){
        if(should_report_errors(&asmb->st)){
            axx_diagf(1, 0, " error - .ORG argument contains undefined label.\n");
        }
        return 1;
    }
    if((u.w[3]>>63)&1ULL){
        if(should_report_errors(&asmb->st)){
            char nb[96]; u256_to_pydec(u, nb, sizeof(nb));
            axx_diagf(1, 0, " error - .ORG address must be non-negative, got %s.\n", nb);
        }
        return 1;
    }
    if(io+2<=(int)strlen(l2) && axx_upper_char(l2[io])==','&&axx_upper_char(l2[io+1])=='P'){
        if(u256_gt_signed(u,asmb->st.pc)){
            uint256_t _span = u256_sub(u, asmb->st.pc);
            if(u256_gt_signed(_span, u256_from_u64(ORG_FILL_MAX))){
                if(should_report_errors(&asmb->st)){
                    char sb2[96]; u256_to_pydec(_span, sb2, sizeof(sb2));
                    axx_diagf(1, 0, " error - .ORG ,P fill count %s exceeds maximum %llu.\n",
                              sb2, (unsigned long long)ORG_FILL_MAX);
                }
                return 1;
            }
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
        LabelEntry *le=lmap_find(&st->labels,s);
        int is_equ_v = le ? le->is_equ : 0;
        int is_undef_v = le ? le->is_undef : 0;
        if(!lmap_find(&st->export_labels,s)){
            sv_push(&st->export_order, s);
        }
        lmap_set(&st->export_labels,s,v,sec,is_equ_v,is_undef_v);
        if(buf[idx]==',') idx++;
    }
    return 1;
}

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
        if(idx > 0 && buf[idx-1]==':' && idx < blen && buf[idx]==':')
            idx--;
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
                for(int _ci=0;rt_str[_ci];_ci++)
                    if(rt_str[_ci]>='A'&&rt_str[_ci]<='Z') rt_str[_ci]+=32;
                int rtype = elf_machine_named(_mtbl_ext, rt_str);
                if(rtype < 0)
                    axx_diagf(0, 0, " warning - unknown reloc type '%s' in .EXTERN for machine %d\n",
                               rt_str, st->elf_machine);
                else
                    reloc_type = rtype;
            }
        }
        if(idx < blen && buf[idx]==':') idx++;
        LabelEntry *existing=lmap_find(&st->labels,s);
        if(!existing){
            lmap_set_imported(&st->labels, s, u256_zero(), ".text", reloc_type);
        } else if(existing->is_imported){
            if(reloc_type >= 0 && existing->reloc_type_override >= 0)
                existing->reloc_type_override = reloc_type;
        }
        idx=axx_skipspc(buf,idx);
        if(buf[idx]==',') idx++;
    }
    return 1;
}

static int adir_reloctype(Assembler *asmb, const char *l, const char *l2){
    AsmState *st=&asmb->st;
    char up[16]; axx_strupr_to(up,l,sizeof(up));
    if(strcmp(up,".RELOCTYPE")!=0) return 0;

    const ElfMachineInfo *_mtbl_rt = elf_machine_find(st->elf_machine);
    if(!_mtbl_rt){
        axx_diagf(0, 0, " warning - .RELOCTYPE: no relocation table for machine %d\n",
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
                axx_diagf(0, 0, " warning - .RELOCTYPE: too many arguments "
                           "(only 4 widths -- 8/16/32/64-bit -- are supported)\n");
            break;
        }

        char name[64]={0};
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
                axx_diagf(0, 0, " warning - unknown reloc type '%s' in "
                           ".RELOCTYPE for machine %d\n", name, st->elf_machine);
            } else {
                int expected_width = _widths[pos];
                int actual_width = elf_machine_reloc_bytes(_mtbl_rt, rtype);
                if(actual_width != 0 && actual_width != expected_width){
                    axx_diagf(0, 0, " warning - .RELOCTYPE: '%s' is a %d-bit "
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
        idx++;
    }
    return 1;
}

typedef struct {
    int       valid;
    int       score_expr, score_sym, score_lit;
    int       pln;
    PatEntry *pat;
    PatVar    vars[26];
    struct { char *name; uint64_t val; int word_idx; } *refs;
    int       refs_len;
    struct { int set; char *label_name; uint64_t label_val; } vtl[26];
    SymMap    symbols;
    StrVec    check_constraints[26];
    char      swordchars[256];
    uint256_t padding;
    int       bts;
    int       endian_big;
    int       vliwbits, vliwinstbits, vliwtemplatebits, vliwflag;
    IntVec    vliwnop;
    VliwSet   vliwset;
    int       error_undefined_label;

    char    **diags;
    int      *diag_seterr;
    int       diags_len;
} BestMatch;

static void best_init(BestMatch *b){
    memset(b, 0, sizeof(*b));
}

static void best_free(BestMatch *b){
    for(int i=0;i<b->diags_len;i++) free(b->diags[i]);
    free(b->diags); free(b->diag_seterr);
    b->diags = NULL; b->diag_seterr = NULL; b->diags_len = 0;
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

static int score_less(int e1,int s1,int l1, int e2,int s2,int l2){
    if(e1 != e2) return e1 < e2;
    if(l1 != l2) return l1 > l2;
    return s1 < s2;
}

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
    for(int i=0;i<26;i++){
        b->vtl[i].set       = st->elf_var_to_label[i].set;
        b->vtl[i].label_val = st->elf_var_to_label[i].label_val;
        b->vtl[i].label_name = st->elf_var_to_label[i].label_name
                               ? strdup(st->elf_var_to_label[i].label_name) : NULL;
    }
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

static int pat_prefix_matches(const char *pat, const char *lin){
    char pfx[64];
    int np = 0;
    for(const char *p = pat; *p && np < (int)sizeof(pfx)-1; p++){
        if(*p >= 'A' && *p <= 'Z') pfx[np++] = *p;
        else if(*p == ' ') continue;
        else break;
    }
    if(np == 0) return 1;
    int k = 0;
    for(const char *q = lin; *q; q++){
        if(*q == ' ') continue;
        if(axx_upper_char(*q) != pfx[k]) return 0;
        k++;
        if(k == np) return 1;
    }
    return 0;
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
    {
        char _adup[16]; axx_strupr_to(_adup,l,sizeof(_adup));
        if(strcmp(_adup,".ASCII")==0){
            if(!adir_ascii(asmb,l,l2) && should_report_errors(&asmb->st)){
                char r[1024]; m_pyrepr(l2?l2:"", r, sizeof(r));
                axx_diagf(1, 0, " error - .ASCII: failed to process string argument: %s\n", r);
            }
            *idx_out=idx; return 1;
        }
        if(strcmp(_adup,".ASCIZ")==0){
            if(!adir_asciiz(asmb,l,l2) && should_report_errors(&asmb->st)){
                char r[1024]; m_pyrepr(l2?l2:"", r, sizeof(r));
                axx_diagf(1, 0, " error - .ASCIZ: failed to process string argument: %s\n", r);
            }
            *idx_out=idx; return 1;
        }
    }
    { char up[16]; axx_strupr_to(up,l,sizeof(up));
      if(strcmp(up,".INCLUDE")==0){
          char raw[512]; axx_get_string(l2,raw,sizeof(raw));
          if(raw[0]){
              char resolved[1024];
              const char *cur = st->current_file;
              if(strcmp(raw,"stdin")==0){
                  strncpy(resolved, raw, sizeof(resolved)-1);
                  resolved[sizeof(resolved)-1]='\0';
              } else if(cur && cur[0] && strcmp(cur,"(stdin)")!=0 && strcmp(cur,"stdin")!=0){
                  char abs_buf[1024], dir_buf[1024];
                  if(cur[0]=='/'){
                      strncpy(abs_buf, cur, sizeof(abs_buf)-1);
                      abs_buf[sizeof(abs_buf)-1]='\0';
                  } else {
                      char cwd_buf[1024];
                      if(getcwd(cwd_buf, sizeof(cwd_buf)))
                          snprintf(abs_buf, sizeof(abs_buf), "%s/%s", cwd_buf, cur);
                      else {
                          strncpy(abs_buf, cur, sizeof(abs_buf)-1);
                          abs_buf[sizeof(abs_buf)-1]='\0';
                      }
                  }
                  axx_dir_of(abs_buf, dir_buf, sizeof(dir_buf));
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


    if(!l[0]){ *idx_out=idx; return 0; }

    int se=0, oerr=0, pln=0;
    int idxs_val=0;
    int loopflag=1;
    PatEntry *oerr_entry=NULL;
    int hit_sentinel=0;
    BestMatch best;
    best_init(&best);

    for(int pi=0;pi<st->pat.len;pi++){
        PatEntry *i=&st->pat.data[pi];
        pln++;
        for(int vi=0;vi<26;vi++){ st->vars[vi].val=u256_zero(); st->vars[vi].is_undef=0; }

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

        char lin[8192];
        if(l2[0]) snprintf(lin,sizeof(lin),"%s %s",l,l2);
        else      snprintf(lin,sizeof(lin),"%s",l);
        axx_reduce_spaces(lin);

        if(!i->f[0][0]){
            hit_sentinel=1;
            if(!best.valid){
                int io2;
                uint256_t idxv2=expr_expression_pat(asmb,i->f[3],0,&io2);
                idxs_val=(int)u256_to_i64(idxv2);
            }
            break;
        }

        if(!pat_prefix_matches(i->f[0], lin)) continue;

        st->error_undefined_label=0;
        st->expmode=EXP_ASM;

        PatVar    saved_vars[26];
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

        st->in_match_attempt = 1;
        diag_capture_begin(st);
        int _match_ok = pat_match0(asmb,lin,i->f[0]);
        st->in_match_attempt = 0;
        char **_cand_diags = NULL; int *_cand_seterr = NULL; int _cand_ndiag = 0;
        diag_capture_take(st, &_cand_diags, &_cand_seterr, &_cand_ndiag);
        if(!_match_ok){
            for(int di=0; di<_cand_ndiag; di++) free(_cand_diags[di]);
            free(_cand_diags); free(_cand_seterr);
            _cand_diags = NULL; _cand_seterr = NULL; _cand_ndiag = 0;
        }

        if(_match_ok){
            if(!best.valid ||
               score_less(st->match_score_expr, st->match_score_sym,
                          st->match_score_lit,
                          best.score_expr, best.score_sym, best.score_lit)){
                best_capture(st, &best, i, pln, saved_refs_len);
                best.diags       = _cand_diags;
                best.diag_seterr = _cand_seterr;
                best.diags_len   = _cand_ndiag;
                _cand_diags = NULL; _cand_seterr = NULL; _cand_ndiag = 0;
            }
            for(int di=0; di<_cand_ndiag; di++) free(_cand_diags[di]);
            free(_cand_diags); free(_cand_seterr);
            _cand_diags = NULL; _cand_seterr = NULL; _cand_ndiag = 0;
            memcpy(st->vars, saved_vars, sizeof(saved_vars));
            for(int ri2=saved_refs_len; ri2<st->elf_refs_len; ri2++)
                free(st->elf_refs[ri2].name);
            st->elf_refs_len = saved_refs_len;
            for(int vi=0;vi<26;vi++){
                free(st->elf_var_to_label[vi].label_name);
                st->elf_var_to_label[vi].set        = saved_vtl[vi].set;
                st->elf_var_to_label[vi].label_val  = saved_vtl[vi].label_val;
                st->elf_var_to_label[vi].label_name = saved_vtl[vi].label_name;
                saved_vtl[vi].label_name = NULL;
            }
            st->error_undefined_label=0;

            if(best.score_expr==0 && best.score_sym==0) break;
        } else {
            for(int vi=0;vi<26;vi++) free(saved_vtl[vi].label_name);
            st->error_undefined_label=0;
        }
    }

    if(best.valid){
        PatEntry *i = best.pat;
        pln = best.pln;
        loopflag = 0;

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
        st->error_undefined_label = best.error_undefined_label;
        diag_replay(st, best.diags, best.diag_seterr, best.diags_len);
        st->expmode = EXP_ASM;

        st->pc_instr_start = st->pc;
        st->pc_instr_end   = st->pc_instr_start;
        {
            int _probe_sm_saved  = st->pass1_size_mode;
            int _probe_refs_len  = st->elf_refs_len;
            int _probe_widx_saved = st->elf_current_word_idx;
            st->pass1_size_mode = 1;
            IntVec _probe_objl; iv_init(&_probe_objl);
            int _probe_err_undef_saved = st->error_undefined_label;
            st->error_undefined_label = 0;
            makeobj(asmb, i->f[2], &_probe_objl);
            uint256_t _probe_sz = u256_from_i64((int64_t)_probe_objl.len);
            st->pc_instr_end = u256_add(st->pc_instr_start, _probe_sz);
            iv_free(&_probe_objl);
            for(int ri2=_probe_refs_len; ri2<st->elf_refs_len; ri2++)
                free(st->elf_refs[ri2].name);
            st->elf_refs_len        = _probe_refs_len;
            st->elf_current_word_idx = _probe_widx_saved;
            st->pass1_size_mode     = _probe_sm_saved;
            st->error_undefined_label = _probe_err_undef_saved;
        }
        int err_triggered = dir_error(asmb,i->f[1]);
        if(!err_triggered){
            makeobj(asmb,i->f[2],objl_out);
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
        loopflag=0;
    }
    best_free(&best);

    if(loopflag){ se=1; pln=0; }

    if(should_report_errors(st)){
        if(st->error_undefined_label){
            axx_diagf(1, 0, " error - Undefined label in expression.  [%s:%d]\n",
                       st->current_file, (int)st->ln);
            *idx_out=idx; return 0;
        }
        if(se){
            axx_diagf(1, 0, " error - Syntax error.  [%s:%d]\n",
                       st->current_file, (int)st->ln);
            *idx_out=idx; return 0;
        }
        if(oerr){
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

typedef struct { const char *name; uint64_t val; int word_idx; } ElfRef;

static int elf_ref_cmp(const void *a, const void *b){
    int ia = ((const ElfRef *)a)->word_idx;
    int ib = ((const ElfRef *)b)->word_idx;
    return (ia > ib) - (ia < ib);
}

/* ソース1行を処理する主関数。
 *
 *   1. タブ・改行の正規化 → コメント除去 → `\!` エスケープ解決
 *   2. 行頭の `label:` / `.EQU` を処理
 *   3. VLIW スロット数を数える
 *   4. lineassemble2() でパターン照合とエンコードを行う
 *   5. VLIW 継続なら vliwprocess() へ、そうでなければバイト列を出力
 *   6. パス2かつ -o なら、この命令ぶんの ELF リロケーションを確定させる
 *
 * リロケーションは、式評価中に集めた (ラベル名, 生値, ワード番号) の並びを、
 * 同じラベルへの連続参照ごとにまとめて1件にし、加数を
 * 「生値 - 対象フィールドの絶対位置 [+ PC相対なら命令アドレス]」で求める。 */
static int lineassemble(Assembler *asmb, const char *line_in){
    AsmState *st=&asmb->st;

    size_t lin_len = strlen(line_in);
    char *line = malloc(lin_len + 2);
    if(!line){ perror("malloc"); return 0; }
    memcpy(line, line_in, lin_len + 1);

    for(char*p=line;*p;p++){ if(*p=='\t') *p=' '; if(*p=='\n'||*p=='\r') *p=' '; }
    axx_reduce_spaces(line);
    axx_remove_comment_asm(line);
    if(!line[0]){ free(line); return 0; }
    axx_resolve_vliw_escapes(line);

    for(int _ci = 0; _ci < 26; _ci++){
        sv_free(&asmb->st.check_constraints[_ci]);
        sv_init(&asmb->st.check_constraints[_ci]);
    }

    smap_clear(&asmb->st.symbols);
    for(int pi=0; pi<asmb->st.patsymbols.nb; pi++)
        for(SymEntry *se=asmb->st.patsymbols.buckets[pi]; se; se=se->next)
            smap_set(&asmb->st.symbols, se->key, se->val);

    char *processed = malloc(lin_len + 2);
    if(!processed){ perror("malloc"); free(line); return 0; }
    adir_label_processing(asmb, line, processed, lin_len + 2);
    free(line);

    if(st->pc.w[1]||st->pc.w[2]||st->pc.w[3]){
        if(!st->pc_overflow_set || u256_gt_signed(st->pc, st->pc_overflow_max)){
            st->pc_overflow_max = st->pc;
            st->pc_overflow_set = 1;
        }
    }

    /* VLIW スロット数を数える。
     * 番兵の判定は引用符・文字リテラルの外だけで行う（理由は
     * axx_get_param_to_spc() のコメントを参照）。 */
    {
        int _vcnt = 0;
        int _has_content = 0;
        int _in_dq = 0;
        const char *_pp = processed;
        while(*_pp){
            char _c = *_pp;
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
            if(_c == '\'' && !_in_dq){
                if(_pp[1] == '\\' && _pp[2] && _pp[3] == '\''){ _pp += 4; _has_content = 1; continue; }
                else if(_pp[1] && _pp[2] == '\''){ _pp += 3; _has_content = 1; continue; }
                _pp++; _has_content = 1;
                continue;
            }
            if(!_in_dq && (_c == VLIW_SEP_CHAR || _c == VLIW_STOP_CHAR)){
                if(_has_content){ _vcnt++; _has_content = 0; }
                _pp++;
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
    int is_vliw_cont=(st->vliwflag && (rest[0]==VLIW_SEP_CHAR||rest[0]==VLIW_STOP_CHAR));

    if(!is_vliw_cont){
        if(st->elf_objfile[0] && st->pas==2 && objl.len>0 && st->elf_refs_len>0){
            int bpw = (st->bts+7)/8; if(bpw<1) bpw=1;
            const char *sec_name = st->current_section;
            SecEntry *_rse = secmap_find(&st->sections, sec_name);
            uint64_t sec_completed_words = _rse ? u256_to_u64(_rse->size) : 0;
            uint64_t sec_entry_pc_cur    = _rse ? u256_to_u64(_rse->entry_pc) : 0;
            uint64_t cur_pc    = u256_to_u64(st->pc);

            const ElfMachineInfo *_mtbl_rm = elf_machine_find(st->elf_machine);
            #define RTYPE_FOR(nb) reloctype_for(st, _mtbl_rm, (nb))

            ElfRef *_valid = (ElfRef*)malloc((size_t)st->elf_refs_len * sizeof(ElfRef));
            if(!_valid){perror("malloc");exit(1);}
            int _nvalid = 0;
            for(int _ri=0; _ri<st->elf_refs_len; _ri++){
                if(st->elf_refs[_ri].word_idx >= 0)
                    _valid[_nvalid++] = (ElfRef){st->elf_refs[_ri].name,
                                              st->elf_refs[_ri].val,
                                              st->elf_refs[_ri].word_idx};
            }
            qsort(_valid, (size_t)_nvalid, sizeof(ElfRef), elf_ref_cmp);

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
                int _rtype = 0;
                int _rtype_is_default_guess = 0;
                {
                    LabelEntry *_le = lmap_find(&st->labels, _lname);
                    if(_le && _le->reloc_type_override >= 0){
                        int _rt_ov = _le->reloc_type_override;
                        int _expected = elf_machine_reloc_bytes(_mtbl_rm, _rt_ov);
                        if(_expected == 0 || _expected == _nbytes)
                            _rtype = _rt_ov;
                        else {
                            _rtype = RTYPE_FOR(_nbytes);
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
                    int _bts = st->bts;
                    uint64_t _wmask = (_bts < 64)
                        ? (((uint64_t)1 << _bts) - 1)
                        : (uint64_t)-1;
                    uint64_t _raw_val = 0;
                    if(!st->endian_big){
                        for(int _k = 0; _k < _nwords; _k++){
                            int _wk = _widx + _k;
                            if(_wk < objl.len){
                                uint64_t _wv = u256_to_u64(objl.data[_wk]) & _wmask;
                                _raw_val |= _wv << (_bts * _k);
                            }
                        }
                    } else {
                        for(int _k = 0; _k < _nwords; _k++){
                            int _wk = _widx + _k;
                            if(_wk < objl.len){
                                uint64_t _wv = u256_to_u64(objl.data[_wk]) & _wmask;
                                _raw_val = (_raw_val << _bts) | _wv;
                            }
                        }
                    }
                    {
                        int _field_bits = _nwords * _bts;
                        if(_field_bits > 0 && _field_bits < 64
                           && _raw_val >= ((uint64_t)1 << (_field_bits - 1))){
                            _raw_val -= ((uint64_t)1 << _field_bits);
                        }
                    }
                    int64_t _abs_w_bytes = (int64_t)_valid[_gi].val * (int64_t)bpw;

                    if(_rtype_is_default_guess && _rtype == 2 && _nbytes == 4
                       && st->elf_machine == 62
                       && (int64_t)_raw_val == _abs_w_bytes){
                        _rtype = 10;
                    }

                    if(_rtype_is_default_guess && st->elf_machine == 4){
                        int _is_pcrel_guess_m68k = elf_machine_is_pcrel(_mtbl_rm, _rtype);
                        if(_is_pcrel_guess_m68k && (int64_t)_raw_val == _abs_w_bytes){
                            switch(_nbytes){
                                case 4: _rtype = 1; break;
                                case 2: _rtype = 2; break;
                                case 1: _rtype = 3; break;
                            }
                        } else if(!_is_pcrel_guess_m68k && (int64_t)_raw_val != _abs_w_bytes){
                            switch(_nbytes){
                                case 4: _rtype = 4; break;
                                case 2: _rtype = 5; break;
                                case 1: _rtype = 6; break;
                            }
                        }
                    }

                    int64_t _addend;
                    {
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




typedef struct { uint8_t*b; size_t len,cap; } WBB;
typedef struct { const char*name; uint64_t bs,bsz,fl; uint8_t*data; } WCS;
typedef struct { uint16_t shndx; uint64_t sv; } WSR;
typedef struct { int64_t off; const char*sym; int rtype; int64_t addend; int nbytes; } WRE;
typedef struct { WRE*data; int len,cap; } WRL;
typedef struct { const char*name; int idx; } WSNI;
typedef struct { const char*name; uint64_t val; int is_equ; int is_imported; int reloc_type_override; const char*section; } WLK;
typedef struct { const char *name; uint8_t *data; size_t len; } DSEC;
typedef struct { const char *name; int target; uint8_t *data; size_t len; } DREL;
typedef struct { uint8_t*b; size_t len,cap; } RB;
typedef struct { uint64_t off; int sym; int rtype; int64_t addend; } DRE;
typedef struct { DRE*d; int len,cap; } DRV;
typedef struct { uint64_t wpc; int file; int line; } LROW;

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

static WSR weo_shndx(WCS*csecs,int ncs,uint64_t ba,const char*sec_name,
                      SecRangeVec*ranges,int bpw){
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
        uint64_t sv = ba - csecs[best_i].bs;
        if(ba < csecs[best_i].bs) sv = 0;
        return (WSR){(uint16_t)(best_i+1), sv};
    }
    return (WSR){0xfff1,ba};
}

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

static int cmp_wlk(const void*a,const void*b){ return strcmp(((const WLK*)a)->name,((const WLK*)b)->name); }

static int weo_isexp(WLK*earr,int ne,const char*nm){
    for(int i=0;i<ne;i++) if(!strcmp(earr[i].name,nm)) return 1;
    return 0;
}

static int weo_symof(WSNI*snimap,int snimap_len,const char*nm){
    for(int i=0;i<snimap_len;i++) if(!strcmp(snimap[i].name,nm)) return snimap[i].idx;
    return 0;
}

static int weo_isno(WCS*csecs,int i){
    char _n[64]; int _j=0;
    for(;csecs[i].name[_j]&&_j<63;_j++) _n[_j]=(char)axx_upper_char(csecs[i].name[_j]);
    _n[_j]=0;
    return strncmp(_n,".BSS",4)==0;
}

static void weo_pad(FILE*f,uint64_t t){
    long c=ftell(f);
    if(c < 0){ fprintf(stderr,"weo_pad: ftell failed\n"); return; }
    while((uint64_t)c<t){fputc(0,f);c++;}
}

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
static void rb_waddr(RB*r,uint64_t v,int addr_sz,int is_le){
    if(addr_sz==8) rb_w8(r,v,is_le); else rb_w4(r,(uint32_t)v,is_le);
}
static void drv_add(DRV*v,uint64_t off,int sym,int rtype,int64_t add){
    if(v->len>=v->cap){ v->cap=v->cap?v->cap*2:8; v->d=realloc(v->d,(size_t)v->cap*sizeof(DRE)); if(!v->d){perror("realloc");exit(1);} }
    v->d[v->len++]=(DRE){off,sym,rtype,add};
}
static uint8_t* dwarf_pack_relocs(DRV*v,size_t*outlen,int is_le,int is_elf64,int is_rela){
    size_t entsz = is_elf64 ? (is_rela?24:16) : (is_rela?12:8);
    size_t n=(size_t)v->len*entsz; uint8_t*b=calloc(1,n?n:1);
    for(int i=0;i<v->len;i++){
        uint8_t*p=b+(size_t)i*entsz;
        if(is_elf64){
            uint64_t rinfo=((uint64_t)v->d[i].sym<<32)|((uint32_t)v->d[i].rtype);
            weo_w8(p,v->d[i].off,is_le); weo_w8(p+8,rinfo,is_le);
            if(is_rela) weo_w8s(p+16,v->d[i].addend,is_le);
        } else {
            uint32_t rinfo=((uint32_t)(v->d[i].sym&0xffffff)<<8)|((uint8_t)v->d[i].rtype);
            weo_w4(p,(uint32_t)v->d[i].off,is_le); weo_w4(p+4,rinfo,is_le);
            if(is_rela) weo_w4(p+8,(uint32_t)v->d[i].addend,is_le);
        }
    }
    *outlen=n; return b;
}
static int lrow_cmp(const void*a,const void*b){ uint64_t x=((const LROW*)a)->wpc,y=((const LROW*)b)->wpc; return x<y?-1:(x>y?1:0); }

/* ELF リロケータブルオブジェクト(.o)を書き出す。
 * elfclass に応じて ELF32/ELF64 を、is_rela に応じて .rel/.rela を出し分ける。
 * Elf32_Sym と Elf64_Sym はフィールドの幅だけでなく並び順自体が違う点に注意。
 * -g 指定時は .debug_info/.debug_abbrev/.debug_line も生成する（64bit のみ）。 */
static void write_elf_obj(AsmState *st, const char *path, int machine){
    int bpw = (st->bts+7)/8; if(bpw<1) bpw=1;

    int _is_le  = !st->endian_big;
    int _ei_data = _is_le ? 1 : 2;

    const ElfMachineInfo *_mtbl_w = elf_machine_find(machine);
    int _is_rela_w = !_mtbl_w || _mtbl_w->is_rela;

    int _native_elfclass = _mtbl_w ? _mtbl_w->elfclass : 2;
    int _elfclass = st->elf_class ? st->elf_class : _native_elfclass;
    if(_elfclass != _native_elfclass){
        axx_diagf(0, 0, " warning - -f forced ELF%s for machine %d, whose "
                   "conventional class is ELF%s; writing a non-default "
                   "(but well-formed) combination.\n",
                   _elfclass==2 ? "64" : "32", machine,
                   _native_elfclass==2 ? "64" : "32");
    }
    int _is_elf64 = (_elfclass == 2);

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
    #define WEO_LE2(p,v)  WEO_W2(p,v)
    #define WEO_LE4(p,v)  WEO_W4(p,v)
    #define WEO_LE8(p,v)  WEO_W8(p,v)
    #define WEO_LE8S(p,v) WEO_W8S(p,v)



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

    int WEO_SYMSZ = _is_elf64 ? 24 : 16;
    WBB symtab_bb; symtab_bb.b=calloc(32,(size_t)WEO_SYMSZ); symtab_bb.len=0; symtab_bb.cap=32*WEO_SYMSZ;
    int nsyms=0;
    WSNI *snimap=calloc((size_t)(st->labels.count+st->export_labels.count+8),sizeof(WSNI));
    int snimap_len=0;

    weo_sym(&symtab_bb,&nsyms,_is_le,_is_elf64,0,0,0,0,0,0);
    for(int i=0;i<ncs;i++) weo_sym(&symtab_bb,&nsyms,_is_le,_is_elf64,0,0x03,0,(uint16_t)(i+1),0,0);

    int nl=0;
    WLK *larr=calloc((size_t)(st->labels.count?st->labels.count:1),sizeof(WLK));
    {for(int bi=0;bi<st->labels.nbuckets;bi++)
        for(LabelEntry*e=st->labels.buckets[bi];e;e=e->next){
            if(e->is_undef) continue;
            larr[nl++]=(WLK){e->key,u256_to_u64(e->value),e->is_equ,e->is_imported,e->reloc_type_override,e->section};}}
    qsort(larr,nl,sizeof(WLK),cmp_wlk);

    int ne=0;
    WLK *earr=calloc((size_t)(st->export_labels.count?st->export_labels.count:1),sizeof(WLK));
    {for(int bi=0;bi<st->export_labels.nbuckets;bi++)
        for(LabelEntry*e=st->export_labels.buckets[bi];e;e=e->next){
            if(e->is_undef) continue;
            LabelEntry *_fl=lmap_find(&st->labels,e->key);
            int _rto = _fl ? _fl->reloc_type_override : -1;
            earr[ne++]=(WLK){e->key,u256_to_u64(e->value),e->is_equ,0,_rto,e->section};}}
    qsort(earr,ne,sizeof(WLK),cmp_wlk);


    for(int i=0;i<nl;i++){
        if(weo_isexp(earr,ne,larr[i].name)) continue;
        if(larr[i].is_imported) continue;
        int _equ_has_reloc = larr[i].is_equ && (larr[i].reloc_type_override >= 0);
        WSR sr = (larr[i].is_equ && !_equ_has_reloc)
                 ? (WSR){0xfff1, larr[i].val}
                 : weo_shndx(csecs,ncs,larr[i].val*(uint64_t)bpw,larr[i].section,&st->section_ranges,bpw);
        uint32_t noff=wbb_str(&strtab_bb,larr[i].name);
        snimap[snimap_len++]=(WSNI){larr[i].name,nsyms};
        weo_sym(&symtab_bb,&nsyms,_is_le,_is_elf64,noff,0x00,0,sr.shndx,sr.sv,0);
    }
    int first_global=nsyms;
    for(int i=0;i<nl;i++){
        if(!larr[i].is_imported) continue;
        if(weo_isexp(earr,ne,larr[i].name)) continue;
        uint32_t noff=wbb_str(&strtab_bb,larr[i].name);
        snimap[snimap_len++]=(WSNI){larr[i].name,nsyms};
        weo_sym(&symtab_bb,&nsyms,_is_le,_is_elf64,noff,0x10,0,0,0,0);
    }
    for(int i=0;i<ne;i++){
        int _equ_has_reloc = earr[i].is_equ && (earr[i].reloc_type_override >= 0);
        WSR sr = (earr[i].is_equ && !_equ_has_reloc)
                 ? (WSR){0xfff1, earr[i].val}
                 : weo_shndx(csecs,ncs,earr[i].val*(uint64_t)bpw,earr[i].section,&st->section_ranges,bpw);
        uint32_t noff=wbb_str(&strtab_bb,earr[i].name);
        snimap[snimap_len++]=(WSNI){earr[i].name,nsyms};
        weo_sym(&symtab_bb,&nsyms,_is_le,_is_elf64,noff,0x10,0,sr.shndx,sr.sv,0);
    }


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

    DSEC dbg_prog[3]; int n_dbg_prog=0;
    DREL dbg_rela[2]; int n_dbg_rela=0;
    for(int _i=0;_i<3;_i++){ dbg_prog[_i]=(DSEC){NULL,NULL,0}; }
    for(int _i=0;_i<2;_i++){ dbg_rela[_i]=(DREL){NULL,0,NULL,0}; }

    const ElfMachineInfo *_mtbl_dbg = elf_machine_find(machine);
    if(st->gen_debug && st->line_map_len>0 && !_mtbl_dbg){
        axx_diagf(0, 0, " warning - DWARF debug info (-g) is not supported for "
                   "unknown machine %d; skipping debug sections.\n", machine);
    }
    if(st->gen_debug && st->line_map_len>0 && _mtbl_dbg){


        int addr_sz = _is_elf64 ? 8 : 4;
        int is_rela_dbg = _is_rela_w;

        int abs64 = _mtbl_dbg->dwarf_abs;

        RB abv; rb_init(&abv);
        rb_uleb(&abv,1); rb_uleb(&abv,0x11); rb_u8(&abv,1);
        rb_uleb(&abv,0x25);rb_uleb(&abv,0x08);
        rb_uleb(&abv,0x13);rb_uleb(&abv,0x05);
        rb_uleb(&abv,0x03);rb_uleb(&abv,0x08);
        rb_uleb(&abv,0x1b);rb_uleb(&abv,0x08);
        rb_uleb(&abv,0x11);rb_uleb(&abv,0x01);
        rb_uleb(&abv,0x12);rb_uleb(&abv,0x07);
        rb_uleb(&abv,0x10);rb_uleb(&abv,0x17);
        rb_uleb(&abv,0);rb_uleb(&abv,0);
        rb_uleb(&abv,2); rb_uleb(&abv,0x0a); rb_u8(&abv,0);
        rb_uleb(&abv,0x03);rb_uleb(&abv,0x08);
        rb_uleb(&abv,0x11);rb_uleb(&abv,0x01);
        rb_uleb(&abv,0);rb_uleb(&abv,0);
        rb_uleb(&abv,0);

        int primary_idx=0; uint64_t primary_size=0;
        for(int i=0;i<ncs;i++) if(strcmp(csecs[i].name,st->line_map[0].section)==0){ primary_idx=i+1; break; }
        if(primary_idx==0 && ncs>0) primary_idx=1;
        if(primary_idx>0) primary_size=csecs[primary_idx-1].bsz;

        char cwd[1024]; if(!getcwd(cwd,sizeof(cwd))) strcpy(cwd,".");
        const char *cu_name = st->line_map[0].file[0]?st->line_map[0].file:"(source)";
        const char *producer = "axx general assembler (C, DWARF4)";

        DRV info_relas={0,0,0};
        RB die; rb_init(&die);
        rb_uleb(&die,1);
        rb_cstr(&die,producer);
        rb_w2(&die,0x8001,_is_le);
        rb_cstr(&die,cu_name);
        rb_cstr(&die,cwd);
        if(primary_idx>0) drv_add(&info_relas,die.len,primary_idx,abs64,0);
        rb_waddr(&die,0,addr_sz,_is_le);
        rb_w8(&die,primary_size,_is_le);
        rb_w4(&die,0,_is_le);
        for(int i=0;i<nl;i++){
            if(larr[i].is_equ || larr[i].is_imported) continue;
            WSR sr = weo_shndx(csecs,ncs,larr[i].val*(uint64_t)bpw,larr[i].section,&st->section_ranges,bpw);
            if(sr.shndx==0xfff1) continue;
            rb_uleb(&die,2);
            rb_cstr(&die,larr[i].name);
            drv_add(&info_relas,die.len,(int)sr.shndx,abs64,(int64_t)sr.sv);
            rb_waddr(&die,is_rela_dbg?0:sr.sv,addr_sz,_is_le);
        }
        rb_uleb(&die,0);
        RB info; rb_init(&info);
        rb_w4(&info,(uint32_t)(2+4+1+die.len),_is_le);
        rb_w2(&info,4,_is_le);
        rb_w4(&info,0,_is_le);
        rb_u8(&info,(uint8_t)addr_sz);
        size_t info_prefix=info.len;
        rb_app(&info,die.b,die.len);
        free(die.b);

        DRV line_relas={0,0,0};
        const char **files=calloc((size_t)st->line_map_len,sizeof(char*)); int nfiles=0;
        int *row_file=calloc((size_t)st->line_map_len,sizeof(int));
        for(int i=0;i<st->line_map_len;i++){
            const char *fn=st->line_map[i].file[0]?st->line_map[i].file:"(source)";
            int fi=0; for(;fi<nfiles;fi++) if(strcmp(files[fi],fn)==0) break;
            if(fi==nfiles) files[nfiles++]=fn;
            row_file[i]=fi+1;
        }
        RB hb; rb_init(&hb);
        rb_u8(&hb,1);
        rb_u8(&hb,1);
        rb_u8(&hb,1);
        rb_u8(&hb,(uint8_t)(int8_t)-5);
        rb_u8(&hb,14);
        rb_u8(&hb,13);
        { static const uint8_t sol[12]={0,1,1,1,1,0,0,0,1,0,0,1}; rb_app(&hb,sol,12); }
        rb_u8(&hb,0);
        for(int fi=0;fi<nfiles;fi++){ rb_cstr(&hb,files[fi]); rb_uleb(&hb,0);rb_uleb(&hb,0);rb_uleb(&hb,0); }
        rb_u8(&hb,0);

        RB prog; rb_init(&prog);
        size_t prog_base = 4+2+4+hb.len;
        for(int s=0;s<ncs;s++){
            int cnt=0;
            for(int i=0;i<st->line_map_len;i++) if(strcmp(st->line_map[i].section,csecs[s].name)==0) cnt++;
            if(cnt==0) continue;
            LROW *rows=calloc((size_t)cnt,sizeof(LROW)); int k=0;
            for(int i=0;i<st->line_map_len;i++) if(strcmp(st->line_map[i].section,csecs[s].name)==0){
                rows[k].wpc=st->line_map[i].word_pc; rows[k].file=row_file[i]; rows[k].line=st->line_map[i].line; k++;
            }
            qsort(rows,(size_t)cnt,sizeof(LROW),lrow_cmp);
            uint64_t first_off = dwarf_word_offset(st, csecs[s].name, rows[0].wpc, bpw);
            rb_u8(&prog,0); rb_uleb(&prog,1+(uint64_t)addr_sz); rb_u8(&prog,2);
            drv_add(&line_relas, prog_base+prog.len, s+1, abs64, (int64_t)first_off);
            rb_waddr(&prog,is_rela_dbg?0:first_off,addr_sz,_is_le);
            uint64_t cur_off=first_off; int cur_line=1, cur_file=1;
            for(int i=0;i<cnt;i++){
                uint64_t boff = dwarf_word_offset(st, csecs[s].name, rows[i].wpc, bpw);
                if(rows[i].file!=cur_file){ rb_u8(&prog,4); rb_uleb(&prog,(uint64_t)rows[i].file); cur_file=rows[i].file; }
                if(rows[i].line!=cur_line){ rb_u8(&prog,3); rb_sleb(&prog,(int64_t)rows[i].line-cur_line); cur_line=rows[i].line; }
                if(boff>cur_off){ rb_u8(&prog,2); rb_uleb(&prog,boff-cur_off); cur_off=boff; }
                rb_u8(&prog,1);
            }
            uint64_t end_off=csecs[s].bsz;
            if(end_off>cur_off){ rb_u8(&prog,2); rb_uleb(&prog,end_off-cur_off); }
            rb_u8(&prog,0); rb_uleb(&prog,1); rb_u8(&prog,1);
            free(rows);
        }
        free(files); free(row_file);

        RB line; rb_init(&line);
        rb_w4(&line,(uint32_t)(2+4+hb.len+prog.len),_is_le);
        rb_w2(&line,4,_is_le);
        rb_w4(&line,(uint32_t)hb.len,_is_le);
        rb_app(&line,hb.b,hb.len);
        rb_app(&line,prog.b,prog.len);
        free(hb.b); free(prog.b);


        dbg_prog[n_dbg_prog++]=(DSEC){".debug_abbrev",abv.b,abv.len};
        int info_pi=n_dbg_prog; dbg_prog[n_dbg_prog++]=(DSEC){".debug_info",info.b,info.len};
        int line_pi=n_dbg_prog; dbg_prog[n_dbg_prog++]=(DSEC){".debug_line",line.b,line.len};
        for(int i=0;i<info_relas.len;i++) info_relas.d[i].off += info_prefix;
        if(info_relas.len>0){ size_t L; uint8_t*B=dwarf_pack_relocs(&info_relas,&L,_is_le,_is_elf64,is_rela_dbg); dbg_rela[n_dbg_rela++]=(DREL){is_rela_dbg?".rela.debug_info":".rel.debug_info",info_pi,B,L}; }
        if(line_relas.len>0){ size_t L; uint8_t*B=dwarf_pack_relocs(&line_relas,&L,_is_le,_is_elf64,is_rela_dbg); dbg_rela[n_dbg_rela++]=(DREL){is_rela_dbg?".rela.debug_line":".rel.debug_line",line_pi,B,L}; }
        free(info_relas.d); free(line_relas.d);
    }
    uint32_t dbg_prog_noff[3]={0,0,0};
    uint32_t dbg_rela_noff[2]={0,0};
    for(int i=0;i<n_dbg_prog;i++) dbg_prog_noff[i]=wbb_str(&shstr,dbg_prog[i].name);
    for(int i=0;i<n_dbg_rela;i++) dbg_rela_noff[i]=wbb_str(&shstr,dbg_rela[i].name);

    uint64_t foff=_is_elf64?64:52;
    uint64_t *sec_fo=calloc((size_t)ncs,sizeof(uint64_t));
    for(int i=0;i<ncs;i++){
        foff=WEO_ALIGN(foff,16); sec_fo[i]=foff;
        if(!weo_isno(csecs,i)) foff+=csecs[i].bsz;
    }
    uint64_t *rela_fo=calloc((size_t)(nrela?nrela:1),sizeof(uint64_t));
    for(int ri2=0;ri2<nrela;ri2++){foff=WEO_ALIGN(foff,8);rela_fo[ri2]=foff;foff+=rela_szs[ri2];}
    uint64_t sym_fo=WEO_ALIGN(foff,8); foff=sym_fo+(uint64_t)nsyms*(uint64_t)WEO_SYMSZ;
    uint64_t str_fo=foff;     foff+=strtab_bb.len;
    uint64_t shstr_fo=foff;   foff+=shstr.len;
    uint64_t dbg_prog_fo[3]={0,0,0};
    for(int i=0;i<n_dbg_prog;i++){ foff=WEO_ALIGN(foff,1); dbg_prog_fo[i]=foff; foff+=dbg_prog[i].len; }
    uint64_t dbg_rela_fo[2]={0,0};
    for(int i=0;i<n_dbg_rela;i++){ foff=WEO_ALIGN(foff,8); dbg_rela_fo[i]=foff; foff+=dbg_rela[i].len; }
    uint64_t shdr_fo=WEO_ALIGN(foff,8);

    int ndbg=n_dbg_prog+n_dbg_rela;
    int tot_sh=1+ncs+nrela+3+ndbg;
    int shstrndx=ncs+nrela+3;
    int dbg_base=ncs+nrela+3;
    int sym_shidx=ncs+nrela+1;
    int str_shidx=ncs+nrela+2;

    FILE *fp=fopen(path,"wb");
    if(!fp){
        if(should_report_errors(st)){
            axx_diagf(1, 0, " error - cannot create ELF output file '%s': %s\n", path, strerror(errno));
        }
        goto weo_done;
    }

    if(_is_elf64){
        uint8_t eh[64]={0};
        eh[0]=0x7f;eh[1]='E';eh[2]='L';eh[3]='F';
        eh[4]=2;eh[5]=(uint8_t)_ei_data;eh[6]=1;eh[7]=st->osabi;
        WEO_LE2(eh+16,1); WEO_LE2(eh+18,(uint16_t)machine); WEO_LE4(eh+20,1);
        WEO_LE8(eh+40,shdr_fo);
        WEO_LE2(eh+52,64); WEO_LE2(eh+58,64);
        WEO_LE2(eh+60,(uint16_t)tot_sh); WEO_LE2(eh+62,(uint16_t)shstrndx);
        fwrite(eh,1,64,fp);
    } else {
        uint8_t eh[52]={0};
        eh[0]=0x7f;eh[1]='E';eh[2]='L';eh[3]='F';
        eh[4]=1;eh[5]=(uint8_t)_ei_data;eh[6]=1;eh[7]=st->osabi;
        WEO_LE2(eh+16,1); WEO_LE2(eh+18,(uint16_t)machine); WEO_LE4(eh+20,1);
        WEO_LE4(eh+32,(uint32_t)shdr_fo);
        WEO_LE2(eh+40,52); WEO_LE2(eh+46,40);
        WEO_LE2(eh+48,(uint16_t)tot_sh); WEO_LE2(eh+50,(uint16_t)shstrndx);
        fwrite(eh,1,52,fp);
    }


    for(int i=0;i<ncs;i++){
        weo_pad(fp,sec_fo[i]);
        if(!weo_isno(csecs,i) && csecs[i].bsz) fwrite(csecs[i].data,1,(size_t)csecs[i].bsz,fp);
    }
    for(int ri2=0;ri2<nrela;ri2++){weo_pad(fp,rela_fo[ri2]);if(rela_szs[ri2])fwrite(rela_bufs[ri2],1,rela_szs[ri2],fp);}
    weo_pad(fp,sym_fo); fwrite(symtab_bb.b,1,(size_t)nsyms*(size_t)WEO_SYMSZ,fp);
    fwrite(strtab_bb.b,1,strtab_bb.len,fp);
    fwrite(shstr.b,1,shstr.len,fp);
    for(int i=0;i<n_dbg_prog;i++){ weo_pad(fp,dbg_prog_fo[i]); if(dbg_prog[i].len) fwrite(dbg_prog[i].data,1,dbg_prog[i].len,fp); }
    for(int i=0;i<n_dbg_rela;i++){ weo_pad(fp,dbg_rela_fo[i]); if(dbg_rela[i].len) fwrite(dbg_rela[i].data,1,dbg_rela[i].len,fp); }
    weo_pad(fp,shdr_fo);

    weo_shdr(fp,_is_le,_is_elf64,0,0,0,0,0,0,0,0,0,0);
    for(int i=0;i<ncs;i++){
        char _un[64]; int _ui=0;
        for(;csecs[i].name[_ui]&&_ui<63;_ui++) _un[_ui]=(char)axx_upper_char(csecs[i].name[_ui]);
        _un[_ui]=0;
        uint32_t _sh_type = (strncmp(_un,".BSS",4)==0) ? 8 : 1;
        weo_shdr(fp,_is_le,_is_elf64,sec_noff[i],_sh_type,csecs[i].fl,0,sec_fo[i],csecs[i].bsz,0,0,16,0);
    }
    {
    uint32_t _word_align = _is_elf64?8:4;
    uint32_t _rel_sh_type = _is_rela_w?4:9;
    for(int ri2=0;ri2<nrela;ri2++)
        weo_shdr(fp,_is_le,_is_elf64,rela_noff[ri2],_rel_sh_type,0x40,0,rela_fo[ri2],rela_szs[ri2],
                 (uint32_t)sym_shidx,(uint32_t)(rs_idx[ri2]+1),_word_align,(uint64_t)_reloc_entsz);
    weo_shdr(fp,_is_le,_is_elf64,sym_noff,2,0,0,sym_fo,(uint64_t)nsyms*(uint64_t)WEO_SYMSZ,
             (uint32_t)str_shidx,(uint32_t)first_global,_word_align,(uint64_t)WEO_SYMSZ);
    }
    weo_shdr(fp,_is_le,_is_elf64,str_noff,3,0,0,str_fo,strtab_bb.len,0,0,1,0);
    weo_shdr(fp,_is_le,_is_elf64,shstr_noff,3,0,0,shstr_fo,shstr.len,0,0,1,0);
    for(int i=0;i<n_dbg_prog;i++)
        weo_shdr(fp,_is_le,_is_elf64,dbg_prog_noff[i],1,0,0,dbg_prog_fo[i],dbg_prog[i].len,0,0,1,0);
    {
    uint32_t _dbg_word_align = _is_elf64?8:4;
    uint32_t _dbg_rel_sh_type = _is_rela_w?4:9;
    for(int i=0;i<n_dbg_rela;i++)
        weo_shdr(fp,_is_le,_is_elf64,dbg_rela_noff[i],_dbg_rel_sh_type,0x40,0,dbg_rela_fo[i],dbg_rela[i].len,
                 (uint32_t)sym_shidx,(uint32_t)(dbg_base+1+dbg_rela[i].target),_dbg_word_align,(uint64_t)_reloc_entsz);
    }
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


#include <setjmp.h>

enum {
    MACRO_MAX_DEPTH          = 200,
    MACRO_MAX_INCLUDE_DEPTH  = 64,
    MACRO_MAX_SCOPES         = 256,
    MACRO_MAX_ARGS           = 64
};
#define MACRO_MAX_ITER   1000000L
#define MACRO_MAX_LINES  2000000L
#define MACRO_MAX_ARENA  ((size_t)512*1024*1024)

typedef struct MArenaBlk { struct MArenaBlk *next; size_t used, cap; char *data; } MArenaBlk;
typedef struct { MArenaBlk *head; size_t total; } MArena;

typedef struct MacroPP MacroPP;
static void m_fail(MacroPP *mp, const char *file, int line, const char *fmt, ...);

typedef struct { int is_str; long long i; char *s; } MVal;

typedef struct { char *text; const char *file; int line; } MLine;
typedef struct { MLine *d; int len, cap; } MLineVec;

typedef enum {
    MN_TEXT, MN_IF, MN_WHILE, MN_DEF, MN_SET, MN_LOCAL, MN_UNDEF,
    MN_CALL, MN_RETURN, MN_BREAK, MN_CONTINUE, MN_ERROR, MN_WARNING,
    MN_ECHO, MN_INCLUDE
} MNKind;

typedef struct MNode MNode;
typedef struct { MNode **d; int len, cap; } MBlock;

struct MNode {
    MNKind      kind;
    const char *file;
    int         line;
    char       *a;
    char       *b;
    char      **conds;
    MBlock     *arms;
    int         narms;
    MBlock     *elsebody;
    MBlock     *body;
    char      **params;
    char      **defaults;
    int         nparams;
};

typedef struct {
    char   *name;
    char  **params;
    char  **defaults;
    int     nparams;
    MBlock *body;
    const char *file;
    int     line;
    int     defined;
} MFunc;

typedef struct { char **names; MVal *vals; int len, cap; } MScope;

typedef enum { MCTL_NONE = 0, MCTL_BREAK, MCTL_CONTINUE, MCTL_RETURN } MCtl;

struct MacroPP {
    Assembler *asmb;
    MArena     arena;

    MFunc     *funcs;
    int        nfuncs, cfuncs;
    char     **declared;
    int        ndecl, cdecl;

    MScope    *scopes[MACRO_MAX_SCOPES];
    int        nscopes;

    MLineVec  *out;
    int        depth;
    long long  uid;
    long       nemitted;

    char      *inc_stack[MACRO_MAX_INCLUDE_DEPTH];
    int        ninc;

    MCtl       ctl;
    MVal       retval;

    int        enabled;
    int        had_error;

    char      *pending_buf;

    const char *cur_expr;

    int        pat_mode;

    char     **reported;
    int        nreported, creported;

    jmp_buf    jb;
    int        jb_active;
};


static void *marena_alloc(MArena *a, size_t n){
    n = (n + 15) & ~(size_t)15;
    if(a->head && a->head->cap - a->head->used >= n){
        void *p = a->head->data + a->head->used;
        a->head->used += n;
        return p;
    }
    size_t cap = n > 65536 ? n : 65536;
    MArenaBlk *b = malloc(sizeof(MArenaBlk));
    if(!b){ perror("malloc"); exit(1); }
    b->data = malloc(cap);
    if(!b->data){ perror("malloc"); exit(1); }
    b->cap = cap; b->used = n; b->next = a->head;
    a->head = b;
    a->total += cap;
    return b->data;
}
static void marena_reset(MArena *a){
    MArenaBlk *b = a->head;
    while(b){ MArenaBlk *n = b->next; free(b->data); free(b); b = n; }
    a->head = NULL; a->total = 0;
}
static char *marena_strndup(MArena *a, const char *s, size_t n){
    char *p = marena_alloc(a, n + 1);
    memcpy(p, s, n); p[n] = '\0';
    return p;
}
static char *marena_strdup(MArena *a, const char *s){
    return marena_strndup(a, s, strlen(s));
}


static void mblock_push(MacroPP *mp, MBlock *b, MNode *n){
    if(b->len >= b->cap){
        int nc = b->cap ? b->cap * 2 : 8;
        MNode **nd = marena_alloc(&mp->arena, (size_t)nc * sizeof(MNode*));
        if(b->len) memcpy(nd, b->d, (size_t)b->len * sizeof(MNode*));
        b->d = nd; b->cap = nc;
    }
    b->d[b->len++] = n;
}
static void mlinevec_push(MacroPP *mp, MLineVec *v, char *text, const char *file, int line){
    if(v->len >= v->cap){
        int nc = v->cap ? v->cap * 2 : 64;
        MLine *nd = marena_alloc(&mp->arena, (size_t)nc * sizeof(MLine));
        if(v->len) memcpy(nd, v->d, (size_t)v->len * sizeof(MLine));
        v->d = nd; v->cap = nc;
    }
    v->d[v->len].text = text;
    v->d[v->len].file = file;
    v->d[v->len].line = line;
    v->len++;
}


static void macro_init(MacroPP *mp, Assembler *asmb){
    memset(mp, 0, sizeof(*mp));
    mp->asmb = asmb;
    mp->enabled = 1;
}
static void macro_reset_pass(MacroPP *mp){
    for(int i = 0; i < mp->nscopes; i++){
        free(mp->scopes[i]->names);
        free(mp->scopes[i]->vals);
        free(mp->scopes[i]);
    }
    mp->nscopes = 0;
    marena_reset(&mp->arena);
    mp->funcs = NULL;   mp->nfuncs = mp->cfuncs = 0;
    mp->declared = NULL; mp->ndecl = mp->cdecl = 0;
    mp->out = NULL;
    mp->depth = 0;
    mp->uid = 0;
    mp->nemitted = 0;
    mp->ninc = 0;
    mp->ctl = MCTL_NONE;
    mp->retval.is_str = 0; mp->retval.i = 0; mp->retval.s = NULL;
    mp->jb_active = 0;
    MScope *g = calloc(1, sizeof(MScope));
    if(!g){ perror("calloc"); exit(1); }
    mp->scopes[mp->nscopes++] = g;
}
static void macro_free(MacroPP *mp){
    macro_reset_pass(mp);
    for(int i = 0; i < mp->nscopes; i++){
        free(mp->scopes[i]->names); free(mp->scopes[i]->vals); free(mp->scopes[i]);
    }
    mp->nscopes = 0;
    for(int i = 0; i < mp->nreported; i++) free(mp->reported[i]);
    free(mp->reported); mp->reported = NULL; mp->nreported = mp->creported = 0;
    marena_reset(&mp->arena);
}


static int m_first_report(MacroPP *mp, const char *msg){
    for(int i = 0; i < mp->nreported; i++)
        if(strcmp(mp->reported[i], msg) == 0) return 0;
    if(mp->nreported >= mp->creported){
        mp->creported = mp->creported ? mp->creported * 2 : 16;
        char **t = realloc(mp->reported, (size_t)mp->creported * sizeof(char*));
        if(!t){ perror("realloc"); exit(1); }
        mp->reported = t;
    }
    mp->reported[mp->nreported++] = strdup(msg);
    return 1;
}

static void m_warn(MacroPP *mp, const char *file, int line, const char *fmt, ...){
    char body[1024];
    va_list ap; va_start(ap, fmt);
    vsnprintf(body, sizeof(body), fmt, ap);
    va_end(ap);
    char msg[1200];
    if(line < 0) snprintf(msg, sizeof(msg), "%s: %s", file ? file : "?", body);
    else snprintf(msg, sizeof(msg), "%s:%d: %s", file ? file : "?", line, body);
    if(m_first_report(mp, msg))
        axx_diagf(0, 1, " warning - %s\n", msg);
}

static void m_fail(MacroPP *mp, const char *file, int line, const char *fmt, ...){
    char body[1024];
    va_list ap; va_start(ap, fmt);
    vsnprintf(body, sizeof(body), fmt, ap);
    va_end(ap);
    char msg[1200];
    if(line < 0) snprintf(msg, sizeof(msg), "%s: %s", file ? file : "?", body);
    else snprintf(msg, sizeof(msg), "%s:%d: %s", file ? file : "?", line, body);
    if(m_first_report(mp, msg))
        axx_diagf(0, 1, " error - %s\n", msg);
    mp->had_error = 1;
    if(mp->asmb) mp->asmb->st.had_error = 1;
    if(mp->pending_buf){ free(mp->pending_buf); mp->pending_buf = NULL; }
    if(mp->jb_active) longjmp(mp->jb, 1);
    exit(1);
}


static void m_pyrepr(const char *s, char *out, size_t outsz){
    if(outsz < 3){ if(outsz) out[0] = '\0'; return; }
    int has_sq = strchr(s, '\'') != NULL;
    int has_dq = strchr(s, '"') != NULL;
    char q = (has_sq && !has_dq) ? '"' : '\'';
    size_t o = 0;
    out[o++] = q;
    for(const unsigned char *p = (const unsigned char*)s; *p; p++){
        unsigned char c = *p;
        if(o + 6 >= outsz) break;
        if(c == '\\' || c == (unsigned char)q){ out[o++] = '\\'; out[o++] = (char)c; }
        else if(c == '\n'){ out[o++] = '\\'; out[o++] = 'n'; }
        else if(c == '\t'){ out[o++] = '\\'; out[o++] = 't'; }
        else if(c == '\r'){ out[o++] = '\\'; out[o++] = 'r'; }
        else if(c < 0x20 || c == 0x7f){
            int nn = snprintf(out + o, outsz - o, "\\x%02x", c);
            o += (nn > 0) ? (size_t)nn : 0;
        } else out[o++] = (char)c;
    }
    out[o++] = q;
    out[o] = '\0';
}


static MVal mv_int(long long v){ MVal r; r.is_str = 0; r.i = v; r.s = NULL; return r; }
static MVal mv_str(char *s){ MVal r; r.is_str = 1; r.i = 0; r.s = s; return r; }
static int  mv_truth(MVal v){ return v.is_str ? (v.s && v.s[0]) : (v.i != 0); }

static char *mv_to_text(MacroPP *mp, MVal v){
    if(v.is_str) return v.s ? v.s : (char*)"";
    char buf[32];
    snprintf(buf, sizeof(buf), "%lld", v.i);
    return marena_strdup(&mp->arena, buf);
}
static long long mv_need_int(MacroPP *mp, MVal v, const char *file, int line){
    if(v.is_str){
        char vr[600], er[600];
        m_pyrepr(v.s ? v.s : "", vr, sizeof(vr));
        if(mp->cur_expr) m_pyrepr(mp->cur_expr, er, sizeof(er));
        else { er[0] = '?'; er[1] = '\0'; }
        m_fail(mp, file, line, "macro expression: expected an integer, got the string %s in %s", vr, er);
    }
    return v.i;
}
static long long m_cdiv(long long a, long long b){
    long long q = (a < 0 ? -a : a) / (b < 0 ? -b : b);
    return ((a >= 0) == (b >= 0)) ? q : -q;
}
static long long m_cmod(long long a, long long b){ return a - m_cdiv(a, b) * b; }


static MScope *m_scope(MacroPP *mp){ return mp->scopes[mp->nscopes - 1]; }

static MVal *m_scope_find(MScope *sc, const char *name){
    for(int i = 0; i < sc->len; i++)
        if(strcmp(sc->names[i], name) == 0) return &sc->vals[i];
    return NULL;
}
static void m_scope_set(MScope *sc, char *name, MVal v){
    MVal *p = m_scope_find(sc, name);
    if(p){ *p = v; return; }
    if(sc->len >= sc->cap){
        sc->cap = sc->cap ? sc->cap * 2 : 8;
        sc->names = realloc(sc->names, (size_t)sc->cap * sizeof(char*));
        sc->vals  = realloc(sc->vals,  (size_t)sc->cap * sizeof(MVal));
        if(!sc->names || !sc->vals){ perror("realloc"); exit(1); }
    }
    sc->names[sc->len] = name;
    sc->vals[sc->len]  = v;
    sc->len++;
}
static void m_scope_del(MScope *sc, const char *name){
    for(int i = 0; i < sc->len; i++)
        if(strcmp(sc->names[i], name) == 0){
            for(int j = i; j < sc->len - 1; j++){
                sc->names[j] = sc->names[j+1];
                sc->vals[j]  = sc->vals[j+1];
            }
            sc->len--;
            return;
        }
}

static MFunc *m_func_find(MacroPP *mp, const char *name){
    for(int i = 0; i < mp->nfuncs; i++)
        if(strcmp(mp->funcs[i].name, name) == 0) return &mp->funcs[i];
    return NULL;
}
static MFunc *m_func_add(MacroPP *mp, const char *name){
    if(mp->nfuncs >= mp->cfuncs){
        int nc = mp->cfuncs ? mp->cfuncs * 2 : 16;
        MFunc *nd = marena_alloc(&mp->arena, (size_t)nc * sizeof(MFunc));
        memset(nd, 0, (size_t)nc * sizeof(MFunc));
        if(mp->nfuncs) memcpy(nd, mp->funcs, (size_t)mp->nfuncs * sizeof(MFunc));
        mp->funcs = nd; mp->cfuncs = nc;
    }
    MFunc *f = &mp->funcs[mp->nfuncs++];
    memset(f, 0, sizeof(*f));
    f->name = marena_strdup(&mp->arena, name);
    return f;
}
static int m_declared(MacroPP *mp, const char *name){
    for(int i = 0; i < mp->ndecl; i++)
        if(strcmp(mp->declared[i], name) == 0) return 1;
    return 0;
}
static void m_declare(MacroPP *mp, const char *name){
    if(m_declared(mp, name)) return;
    if(mp->ndecl >= mp->cdecl){
        int nc = mp->cdecl ? mp->cdecl * 2 : 16;
        char **nd = marena_alloc(&mp->arena, (size_t)nc * sizeof(char*));
        if(mp->ndecl) memcpy(nd, mp->declared, (size_t)mp->ndecl * sizeof(char*));
        mp->declared = nd; mp->cdecl = nc;
    }
    mp->declared[mp->ndecl++] = marena_strdup(&mp->arena, name);
}

static int m_is_defined(MacroPP *mp, const char *name){
    if(m_func_find(mp, name)) return 1;
    for(int i = mp->nscopes - 1; i >= 0; i--)
        if(m_scope_find(mp->scopes[i], name)) return 1;
    return 0;
}
static MVal m_lookup(MacroPP *mp, const char *name, const char *file, int line){
    for(int i = mp->nscopes - 1; i >= 0; i--){
        MVal *p = m_scope_find(mp->scopes[i], name);
        if(p) return *p;
    }
    if(m_func_find(mp, name))
        m_fail(mp, file, line, "macro '%s' used as a variable (call it as '%s(...)')", name, name);
    m_fail(mp, file, line, "undefined macro variable '%s'", name);
    return mv_int(0);
}
static void m_assign(MacroPP *mp, const char *name, MVal v){
    for(int i = mp->nscopes - 1; i >= 0; i--){
        MVal *p = m_scope_find(mp->scopes[i], name);
        if(p){ *p = v; return; }
    }
    m_scope_set(m_scope(mp), marena_strdup(&mp->arena, name), v);
}


typedef struct { const char *s; int i; MacroPP *mp; const char *file; int line; } MEP;

static MVal mep_ternary(MEP *p);
static MVal m_call_value(MacroPP *mp, const char *name, MVal *args, int nargs,
                         const char *file, int line);

static void mep_skip(MEP *p){ while(p->s[p->i] == ' ' || p->s[p->i] == '\t') p->i++; }

static int mep_eat(MEP *p, const char *tok){
    mep_skip(p);
    size_t n = strlen(tok);
    if(strncmp(p->s + p->i, tok, n) != 0) return 0;
    p->i += (int)n;
    return 1;
}
static void mep_expect(MEP *p, const char *tok){
    if(!mep_eat(p, tok)){
        char tokr[16], sr[600];
        m_pyrepr(tok, tokr, sizeof(tokr));
        m_pyrepr(p->s, sr, sizeof(sr));
        m_fail(p->mp, p->file, p->line, "macro expression: expected %s in %s", tokr, sr);
    }
}
static char mep_peek(MEP *p){ mep_skip(p); return p->s[p->i]; }

static char *mep_ident(MEP *p){
    mep_skip(p);
    int j = p->i;
    while(p->s[j] && (isalnum((unsigned char)p->s[j]) || p->s[j] == '_')) j++;
    if(j == p->i){
        char sr[600]; m_pyrepr(p->s, sr, sizeof(sr));
        m_fail(p->mp, p->file, p->line, "macro expression: expected a name in %s", sr);
    }
    char *r = marena_strndup(&p->mp->arena, p->s + p->i, (size_t)(j - p->i));
    p->i = j;
    return r;
}

static MVal mep_number(MEP *p){
    const char *s = p->s;
    int j = p->i, base = 10, start;
    if(s[j] == '0' && (s[j+1] == 'x' || s[j+1] == 'X')){ base = 16; j += 2; }
    else if(s[j] == '0' && (s[j+1] == 'b' || s[j+1] == 'B')){ base = 2; j += 2; }
    else if(s[j] == '0' && (s[j+1] == 'o' || s[j+1] == 'O')){ base = 8; j += 2; }
    start = j;
    long long v = 0;
    int ndig = 0;
    while(s[j]){
        char c = s[j];
        int d;
        if(c == '_'){ j++; continue; }
        if(c >= '0' && c <= '9') d = c - '0';
        else if(c >= 'a' && c <= 'f') d = c - 'a' + 10;
        else if(c >= 'A' && c <= 'F') d = c - 'A' + 10;
        else break;
        if(d >= base) break;
        v = v * base + d;
        ndig++; j++;
    }
    if(ndig == 0 || j == start){
        char sr[600]; m_pyrepr(p->s, sr, sizeof(sr));
        m_fail(p->mp, p->file, p->line, "macro expression: malformed number in %s", sr);
    }
    p->i = j;
    return mv_int(v);
}

static char *mep_string(MEP *p, char q, int *len_out){
    const char *s = p->s;
    int j = p->i + 1;
    char *buf = marena_alloc(&p->mp->arena, strlen(s) + 1);
    int n = 0;
    while(s[j]){
        char c = s[j];
        if(c == '\\' && s[j+1]){
            char e = s[j+1];
            char out;
            switch(e){
                case 'n': out = '\n'; break;
                case 't': out = '\t'; break;
                case 'r': out = '\r'; break;
                case '0': out = '\0'; break;
                default:  out = e;    break;
            }
            buf[n++] = out; j += 2; continue;
        }
        if(c == q){ buf[n] = '\0'; p->i = j + 1; if(len_out) *len_out = n; return buf; }
        buf[n++] = c; j++;
    }
    {
        char sr[600]; m_pyrepr(p->s, sr, sizeof(sr));
        m_fail(p->mp, p->file, p->line, "macro expression: unterminated string literal in %s", sr);
    }
    return NULL;
}

static MVal mep_primary(MEP *p){
    mep_skip(p);
    char c = p->s[p->i];
    if(!c){
        char sr[600]; m_pyrepr(p->s, sr, sizeof(sr));
        m_fail(p->mp, p->file, p->line, "macro expression: unexpected end of expression in %s", sr);
    }

    if(c == '('){
        p->i++;
        MVal v = mep_ternary(p);
        mep_expect(p, ")");
        return v;
    }
    if(c == '"'){
        int n = 0;
        char *t = mep_string(p, '"', &n);
        return mv_str(t);
    }
    if(c == '\''){
        int n = 0;
        char *t = mep_string(p, '\'', &n);
        if(n == 1) return mv_int((unsigned char)t[0]);
        return mv_str(t);
    }
    if(isdigit((unsigned char)c)) return mep_number(p);

    if(c == '_' || isalpha((unsigned char)c)){
        char *name = mep_ident(p);
        if(strcmp(name, "defined") == 0){
            mep_expect(p, "(");
            char *inner = mep_ident(p);
            mep_expect(p, ")");
            return mv_int(m_is_defined(p->mp, inner) ? 1 : 0);
        }
        if(mep_peek(p) == '('){
            p->i++;
            MVal args[MACRO_MAX_ARGS];
            int nargs = 0;
            if(mep_peek(p) == ')') p->i++;
            else {
                for(;;){
                    if(nargs >= MACRO_MAX_ARGS)
                        m_fail(p->mp, p->file, p->line, "macro call '%s': too many arguments", name);
                    args[nargs++] = mep_ternary(p);
                    if(mep_eat(p, ",")) continue;
                    mep_expect(p, ")");
                    break;
                }
            }
            return m_call_value(p->mp, name, args, nargs, p->file, p->line);
        }
        return m_lookup(p->mp, name, p->file, p->line);
    }
    {
        char cbuf[2] = { c, 0 }, cr[16], sr[600];
        m_pyrepr(cbuf, cr, sizeof(cr));
        m_pyrepr(p->s, sr, sizeof(sr));
        m_fail(p->mp, p->file, p->line, "macro expression: unexpected character %s in %s", cr, sr);
    }
    return mv_int(0);
}

static MVal mep_unary(MEP *p){
    mep_skip(p);
    if(p->s[p->i] == '!' && p->s[p->i+1] != '='){ p->i++; return mv_int(mv_truth(mep_unary(p)) ? 0 : 1); }
    if(p->s[p->i] == '~'){ p->i++; return mv_int(~mv_need_int(p->mp, mep_unary(p), p->file, p->line)); }
    if(p->s[p->i] == '-'){ p->i++; return mv_int(-mv_need_int(p->mp, mep_unary(p), p->file, p->line)); }
    if(p->s[p->i] == '+'){ p->i++; return mep_unary(p); }
    return mep_primary(p);
}

static MVal mep_mul(MEP *p){
    MVal v = mep_unary(p);
    for(;;){
        mep_skip(p);
        char c = p->s[p->i];
        if(c == '*'){
            p->i++;
            MVal r = mep_unary(p);
            if(v.is_str && !r.is_str){
                long long n = r.i < 0 ? 0 : r.i;
                size_t l = strlen(v.s);
                if(n * (long long)l > 16*1024*1024){
                    char sr[600]; m_pyrepr(p->s, sr, sizeof(sr));
                    m_fail(p->mp, p->file, p->line, "macro expression: string repetition too large in %s", sr);
                }
                char *b = marena_alloc(&p->mp->arena, (size_t)n * l + 1);
                b[0] = '\0';
                for(long long k = 0; k < n; k++) memcpy(b + (size_t)k*l, v.s, l);
                b[(size_t)n*l] = '\0';
                v = mv_str(b);
            } else if(!v.is_str && r.is_str){
                MVal t = v; v = r; r = t;
                long long n = r.i < 0 ? 0 : r.i;
                size_t l = strlen(v.s);
                char *b = marena_alloc(&p->mp->arena, (size_t)n * l + 1);
                for(long long k = 0; k < n; k++) memcpy(b + (size_t)k*l, v.s, l);
                b[(size_t)n*l] = '\0';
                v = mv_str(b);
            } else {
                v = mv_int(mv_need_int(p->mp, v, p->file, p->line) *
                           mv_need_int(p->mp, r, p->file, p->line));
            }
        } else if(c == '/'){
            p->i++;
            long long r = mv_need_int(p->mp, mep_unary(p), p->file, p->line);
            if(r == 0){
                char sr[600]; m_pyrepr(p->s, sr, sizeof(sr));
                m_fail(p->mp, p->file, p->line, "macro expression: division by zero in %s", sr);
            }
            v = mv_int(m_cdiv(mv_need_int(p->mp, v, p->file, p->line), r));
        } else if(c == '%'){
            p->i++;
            long long r = mv_need_int(p->mp, mep_unary(p), p->file, p->line);
            if(r == 0){
                char sr[600]; m_pyrepr(p->s, sr, sizeof(sr));
                m_fail(p->mp, p->file, p->line, "macro expression: modulo by zero in %s", sr);
            }
            v = mv_int(m_cmod(mv_need_int(p->mp, v, p->file, p->line), r));
        } else return v;
    }
}

static MVal mep_add(MEP *p){
    MVal v = mep_mul(p);
    for(;;){
        mep_skip(p);
        char c = p->s[p->i];
        if(c == '+'){
            p->i++;
            MVal r = mep_mul(p);
            if(v.is_str || r.is_str){
                char *a = mv_to_text(p->mp, v), *b = mv_to_text(p->mp, r);
                size_t la = strlen(a), lb = strlen(b);
                char *t = marena_alloc(&p->mp->arena, la + lb + 1);
                memcpy(t, a, la); memcpy(t + la, b, lb + 1);
                v = mv_str(t);
            } else v = mv_int(v.i + r.i);
        } else if(c == '-'){
            p->i++;
            v = mv_int(mv_need_int(p->mp, v, p->file, p->line) -
                       mv_need_int(p->mp, mep_mul(p), p->file, p->line));
        } else return v;
    }
}

static MVal mep_shift(MEP *p){
    MVal v = mep_add(p);
    for(;;){
        mep_skip(p);
        if(p->s[p->i] == '<' && p->s[p->i+1] == '<'){
            p->i += 2;
            long long n = mv_need_int(p->mp, mep_add(p), p->file, p->line);
            if(n < 0 || n > 63){
                char sr[600]; m_pyrepr(p->s, sr, sizeof(sr));
                m_fail(p->mp, p->file, p->line, "macro expression: shift count out of range in %s", sr);
            }
            v = mv_int(mv_need_int(p->mp, v, p->file, p->line) << n);
        } else if(p->s[p->i] == '>' && p->s[p->i+1] == '>'){
            p->i += 2;
            long long n = mv_need_int(p->mp, mep_add(p), p->file, p->line);
            if(n < 0 || n > 63){
                char sr[600]; m_pyrepr(p->s, sr, sizeof(sr));
                m_fail(p->mp, p->file, p->line, "macro expression: shift count out of range in %s", sr);
            }
            v = mv_int(mv_need_int(p->mp, v, p->file, p->line) >> n);
        } else return v;
    }
}

static int m_order(MEP *p, MVal a, MVal b, int or_equal){
    if(a.is_str != b.is_str){
        char sr[600]; m_pyrepr(p->s, sr, sizeof(sr));
        m_fail(p->mp, p->file, p->line, "macro expression: cannot order a string against an integer in %s", sr);
    }
    if(a.is_str){
        int c = strcmp(a.s ? a.s : "", b.s ? b.s : "");
        return or_equal ? (c <= 0) : (c < 0);
    }
    return or_equal ? (a.i <= b.i) : (a.i < b.i);
}

static MVal mep_rel(MEP *p){
    MVal v = mep_shift(p);
    for(;;){
        mep_skip(p);
        if(p->s[p->i] == '<' && p->s[p->i+1] == '<') return v;
        if(p->s[p->i] == '>' && p->s[p->i+1] == '>') return v;
        if(mep_eat(p, "<="))      v = mv_int(m_order(p, v, mep_shift(p), 1));
        else if(mep_eat(p, ">=")) { MVal r = mep_shift(p); v = mv_int(m_order(p, r, v, 1)); }
        else if(mep_eat(p, "<"))  v = mv_int(m_order(p, v, mep_shift(p), 0));
        else if(mep_eat(p, ">"))  { MVal r = mep_shift(p); v = mv_int(m_order(p, r, v, 0)); }
        else return v;
    }
}

static int m_equal(MVal a, MVal b){
    if(a.is_str != b.is_str) return 0;
    if(a.is_str) return strcmp(a.s ? a.s : "", b.s ? b.s : "") == 0;
    return a.i == b.i;
}

static MVal mep_eq(MEP *p){
    MVal v = mep_rel(p);
    for(;;){
        if(mep_eat(p, "=="))      v = mv_int(m_equal(v, mep_rel(p)) ? 1 : 0);
        else if(mep_eat(p, "!=")) v = mv_int(m_equal(v, mep_rel(p)) ? 0 : 1);
        else return v;
    }
}

static MVal mep_band(MEP *p){
    MVal v = mep_eq(p);
    for(;;){
        mep_skip(p);
        if(p->s[p->i] == '&' && p->s[p->i+1] != '&'){
            p->i++;
            v = mv_int(mv_need_int(p->mp, v, p->file, p->line) &
                       mv_need_int(p->mp, mep_eq(p), p->file, p->line));
        } else return v;
    }
}
static MVal mep_bxor(MEP *p){
    MVal v = mep_band(p);
    for(;;){
        mep_skip(p);
        if(p->s[p->i] == '^'){
            p->i++;
            v = mv_int(mv_need_int(p->mp, v, p->file, p->line) ^
                       mv_need_int(p->mp, mep_band(p), p->file, p->line));
        } else return v;
    }
}
static MVal mep_bor(MEP *p){
    MVal v = mep_bxor(p);
    for(;;){
        mep_skip(p);
        if(p->s[p->i] == '|' && p->s[p->i+1] != '|'){
            p->i++;
            v = mv_int(mv_need_int(p->mp, v, p->file, p->line) |
                       mv_need_int(p->mp, mep_bxor(p), p->file, p->line));
        } else return v;
    }
}
static MVal mep_land(MEP *p){
    MVal v = mep_bor(p);
    while(mep_eat(p, "&&")){
        MVal r = mep_bor(p);
        v = mv_int((mv_truth(v) && mv_truth(r)) ? 1 : 0);
    }
    return v;
}
static MVal mep_lor(MEP *p){
    MVal v = mep_land(p);
    while(mep_eat(p, "||")){
        MVal r = mep_land(p);
        v = mv_int((mv_truth(v) || mv_truth(r)) ? 1 : 0);
    }
    return v;
}
static MVal mep_ternary(MEP *p){
    MVal c = mep_lor(p);
    mep_skip(p);
    if(p->s[p->i] == '?'){
        p->i++;
        MVal a = mep_ternary(p);
        mep_expect(p, ":");
        MVal b = mep_ternary(p);
        return mv_truth(c) ? a : b;
    }
    return c;
}

static MVal m_eval(MacroPP *mp, const char *text, const char *file, int line){
    while(*text == ' ' || *text == '\t') text++;
    if(!*text) m_fail(mp, file, line, "empty macro expression");
    const char *saved_cur_expr = mp->cur_expr;
    mp->cur_expr = text;
    MEP p; p.s = text; p.i = 0; p.mp = mp; p.file = file; p.line = line;
    MVal v = mep_ternary(&p);
    mep_skip(&p);
    if(p.s[p.i]){
        char tailr[600], sr[600];
        m_pyrepr(p.s + p.i, tailr, sizeof(tailr));
        m_pyrepr(p.s, sr, sizeof(sr));
        m_fail(mp, file, line, "macro expression: unexpected trailing text %s in %s", tailr, sr);
    }
    mp->cur_expr = saved_cur_expr;
    return v;
}


static void m_bi_argc(MacroPP *mp, const char *name, int n, int lo, int hi,
                      const char *file, int line){
    if(n < lo || n > hi)
        m_fail(mp, file, line, "%s() takes %d..%d argument(s), got %d", name, lo, hi, n);
}

static int m_builtin(MacroPP *mp, const char *name, MVal *a, int n,
                     const char *file, int line, MVal *out){
    if(strcmp(name, "len") == 0){
        m_bi_argc(mp, "len", n, 1, 1, file, line);
        *out = mv_int((long long)strlen(mv_to_text(mp, a[0])));
        return 1;
    }
    if(strcmp(name, "str") == 0){
        m_bi_argc(mp, "str", n, 1, 1, file, line);
        *out = mv_str(mv_to_text(mp, a[0]));
        return 1;
    }
    if(strcmp(name, "hex") == 0){
        m_bi_argc(mp, "hex", n, 1, 2, file, line);
        long long v = mv_need_int(mp, a[0], file, line);
        long long w = (n > 1) ? mv_need_int(mp, a[1], file, line) : 0;
        if(w < 0 || w > 64) w = 0;
        char buf[80];
        unsigned long long uv = (v < 0) ? (unsigned long long)(-v) : (unsigned long long)v;
        snprintf(buf, sizeof(buf), "%s%0*llx", v < 0 ? "-" : "", (int)w, uv);
        *out = mv_str(marena_strdup(&mp->arena, buf));
        return 1;
    }
    if(strcmp(name, "int") == 0){
        m_bi_argc(mp, "int", n, 1, 2, file, line);
        if(!a[0].is_str){ *out = a[0]; return 1; }
        int base = (n > 1) ? (int)mv_need_int(mp, a[1], file, line) : 0;
        errno = 0;
        char *end = NULL;
        long long v = strtoll(a[0].s ? a[0].s : "", &end, base);
        while(end && (*end == ' ' || *end == '\t')) end++;
        if(!end || end == a[0].s || *end)
            m_fail(mp, file, line, "int(\"%s\") is not a number", a[0].s ? a[0].s : "");
        *out = mv_int(v);
        return 1;
    }
    if(strcmp(name, "upper") == 0 || strcmp(name, "lower") == 0){
        m_bi_argc(mp, name, n, 1, 1, file, line);
        char *t = marena_strdup(&mp->arena, mv_to_text(mp, a[0]));
        for(char *q = t; *q; q++)
            *q = (name[0] == 'u') ? (char)toupper((unsigned char)*q)
                                  : (char)tolower((unsigned char)*q);
        *out = mv_str(t);
        return 1;
    }
    if(strcmp(name, "substr") == 0){
        m_bi_argc(mp, "substr", n, 2, 3, file, line);
        char *t = mv_to_text(mp, a[0]);
        long long l = (long long)strlen(t);
        long long st = mv_need_int(mp, a[1], file, line);
        if(st < 0) st = 0;
        if(st > l) st = l;
        long long cnt = (n > 2) ? mv_need_int(mp, a[2], file, line) : l - st;
        if(cnt < 0) cnt = 0;
        if(st + cnt > l) cnt = l - st;
        *out = mv_str(marena_strndup(&mp->arena, t + st, (size_t)cnt));
        return 1;
    }
    if(strcmp(name, "abs") == 0){
        m_bi_argc(mp, "abs", n, 1, 1, file, line);
        long long v = mv_need_int(mp, a[0], file, line);
        *out = mv_int(v < 0 ? -v : v);
        return 1;
    }
    if(strcmp(name, "min") == 0 || strcmp(name, "max") == 0){
        m_bi_argc(mp, name, n, 1, MACRO_MAX_ARGS, file, line);
        MVal best = a[0];
        MEP dummy; dummy.mp = mp; dummy.file = file; dummy.line = line; dummy.s = ""; dummy.i = 0;
        for(int k = 1; k < n; k++){
            int lt = m_order(&dummy, a[k], best, 0);
            if((name[1] == 'i') ? lt : !lt && !m_equal(a[k], best)) best = a[k];
        }
        *out = best;
        return 1;
    }
    if(strcmp(name, "uid") == 0){
        m_bi_argc(mp, "uid", n, 0, 0, file, line);
        *out = mv_int(++mp->uid);
        return 1;
    }
    return 0;
}


static void m_exec_block(MacroPP *mp, MBlock *b);

static MVal m_invoke(MacroPP *mp, MFunc *f, MVal *args, int nargs,
                     const char *file, int line){
    int nreq = 0;
    for(int i = 0; i < f->nparams; i++) if(!f->defaults[i]) nreq++;
    if(nargs > f->nparams || nargs < nreq)
        m_fail(mp, file, line, "macro '%s' takes %d..%d argument(s), got %d",
               f->name, nreq, f->nparams, nargs);
    if(mp->depth >= MACRO_MAX_DEPTH)
        m_fail(mp, file, line, "macro recursion deeper than %d while expanding '%s'",
               MACRO_MAX_DEPTH, f->name);
    if(mp->nscopes >= MACRO_MAX_SCOPES)
        m_fail(mp, file, line, "macro scope nesting too deep");

    MScope *sc = calloc(1, sizeof(MScope));
    if(!sc){ perror("calloc"); exit(1); }

    MVal bound[MACRO_MAX_ARGS];
    for(int i = 0; i < f->nparams; i++)
        bound[i] = (i < nargs) ? args[i] : m_eval(mp, f->defaults[i], file, line);

    mp->scopes[mp->nscopes++] = sc;
    for(int i = 0; i < f->nparams; i++)
        m_scope_set(sc, f->params[i], bound[i]);
    mp->uid++;
    m_scope_set(sc, marena_strdup(&mp->arena, "__id__"), mv_int(mp->uid));
    m_scope_set(sc, marena_strdup(&mp->arena, "__name__"),
                mv_str(marena_strdup(&mp->arena, f->name)));

    mp->depth++;
    m_exec_block(mp, f->body);
    mp->depth--;

    mp->nscopes--;
    free(sc->names); free(sc->vals); free(sc);

    MVal r = mv_int(0);
    if(mp->ctl == MCTL_RETURN){ r = mp->retval; mp->ctl = MCTL_NONE; }
    return r;
}

static MVal m_call_value(MacroPP *mp, const char *name, MVal *args, int nargs,
                         const char *file, int line){
    MVal out;
    if(m_builtin(mp, name, args, nargs, file, line, &out)) return out;
    MFunc *f = m_func_find(mp, name);
    if(!f || !f->defined)
        m_fail(mp, file, line, "call to undefined macro '%s'", name);
    int mark = mp->out ? mp->out->len : 0;
    MVal v = m_invoke(mp, f, args, nargs, file, line);
    if(mp->out && mp->out->len != mark){
        char *emitted = mp->out->d[mark].text;
        mp->out->len = mark;
        char *e0 = emitted, *e1;
        while(*e0==' '||*e0=='\t'||*e0=='\n'||*e0=='\r'||*e0=='\f'||*e0=='\v') e0++;
        e1 = e0 + strlen(e0);
        while(e1 > e0 && (e1[-1]==' '||e1[-1]=='\t'||e1[-1]=='\n'||e1[-1]=='\r'||e1[-1]=='\f'||e1[-1]=='\v')) e1--;
        char stripped[600]; size_t sl = (size_t)(e1-e0); if(sl>=sizeof(stripped)) sl=sizeof(stripped)-1;
        memcpy(stripped, e0, sl); stripped[sl]='\0';
        char er[600]; m_pyrepr(stripped, er, sizeof(er));
        m_fail(mp, file, line,
               "macro '%s' emits source text (%s) but was called from inside an "
               "expression, where there is nowhere to put it", name, er);
    }
    return v;
}



typedef struct {
    char fill;
    char align;
    char sign;
    int  has_fill;
    int  zcoerce;
    int  alt;
    int  zeropad;
    int  width;
    char group;
    int  has_prec;
    int  prec;
    char type;
} MFmt;

static int m_is_align(char c){
    return c == '<' || c == '>' || c == '=' || c == '^';
}

static int m_fmt_parse(const char *spec, MFmt *f){
    memset(f, 0, sizeof(*f));
    f->fill = ' ';
    const char *p = spec;
    if(p[0] && p[1] && m_is_align(p[1])){
        f->fill = p[0]; f->align = p[1]; f->has_fill = 1; p += 2;
    }
    else if(p[0] && m_is_align(p[0])){ f->align = p[0]; p++; }
    if(*p == '+' || *p == '-' || *p == ' '){ f->sign = *p; p++; }
    if(*p == 'z'){ f->zcoerce = 1; p++; }
    if(*p == '#'){ f->alt = 1; p++; }
    if(*p == '0'){
        f->zeropad = 1;
        if(!f->has_fill) f->fill = '0';
        p++;
    }
    while(isdigit((unsigned char)*p)){
        f->width = f->width * 10 + (*p - '0');
        if(f->width > 1000000) return 0;
        p++;
    }
    if(*p == ',' || *p == '_'){ f->group = *p; p++; }
    if(*p == '.'){
        p++;
        if(!isdigit((unsigned char)*p)) return 0;
        f->has_prec = 1;
        while(isdigit((unsigned char)*p)){
            f->prec = f->prec * 10 + (*p - '0');
            if(f->prec > 1000000) return 0;
            p++;
        }
    }
    if(*p){
        if(!strchr("bcdeEfFgGnosxX%", *p)) return 0;
        f->type = *p;
        p++;
    }
    return *p == '\0';
}

static int m_group_len(int n, int iv){
    return n + (n - 1) / iv;
}

static int m_group_emit(char *out, const char *digits, int n, int iv, char sep){
    int lead = n % iv;
    if(lead == 0) lead = iv;
    int o = 0, i = 0;
    for(int k = 0; k < lead; k++) out[o++] = digits[i++];
    while(i < n){
        out[o++] = sep;
        for(int k = 0; k < iv; k++) out[o++] = digits[i++];
    }
    out[o] = '\0';
    return o;
}

static int m_utf8_len(const char *s){
    int n = 0;
    for(const unsigned char *p = (const unsigned char*)s; *p; p++)
        if((*p & 0xc0) != 0x80) n++;
    return n;
}

static size_t m_utf8_off(const char *s, int n){
    const unsigned char *p = (const unsigned char*)s;
    size_t i = 0;
    int seen = 0;
    while(p[i]){
        if((p[i] & 0xc0) != 0x80){
            if(seen == n) return i;
            seen++;
        }
        i++;
    }
    return i;
}

static char *m_fmt_pad(MacroPP *mp, const char *head, const char *body,
                       MFmt *f, char defalign){
    int hl = (int)strlen(head), bl = (int)strlen(body);
    int total = m_utf8_len(head) + m_utf8_len(body);
    char align = f->align ? f->align : defalign;
    if(total >= f->width){
        char *r = marena_alloc(&mp->arena, (size_t)total + 1);
        memcpy(r, head, (size_t)hl);
        memcpy(r + hl, body, (size_t)bl + 1);
        return r;
    }
    int pad = f->width - total;
    char *r = marena_alloc(&mp->arena, (size_t)(hl + bl + pad) + 1);
    int o = 0;
    if(align == '='){
        memcpy(r, head, (size_t)hl); o = hl;
        for(int k = 0; k < pad; k++) r[o++] = f->fill;
        memcpy(r + o, body, (size_t)bl); o += bl;
    } else if(align == '<'){
        memcpy(r, head, (size_t)hl); o = hl;
        memcpy(r + o, body, (size_t)bl); o += bl;
        for(int k = 0; k < pad; k++) r[o++] = f->fill;
    } else if(align == '^'){
        int left = pad / 2, right = pad - left;
        for(int k = 0; k < left; k++) r[o++] = f->fill;
        memcpy(r + o, head, (size_t)hl); o += hl;
        memcpy(r + o, body, (size_t)bl); o += bl;
        for(int k = 0; k < right; k++) r[o++] = f->fill;
    } else {
        for(int k = 0; k < pad; k++) r[o++] = f->fill;
        memcpy(r + o, head, (size_t)hl); o += hl;
        memcpy(r + o, body, (size_t)bl); o += bl;
    }
    r[o] = '\0';
    return r;
}

static int m_utf8(unsigned long cp, char *out){
    if(cp < 0x80){ out[0] = (char)cp; return 1; }
    if(cp < 0x800){
        out[0] = (char)(0xc0 | (cp >> 6));
        out[1] = (char)(0x80 | (cp & 0x3f));
        return 2;
    }
    if(cp < 0x10000){
        out[0] = (char)(0xe0 | (cp >> 12));
        out[1] = (char)(0x80 | ((cp >> 6) & 0x3f));
        out[2] = (char)(0x80 | (cp & 0x3f));
        return 3;
    }
    out[0] = (char)(0xf0 | (cp >> 18));
    out[1] = (char)(0x80 | ((cp >> 12) & 0x3f));
    out[2] = (char)(0x80 | ((cp >> 6) & 0x3f));
    out[3] = (char)(0x80 | (cp & 0x3f));
    return 4;
}

static char *m_fmt_int(MacroPP *mp, long long iv, MFmt *f, int *err){
    char type = f->type ? f->type : 'd';
    int isfloat = (type=='e'||type=='E'||type=='f'||type=='F'
                   ||type=='g'||type=='G'||type=='%');
    if(type == 's'){ *err = 1; return NULL; }
    if(!isfloat && f->has_prec){ *err = 1; return NULL; }
    if(!isfloat && f->zcoerce){ *err = 1; return NULL; }
    if(type == 'c'){
        if(f->sign || f->alt || f->group || f->has_prec){ *err = 1; return NULL; }
        if(iv < 0 || iv > 0x10FFFF){ *err = 1; return NULL; }
        if(iv == 0) return m_fmt_pad(mp, "", "", f, '>');
        char buf[8];
        int n = m_utf8((unsigned long)iv, buf);
        buf[n] = '\0';
        return m_fmt_pad(mp, "", buf, f, '>');
    }
    if(f->group == ',' && strchr("xXob", type)){ *err = 1; return NULL; }
    if(f->group && type == 'n'){ *err = 1; return NULL; }

    int neg = 0;
    char head[8]; int hn = 0;
    char digits[512];
    int nd = 0;
    const char *prefix = "";

    if(isfloat){
        double d = (double)iv;
        int prec = f->has_prec ? f->prec : 6;
        char conv = type;
        if(type == '%'){ d *= 100.0; conv = 'f'; }
        if(d < 0){ neg = 1; d = -d; }
        char cfmt[16];
        snprintf(cfmt, sizeof(cfmt), "%%%s.%d%c", f->alt ? "#" : "", prec, conv);
        nd = snprintf(digits, sizeof(digits), cfmt, d);
        if(type == '%'){ digits[nd++] = '%'; digits[nd] = '\0'; }
    } else {
        unsigned long long uv;
        if(iv < 0){ neg = 1; uv = (unsigned long long)(-(iv + 1)) + 1ULL; }
        else uv = (unsigned long long)iv;
        switch(type){
            case 'd': case 'n':
                nd = snprintf(digits, sizeof(digits), "%llu", uv); break;
            case 'x':
                nd = snprintf(digits, sizeof(digits), "%llx", uv);
                if(f->alt) prefix = "0x";
                break;
            case 'X':
                nd = snprintf(digits, sizeof(digits), "%llX", uv);
                if(f->alt) prefix = "0X";
                break;
            case 'o':
                nd = snprintf(digits, sizeof(digits), "%llo", uv);
                if(f->alt) prefix = "0o";
                break;
            case 'b': {
                char tmp[80]; int t = 0;
                if(uv == 0) tmp[t++] = '0';
                while(uv){ tmp[t++] = (char)('0' + (uv & 1)); uv >>= 1; }
                for(int k = 0; k < t; k++) digits[k] = tmp[t-1-k];
                digits[t] = '\0'; nd = t;
                if(f->alt) prefix = "0b";
                break;
            }
            default: *err = 1; return NULL;
        }
    }

    if(neg) head[hn++] = '-';
    else if(f->sign == '+') head[hn++] = '+';
    else if(f->sign == ' ') head[hn++] = ' ';
    head[hn] = '\0';

    char headbuf[16];
    snprintf(headbuf, sizeof(headbuf), "%s%s", head, prefix);

    if(!f->group)
        return m_fmt_pad(mp, headbuf, digits, f,
                         (f->zeropad && !f->align) ? '=' : '>');

    int iv_step = strchr("xXob", type) ? 4 : 3;
    int intlen;
    if(isfloat){
        intlen = 0;
        while(intlen < nd && isdigit((unsigned char)digits[intlen])) intlen++;
    } else {
        intlen = nd;
    }
    const char *tail = digits + intlen;

    int want = intlen;
    char eff_align = f->align ? f->align : (f->zeropad ? '=' : '>');
    if(eff_align == '=' && f->fill == '0'){
        int avail = f->width - (int)strlen(headbuf) - (int)strlen(tail);
        while(m_group_len(want, iv_step) < avail) want++;
    }
    if(want > 400){ *err = 1; return NULL; }

    char padded[512];
    int lead = want - intlen;
    for(int k = 0; k < lead; k++) padded[k] = '0';
    memcpy(padded + lead, digits, (size_t)intlen);
    char grouped[1024];
    int gl = m_group_emit(grouped, padded, want, iv_step, f->group);
    snprintf(grouped + gl, sizeof(grouped) - (size_t)gl, "%s", tail);
    return m_fmt_pad(mp, headbuf, grouped, f,
                     (f->zeropad && !f->align) ? '=' : '>');
}

static char *m_fmt_str(MacroPP *mp, const char *s, MFmt *f, int *err){
    if(f->type && f->type != 's'){ *err = 1; return NULL; }
    if(f->sign || f->alt || f->group || f->zcoerce){ *err = 1; return NULL; }
    if(f->align == '='){ *err = 1; return NULL; }
    char *body = (char*)s;
    if(f->has_prec && f->prec < m_utf8_len(s))
        body = marena_strndup(&mp->arena, s, m_utf8_off(s, f->prec));
    return m_fmt_pad(mp, "", body, f, '<');
}

static char *m_format_value(MacroPP *mp, const char *body, const char *file, int line){
    int len = (int)strlen(body);
    int spec_at = -1;
    char quote = 0;
    int par = 0, seen_q = 0;
    for(int k = 0; k < len; k++){
        char c = body[k];
        if(quote){
            if(c == '\\'){ k++; continue; }
            if(c == quote) quote = 0;
            continue;
        }
        if(c == '"' || c == '\'') quote = c;
        else if(c == '(' || c == '[') par++;
        else if(c == ')' || c == ']') par--;
        else if(c == '?' && par == 0) seen_q = 1;
        else if(c == ':' && par == 0 && !seen_q){ spec_at = k; break; }
    }
    char *expr = (spec_at >= 0) ? marena_strndup(&mp->arena, body, (size_t)spec_at)
                                : (char*)body;
    const char *spec = (spec_at >= 0) ? body + spec_at + 1 : NULL;
    MVal v = m_eval(mp, expr, file, line);
    if(!spec) return mv_to_text(mp, v);
    while(*spec == ' ') spec++;
    if(!*spec) return mv_to_text(mp, v);

    MFmt f;
    int err = 0;
    char *out = NULL;
    if(!m_fmt_parse(spec, &f)) err = 1;
    else if(v.is_str) out = m_fmt_str(mp, v.s ? v.s : "", &f, &err);
    else out = m_fmt_int(mp, v.i, &f, &err);
    if(err || !out){
        if(v.is_str)
            m_fail(mp, file, line, "bad format spec ':%s' for value '%s'",
                   spec, v.s ? v.s : "");
        m_fail(mp, file, line, "bad format spec ':%s' for value %lld", spec, v.i);
    }
    return out;
}

static char *m_interpolate(MacroPP *mp, const char *text, const char *file, int line){
    if(!strstr(text, "!{")) return (char*)text;
    size_t cap = strlen(text) + 256, n = 0;
    char *out = malloc(cap);
    if(!out){ perror("malloc"); exit(1); }
    int i = 0, len = (int)strlen(text);
    while(i < len){
        if(text[i] == '\\' && text[i+1] == '!' && text[i+2] == '{'){
            if(n + 3 >= cap){ cap *= 2; out = realloc(out, cap); }
            out[n++] = '!'; out[n++] = '{';
            i += 3; continue;
        }
        if(!(text[i] == '!' && text[i+1] == '{')){
            if(n + 2 >= cap){ cap *= 2; out = realloc(out, cap); if(!out){perror("realloc");exit(1);} }
            out[n++] = text[i++];
            continue;
        }
        int j = i + 2, depth = 1;
        char quote = 0;
        while(j < len){
            char c = text[j];
            if(quote){
                if(c == '\\'){ j += 2; continue; }
                if(c == quote) quote = 0;
            } else if(c == '"' || c == '\'') quote = c;
            else if(c == '{') depth++;
            else if(c == '}'){ if(--depth == 0) break; }
            j++;
        }
        if(j >= len){
            free(out);
            m_fail(mp, file, line, "unterminated '!{' in line");
        }
        char *body = marena_strndup(&mp->arena, text + i + 2, (size_t)(j - i - 2));
        char *val;
        mp->pending_buf = out;
        val = m_format_value(mp, body, file, line);
        mp->pending_buf = NULL;
        size_t vl = strlen(val);
        while(n + vl + 1 >= cap){ cap *= 2; out = realloc(out, cap); if(!out){perror("realloc");exit(1);} }
        memcpy(out + n, val, vl);
        n += vl;
        i = j + 1;
    }
    out[n] = '\0';
    char *r = marena_strndup(&mp->arena, out, n);
    free(out);
    return r;
}


static char *m_strip_comment(MacroPP *mp, const char *text){
    int i = 0; char quote = 0;
    while(text[i]){
        char c = text[i];
        if(quote){
            if(c == '\\'){ i += 2; continue; }
            if(c == quote) quote = 0;
        } else if(c == '"' || c == '\'') quote = c;
        else if(mp->pat_mode){
            if(c == '/' && text[i+1] == '*') break;
        }
        else if(c == ';') break;
        i++;
    }
    while(i > 0 && (text[i-1] == ' ' || text[i-1] == '\t')) i--;
    return marena_strndup(&mp->arena, text, (size_t)i);
}

static const char *m_lstrip(const char *s){
    while(*s == ' ' || *s == '\t') s++;
    return s;
}
static char *m_rstrip(MacroPP *mp, const char *s){
    size_t n = strlen(s);
    while(n > 0 && (s[n-1] == ' ' || s[n-1] == '\t')) n--;
    return marena_strndup(&mp->arena, s, n);
}
static char *m_trim(MacroPP *mp, const char *s){ return m_rstrip(mp, m_lstrip(s)); }

static const char *m_statement_word(const char *text, char *word, size_t wsz){
    const char *t = m_lstrip(text);
    if(t[0] != '!' || t[1] == '!') return NULL;
    size_t j = 1;
    while(t[j] && (isalnum((unsigned char)t[j]) || t[j] == '_')) j++;
    if(j == 1) return NULL;
    size_t n = j - 1;
    if(n >= wsz) n = wsz - 1;
    memcpy(word, t + 1, n); word[n] = '\0';
    return t + j;
}

static int m_is_keyword(const char *w){
    static const char *kw[] = { "if","then","else","elif","while","def","return",
                                "set","local","break","continue","error","warning",
                                "echo","include","undef", NULL };
    for(int i = 0; kw[i]; i++) if(strcasecmp(w, kw[i]) == 0) return 1;
    return 0;
}


typedef struct { MLine *d; int n; } MSrc;

static MBlock *m_parse_block(MacroPP *mp, MSrc *src, int *ip, int depth);

static MNode *m_node(MacroPP *mp, MNKind k, const char *file, int line){
    MNode *n = marena_alloc(&mp->arena, sizeof(MNode));
    memset(n, 0, sizeof(*n));
    n->kind = k; n->file = file; n->line = line;
    return n;
}

static char *m_parse_header(MacroPP *mp, const char *text, const char *kw,
                            const char *file, int line){
    char *t = m_trim(mp, text);
    size_t kl = strlen(kw) + 1;
    if(strlen(t) < kl) m_fail(mp, file, line, "malformed '!%s' header", kw);
    char *body = m_rstrip(mp, t + kl);
    size_t bl = strlen(body);
    if(bl == 0 || body[bl-1] != '{')
        m_fail(mp, file, line, "'!%s' header must end with '{'", kw);
    body[bl-1] = '\0';
    if(strcmp(kw, "if") == 0 || strcmp(kw, "elif") == 0){
        int at = -1; char quote = 0;
        for(int k = 0; body[k]; k++){
            char c = body[k];
            if(quote){ if(c == '\\'){ k++; continue; } if(c == quote) quote = 0; continue; }
            if(c == '"' || c == '\'') quote = c;
            else if(c == '!' && strncasecmp(body + k, "!then", 5) == 0) at = k;
        }
        if(at < 0) m_fail(mp, file, line, "'!%s' needs '!then' before '{'", kw);
        body[at] = '\0';
    }
    return m_trim(mp, body);
}

static MNode *m_parse_if(MacroPP *mp, MSrc *src, int *ip, int depth){
    const char *file = src->d[*ip].file;
    int line = src->d[*ip].line;
    MNode *n = m_node(mp, MN_IF, file, line);
    char *cond = m_parse_header(mp, m_strip_comment(mp, src->d[*ip].text), "if", file, line);

    int cap = 4;
    n->conds = marena_alloc(&mp->arena, (size_t)cap * sizeof(char*));
    n->arms  = marena_alloc(&mp->arena, (size_t)cap * sizeof(MBlock));
    memset(n->arms, 0, (size_t)cap * sizeof(MBlock));

    for(;;){
        (*ip)++;
        MBlock *body = m_parse_block(mp, src, ip, depth + 1);
        if(n->narms >= cap){
            int nc = cap * 2;
            char **nc2 = marena_alloc(&mp->arena, (size_t)nc * sizeof(char*));
            MBlock *na = marena_alloc(&mp->arena, (size_t)nc * sizeof(MBlock));
            memset(na, 0, (size_t)nc * sizeof(MBlock));
            memcpy(nc2, n->conds, (size_t)n->narms * sizeof(char*));
            memcpy(na, n->arms, (size_t)n->narms * sizeof(MBlock));
            n->conds = nc2; n->arms = na; cap = nc;
        }
        n->conds[n->narms] = cond;
        n->arms[n->narms]  = *body;
        n->narms++;

        if(*ip >= src->n)
            m_fail(mp, file, line, "'!if' block is never closed with '}'");
        const char *cfile = src->d[*ip].file;
        int cline = src->d[*ip].line;
        char *close = m_trim(mp, m_strip_comment(mp, src->d[*ip].text));
        const char *tail = m_lstrip(close + 1);
        if(!*tail){ (*ip)++; return n; }

        char w[64];
        const char *rest = m_statement_word(tail, w, sizeof(w));
        if(!rest) m_fail(mp, cfile, cline, "unexpected text after '}': %s", tail);

        if(strcasecmp(w, "elif") == 0){
            cond = m_parse_header(mp, tail, "elif", cfile, cline);
            continue;
        }
        if(strcasecmp(w, "else") == 0){
            const char *r = m_lstrip(rest);
            if(r[0] == '!' && strncasecmp(r, "!if", 3) == 0){
                cond = m_parse_header(mp, r, "if", cfile, cline);
                continue;
            }
            if(r[0] != '{')
                m_fail(mp, cfile, cline, "'!else' must be followed by '{'");
            (*ip)++;
            n->elsebody = m_parse_block(mp, src, ip, depth + 1);
            if(*ip >= src->n)
                m_fail(mp, cfile, cline, "'!else' block is never closed");
            char *c2 = m_trim(mp, m_strip_comment(mp, src->d[*ip].text));
            if(*m_lstrip(c2 + 1))
                m_fail(mp, src->d[*ip].file, src->d[*ip].line,
                       "unexpected text after '}': %s", m_lstrip(c2 + 1));
            (*ip)++;
            return n;
        }
        m_fail(mp, cfile, cline, "unexpected '!%s' after '}'", w);
    }
}

static MNode *m_parse_while(MacroPP *mp, MSrc *src, int *ip, int depth){
    const char *file = src->d[*ip].file;
    int line = src->d[*ip].line;
    MNode *n = m_node(mp, MN_WHILE, file, line);
    n->a = m_parse_header(mp, m_strip_comment(mp, src->d[*ip].text), "while", file, line);
    (*ip)++;
    n->body = m_parse_block(mp, src, ip, depth + 1);
    if(*ip >= src->n)
        m_fail(mp, file, line, "'!while' block is never closed with '}'");
    char *c2 = m_trim(mp, m_strip_comment(mp, src->d[*ip].text));
    if(*m_lstrip(c2 + 1))
        m_fail(mp, src->d[*ip].file, src->d[*ip].line,
               "unexpected text after '}': %s", m_lstrip(c2 + 1));
    (*ip)++;
    return n;
}

static MNode *m_parse_def(MacroPP *mp, MSrc *src, int *ip, int depth){
    const char *file = src->d[*ip].file;
    int line = src->d[*ip].line;
    MNode *n = m_node(mp, MN_DEF, file, line);

    char *t = m_trim(mp, m_strip_comment(mp, src->d[*ip].text));
    if(strlen(t) < 4) m_fail(mp, file, line, "malformed '!def'");
    t = m_rstrip(mp, t + 4);
    size_t tl = strlen(t);
    if(tl == 0 || t[tl-1] != '{')
        m_fail(mp, file, line, "'!def' header must end with '{'");
    t[tl-1] = '\0';
    t = m_trim(mp, t);
    char *op = strchr(t, '(');
    tl = strlen(t);
    if(!op || tl == 0 || t[tl-1] != ')')
        m_fail(mp, file, line, "'!def' needs 'name(p1, p2, ...)'");
    t[tl-1] = '\0';
    char *plist = op + 1;
    *op = '\0';
    char *name = m_trim(mp, t);
    if(!name[0] || !(isalpha((unsigned char)name[0]) || name[0] == '_'))
        m_fail(mp, file, line, "bad macro name '%s'", name);
    for(char *q = name; *q; q++)
        if(!(isalnum((unsigned char)*q) || *q == '_'))
            m_fail(mp, file, line, "bad macro name '%s'", name);
    if(m_is_keyword(name))
        m_fail(mp, file, line, "'%s' is a reserved macro name", name);
    {
        MVal probe; MVal noargs[1];
        (void)probe; (void)noargs;
        static const char *bi[] = {"len","str","hex","int","upper","lower",
                                   "substr","abs","min","max","uid","defined",NULL};
        for(int k = 0; bi[k]; k++)
            if(strcmp(name, bi[k]) == 0)
                m_fail(mp, file, line, "'%s' is a reserved macro name", name);
    }
    n->a = name;

    int cap = 8;
    n->params   = marena_alloc(&mp->arena, (size_t)cap * sizeof(char*));
    n->defaults = marena_alloc(&mp->arena, (size_t)cap * sizeof(char*));
    plist = m_trim(mp, plist);
    if(plist[0]){
        char *p = plist;
        while(1){
            char *comma = strchr(p, ',');
            char *one = comma ? m_trim(mp, marena_strndup(&mp->arena, p, (size_t)(comma - p)))
                              : m_trim(mp, p);
            if(n->nparams >= cap){
                int nc = cap * 2;
                char **np = marena_alloc(&mp->arena, (size_t)nc * sizeof(char*));
                char **nd = marena_alloc(&mp->arena, (size_t)nc * sizeof(char*));
                memcpy(np, n->params,   (size_t)n->nparams * sizeof(char*));
                memcpy(nd, n->defaults, (size_t)n->nparams * sizeof(char*));
                n->params = np; n->defaults = nd; cap = nc;
            }
            char *eq = strchr(one, '=');
            if(eq){
                *eq = '\0';
                n->params[n->nparams]   = m_trim(mp, one);
                n->defaults[n->nparams] = m_trim(mp, eq + 1);
            } else {
                n->params[n->nparams]   = one;
                n->defaults[n->nparams] = NULL;
            }
            char *pn = n->params[n->nparams];
            if(!pn[0] || !(isalpha((unsigned char)pn[0]) || pn[0] == '_'))
                m_fail(mp, file, line, "bad parameter name '%s' in '!def %s'", pn, name);
            n->nparams++;
            if(!comma) break;
            p = comma + 1;
        }
    }
    {
        const char *seen = NULL;
        for(int k = 0; k < n->nparams; k++){
            if(!n->defaults[k] && seen)
                m_fail(mp, file, line,
                       "parameter '%s' without a default follows '%s' which has one",
                       n->params[k], seen);
            if(n->defaults[k]) seen = n->params[k];
        }
    }

    m_declare(mp, name);

    (*ip)++;
    n->body = m_parse_block(mp, src, ip, depth + 1);
    if(*ip >= src->n)
        m_fail(mp, file, line, "'!def %s' block is never closed", name);
    char *c2 = m_trim(mp, m_strip_comment(mp, src->d[*ip].text));
    if(*m_lstrip(c2 + 1))
        m_fail(mp, src->d[*ip].file, src->d[*ip].line,
               "unexpected text after '}': %s", m_lstrip(c2 + 1));
    (*ip)++;
    return n;
}

static MNode *m_parse_simple(MacroPP *mp, const char *w, const char *rest,
                             const char *file, int line){
    if(strcasecmp(w, "set") == 0 || strcasecmp(w, "local") == 0){
        MNode *n = m_node(mp, strcasecmp(w, "set") == 0 ? MN_SET : MN_LOCAL, file, line);
        const char *eq = strchr(rest, '=');
        if(!eq){
            if(n->kind == MN_SET)
                m_fail(mp, file, line, "'!set' needs 'name = expression'");
            n->a = m_trim(mp, rest);
            n->b = NULL;
        } else {
            n->a = m_trim(mp, marena_strndup(&mp->arena, rest, (size_t)(eq - rest)));
            n->b = m_trim(mp, eq + 1);
        }
        if(!n->a[0]) m_fail(mp, file, line, "'!%s' needs a variable name", w);
        return n;
    }
    if(strcasecmp(w, "undef") == 0){
        MNode *n = m_node(mp, MN_UNDEF, file, line);
        n->a = m_trim(mp, rest);
        return n;
    }
    if(strcasecmp(w, "return") == 0){
        MNode *n = m_node(mp, MN_RETURN, file, line);
        char *t = m_trim(mp, rest);
        n->a = t[0] ? t : NULL;
        return n;
    }
    if(strcasecmp(w, "break") == 0)    return m_node(mp, MN_BREAK, file, line);
    if(strcasecmp(w, "continue") == 0) return m_node(mp, MN_CONTINUE, file, line);
    if(strcasecmp(w, "error") == 0 || strcasecmp(w, "warning") == 0 ||
       strcasecmp(w, "echo") == 0 || strcasecmp(w, "include") == 0){
        MNKind k = (strcasecmp(w, "error") == 0)   ? MN_ERROR :
                   (strcasecmp(w, "warning") == 0) ? MN_WARNING :
                   (strcasecmp(w, "echo") == 0)    ? MN_ECHO : MN_INCLUDE;
        MNode *n = m_node(mp, k, file, line);
        n->a = m_trim(mp, rest);
        return n;
    }
    MNode *n = m_node(mp, MN_CALL, file, line);
    n->a = marena_strdup(&mp->arena, w);
    n->b = m_trim(mp, rest);
    return n;
}

static MBlock *m_parse_block(MacroPP *mp, MSrc *src, int *ip, int depth){
    MBlock *b = marena_alloc(&mp->arena, sizeof(MBlock));
    memset(b, 0, sizeof(*b));
    while(*ip < src->n){
        const char *text = src->d[*ip].text;
        const char *file = src->d[*ip].file;
        int line = src->d[*ip].line;

        if(depth > 0 && m_lstrip(text)[0] == '}') return b;

        char w[64];
        const char *rest = m_statement_word(m_strip_comment(mp, text), w, sizeof(w));
        if(!rest){
            MNode *n = m_node(mp, MN_TEXT, file, line);
            n->a = (char*)text;
            mblock_push(mp, b, n);
            (*ip)++;
            continue;
        }
        int is_call_syntax = (m_lstrip(rest)[0] == '(');
        if(!m_is_keyword(w) && !m_declared(mp, w) && !is_call_syntax){
            MNode *n = m_node(mp, MN_TEXT, file, line);
            n->a = (char*)text;
            mblock_push(mp, b, n);
            (*ip)++;
            continue;
        }
        if(strcasecmp(w, "if") == 0){        mblock_push(mp, b, m_parse_if(mp, src, ip, depth)); continue; }
        if(strcasecmp(w, "while") == 0){     mblock_push(mp, b, m_parse_while(mp, src, ip, depth)); continue; }
        if(strcasecmp(w, "def") == 0){       mblock_push(mp, b, m_parse_def(mp, src, ip, depth)); continue; }
        if(strcasecmp(w, "else") == 0 || strcasecmp(w, "elif") == 0 || strcasecmp(w, "then") == 0)
            m_fail(mp, file, line, "'!%s' without a matching '!if'", w);
        mblock_push(mp, b, m_parse_simple(mp, w, rest, file, line));
        (*ip)++;
    }
    if(depth > 0){
        const char *f = src->n ? src->d[src->n-1].file : "?";
        int l = src->n ? src->d[src->n-1].line : 0;
        m_fail(mp, f, l, "unexpected end of file: a macro block opened with '{' is never closed");
    }
    return b;
}


static void m_do_include(MacroPP *mp, const char *name, const char *file, int line);

static void m_parse_args(MacroPP *mp, const char *argtext, MVal *args, int *nargs,
                         const char *file, int line){
    *nargs = 0;
    const char *t = m_lstrip(argtext);
    if(!*t) return;
    if(*t != '(') m_fail(mp, file, line, "macro call needs parentheses");
    MEP p; p.s = t; p.i = 0; p.mp = mp; p.file = file; p.line = line;
    mep_expect(&p, "(");
    if(mep_peek(&p) == ')') p.i++;
    else {
        for(;;){
            if(*nargs >= MACRO_MAX_ARGS)
                m_fail(mp, file, line, "macro call: too many arguments");
            args[(*nargs)++] = mep_ternary(&p);
            if(mep_eat(&p, ",")) continue;
            mep_expect(&p, ")");
            break;
        }
    }
    mep_skip(&p);
    if(p.s[p.i])
        m_fail(mp, file, line, "unexpected text after macro call: \"%s\"", p.s + p.i);
}

static void m_emit(MacroPP *mp, char *text, const char *file, int line){
    if(mp->nemitted >= MACRO_MAX_LINES)
        m_fail(mp, file, line, "macro expansion produced more than %ld lines; "
               "assuming a runaway macro", MACRO_MAX_LINES);
    if(mp->arena.total > MACRO_MAX_ARENA)
        m_fail(mp, file, line, "macro expansion used more than %zu bytes; "
               "assuming a runaway macro", (size_t)MACRO_MAX_ARENA);
    mp->nemitted++;
    mlinevec_push(mp, mp->out, text, file, line);
}

static void m_exec_node(MacroPP *mp, MNode *n){
    switch(n->kind){
    case MN_TEXT:
        m_emit(mp, m_interpolate(mp, n->a, n->file, n->line), n->file, n->line);
        return;

    case MN_IF:
        for(int k = 0; k < n->narms; k++){
            if(mv_truth(m_eval(mp, n->conds[k], n->file, n->line))){
                m_exec_block(mp, &n->arms[k]);
                return;
            }
        }
        if(n->elsebody) m_exec_block(mp, n->elsebody);
        return;

    case MN_WHILE: {
        long count = 0;
        while(mv_truth(m_eval(mp, n->a, n->file, n->line))){
            if(++count > MACRO_MAX_ITER)
                m_fail(mp, n->file, n->line,
                       "'!while' ran more than %ld iterations; assuming it never terminates",
                       MACRO_MAX_ITER);
            m_exec_block(mp, n->body);
            if(mp->ctl == MCTL_CONTINUE){ mp->ctl = MCTL_NONE; continue; }
            if(mp->ctl == MCTL_BREAK){ mp->ctl = MCTL_NONE; break; }
            if(mp->ctl == MCTL_RETURN) return;
        }
        return;
    }

    case MN_DEF: {
        MFunc *prev = m_func_find(mp, n->a);
        if(prev && prev->defined && !(prev->file == n->file && prev->line == n->line))
            m_warn(mp, n->file, n->line, "macro '%s' redefined (previous definition at %s:%d)",
                   n->a, prev->file, prev->line);
        MFunc *f = prev ? prev : m_func_add(mp, n->a);
        f->params   = n->params;
        f->defaults = n->defaults;
        f->nparams  = n->nparams;
        f->body     = n->body;
        f->file     = n->file;
        f->line     = n->line;
        f->defined  = 1;
        return;
    }

    case MN_SET:
        m_assign(mp, n->a, m_eval(mp, n->b, n->file, n->line));
        return;

    case MN_LOCAL:
        m_scope_set(m_scope(mp), marena_strdup(&mp->arena, n->a),
                    n->b ? m_eval(mp, n->b, n->file, n->line) : mv_int(0));
        return;

    case MN_UNDEF: {
        for(int i = 0; i < mp->nfuncs; i++)
            if(strcmp(mp->funcs[i].name, n->a) == 0){ mp->funcs[i].defined = 0; break; }
        for(int i = mp->nscopes - 1; i >= 0; i--)
            if(m_scope_find(mp->scopes[i], n->a)){ m_scope_del(mp->scopes[i], n->a); break; }
        return;
    }

    case MN_CALL: {
        MFunc *f = m_func_find(mp, n->a);
        if(!f || !f->defined)
            m_fail(mp, n->file, n->line, "call to undefined macro '%s'", n->a);
        MVal args[MACRO_MAX_ARGS];
        int nargs = 0;
        m_parse_args(mp, n->b, args, &nargs, n->file, n->line);
        m_invoke(mp, f, args, nargs, n->file, n->line);
        return;
    }

    case MN_RETURN:
        mp->retval = n->a ? m_eval(mp, n->a, n->file, n->line) : mv_int(0);
        mp->ctl = MCTL_RETURN;
        return;

    case MN_BREAK:    mp->ctl = MCTL_BREAK;    return;
    case MN_CONTINUE: mp->ctl = MCTL_CONTINUE; return;

    case MN_ERROR: {
        MVal v = m_eval(mp, n->a, n->file, n->line);
        m_fail(mp, n->file, n->line, "%s", mv_to_text(mp, v));
        return;
    }
    case MN_WARNING: {
        MVal v = m_eval(mp, n->a, n->file, n->line);
        m_warn(mp, n->file, n->line, "%s", mv_to_text(mp, v));
        return;
    }
    case MN_ECHO: {
        MVal v = m_eval(mp, n->a, n->file, n->line);
        if(!mp->asmb || mp->asmb->st.pas != 1)
            fprintf(stderr, "%s\n", mv_to_text(mp, v));
        return;
    }
    case MN_INCLUDE: {
        MVal v = m_eval(mp, n->a, n->file, n->line);
        if(!v.is_str) m_fail(mp, n->file, n->line, "'!include' needs a file name string");
        m_do_include(mp, v.s, n->file, n->line);
        return;
    }
    }
}

static void m_exec_block(MacroPP *mp, MBlock *b){
    for(int i = 0; i < b->len; i++){
        m_exec_node(mp, b->d[i]);
        if(mp->ctl != MCTL_NONE) return;
    }
}


static void m_read_lines(MacroPP *mp, FILE *f, const char *display, MSrc *out){
    int cap = 256, n = 0;
    MLine *d = marena_alloc(&mp->arena, (size_t)cap * sizeof(MLine));
    char *line = NULL; size_t lcap = 0;
    ssize_t r;
    char *name = marena_strdup(&mp->arena, display);
    while((r = getline(&line, &lcap, f)) != -1){
        while(r > 0 && (line[r-1] == '\n' || line[r-1] == '\r')) line[--r] = '\0';
        if(n >= cap){
            int nc = cap * 2;
            MLine *nd = marena_alloc(&mp->arena, (size_t)nc * sizeof(MLine));
            memcpy(nd, d, (size_t)n * sizeof(MLine));
            d = nd; cap = nc;
        }
        d[n].text = marena_strndup(&mp->arena, line, (size_t)r);
        d[n].file = name;
        d[n].line = n + 1;
        n++;
    }
    free(line);
    out->d = d; out->n = n;
}

static void m_do_include(MacroPP *mp, const char *name, const char *file, int line){
    char path[1024];
    if(name[0] == '/'){
        snprintf(path, sizeof(path), "%s", name);
    } else {
        char dir[1024];
        axx_dir_of(file && file[0] ? file : ".", dir, sizeof(dir));
        if(dir[0] == '.' && dir[1] == '\0')
            snprintf(path, sizeof(path), "%s", name);
        else
            axx_resolve_path(dir, name, path, sizeof(path));
    }
    char real[PATH_MAX];
    if(!realpath(path, real)){ snprintf(real, sizeof(real), "%s", path); }
    for(int i = 0; i < mp->ninc; i++)
        if(strcmp(mp->inc_stack[i], real) == 0)
            m_fail(mp, file, line, "circular '!include' of \"%s\"", name);
    if(mp->ninc >= MACRO_MAX_INCLUDE_DEPTH)
        m_fail(mp, file, line, "'!include' nested deeper than %d", MACRO_MAX_INCLUDE_DEPTH);

    FILE *f = fopen(path, "rt");
    if(!f) m_fail(mp, file, line, "cannot '!include' \"%s\": %s", name, strerror(errno));

    MSrc src;
    m_read_lines(mp, f, path, &src);
    fclose(f);

    mp->inc_stack[mp->ninc++] = marena_strdup(&mp->arena, real);
    int ip = 0;
    MBlock *b = m_parse_block(mp, &src, &ip, 0);
    m_exec_block(mp, b);
    mp->ninc--;
}

static int m_contains_macros(MSrc *src){
    for(int i = 0; i < src->n; i++){
        if(strchr(src->d[i].text, '!')) return 1;
        if(m_lstrip(src->d[i].text)[0] == '}') return 1;
    }
    return 0;
}

static int m_has_interpolation(const char *t){
    for(const char *p = strstr(t, "!{"); p; p = strstr(p + 2, "!{"))
        if(p == t || p[-1] != '\\') return 1;
    return 0;
}

static int m_has_macro_constructs(MacroPP *mp, MSrc *src){
    for(int i = 0; i < src->n; i++){
        const char *t = src->d[i].text;
        if(m_lstrip(t)[0] == '}') return 1;
        if(m_has_interpolation(t)) return 1;
        char w[64];
        const char *rest = m_statement_word(t, w, sizeof(w));
        if(!rest) continue;
        if(m_is_keyword(w) || m_declared(mp, w) || m_lstrip(rest)[0] == '(')
            return 1;
    }
    return 0;
}

static MLineVec macro_expand(MacroPP *mp, FILE *f, const char *display){
    MLineVec result;
    memset(&result, 0, sizeof(result));

    MSrc src;
    m_read_lines(mp, f, display, &src);

    if(!mp->enabled
       || !(mp->pat_mode ? m_has_macro_constructs(mp, &src)
                         : m_contains_macros(&src))){
        for(int i = 0; i < src.n; i++)
            mlinevec_push(mp, &result, src.d[i].text, src.d[i].file, src.d[i].line);
        return result;
    }
    if(mp->had_error) return result;

    MLineVec *saved_out = mp->out;
    int saved_depth = mp->depth, saved_scopes = mp->nscopes;
    jmp_buf saved_jb;
    int saved_active = mp->jb_active;
    if(saved_active) memcpy(saved_jb, mp->jb, sizeof(jmp_buf));

    mp->out = &result;
    mp->jb_active = 1;
    if(setjmp(mp->jb) == 0){
        int ip = 0;
        MBlock *b = m_parse_block(mp, &src, &ip, 0);
        m_exec_block(mp, b);
        if(mp->ctl == MCTL_RETURN)
            m_fail(mp, display, -1, "'!return' outside a macro definition");
        if(mp->ctl == MCTL_BREAK || mp->ctl == MCTL_CONTINUE)
            m_fail(mp, display, -1, "'!break'/'!continue' outside a '!while' loop");
    } else {
        memset(&result, 0, sizeof(result));
        while(mp->nscopes > saved_scopes){
            MScope *sc = mp->scopes[--mp->nscopes];
            free(sc->names); free(sc->vals); free(sc);
        }
        mp->depth = saved_depth;
        mp->ctl = MCTL_NONE;
    }

    mp->jb_active = saved_active;
    if(saved_active) memcpy(mp->jb, saved_jb, sizeof(jmp_buf));
    mp->out = saved_out;
    return result;
}

static MacroPP g_macro;

static MacroPP g_pat_macro;

static void macro_init_pattern(Assembler *asmb){
    macro_init(&g_pat_macro, asmb);
    g_pat_macro.pat_mode = 1;
}

static void macro_reset_pass_pattern(void){
    macro_reset_pass(&g_pat_macro);
}

static char **pat_macro_expand(FILE *f, const char *display, int *nlines){
    MLineVec v = macro_expand(&g_pat_macro, f, display);
    char **out = malloc(sizeof(char*) * (size_t)(v.len + 1));
    if(!out){ perror("malloc"); exit(1); }
    for(int i = 0; i < v.len; i++){
        out[i] = strdup(v.d[i].text ? v.d[i].text : "");
        if(!out[i]){ perror("strdup"); exit(1); }
    }
    out[v.len] = NULL;
    *nlines = v.len;
    return out;
}

static void pat_macro_expand_free(char **v, int n){
    if(!v) return;
    for(int i = 0; i < n; i++) free(v[i]);
    free(v);
}

static void fileassemble(Assembler *asmb, const char *fn){
    AsmState *st=&asmb->st;

    if(st->fnstack.len == 0) macro_reset_pass(&g_macro);

    {
        int is_stdin_fn = (strcmp(fn,"stdin")==0 || strcmp(fn,"(stdin)")==0);
        for(int si=0; si<st->fnstack.len; si++){
            const char *already = st->fnstack.data[si];
            if(!already || !already[0]) continue;
            int is_stdin_already = (strcmp(already,"stdin")==0 || strcmp(already,"(stdin)")==0);
            if(is_stdin_fn && is_stdin_already){
                axx_diagf(1, 0, " error - circular .INCLUDE detected: '%s' is already being assembled.\n", fn);
                return;
            }
            if(!is_stdin_fn && !is_stdin_already){
                char abs_fn[4096]={0}, abs_al[4096]={0};
                if(realpath(fn,   abs_fn) && realpath(already, abs_al)
                   && strcmp(abs_fn, abs_al)==0){
                    axx_diagf(1, 0, " error - circular .INCLUDE detected: '%s' is already being assembled.\n", fn);
                    return;
                }
            }
        }
    }

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
        if(st->stdin_tmp_path[0] == '\0'){
            char tmpl[] = "/tmp/axx_XXXXXX";
            int fd = mkstemp(tmpl);
            if(fd >= 0){
                close(fd);
                strncpy(st->stdin_tmp_path, tmpl, sizeof(st->stdin_tmp_path)-1);
            } else {
                strncpy(st->stdin_tmp_path, "axx.tmp", sizeof(st->stdin_tmp_path)-1);
            }
            stdin_buf=file_input_from_stdin();
            FILE *tmpf=fopen(st->stdin_tmp_path,"wt");
            if(tmpf){ fwrite(stdin_buf,1,strlen(stdin_buf),tmpf); fclose(tmpf); }
        }
        fn=st->stdin_tmp_path;
    }

    f=axx_open_input(fn, "source file");
    if(!f) goto done;
    {
        MLineVec _mexp = macro_expand(&g_macro, f, st->current_file);
        fclose(f); f=NULL;
        for(int _mi=0; _mi<_mexp.len; _mi++){
            strncpy(st->current_file, _mexp.d[_mi].file, sizeof(st->current_file)-1);
            st->current_file[sizeof(st->current_file)-1]='\0';
            st->ln = _mexp.d[_mi].line;
            lineassemble0(asmb, _mexp.d[_mi].text);
        }
    }
    if(f) fclose(f);

done:
    free(stdin_buf);
    strncpy(st->current_file, _caller_file, sizeof(st->current_file)-1);
    st->current_file[sizeof(st->current_file)-1] = '\0';
    sv_pop(&st->fnstack);
    st->ln = is_pop(&st->lnstack);
}

static void setpatsymbols(Assembler *asmb){
    SymMap fresh; smap_init(&fresh);

    for(int pi=0; pi<asmb->st.pat.len; pi++){
        PatEntry *e=&asmb->st.pat.data[pi];
        if(!e) continue;

        if(strcmp(e->f[0],".setsym")==0){
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
        if(strcmp(e->f[0],".bits")==0){
            dir_bits(asmb, e);
            continue;
        }
    }

    smap_free(&asmb->st.patsymbols); smap_init(&asmb->st.patsymbols);
    smap_clear(&asmb->st.symbols);
    for(int i=0; i<fresh.nb; i++)
        for(SymEntry *e=fresh.buckets[i]; e; e=e->next){
            smap_set(&asmb->st.patsymbols, e->key, e->val);
            smap_set(&asmb->st.symbols,    e->key, e->val);
        }
    smap_free(&fresh);
}

static int imp_label(Assembler *asmb, const char *l){

    char buf[4096];
    strncpy(buf, l, sizeof(buf)-1); buf[sizeof(buf)-1] = '\0';
    int blen = (int)strlen(buf);
    while(blen > 0 && (buf[blen-1]=='\n'||buf[blen-1]=='\r')) buf[--blen] = '\0';
    if(!buf[0]) return 0;

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
        int reloc_type = -1;
        char *sep = strstr(labelbuf, "::");
        if(sep){
            *sep = '\0';
            const char *rt_str = sep + 2;
            reloc_type = elf_machine_named(elf_machine_find(asmb->st.elf_machine), rt_str);
            if(reloc_type < 0)
                axx_diagf(0, 0, " warning - unknown reloc type '%s' for imported label '%s'\n",
                           rt_str, label);
        }
        if(!label[0]) return 0;
        char *endp;
        uint64_t v = strtoull(fields[1], &endp, 16);
        if(endp == fields[1]) return 0;

        const char *section = ".text";
        for(int i = 0; i < asmb->imp_sections.len; i++){
            SecRange *se = &asmb->imp_sections.data[i];
            uint64_t s0 = u256_to_u64(se->start);
            uint64_t sz = u256_to_u64(se->len);
            if(sz > 0 && v >= s0 && v < s0 + sz){ section = se->name; break; }
            if(sz == 0 && v == s0)               { section = se->name; break; }
        }
        {
            int _bpw = (asmb->st.bts+7)/8; if(_bpw<1) _bpw=1;
            v /= (uint64_t)_bpw;
        }
        lmap_set_imported(&asmb->st.labels, label, u256_from_u64(v), section, reloc_type);
        return 1;
    }

    return 0;
}

static void print_usage(const char *prog){
    printf("usage: %s patternfile [sourcefile] [--osabi OSNAME] [-b outfile] [-e export_tsv] [-E export_elf_tsv] [-i import_tsv] [-o elf_obj] [-f {32,64}] [-m machine] [-v] [-d] [-g] [--no-macro] [-P [file]] [-p [file]]\n",prog);
    printf("  --no-macro   disable the macro preprocessor layer (!if/!while/!def/!return/!set and !{...})\n");
    printf("  -P [file]    macro-expand the source and write it out (stdout if file is omitted), then stop\n");
    printf("  -p [file]    macro-expand the pattern file and write it out (stdout if file is omitted), then stop\n");
    printf("axx general assembler programmed and designed by Taisuke Maekawa\n");
}

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
                          e->is_equ, e->is_imported, e->reloc_type_override, e->is_undef);
}

typedef struct {
    char    s[16];
    int     nu;
} OSABIENT;

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
    macro_init(&g_macro, asmb);
    macro_init_pattern(asmb);

    const char *patternfile=NULL, *sourcefile=NULL;
    char osabistr[16]="FreeBSD";
    const char *macro_expand_dest=NULL;
    const char *pat_macro_expand_dest=NULL;

    for(int i=1;i<argc;i++){
        if(strcmp(argv[i],"--osabi")==0&&i+1<argc){ strncpy(osabistr,argv[++i],sizeof(osabistr)-1); }
        else if(strcmp(argv[i],"-b")==0&&i+1<argc){ strncpy(st->outfile,argv[++i],sizeof(st->outfile)-1); }
        else if(strcmp(argv[i],"-e")==0&&i+1<argc){ strncpy(st->expfile,argv[++i],sizeof(st->expfile)-1); }
        else if(strcmp(argv[i],"-E")==0&&i+1<argc){ strncpy(st->expfile_elf,argv[++i],sizeof(st->expfile_elf)-1); }
        else if(strcmp(argv[i],"-i")==0&&i+1<argc){ strncpy(st->impfile,argv[++i],sizeof(st->impfile)-1); }
        else if(strcmp(argv[i],"-o")==0&&i+1<argc){ strncpy(st->elf_objfile,argv[++i],sizeof(st->elf_objfile)-1); }
        else if(strcmp(argv[i],"-f")==0&&i+1<argc){
            const char *_fs = argv[++i];
            if(strcmp(_fs,"64")==0){ st->elf_class = 2; }
            else if(strcmp(_fs,"32")==0){ st->elf_class = 1; }
            else {
                axx_diagf(0, 0, " error - -f: invalid choice: %s (choose from 32, 64)\n", _fs);
                return 1;
            }
        }
        else if(strcmp(argv[i],"-m")==0&&i+1<argc){
            int _mval = atoi(argv[++i]);
            if(!elf_machine_find(_mval)){
                char _known[512]; int _kn=0;
                for(int _mi=0; _mi<ELF_MACHINES_N && _kn < (int)sizeof(_known)-40; _mi++){
                    _kn += snprintf(_known+_kn, sizeof(_known)-(size_t)_kn, "%s%d (%s)",
                                     _mi?", ":"", ELF_MACHINES[_mi].machine, ELF_MACHINES[_mi].name);
                }
                axx_diagf(0, 0, " error - -m/--machine value %d is not a supported ELF "
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
        else if(strcmp(argv[i],"--no-macro")==0){ g_macro.enabled=0; g_pat_macro.enabled=0; }
        else if(strncmp(argv[i],"--macro-expand-pattern=",23)==0){
            pat_macro_expand_dest=argv[i]+23;
            if(!*pat_macro_expand_dest) pat_macro_expand_dest="-";
        }
        else if(strcmp(argv[i],"-p")==0||strcmp(argv[i],"--macro-expand-pattern")==0){
            if(i+1<argc && argv[i+1][0]!='-' && patternfile)
                pat_macro_expand_dest=argv[++i];
            else
                pat_macro_expand_dest="-";
        }
        else if(strncmp(argv[i],"--macro-expand=",15)==0){
            macro_expand_dest=argv[i]+15;
            if(!*macro_expand_dest) macro_expand_dest="-";
        }
        else if(strcmp(argv[i],"-P")==0||strcmp(argv[i],"--macro-expand")==0){
            if(i+1<argc && argv[i+1][0]!='-' && patternfile && sourcefile)
                macro_expand_dest=argv[++i];
            else
                macro_expand_dest="-";
        }
        else if(argv[i][0]!='-'){
            if(!patternfile) patternfile=argv[i];
            else if(!sourcefile) sourcefile=argv[i];
            else{
                fprintf(stderr,"error: unexpected extra argument '%s'.\n",argv[i]);
                print_usage(argv[0]);
                return 1;
            }
        }
        else{
            fprintf(stderr,"error: unknown option '%s'.\n",argv[i]);
            print_usage(argv[0]);
            return 1;
        }
    }

    int osa = find_osabi(osabistr);
    if (osa==-1) {
        fprintf(stderr, "warning: unknown --osabi value '%s'; "
                "valid choices are Linux/linux/FreeBSD/freebsd. Using 'FreeBSD'.\n",
                osabistr);
        osa = find_osabi("FreeBSD");
    }
    st->osabi = osa;

    if(!patternfile){ print_usage(argv[0]); return 1; }

    readpat(asmb,patternfile);
    setpatsymbols(asmb);

    if(st->impfile[0]){
        FILE *lf=axx_open_input(st->impfile, "import file");
        if(!lf){ exit_code=1; goto cleanup; }
        { char *l=NULL; size_t lc=0; while(getline(&l,&lc,lf)!=-1) imp_label(asmb,l); free(l); fclose(lf); }
    }

    if(st->outfile[0]) remove(st->outfile);

    if(pat_macro_expand_dest){
        if(!patternfile){
            axx_diagf(0, 0, " error - -p/--macro-expand-pattern needs a pattern file.\n");
            exit_code=1; goto cleanup;
        }
        FILE *pf=fopen(patternfile,"rt");
        if(!pf){
            { char eb[1200]; axx_oserr_str(patternfile, errno, eb, sizeof(eb));
              axx_diagf(0, 0, " error - cannot open pattern file '%s': %s\n",
                        patternfile, eb); }
            exit_code=1; goto cleanup;
        }
        macro_reset_pass_pattern();
        int _pn=0;
        char **_pv=pat_macro_expand(pf, patternfile, &_pn);
        if(g_pat_macro.had_error || st->had_error){
            pat_macro_expand_free(_pv,_pn); exit_code=1; goto cleanup;
        }
        FILE *of = (strcmp(pat_macro_expand_dest,"-")==0) ? stdout
                                                          : fopen(pat_macro_expand_dest,"wt");
        if(!of){
            axx_diagf(0, 0, " error - cannot write '%s': %s\n",
                       pat_macro_expand_dest, strerror(errno));
            pat_macro_expand_free(_pv,_pn); exit_code=1; goto cleanup;
        }
        for(int _pi=0;_pi<_pn;_pi++) fprintf(of,"%s\n",_pv[_pi]);
        if(of!=stdout) fclose(of);
        pat_macro_expand_free(_pv,_pn);
        goto cleanup;
    }

    if(macro_expand_dest){
        if(!sourcefile){
            axx_diagf(0, 0, " error - -P/--macro-expand needs a source file.\n");
            exit_code=1; goto cleanup;
        }
        FILE *mf=fopen(sourcefile,"rt");
        if(!mf){
            { char eb[1200]; axx_oserr_str(sourcefile, errno, eb, sizeof(eb));
              axx_diagf(0, 0, " error - cannot open source file '%s': %s\n",
                        sourcefile, eb); }
            exit_code=1; goto cleanup;
        }
        macro_reset_pass(&g_macro);
        MLineVec mv=macro_expand(&g_macro, mf, sourcefile);
        fclose(mf);
        if(g_macro.had_error || st->had_error){ exit_code=1; goto cleanup; }
        FILE *of = (strcmp(macro_expand_dest,"-")==0) ? stdout
                                                      : fopen(macro_expand_dest,"wt");
        if(!of){
            axx_diagf(0, 0, " error - cannot write '%s': %s\n",
                       macro_expand_dest, strerror(errno));
            exit_code=1; goto cleanup;
        }
        for(int _mi=0;_mi<mv.len;_mi++) fprintf(of,"%s\n",mv.d[_mi].text);
        if(of!=stdout) fclose(of);
        goto cleanup;
    }

    if(!sourcefile){
        st->pc=u256_zero(); st->pas=0; st->ln=1;
        strncpy(st->current_file,"(stdin)",sizeof(st->current_file)-1);
        char *line=NULL; size_t lcap=0;
        while(1){
            printf("%016llx: >> ",(unsigned long long)u256_to_u64(st->pc));
            fflush(stdout);
            if(getline(&line,&lcap,stdin)==-1) break;
            int ll=(int)strlen(line);
            while(ll>0&&(line[ll-1]=='\n'||line[ll-1]=='\r')) line[--ll]=0;
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
#define MAX_RELAX 16
        LabelMap imported_labels;
        lmap_init(&imported_labels);
        for(int bi=0; bi<st->labels.nbuckets; bi++)
            for(LabelEntry *e=st->labels.buckets[bi]; e; e=e->next)
                lmap_set_full(&imported_labels, e->key, e->value, e->section,
                              e->is_equ, e->is_imported, e->reloc_type_override, e->is_undef);

        PatVar    initial_vars[26];
        memcpy(initial_vars, st->vars, sizeof(initial_vars));

        LabelMap prev_labels;
        lmap_init(&prev_labels);
        int converged = 0;

        LabelMap history[MAX_RELAX];
        int history_count = 0;

        st->relax_prev = &prev_labels;

        for(int relax=0; relax<MAX_RELAX; relax++){
            st->relax_optimistic = (relax == 0);
            st->pc=u256_zero(); st->pas=1; st->ln=1;
            lmap_free(&st->labels); lmap_init(&st->labels);
            for(int bi=0; bi<imported_labels.nbuckets; bi++)
                for(LabelEntry *e=imported_labels.buckets[bi]; e; e=e->next)
                    lmap_set_full(&st->labels, e->key, e->value, e->section,
                                  e->is_equ, e->is_imported, e->reloc_type_override, e->is_undef);
            secmap_clear(&st->sections);
            secrangevec_clear(&st->section_ranges);
            strcpy(st->current_section, ".text");
            lmap_free(&st->export_labels); lmap_init(&st->export_labels);
            sv_free(&st->export_order);
            smap_clear(&st->symbols);
            for(int pi=0; pi<st->patsymbols.nb; pi++)
                for(SymEntry *se2=st->patsymbols.buckets[pi]; se2; se2=se2->next)
                    smap_set(&st->symbols, se2->key, se2->val);
            memcpy(st->vars, initial_vars, sizeof(st->vars));
            fileassemble(asmb,sourcefile);

            secmap_finalize_current(st);

            int has_undef = 0;
            for(int bi=0; bi<st->labels.nbuckets && !has_undef; bi++)
                for(LabelEntry *e=st->labels.buckets[bi]; e; e=e->next){
                    if(e->is_equ) continue;
                    if(u256_is_undef_derived(e->value)){ has_undef=1; break; }
                }

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
                        axx_diagf(0, 1, " error - Pass1 relaxation is oscillating with period %d "
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

            lmap_free(&prev_labels); lmap_init(&prev_labels);
            for(int bi=0; bi<st->labels.nbuckets; bi++)
                for(LabelEntry *e=st->labels.buckets[bi]; e; e=e->next)
                    lmap_set_full(&prev_labels, e->key, e->value, e->section,
                                  e->is_equ, e->is_imported, e->reloc_type_override, e->is_undef);

            if(converged){
                if(st->debug)
                    fprintf(stderr,"Pass1 relaxation converged after %d iteration(s)\n",
                            relax+1);
                break;
            }
        }
        for(int hi=0; hi<history_count; hi++) lmap_free(&history[hi]);
        LabelMap pass1_final;
        lmap_init(&pass1_final);
        for(int bi=0; bi<st->labels.nbuckets; bi++)
            for(LabelEntry *e=st->labels.buckets[bi]; e; e=e->next)
                if(!e->is_equ)
                    lmap_set_full(&pass1_final, e->key, e->value, e->section,
                                  e->is_equ, e->is_imported, e->reloc_type_override, e->is_undef);

        lmap_free(&prev_labels);
        lmap_free(&imported_labels);
        st->relax_prev = NULL;
        st->relax_optimistic = 0;

        if(!converged){
            axx_diagf(0, 1, " error - Pass1 relaxation did not converge after %d iterations; "
                       "addresses would be incorrect for variable-length instructions "
                       "with forward references.\n", MAX_RELAX);
            fprintf(stderr,"         Aborting: no output file written.\n");
            lmap_free(&pass1_final);
            exit_code = 1;
            goto cleanup;
        }
#undef MAX_RELAX

        st->pc=u256_zero(); st->pas=2; st->ln=1;
        for(int ri=0;ri<st->reloc_count;ri++){
            free(st->relocations[ri].section);
            free(st->relocations[ri].sym);
        }
        st->reloc_count=0;
        for(int _li=0;_li<st->line_map_len;_li++){
            free(st->line_map[_li].section);
            free(st->line_map[_li].file);
        }
        st->line_map_len=0;
        secmap_clear(&st->sections);
        secrangevec_clear(&st->section_ranges);
        strcpy(st->current_section, ".text");
        fileassemble(asmb,sourcefile);

        secmap_finalize_current(st);

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
                axx_diagf(0, 0, " error - address mismatch between pass1 and pass2 "
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
                fprintf(stderr,"         Aborting: no output file written.\n");
                lmap_free(&pass1_final);
                exit_code = 1;
                goto cleanup;
            }
        }
        lmap_free(&pass1_final);

        if(st->had_error){
            axx_diagf(0, 0, " error - one or more errors were reported during assembly; "
                       "output would be incomplete or wrong.\n");
            fprintf(stderr,"         Aborting: no output file written.\n");
            exit_code = 1;
            goto cleanup;
        }
    }

    binary_flush(st);

    if(st->had_error){ exit_code = 1; goto cleanup; }

    if(st->elf_objfile[0]){
        write_elf_obj(st, st->elf_objfile, st->elf_machine);
        if(st->had_error){
            axx_diagf(0, 0, " error - one or more errors were reported during assembly; "
                       "output would be incomplete or wrong.\n");
            fprintf(stderr,"         Aborting: no output file written.\n");
            exit_code = 1;
            goto cleanup;
        }
    }

    if(st->expfile_elf[0] && st->expfile[0])
        fprintf(stderr,"warning: both -e '%s' and -E '%s' specified; "
                "exporting plain format to -e and ELF format to -E separately.\n",
                st->expfile, st->expfile_elf);

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
 \
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
            for(int i=0;i<st->export_order.len;i++){ \
                LabelEntry*e=lmap_find(&st->export_labels, st->export_order.data[i]); \
                { \
                    if(!e || e->is_undef) continue;  \
                    unsigned long long lbl_addr; \
                    if(e->is_equ){ \
                        lbl_addr=(unsigned long long)u256_to_u64(e->value); \
                    } else { \
                        lbl_addr=(unsigned long long)u256_to_u64(e->value) \
                                 *(unsigned long long)_bpw_export; \
                    } \
 \
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

cleanup:
    if(st->stdin_tmp_path[0]){
        unlink(st->stdin_tmp_path);
        st->stdin_tmp_path[0] = '\0';
    }

    for(int _li=0;_li<st->line_map_len;_li++){
        free(st->line_map[_li].section);
        free(st->line_map[_li].file);
    }
    free(st->line_map);
    st->line_map=NULL; st->line_map_len=0; st->line_map_cap=0;

    macro_free(&g_macro);
    macro_free(&g_pat_macro);

    return exit_code;
}
