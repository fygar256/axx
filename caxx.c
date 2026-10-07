

/*
 * caxx — axx 汎用アセンブラの C 実装（愛称 Caxx）。
 *
 * 同じディレクトリの axx.py（Python 版・こちらが原典）の移植で、同じ入力に対して
 * 同じバイト列を出すことを目標に保守されている。食い違いが出たらどちらかのバグ。
 * 仕様と設計の説明は axx.py 冒頭を参照。こちらははるかに速いが、新機能は
 * まず Python 側に入るので、ときどき遅れる。
 *
 * axx は命令セットをコードに持たず、外部のパターンファイル（.axx）から
 * 「ニーモニックの書式 → 機械語のバイト列」の対応を読む。パターンファイルを
 * 差し替えるだけで任意の ISA を扱える。
 *
 *     caxx <パターンファイル.axx> <ソース.s> -o <出力.o>
 *
 * 処理の流れ:
 *   1. パターンファイル読み込み（readpat、.INCLUDE を再帰展開）
 *   2. マクロ展開（macro_expand）
 *   3. パス1: 長さの収束。可変長命令の長さが前方参照ラベルの値で決まるため、
 *      全ラベルのアドレスが前回の反復と一致するまで繰り返す（リラクゼーション）
 *   4. パス2: 確定アドレスでバイト列と ELF リロケーションを作る
 *   5. 出力: ELF オブジェクト / 生バイナリ / ラベル TSV
 *
 * 計算能力は 3 層に分かれ、停止性の扱いが違う。マクロ層（macro_*）は制限なし、
 * パターン層は意図的にチューリング不完全で照合の停止性を保証、ミニ言語
 * （mini_*）は `.call` で名指しされたときだけ動き、上限付き。
 *
 * ファイルの構成（上から順に）:
 *   - uint256_t      256bit 整数演算。アドレスと即値の内部表現
 *   - 各種コンテナ   ラベル表・シンボル表・セクション表・出力バッファ
 *   - AsmState       アセンブル中の全状態
 *   - axx_*          行の前処理（コメント除去・エスケープ・トークン切り出し）
 *   - IEEE754 変換   32/64/128bit 浮動小数点のビットパターン生成
 *   - expr_*         式評価器（優先順位ごとの再帰下降）
 *   - pat_*          パターン照合
 *   - dir_* / adir_* パターン側 / ソース側のディレクティブ処理
 *   - makeobj        出力欄からワード列を作る
 *   - vliwprocess    VLIW/EPIC バンドルの組み立て
 *   - lineassemble   1 行を処理する主ループ
 *   - write_elf_obj  ELF オブジェクト出力
 *   - macro_*        行指向マクロ層（!def / !if / !while）
 *   - mini_*         ミニ言語（.func / .call）
 *   - main           コマンドライン処理と全体の駆動
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
#include <setjmp.h>

static void axx_diagf(int set_error, int force, const char *fmt, ...);
static void m_pyrepr(const char *s, char *out, size_t outsz);
static void m_pyrepr_n(const char *s, size_t n, char *out, size_t outsz);
static size_t utf8_prefix_bytes(const char *s, size_t avail, int nchars);
static int  m_utf8(unsigned long cp, char *out);
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

/* アドレスと即値の内部表現。64bit を 4 本並べた 256bit 整数で、w[0] が最下位。
   Python 側が多倍長で計算するところを同じ幅にそろえるための型。 */
typedef struct { uint64_t w[4]; } uint256_t;
static void u256_to_pydec(uint256_t a, char *out, size_t outsz);
static void m_echo_write(char *const *items, int n);

/* パターン変数 1 個ぶんの束縛。is_undef は未定義ラベル由来、is_float は
   浮動小数点として捕らえた値、text_off は `!L` が覚えたソースの綴りの位置。 */
typedef struct { uint256_t val; int is_undef; int is_float; int text_off; } PatVar;

/* パターン変数の置き場。名前は綴りだけで決まり、長さは問わない（`a` でも
   `var_2` でも同じ規則）。g_varhash が名前 → スロット番号の表で、同じ籠に
   入った名前は g_varnext でつなぐ。名前引きは照合 1 回あたり何度も呼ばれる
   ので、全走査ではなくこの表を引く。 */
#define NVARS 256
static int    g_nvars = 0;
static char  *g_varnames[NVARS];
static int    g_varlen[NVARS];

#define VARHASH_NB 256
static int    g_varhash[VARHASH_NB];
static int    g_varnext[NVARS];
static int    g_varhash_init = 0;

/* 使い回しの作業領域。照合は 1 行につき何百回も呼ばれるので、そのたびに
   malloc/free しないための札付きバッファ。busy の間は貸し出し中。 */
typedef struct { char *p; size_t cap; int busy; } ScratchBuf;

/* 作業領域を借りる。足りなければ伸ばす。貸し出し中なら自分で確保して返す。 */
static char *sbuf_take(ScratchBuf *b, size_t need){
    if(b->busy){
        char *q = malloc(need);
        if(!q){ perror("malloc"); exit(1); }
        return q;
    }
    if(b->cap < need){
        char *q = realloc(b->p, need);
        if(!q){ perror("realloc"); exit(1); }
        b->p = q; b->cap = need;
    }
    b->busy = 1;
    return b->p;
}

/* 借りた作業領域を返す。自分で確保したものならここで解放する。 */
static void sbuf_give(ScratchBuf *b, char *q){
    if(q == b->p) b->busy = 0;
    else free(q);
}

/* 長さを切って写す。書式付けが要らないところで snprintf を使わないため。 */
static void axx_copy_trunc(char *dst, size_t dsz, const char *src){
    if(dsz == 0) return;
    size_t n = strlen(src);
    if(n > dsz - 1) n = dsz - 1;
    memcpy(dst, src, n);
    dst[n] = '\0';
}

/* パターン変数名の長さ。小文字で始まり、小文字・数字・`_` が続く。 */
static int var_name_len(const char *s){
    if(!(s[0] >= 'a' && s[0] <= 'z')) return 0;
    int n = 1;
    while((s[n]>='a'&&s[n]<='z')||(s[n]>='0'&&s[n]<='9')||s[n]=='_') n++;
    return n;
}

/* 先頭 len 文字がちょうど変数名 1 個か。 */
static int is_var_name_n(const char *s, int len){
    if(len <= 0) return 0;
    if(!(s[0] >= 'a' && s[0] <= 'z')) return 0;
    for(int i = 1; i < len; i++)
        if(!((s[i]>='a'&&s[i]<='z')||(s[i]>='0'&&s[i]<='9')||s[i]=='_')) return 0;
    return 1;
}

/* 名前をスロット番号にする。長さは問わない。create が真なら無ければ作る。 */
static int var_slot(const char *name, int len, int create){
    if(!g_varhash_init){
        for(int i=0;i<VARHASH_NB;i++) g_varhash[i] = -1;
        g_varhash_init = 1;
    }
    char stackbuf[256];
    char *lower = stackbuf;
    char *lower_heap = NULL;
    if(len <= 0) return -1;
    if((size_t)len >= sizeof(stackbuf)){
        lower_heap = malloc((size_t)len + 1);
        if(!lower_heap){ perror("malloc"); exit(1); }
        lower = lower_heap;
    }
    for(int i = 0; i < len; i++) lower[i] = (char)tolower((unsigned char)name[i]);
    lower[len] = '\0';
    if(!is_var_name_n(lower, len)){ free(lower_heap); return -1; }
    unsigned h = 2166136261u;
    for(int i = 0; i < len; i++){ h ^= (unsigned char)lower[i]; h *= 16777619u; }
    h &= VARHASH_NB - 1;
    for(int vi = g_varhash[h]; vi >= 0; vi = g_varnext[vi])
        if(g_varlen[vi] == len && memcmp(g_varnames[vi], lower, (size_t)len) == 0){
            free(lower_heap);
            return vi;
        }
    if(!create){ free(lower_heap); return -1; }
    if(g_nvars >= NVARS){
        fprintf(stderr, " error - too many pattern variable names (maximum %d).\n", NVARS);
        free(lower_heap);
        return -1;
    }
    char *dup = malloc((size_t)len + 1);
    if(!dup){ perror("malloc"); exit(1); }
    memcpy(dup, lower, (size_t)len); dup[len] = '\0';
    free(lower_heap);
    g_varnames[g_nvars] = dup;
    g_varlen[g_nvars]   = len;
    g_varnext[g_nvars]  = g_varhash[h];
    g_varhash[h]        = g_nvars;
    return g_nvars++;
}

/* 診断に出すためのスロットの名前。 */
static const char *var_slot_name(int slot){
    if(slot < 0 || slot >= g_nvars) return "?";
    return g_varnames[slot];
}

typedef struct { int is_str; char *s; uint256_t v; } SymItem;
struct ArrSym { char *name; SymItem *items; int len; };

/* ---- 256bit 整数演算 ----------------------------------------------------
   アドレスと即値はすべてこの型で持つ。Python の多倍長整数と結果をそろえる
   のが目的なので、符号付き演算は 2 の補数、シフトは算術シフト、除算と剰余は
   本体の式評価器の規則（`/` はゼロ方向、`%` は除数の符号）に合わせた
   専用の関数を用意してある。256bit を超えた桁は黙って落ちるので、
   そこから先は warn_u256_wrap で一度だけ警告する。
   ------------------------------------------------------------------------ */
static uint256_t u256_zero(void) {
    uint256_t r; memset(&r,0,sizeof(r)); return r;
}
/* 1。 */
static uint256_t u256_one(void) {
    uint256_t r = u256_zero(); r.w[0]=1; return r;
}
/* 符号付き 64bit から作る（符号拡張する）。 */
static uint256_t u256_from_i64(int64_t v) {
    uint256_t r;
    r.w[0] = (uint64_t)v;
    uint64_t fill = (v < 0) ? (uint64_t)-1 : 0;
    r.w[1]=r.w[2]=r.w[3]=fill;
    return r;
}
/* 符号なし 64bit から作る。 */
static uint256_t u256_from_u64(uint64_t v) {
    uint256_t r = u256_zero(); r.w[0]=v; return r;
}
/* 0 か。 */
static int u256_is_zero(uint256_t a) {
    return (a.w[0]|a.w[1]|a.w[2]|a.w[3]) == 0;
}
/* 等しいか。 */
static int u256_eq(uint256_t a, uint256_t b) {
    return a.w[0]==b.w[0] && a.w[1]==b.w[1] && a.w[2]==b.w[2] && a.w[3]==b.w[3];
}
/* 符号付きで a < b か。 */
static int u256_lt_signed(uint256_t a, uint256_t b) {
    int sa = (int)(a.w[3] >> 63);
    int sb = (int)(b.w[3] >> 63);
    if (sa != sb) return sa > sb;
    if (a.w[3] != b.w[3]) return a.w[3] < b.w[3];
    if (a.w[2] != b.w[2]) return a.w[2] < b.w[2];
    if (a.w[1] != b.w[1]) return a.w[1] < b.w[1];
    return a.w[0] < b.w[0];
}
/* 符号付きで a <= b か。 */
static int u256_le_signed(uint256_t a, uint256_t b) {
    return u256_eq(a,b) || u256_lt_signed(a,b);
}
static int u256_gt_signed(uint256_t a, uint256_t b) { return u256_lt_signed(b,a); }
static int u256_ge_signed(uint256_t a, uint256_t b) { return u256_le_signed(b,a); }

/* 加算（桁上がりを下から伝える）。 */
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
/* 符号反転（2 の補数）。 */
static uint256_t u256_neg(uint256_t a) {
    uint256_t r;
    for(int i=0;i<4;i++) r.w[i]=~a.w[i];
    return u256_add(r, u256_one());
}
/* 減算。 */
static uint256_t u256_sub(uint256_t a, uint256_t b) {
    return u256_add(a, u256_neg(b));
}
/* ビット NOT。 */
static uint256_t u256_not(uint256_t a) {
    uint256_t r; for(int i=0;i<4;i++) r.w[i]=~a.w[i]; return r;
}
/* ビット AND。 */
static uint256_t u256_and(uint256_t a, uint256_t b) {
    uint256_t r; for(int i=0;i<4;i++) r.w[i]=a.w[i]&b.w[i]; return r;
}
/* ビット OR。 */
static uint256_t u256_or(uint256_t a, uint256_t b) {
    uint256_t r; for(int i=0;i<4;i++) r.w[i]=a.w[i]|b.w[i]; return r;
}
/* ビット XOR。 */
static uint256_t u256_xor(uint256_t a, uint256_t b) {
    uint256_t r; for(int i=0;i<4;i++) r.w[i]=a.w[i]^b.w[i]; return r;
}
/* 左シフト。n が幅以上なら 0。 */
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
/* 算術右シフト。符号を保つ。 */
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
/* 乗算。256bit を超えた桁は落ちる。 */
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
/* x*m+d（m と d は 64 ビットに収まる小さな数）。256 ビットを溢れたら *ovf を
   立てる。数値リテラルを読むときに桁あふれを見つけるのに使う。 */
static uint256_t u256_muladd_small(uint256_t x, uint64_t m, uint64_t d, int *ovf){
    __uint128_t carry = d;
    for(int i=0;i<4;i++){
        __uint128_t t = (__uint128_t)x.w[i]*m + carry;
        x.w[i] = (uint64_t)t;
        carry = t >> 64;
    }
    if(carry) *ovf = 1;
    return x;
}
/* 符号付き乗算。 */
static uint256_t u256_mul_signed(uint256_t a, uint256_t b) {
    return u256_mul(a,b);
}
/* 符号なし除算。 */
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
/* `//` … 負の無限方向へ丸める除算。 */
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
/* `/` … ゼロ方向へ切り捨てる除算（`-7/3 == -2`）。 */
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
/* `%` … 結果が除数の符号に従う剰余（`-7%3 == 2`）。Python と同じで、
   C の `%` とは違う。ミニ言語とマクロ層の `%` は C と同じなので、
   層をまたいで式を写すときは負の値に注意。 */
static uint256_t u256_mod(uint256_t a, uint256_t b) {
    if (u256_is_zero(b)) { fprintf(stderr,"Division by zero\n"); return u256_zero(); }
    uint256_t q = u256_floordiv(a,b);
    return u256_sub(a, u256_mul(q,b));
}

/* `**` … べき乗。桁が溢れる前に打ち切る。 */
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
static int u256_is_neg256(uint256_t v){ return (int)(v.w[3]>>63); }
/* 非負の v が max を超えるか。シフト量や指数のように下位 64bit だけ見ると
   危ない場所で、上位の桁が立っていないことまで確かめるために使う。 */
static int u256_nonneg_gt_i64(uint256_t v, int64_t max){
    if(v.w[1] || v.w[2] || v.w[3]) return 1;
    return v.w[0] > (uint64_t)max;
}

/* `@` 演算子。最上位の立っているビットの位置を右から数える。 */
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


#define SEXT_MAX_BITS 128

static int op_msb(uint256_t v){ return u256_nbit(v); }

/* `x'bits` … ビット bits-1 を符号ビットとみなした符号拡張。幅が大きすぎる
   ときは warn_out に印を立て、報告は呼び出し側に任せる。 */
static uint256_t op_sext(uint256_t x, uint256_t bits, int *warn_out){
    *warn_out = 0;
    if(u256_is_neg256(bits) || u256_is_zero(bits)) return u256_zero();
    if(u256_nonneg_gt_i64(bits, SEXT_MAX_BITS)){ *warn_out = 1; return u256_zero(); }
    int tv = (int)u256_to_i64(bits);
    uint256_t mask = u256_not(u256_shl(u256_not(u256_zero()), tv));
    x = u256_and(x, mask);
    uint256_t sign_bit = u256_and(u256_sar(x, tv - 1), u256_one());
    if(!u256_is_zero(sign_bit))
        x = u256_or(x, u256_shl(u256_not(u256_zero()), tv));
    return x;
}

/* `*(x, index)` … 下位から数えて index バイト目より上を残した値。 */
static uint256_t op_byte(uint256_t x, uint256_t index, int *neg_out){
    *neg_out = 0;
    if(u256_is_neg256(index)){ *neg_out = 1; return u256_zero(); }
    int shift = u256_nonneg_gt_i64(index, 256/8) ? 256 : (int)(u256_to_i64(index)*8);
    return u256_sar(x, shift);
}

/* 未定義ラベルの値を表す番兵。巨大な整数にしてあるので、`label+4` のように
   普通の算術に流れ込んでも未定義性が計算結果へ伝わっていく。 */
static uint256_t UNDEF_VAL(void) {
    uint256_t r = u256_not(u256_zero());
    r.w[3] &= 0x7FFFFFFFFFFFFFFFULL;
    return r;
}
static int u256_is_undef(uint256_t a) { return u256_eq(a, UNDEF_VAL()); }
/* 式の演算の毒。オペランドのどちらかが未定義そのものなら結果も未定義にする。
   未定義の値どうしの算術が、番兵の大きさの違い（axx.py は 2**1024-1）によって
   両実装で別の値になるのを防ぐ。axx.py の _undef() と同じ判定。 */
#define UNDEF2(a, b) (u256_is_undef(a) || u256_is_undef(b))
/* 値が未定義ラベル由来かを閾値で判定する。 */
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

/* 正当な巨大値と未定義由来の区別が付かない帯に入っているか。
   この帯では上の判定が誤りうることを一度だけ警告する。 */
static int u256_in_undef_band(uint256_t a){
    int sign = (int)(a.w[3] >> 63);
    uint256_t av = sign ? u256_neg(a) : a;
    return av.w[3] != 0;
}
/* 256bit を超えて桁が落ちたことを一度だけ警告する。 */
static void warn_u256_wrap(const char *op){
    static int warned = 0;
    if(warned) return;
    warned = 1;
    axx_diagf(0, 1, " warning - a value overflowed 256 bits in '%s' and was wrapped; "
                    "axx.py keeps the full precision there, so the two implementations "
                    "disagree above 2**256 (manual 6.4).\n", op);
}

typedef struct {
    char   *buf;
    size_t  len;
    size_t  cap;
} DynStr;

static void ds_init(DynStr *d) { d->buf=NULL; d->len=0; d->cap=0; }
static AXX_UNUSED void ds_free(DynStr *d) { free(d->buf); ds_init(d); }
/* ---- 可変長の文字列とベクタ -------------------------------------------
   DynStr が伸びる文字列、IntVec が 256bit 整数の列、StrVec が文字列の列。
   どれも必要なときだけ倍々に伸ばす。AXX_UNUSED が付いているものは、
   対称性のために置いてあって今は呼ばれていない。
   ------------------------------------------------------------------------ */
static void ds_ensure(DynStr *d, size_t need) {
    if (d->cap >= need+1) return;
    size_t nc = (need+1)*2;
    if(nc<32)nc=32;
    d->buf = realloc(d->buf, nc);
    if(!d->buf){perror("realloc");exit(1);}
    d->cap = nc;
}
/* 文字列を設定する（現在は未使用）。 */
static AXX_UNUSED void ds_set(DynStr *d, const char *s) {
    size_t l = strlen(s);
    ds_ensure(d, l);
    memcpy(d->buf, s, l+1);
    d->len = l;
}
/* 1 文字を設定する（現在は未使用）。 */
static AXX_UNUSED void ds_setc(DynStr *d, char c) {
    ds_ensure(d,1);
    d->buf[0]=c; d->buf[1]=0; d->len=1;
}
/* 文字列を足す（現在は未使用）。 */
static AXX_UNUSED void ds_append(DynStr *d, const char *s) {
    size_t l=strlen(s);
    ds_ensure(d, d->len+l);
    memcpy(d->buf+d->len, s, l+1);
    d->len+=l;
}
/* 1 文字を足す（現在は未使用）。 */
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
/* 整数列に 1 個積む。 */
static void iv_push(IntVec *v, uint256_t x) {
    if(v->len>=v->cap){
        v->cap = v->cap ? v->cap*2 : 8;
        v->data = realloc(v->data, v->cap*sizeof(uint256_t));
        if(!v->data){perror("realloc");exit(1);}
    }
    v->data[v->len++]=x;
}
static void iv_clear(IntVec *v) { v->len=0; }
/* 整数列を写す。 */
static void iv_copy(IntVec *dst, const IntVec *src) {
    iv_clear(dst);
    for(int i=0;i<src->len;i++) iv_push(dst, src->data[i]);
}
/* 整数列を連結する（現在は未使用）。 */
static AXX_UNUSED void iv_append(IntVec *dst, const IntVec *src) {
    for(int i=0;i<src->len;i++) iv_push(dst, src->data[i]);
}

/* 素の int 配列に 1 個積む（必要なら伸ばす）。 */
static void ilst_push(int **arr, int *n, int *cap, int v) {
    if(*n >= *cap){
        *cap = *cap ? *cap*2 : 256;
        *arr = realloc(*arr, (size_t)(*cap)*sizeof(int));
        if(!*arr){perror("realloc");exit(1);}
    }
    (*arr)[(*n)++] = v;
}

typedef struct {
    char **data;
    int    len;
    int    cap;
} StrVec;
static void sv_init(StrVec *v){v->data=NULL;v->len=0;v->cap=0;}
/* 文字列列に 1 個積む。 */
static void sv_push(StrVec *v, const char *s){
    if(v->len>=v->cap){
        v->cap=v->cap?v->cap*2:8;
        v->data=realloc(v->data,v->cap*sizeof(char*));
        if(!v->data){perror("realloc");exit(1);}
    }
    v->data[v->len++]=strdup(s);
}
/* 文字列列にその文字列が含まれるか。 */
static int sv_contains(const StrVec *v, const char *s){
    for(int i = 0; i < v->len; i++) if(strcmp(v->data[i], s) == 0) return 1;
    return 0;
}
/* 文字列列から 1 個外す。 */
static void sv_pop(StrVec *v){
    if(v->len>0){free(v->data[--v->len]);}
}
/* 文字列列を解放する（現在は未使用）。 */
static AXX_UNUSED void sv_free(StrVec *v){
    for(int i=0;i<v->len;i++)free(v->data[i]);
    free(v->data); sv_init(v);
}
/* 添字の要素を差し替える。足りなければ空文字で伸ばす（現在は未使用）。 */
static AXX_UNUSED void sv_set(StrVec *v, int idx, const char *s){
    while(v->len<=idx) sv_push(v, "");
    char *dup = strdup(s);
    if(!dup){perror("strdup"); exit(1);}
    free(v->data[idx]);
    v->data[idx] = dup;
}

typedef struct { StrVec names; char *expr; } EnumDef;

static void enumdef_init(EnumDef *e){ sv_init(&e->names); e->expr=NULL; }
static long long g_arrgen = 0;

typedef struct { int refs; StrVec v; } ChkList;

/* `.check` の許容名リスト。`.check` は配列シンボルを参照できるので、
   同じリストが複数の変数から共有されうる。参照数を数えて、最後の持ち主が
   手放したときだけ解放する。 */
static ChkList *chk_new(void){
    ChkList *c = malloc(sizeof(*c));
    if(!c){ perror("malloc"); exit(1); }
    c->refs = 1;
    sv_init(&c->v);
    return c;
}
static ChkList *chk_ref(ChkList *c){ if(c) c->refs++; return c; }
/* 参照を 1 つ手放す。0 になったら解放する。 */
static void chk_unref(ChkList *c){
    if(!c) return;
    if(--c->refs == 0){ sv_free(&c->v); free(c); }
}
/* スロットの中身を差し替える（古いほうを手放す）。 */
static void chk_install(ChkList **slot, ChkList *nw){
    ChkList *old = *slot;
    *slot = nw;
    chk_unref(old);
}
static int chk_len(const ChkList *c){ return c ? c->v.len : 0; }
static const char *chk_at(const ChkList *c, int i){ return c->v.data[i]; }

/* `.enum` の登録を捨てる。 */
static void enumdef_clear(EnumDef *e){
    sv_free(&e->names);
    free(e->expr); e->expr=NULL;
}
/* `.enum` の登録を写す。 */
static void enumdef_copy(EnumDef *dst, const EnumDef *src){
    enumdef_clear(dst);
    for(int i=0;i<src->names.len;i++) sv_push(&dst->names, src->names.data[i]);
    dst->expr = src->expr ? strdup(src->expr) : NULL;
}

typedef struct { char *pat; char *val; } SubEntry;
typedef struct { char *name; SubEntry *e; int n; int cap; int freed; } SubDef;
typedef struct { SubDef *data; int len; int cap; } SubVec;

static void subv_init(SubVec*v){ v->data=NULL; v->len=0; v->cap=0; }
/* `.sub::名前 … .return` で登録されたサブ表。参照は `!S{{名前}}` で、
   使用箇所より後に定義してよいので、ファイル全体を読んでから解決する。 */
static void subv_free(SubVec*v){
    for(int i=0;i<v->len;i++){
        for(int j=0;j<v->data[i].n;j++){
            free(v->data[i].e[j].pat);
            free(v->data[i].e[j].val);
        }
        free(v->data[i].e);
        free(v->data[i].name);
    }
    free(v->data); subv_init(v);
}
/* 名前でサブ表を引く。 */
static SubDef *subv_find(SubVec*v, const char *name){
    for(int i=0;i<v->len;i++) if(strcmp(v->data[i].name,name)==0) return &v->data[i];
    return NULL;
}
/* `.free` で「この行から先は使わない」と印を付ける。表そのものは消さない。 */
static int subv_mark_freed(SubVec*v, const char *name){
    for(int i=0;i<v->len;i++)
        if(strcasecmp(v->data[i].name, name)==0){ v->data[i].freed = 1; return 1; }
    return 0;
}
/* すべてのサブ表の印を外す。 */
static void subv_unfreeze_all(SubVec*v){
    for(int i=0;i<v->len;i++) v->data[i].freed = 0;
}
/* サブ表を 1 つ作る。 */
static SubDef *subv_new(SubVec*v, const char *name){
    SubDef *old = subv_find(v, name);
    if(old){
        for(int j=0;j<old->n;j++){ free(old->e[j].pat); free(old->e[j].val); }
        old->n = 0;
        return old;
    }
    if(v->len>=v->cap){
        v->cap = v->cap ? v->cap*2 : 8;
        v->data = realloc(v->data, (size_t)v->cap*sizeof(SubDef));
        if(!v->data){ perror("realloc"); exit(1); }
    }
    SubDef *d = &v->data[v->len++];
    d->freed = 0;
    d->name = strdup(name); d->e = NULL; d->n = 0; d->cap = 0;
    if(!d->name){ perror("strdup"); exit(1); }
    return d;
}
/* サブ表にエントリ（パターンと値リスト）を 1 つ足す。 */
static void subdef_push(SubDef *d, const char *pat, const char *val){
    if(d->n>=d->cap){
        d->cap = d->cap ? d->cap*2 : 8;
        d->e = realloc(d->e, (size_t)d->cap*sizeof(SubEntry));
        if(!d->e){ perror("realloc"); exit(1); }
    }
    d->e[d->n].pat = strdup(pat);
    d->e[d->n].val = strdup(val);
    if(!d->e[d->n].pat || !d->e[d->n].val){ perror("strdup"); exit(1); }
    d->n++;
}

/* `.sub::名前` / `!S{{名前}}` に書ける名前か。 */
static int is_sub_name(const char *s){
    if(!s || !s[0]) return 0;
    for(const char *p=s; *p; p++)
        if(!(isalnum((unsigned char)*p) || *p=='_')) return 0;
    return 1;
}


/* ミニ言語の値。整数・配列・文字列のどれか。文字列は UTF-8 のバイトの並びで、
   NUL も入りうるので長さを別に持つ。配列の要素は整数か文字列で、文字列の
   要素があるときだけ astr / alen を持つ（astr[i] が NULL なら arr[i] が整数）。 */
typedef struct {
    int        is_arr;
    int        is_str;
    uint256_t  num;
    uint256_t *arr;
    unsigned char **astr;
    int       *alen;
    int        n, cap;
    unsigned char *str;
    int        slen;
} MiniVal;

typedef enum {
    MX_NUM, MX_VAR, MX_ARRLIT, MX_INDEX, MX_SLICE, MX_LEN, MX_BIN, MX_UN,
    MX_CALL,
    MX_STR,
    MX_CORE,
    MX_TOSTR, MX_CHR, MX_TOINT
} MXKind;

typedef struct MExpr {
    MXKind         k;
    uint256_t      num;
    char          *name;
    char           op[3];
    struct MExpr  *a, *b, *c;
    struct MExpr **items;
    int            nitems;
} MExpr;

typedef enum {
    MS_ASSIGN, MS_EMIT, MS_ECHO, MS_CALL, MS_CALLASSIGN, MS_RETURN, MS_IF,
    MS_WHILE, MS_FOR, MS_NONLOCAL, MS_RAISE, MS_BREAK, MS_CONTINUE
} MSKind;

typedef struct MStmt {
    MSKind         k;
    char          *name;
    char          *fname;
    MExpr         *idx;
    MExpr         *val;
    MExpr        **args;
    int            nargs;
    struct MStmt **body;
    int            nbody;
    struct MStmt **body2;
    int            nbody2;
    char         **names;
    int            nnames;
    const char    *file;
    int            line;
} MStmt;

typedef struct MiniFunc {
    char             *name;
    char            **params;
    int               nparams;
    char            **lines;
    char            **lfiles;
    int              *llines;
    int               nlines, clines;
    MStmt           **body;
    int               nbody;
    struct MiniFunc  *parent;
    struct MiniFunc **children;
    int               nchildren, cchildren;
    char             *file;
    int               line;
    int               depth;
} MiniFunc;

typedef struct { MiniFunc **data; int len; int cap; } MiniFuncVec;

static void mfv_init(MiniFuncVec *v){ v->data = NULL; v->len = 0; v->cap = 0; }

typedef struct { int *data; int len; int cap; } IStack;
static void is_init(IStack*v){v->data=NULL;v->len=0;v->cap=0;}
/* int のスタックに 1 個積む。 */
static void is_push(IStack*v,int x){
    if(v->len>=v->cap){v->cap=v->cap?v->cap*2:8;v->data=realloc(v->data,v->cap*sizeof(int));if(!v->data){perror("realloc");exit(1);}}
    v->data[v->len++]=x;
}
static int is_pop(IStack*v){return v->len>0?v->data[--v->len]:0;}

#define HASH_INIT_CAP 64

typedef struct LabelEntry {
    char          *key;
    uint256_t      value;
    char          *section;
    int            is_equ;
    int            is_imported;
    int            reloc_type_override;
    int            is_undef;
    long long      seq;
    struct LabelEntry *next;
} LabelEntry;

typedef struct {
    LabelEntry **buckets;
    int          nbuckets;
    int          count;
    long long    seq_next;
} LabelMap;

/* ---- ラベル表とシンボル表 ---------------------------------------------
   どちらも開番地法のハッシュ表。ラベル表は定義順（seq）も覚えていて、
   エクスポートとリスティングを書かれた順に出せるようにしてある。
   ------------------------------------------------------------------------ */
static uint32_t hash_str(const char *s) {
    uint32_t h=5381;
    unsigned char c;
    while((c=(unsigned char)*s++)) h=((h<<5)+h)+c;
    return h;
}
/* ラベル表を初期化する。 */
static void lmap_init(LabelMap *m) {
    m->nbuckets=HASH_INIT_CAP;
    m->buckets=calloc(m->nbuckets,sizeof(LabelEntry*));
    m->count=0;
    m->seq_next=0;
}

/* 定義順に並べるための比較関数。 */
static int lmap_cmp_seq(const void *a, const void *b){
    const LabelEntry *x = *(const LabelEntry * const *)a;
    const LabelEntry *y = *(const LabelEntry * const *)b;
    return (x->seq > y->seq) - (x->seq < y->seq);
}
/* ラベルを定義順に並べた配列を返す。出力の順を実装間でそろえるため。 */
static LabelEntry **lmap_in_order(LabelMap *m, int *nout){
    int n = 0;
    LabelEntry **v = malloc((size_t)(m->count ? m->count : 1) * sizeof(LabelEntry*));
    if(!v){ perror("malloc"); exit(1); }
    for(int bi=0; bi<m->nbuckets; bi++)
        for(LabelEntry *e=m->buckets[bi]; e; e=e->next)
            v[n++] = e;
    qsort(v, (size_t)n, sizeof(LabelEntry*), lmap_cmp_seq);
    *nout = n;
    return v;
}
/* ラベル表を解放する。 */
static void lmap_free(LabelMap *m) {
    for(int i=0;i<m->nbuckets;i++){
        LabelEntry *e=m->buckets[i];
        while(e){ LabelEntry*n=e->next; free(e->key); free(e->section); free(e); e=n;}
    }
    free(m->buckets); m->buckets=NULL; m->count=0; m->nbuckets=0;
}
/* 詰まってきたら表を倍にして詰め直す。 */
static void lmap_maybe_grow(LabelMap *m) {
    if(!m->buckets || m->nbuckets <= 0) return;
    if(m->count < m->nbuckets * 4) return;
    int nb = m->nbuckets * 4;
    LabelEntry **nbuf = calloc((size_t)nb, sizeof(LabelEntry*));
    if(!nbuf) return;
    for(int i=0;i<m->nbuckets;i++){
        LabelEntry *e = m->buckets[i];
        while(e){
            LabelEntry *n = e->next;
            uint32_t h = hash_str(e->key) % (uint32_t)nb;
            e->next = nbuf[h]; nbuf[h] = e;
            e = n;
        }
    }
    free(m->buckets);
    m->buckets = nbuf; m->nbuckets = nb;
}

/* ラベルを引く。 */
static LabelEntry *lmap_find(LabelMap *m, const char *key) {
    if(!m->nbuckets) return NULL;
    uint32_t h=hash_str(key)%(uint32_t)m->nbuckets;
    for(LabelEntry*e=m->buckets[h];e;e=e->next)
        if(strcmp(e->key,key)==0) return e;
    return NULL;
}
static int lmap_contains(LabelMap *m, const char *key) { return lmap_find(m,key)!=NULL; }
/* ラベルを定義する。`.equ` のものは再配置情報を持たない定数として扱う。 */
static void lmap_set(LabelMap *m, const char *key, uint256_t val, const char *sec, int is_equ, int is_undef) {
    if(!m->nbuckets) return;
    uint32_t h=hash_str(key)%(uint32_t)m->nbuckets;
    for(LabelEntry*e=m->buckets[h];e;e=e->next){
        if(strcmp(e->key,key)==0){
            e->value=val; free(e->section); e->section=strdup(sec); e->is_equ=is_equ; e->is_undef=is_undef;
            e->is_imported = 0;
            return;
        }
    }
    LabelEntry *e=calloc(1,sizeof(LabelEntry));
    e->key=strdup(key); e->value=val; e->section=strdup(sec);
    e->is_equ=is_equ; e->is_imported=0; e->reloc_type_override=-1; e->is_undef=is_undef;
    e->seq=m->seq_next++;
    e->next=m->buckets[h]; m->buckets[h]=e; m->count++;
    lmap_maybe_grow(m);
}
/* ラベルにリロケーション型を付ける。 */
static void lmap_set_reloc_type(LabelMap *m, const char *key, int reloc_type) {
    LabelEntry *e = lmap_find(m, key);
    if(e) e->reloc_type_override = reloc_type;
}
/* `-i` で取り込んだラベルを登録する。これは後から上書きしてよい。 */
static void lmap_set_imported(LabelMap *m, const char *key, uint256_t val, const char *sec, int reloc_type) {
    if(!m->nbuckets) return;
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
    e->seq=m->seq_next++;
    e->next=m->buckets[h]; m->buckets[h]=e; m->count++;
    lmap_maybe_grow(m);
}
static void lmap_set_full(LabelMap *m, const char *key, uint256_t val,
                          const char *sec, int is_equ, int is_imported, int reloc_type_override,
                          int is_undef) {
    if(!m->nbuckets) return;
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
    e->seq=m->seq_next++;
    e->next=m->buckets[h]; m->buckets[h]=e; m->count++;
    lmap_maybe_grow(m);
}
/* ラベルを消す（現在は未使用）。 */
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
/* ラベルを順に渡す（現在は未使用）。 */
static AXX_UNUSED void lmap_iter(LabelMap *m, lmap_iter_fn fn, void*user){
    for(int i=0;i<m->nbuckets;i++)
        for(LabelEntry*e=m->buckets[i];e;e=e->next)
            fn(e->key,e->value,e->section,user);
}

typedef struct SymEntry { char*key; uint256_t val; struct SymEntry*next; } SymEntry;
typedef struct { SymEntry**buckets; int nb; int count; } SymMap;
static void smap_init(SymMap*m){m->nb=HASH_INIT_CAP;m->buckets=calloc(m->nb,sizeof(SymEntry*));m->count=0;}
/* シンボル表を解放する。 */
static void smap_free(SymMap*m){
    for(int i=0;i<m->nb;i++){SymEntry*e=m->buckets[i];while(e){SymEntry*n=e->next;free(e->key);free(e);e=n;}}
    free(m->buckets);m->buckets=NULL;
}
/* シンボルを引く。 */
static SymEntry *smap_find(SymMap*m,const char*key){
    uint32_t h=hash_str(key)%(uint32_t)m->nb;
    for(SymEntry*e=m->buckets[h];e;e=e->next) if(strcmp(e->key,key)==0)return e;
    return NULL;
}
/* シンボルの値を取る。無ければ 0 を返して値は触らない。 */
static int smap_get(SymMap*m,const char*key,uint256_t*out){
    SymEntry*e=smap_find(m,key); if(e){*out=e->val;return 1;} return 0;
}
/* シンボルを定義する。同じ名前は上書きする。 */
static void smap_set(SymMap*m,const char*key,uint256_t val){
    uint32_t h=hash_str(key)%(uint32_t)m->nb;
    for(SymEntry*e=m->buckets[h];e;e=e->next) if(strcmp(e->key,key)==0){e->val=val;return;}
    SymEntry*e=calloc(1,sizeof(SymEntry)); e->key=strdup(key); e->val=val;
    e->next=m->buckets[h]; m->buckets[h]=e; m->count++;
}
/* シンボルを消す。 */
static void smap_delete(SymMap*m,const char*key){
    uint32_t h=hash_str(key)%(uint32_t)m->nb;
    SymEntry**pp=&m->buckets[h];
    while(*pp){ if(strcmp((*pp)->key,key)==0){SymEntry*d=*pp;*pp=d->next;free(d->key);free(d);m->count--;return;} pp=&(*pp)->next; }
}
/* シンボル表を丸ごと写す。反復の頭で初期状態へ戻すのに使う。 */
static void smap_assign(SymMap *dst, const SymMap *src){
    for(int i=0;i<dst->nb;i++){
        SymEntry **pp = &dst->buckets[i];
        while(*pp){
            SymEntry *e = *pp;
            SymEntry *se = smap_find((SymMap*)src, e->key);
            if(se){ e->val = se->val; pp = &e->next; }
            else { *pp = e->next; free(e->key); free(e); dst->count--; }
        }
    }
    for(int i=0;i<src->nb;i++)
        for(SymEntry *e=src->buckets[i]; e; e=e->next)
            if(!smap_find(dst, e->key)) smap_set(dst, e->key, e->val);
}

/* シンボル表を空にする。 */
static void smap_clear(SymMap*m){
    for(int i=0;i<m->nb;i++){
        SymEntry*e=m->buckets[i];
        while(e){SymEntry*n=e->next;free(e->key);free(e);e=n;}
        m->buckets[i]=NULL;
    }
    m->count=0;
}

typedef struct SecEntry {
    char       *name;
    uint256_t   start;
    uint256_t   size;
    uint256_t   entry_pc;
    int         confirmed;
    struct SecEntry *next;
} SecEntry;
typedef struct { SecEntry**buckets; int nb; SecEntry**order; int count; int cap; } SecMap;
static void secmap_init(SecMap*m){m->nb=16;m->buckets=calloc(m->nb,sizeof(SecEntry*));m->count=0;m->cap=16;m->order=calloc(m->cap,sizeof(SecEntry*));}
/* ---- セクション ---------------------------------------------------------
   セクションは書かれた順に並ぶ。同じ名前を何度も開き直せるので、占めた範囲を
   SecRangeVec に順に積んでおき、セクション内の相対位置はその累積から出す。
   ------------------------------------------------------------------------ */
static SecEntry *secmap_find(SecMap*m,const char*name){
    uint32_t h=hash_str(name)%(uint32_t)m->nb;
    for(SecEntry*e=m->buckets[h];e;e=e->next) if(strcmp(e->name,name)==0)return e;
    return NULL;
}

/* セクション表を解放する（現在は未使用）。 */
static AXX_UNUSED void secmap_free(SecMap*m){
    for(int i=0;i<m->nb;i++){
        SecEntry*e=m->buckets[i];
        while(e){SecEntry*n=e->next;free(e->name);free(e);e=n;}
        m->buckets[i]=NULL;
    }
    free(m->buckets); free(m->order);
    m->buckets=NULL; m->order=NULL; m->count=0; m->cap=0; m->nb=0;
}
/* セクション表を空にする。 */
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
/* セクションが占めた範囲を 1 つ積む。 */
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
/* 範囲の記録を空にする。 */
static void secrangevec_clear(SecRangeVec*v){
    for(int i=0;i<v->len;i++) free(v->data[i].name);
    v->len = 0;
}
/* 範囲の記録を解放する（現在は未使用）。 */
AXX_UNUSED static void secrangevec_free(SecRangeVec*v){
    secrangevec_clear(v);
    free(v->data); v->data=NULL; v->cap=0;
}
/* 絶対のワードアドレスを、そのセクション先頭からの相対位置に直す。
   同じ名前の範囲を書かれた順にたどって累積する。範囲外なら -1。 */
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


#define PAT_FIELDS 6
typedef struct {
    char *f[PAT_FIELDS];
    int       is_dir;
    int       dir_kind;
    int       setsym_const;
    int       setsym_done;
    uint256_t setsym_val;
    int       setsym_plain;
    char     *setsym_key;
    int       elftype_done;
    int       elftype_val;
    int       elftype_wid;
    int       elftype_pcr;
    char      pfx[64];
    int       pfxlen;
    int       pfx_closed;
    void     *chk_cache;
    long long chk_cache_gen;
    void     *echo_items;
    int       echo_nitems;
} PatEntry;

typedef struct {
    PatEntry *data;
    int       len;
    int       cap;
} PatVec;

static void pv_init(PatVec*v){v->data=NULL;v->len=0;v->cap=0;}
enum {
    PD_NONE = 0, PD_SETSYM, PD_CLEARSYM, PD_PADDING, PD_BITS, PD_SYMBOLC,
    PD_VLIW, PD_CHECK, PD_CLRCHECK, PD_RELOC, PD_CLRRELOC, PD_MAP, PD_FREE,
    PD_PASSTHRU, PD_EOL, PD_TEXTMODE, PD_ENUM, PD_CLRENUM, PD_ERRMSG, PD_EPIC,
    PD_ELFTYPE, PD_ELFMACHINE, PD_ELFCLASS, PD_ELFRELA, PD_ELFWIDTH,
    PD_ELFEXTERN, PD_ELFDWARF, PD_ELFHEADER, PD_ELFSECTION, PD_ECHO, PD_ELFFIELD,
    PD_ELFPCGUESS, PD_ELFBUILTIN, PD_ELFEXTRA, PD_ELFDIFF, PD_ELFENCODE,
    PD_ELFRINFO, PD_ELFUNIT, PD_ELFLINK, PD_ELFGROUP, PD_ELFCFI, PD_ELFCFIINIT,
    PD_ELFCFIREG, PD_UNORDERED
};

/* パターン行がどのディレクティブか（種別の番号）。 */
static int pat_dir_kind(const PatEntry *e){
    static const struct { const char *name; int kind; } tbl[] = {
        { ".setsym", PD_SETSYM }, { ".clearsym", PD_CLEARSYM },
        { ".padding", PD_PADDING }, { ".bits", PD_BITS },
        { ".symbolc", PD_SYMBOLC }, { ".vliw", PD_VLIW },
        { ".check", PD_CHECK }, { ".clrcheck", PD_CLRCHECK },
        { ".reloc", PD_RELOC }, { ".clrreloc", PD_CLRRELOC },
        { ".map", PD_MAP }, { ".free", PD_FREE },
        { ".passthru", PD_PASSTHRU }, { ".eol", PD_EOL },
        { ".textmode", PD_TEXTMODE }, { ".enum", PD_ENUM },
        { ".clrenum", PD_CLRENUM }, { ".error", PD_ERRMSG },
        { ".elftype", PD_ELFTYPE },
        { ".elfmachine", PD_ELFMACHINE }, { ".elfclass", PD_ELFCLASS },
        { ".elfrela", PD_ELFRELA }, { ".elfwidth", PD_ELFWIDTH },
        { ".elfextern", PD_ELFEXTERN }, { ".elfdwarf", PD_ELFDWARF },
        { ".elfheader", PD_ELFHEADER }, { ".elfsection", PD_ELFSECTION },
        { ".elffield", PD_ELFFIELD },
        { ".elfpcguess", PD_ELFPCGUESS }, { ".elfbuiltin", PD_ELFBUILTIN },
        { ".elfextra", PD_ELFEXTRA }, { ".elfdiff", PD_ELFDIFF },
        { ".elfencode", PD_ELFENCODE }, { ".elfrinfo", PD_ELFRINFO },
        { ".elfunit", PD_ELFUNIT }, { ".elflink", PD_ELFLINK },
        { ".elfgroup", PD_ELFGROUP },
        { ".elfcfi", PD_ELFCFI }, { ".elfcfiinit", PD_ELFCFIINIT },
        { ".elfcfireg", PD_ELFCFIREG },
        { ".echo", PD_ECHO }, { ".unordered", PD_UNORDERED }, { NULL, 0 } };
    if(!e || !e->f[0] || !e->f[0][0]) return PD_NONE;
    const char *n = e->f[0];
    for(int k=0; tbl[k].name; k++) if(strcmp(n, tbl[k].name) == 0) return tbl[k].kind;
    if(n[0] && n[1] && n[2] && n[3] && !n[4]){
        static const char epic[] = "EPIC";
        int k = 0;
        for(; k < 4; k++){
            char c = n[k];
            if(c >= 'a' && c <= 'z') c = (char)(c - 'a' + 'A');
            if(c != epic[k]) break;
        }
        if(k == 4) return PD_EPIC;
    }
    return PD_NONE;
}

/* パターン行がディレクティブか。`EPIC::` も含める。 */
static int pat_is_directive(const PatEntry *e){
    static const char *tbl[] = {
        ".setsym", ".clearsym", ".padding", ".bits", ".symbolc", ".vliw",
        ".check", ".clrcheck", ".reloc", ".clrreloc", ".map", ".free",
        ".passthru", ".eol", ".textmode", ".enum", ".clrenum", ".error",
        ".elftype", ".elfmachine", ".elfclass", ".elfrela", ".elfwidth",
        ".elfextern", ".elfdwarf", ".elfheader", ".elfsection", ".echo", ".elffield",
        ".elfpcguess", ".elfbuiltin", ".elfextra", ".elfdiff", ".elfencode",
        ".elfrinfo", ".elfunit", ".elflink", ".elfgroup", ".elfcfi", ".elfcfiinit",
        ".elfcfireg", ".unordered", NULL };
    if(!e || !e->f[0] || !e->f[0][0]) return 0;
    const char *n = e->f[0];
    for(int k=0; tbl[k]; k++) if(strcmp(n, tbl[k]) == 0) return 1;
    if(n[0] && n[1] && n[2] && n[3] && !n[4]){
        static const char epic[] = "EPIC";
        int k = 0;
        for(; k < 4; k++){
            char c = n[k];
            if(c >= 'a' && c <= 'z') c = (char)(c - 'a' + 'A');
            if(c != epic[k]) break;
        }
        if(k == 4) return 1;
    }
    return 0;
}

/* 欄が定数式だけで出来ているか（持ち上げの判定に使う）。 */
static int const_setsym_text(const char *s){
    if(!s || !s[0]) return 0;
    int ok = 1;
    for(const char *p=s; *p; p++){
        if(isdigit((unsigned char)*p)) continue;
        if(isspace((unsigned char)*p)) continue;
        if(strchr("+-*/%()<>|&^~", *p)) continue;
        ok = 0; break;
    }
    if(ok) return 1;
    const char *p = s;
    while(isspace((unsigned char)*p)) p++;
    if(!(p[0]=='0' && (p[1]=='x'||p[1]=='X') && isxdigit((unsigned char)p[2]))) return 0;
    p += 2;
    while(isxdigit((unsigned char)*p)) p++;
    while(isspace((unsigned char)*p)) p++;
    return *p == '\0';
}

/* 欄がただの数値か。 */
static int plain_number_text(const char *s){
    if(!s) return 0;
    const char *p = s;
    while(*p==' '||*p=='\t') p++;
    int n = 0;
    if(p[0]=='0' && (p[1]=='x'||p[1]=='X')){
        p += 2;
        while(isxdigit((unsigned char)*p)){ p++; n++; }
    } else {
        while(isdigit((unsigned char)*p)){ p++; n++; }
    }
    if(n == 0) return 0;
    while(*p==' '||*p=='\t') p++;
    return *p == '\0';
}

typedef struct { int is_str; char *text; } EchoItem;

static const char *echo_str_unescape(const char *s, int n, char **out,
                                     char *eb, size_t ebsz){
    char *d = malloc((size_t)n + 1);
    if(!d){ perror("malloc"); exit(1); }
    int w = 0;
    for(int k = 0; k < n; k++){
        char c = s[k];
        if(c == '\\'){
            if(k + 1 >= n){ free(d); return "dangling '\\' in a string"; }
            char e = s[k+1], v;
            if(e == '\\')      v = '\\';
            else if(e == '"')  v = '"';
            else if(e == 'n')  v = '\n';
            else if(e == 't')  v = '\t';
            else {
                snprintf(eb, ebsz, "unknown escape '\\%c' in a string", e);
                free(d);
                return eb;
            }
            d[w++] = v;
            k++;
            continue;
        }
        d[w++] = c;
    }
    d[w] = 0;
    *out = d;
    return NULL;
}

/* `.echo` の解析結果を解放する。 */
static void echo_items_free(EchoItem *v, int n){
    for(int k = 0; k < n; k++) free(v[k].text);
    free(v);
}

static const char *echo_items_parse(const char *text, EchoItem **outv, int *outn,
                                    char *eb, size_t ebsz){
    *outv = NULL;
    *outn = 0;
    int n = (int)strlen(text);
    int i = 0;
    while(i < n && (text[i]==' ' || text[i]=='\t')) i++;
    if(i >= n || text[i] != '(') return "needs '.echo(item, item, ...)'";
    i++;
    int start = i, end = -1, depth = 0, instr = 0;
    while(i < n){
        char c = text[i];
        if(instr){
            if(c == '\\'){ i += 2; continue; }
            if(c == '"') instr = 0;
            i++;
            continue;
        }
        if(c == '"') instr = 1;
        else if(c=='(' || c=='[' || c=='{') depth++;
        else if(c==')' || c==']' || c=='}'){
            if(depth == 0 && c == ')'){ end = i; break; }
            if(depth > 0) depth--;
        }
        i++;
    }
    if(end < 0) return "missing ')'";
    for(const char *q = text + end + 1; *q; q++)
        if(*q != ' ' && *q != '\t') return "unexpected text after '.echo(...)'";

    const char *inner = text + start;
    int m = end - start;
    int cap = 8, cnt = 0;
    int *ps = malloc((size_t)cap * sizeof(int));
    int *pl = malloc((size_t)cap * sizeof(int));
    if(!ps || !pl){ perror("malloc"); exit(1); }
    int bs = 0;
    depth = 0; instr = 0;
    for(int k = 0; k <= m; ){
        if(k == m || (!instr && depth == 0 && inner[k] == ',')){
            if(cnt == cap){
                cap *= 2;
                ps = realloc(ps, (size_t)cap * sizeof(int));
                pl = realloc(pl, (size_t)cap * sizeof(int));
                if(!ps || !pl){ perror("realloc"); exit(1); }
            }
            ps[cnt] = bs;
            pl[cnt] = k - bs;
            cnt++;
            if(k == m) break;
            bs = k + 1;
            k++;
            continue;
        }
        char c = inner[k];
        if(instr){
            if(c == '\\' && k + 1 < m){ k += 2; continue; }
            if(c == '"') instr = 0;
            k++;
            continue;
        }
        if(c == '"') instr = 1;
        else if(c=='(' || c=='[' || c=='{') depth++;
        else if(c==')' || c==']' || c=='}'){ if(depth > 0) depth--; }
        k++;
    }

    if(cnt == 1){
        int a = ps[0], b = ps[0] + pl[0];
        while(a < b && (inner[a]==' ' || inner[a]=='\t')) a++;
        if(a == b){ free(ps); free(pl); return NULL; }
    }

    EchoItem *items = malloc((size_t)cnt * sizeof(EchoItem));
    if(!items){ perror("malloc"); exit(1); }
    int ni = 0;
    const char *err = NULL;
    for(int t = 0; t < cnt; t++){
        int a = ps[t], b = ps[t] + pl[t];
        while(a < b && (inner[a]==' ' || inner[a]=='\t')) a++;
        while(b > a && (inner[b-1]==' ' || inner[b-1]=='\t')) b--;
        if(a == b){ err = "empty item in the argument list"; break; }
        if(inner[a] == '"'){
            int j = a + 1;
            while(j < b){
                if(inner[j] == '\\'){ j += 2; continue; }
                if(inner[j] == '"') break;
                j++;
            }
            if(j >= b){
                snprintf(eb, ebsz, "unterminated string: '%.*s'", b - a, inner + a);
                err = eb;
                break;
            }
            if(j != b - 1){
                snprintf(eb, ebsz, "unexpected text after a string: '%.*s'", b - a, inner + a);
                err = eb;
                break;
            }
            char *sv = NULL;
            const char *e2 = echo_str_unescape(inner + a + 1, j - a - 1, &sv, eb, ebsz);
            if(e2){ err = e2; break; }
            items[ni].is_str = 1;
            items[ni].text   = sv;
            ni++;
        } else {
            char *sv = malloc((size_t)(b - a) + 1);
            if(!sv){ perror("malloc"); exit(1); }
            memcpy(sv, inner + a, (size_t)(b - a));
            sv[b - a] = 0;
            items[ni].is_str = 0;
            items[ni].text   = sv;
            ni++;
        }
    }
    free(ps);
    free(pl);
    if(err){ echo_items_free(items, ni); return err; }
    *outv = items;
    *outn = ni;
    return NULL;
}

/* 各パターン行が「ソース行ごとに変わらない」かを先に印付けする。
   変わらない行は解釈し直さずに済む。 */
static void pat_mark_static(PatVec *v){
    for(int pi=0; pi<v->len; pi++){
        PatEntry *e = &v->data[pi];
        e->is_dir       = pat_is_directive(e);
        e->dir_kind     = e->is_dir ? pat_dir_kind(e) : PD_NONE;
        e->setsym_const = (e->is_dir && strcmp(e->f[0], ".setsym") == 0
                           && e->f[1] && e->f[1][0]
                           && const_setsym_text(e->f[2]));
        e->setsym_done  = 0;
        e->setsym_val   = u256_zero();
        e->elftype_done = 0;
        e->elftype_val  = 0;
        e->elftype_wid  = 0;
        e->elftype_pcr  = 0;
        e->chk_cache    = NULL;
        e->chk_cache_gen = -1;
        free(e->setsym_key);
        e->setsym_key   = NULL;
        e->setsym_plain = (e->is_dir && e->dir_kind == PD_SETSYM
                           && e->f[1] && e->f[1][0]
                           && plain_number_text(e->f[2]));
        if(e->setsym_plain){
            size_t kl = strlen(e->f[1]) + 1;
            e->setsym_key = malloc(kl);
            if(!e->setsym_key){ perror("malloc"); exit(1); }
            for(size_t ki=0; ki<kl; ki++){
                char c = e->f[1][ki];
                e->setsym_key[ki] = (c>='a'&&c<='z') ? (char)(c-32) : c;
            }
        }

        {
            const char *q = e->f[0] ? e->f[0] : "";
            int np = 0;
            for(; *q && np < (int)sizeof(e->pfx)-1; q++){
                if(*q >= 'A' && *q <= 'Z') e->pfx[np++] = *q;
                else if(*q == ' ') continue;
                else break;
            }
            e->pfx[np]  = '\0';
            e->pfxlen   = np;
            int closed = 1;
            if(np >= (int)sizeof(e->pfx)-1){
                closed = 0;
            } else if(*q){
                char c = *q;
                if((c >= 'a' && c <= 'z') || (c >= '0' && c <= '9')
                   || c == '!' || c == '\\' || c == '[') closed = 0;
            }
            e->pfx_closed = closed;
        }
    }
}

static int g_hoist_rows     = 0;
static int g_hoist_first_ai = 0;
static int g_hoist_bits     = 0;
static int g_hoist_padding  = 0;
static int g_hoist_symbolc  = 0;
static int g_hoist_vliw     = 0;

typedef struct { int *rows; int n, cap; } PatRowList;

/* `.unordered` の宣言があったか、そのときディレクティブ行を処理する順
   （pat_unordered_plan() が決める）。 */
static int        g_unordered = 0;
static PatRowList g_dirorder;

/* パターン行番号のリストに 1 個積む。 */
static void prl_push(PatRowList *l, int row){
    if(l->n >= l->cap){
        l->cap = l->cap ? l->cap*2 : 8;
        l->rows = realloc(l->rows, (size_t)l->cap * sizeof(int));
        if(!l->rows){ perror("realloc"); exit(1); }
    }
    l->rows[l->n++] = row;
}

typedef struct PatIdxNode {
    char       key[64];
    PatRowList open;
    PatRowList closed;
    struct PatIdxNode *next;
} PatIdxNode;

#define PATIDX_NB 1024
typedef struct {
    PatIdxNode *buckets[PATIDX_NB];
    PatRowList  always;
    int         maxkeylen;
    int        *cand;
    int         cand_cap;
} PatIndex;

static PatIndex g_patidx;

/* ---- パターン索引 -------------------------------------------------------
   照合は全パターンを試して最良のものを選ぶ方式なので、素直に書くと 1 行あたり
   全件走査になる。ニーモニック先頭の大文字列を鍵にして候補を絞る。
   鍵のどれにも属さない行（先頭が大文字でない書式とディレクティブ）だけは
   always として常に試すので、絞っても結果は変わらない。
   ------------------------------------------------------------------------ */
static uint32_t patidx_hash(const char *k, int n){
    uint32_t h = 2166136261u;
    for(int i=0;i<n;i++){ h ^= (unsigned char)k[i]; h *= 16777619u; }
    return h;
}

/* 鍵に対応する索引の節を引く（create なら作る）。 */
static PatIdxNode *patidx_node(PatIndex *ix, const char *k, int n, int create){
    uint32_t b = patidx_hash(k,n) & (PATIDX_NB-1);
    for(PatIdxNode *p=ix->buckets[b]; p; p=p->next)
        if((int)strlen(p->key)==n && memcmp(p->key,k,(size_t)n)==0) return p;
    if(!create) return NULL;
    PatIdxNode *p = calloc(1, sizeof(*p));
    if(!p){ perror("calloc"); exit(1); }
    memcpy(p->key,k,(size_t)n); p->key[n]='\0';
    p->next = ix->buckets[b]; ix->buckets[b] = p;
    return p;
}

/* パターン表から索引を作る。 */
static void patidx_build(PatIndex *ix, PatVec *v){
    for(int pi=0; pi<v->len; pi++){
        PatEntry *e = &v->data[pi];
        if(e->is_dir && g_unordered) continue;
        if(e->pfxlen == 0 || e->is_dir){ prl_push(&ix->always, pi); continue; }
        PatIdxNode *nd = patidx_node(ix, e->pfx, e->pfxlen, 1);
        prl_push(e->pfx_closed ? &nd->closed : &nd->open, pi);
        if(e->pfxlen > ix->maxkeylen) ix->maxkeylen = e->pfxlen;
    }
    g_hoist_first_ai = 0;
    while(g_hoist_first_ai < ix->always.n
          && ix->always.rows[g_hoist_first_ai] < g_hoist_rows) g_hoist_first_ai++;
}

/* 候補の行番号を昇順に並べるための比較関数。 */
static int patidx_cmp_int(const void *a, const void *b){
    int x = *(const int*)a, y = *(const int*)b;
    return (x>y) - (x<y);
}

/* ソース行 1 行に対して、照合を試す価値のある行番号を返す。
   鍵を 1 文字ずつ伸ばして引く。ニーモニックがそこで終わっている書式は、
   ソース側の次の文字が語を続ける文字でないときだけ候補にする。これを外すと
   `ADD` のパターンが `ADDS` の行に当たってしまう。 */
static int patidx_candidates(PatIndex *ix, const char *lin, int **out){
    char key[64];
    char nextraw[65];
    int  n = 0;
    int  lim = ix->maxkeylen < (int)sizeof(key) ? ix->maxkeylen : (int)sizeof(key)-1;
    for(const char *q=lin; *q && n<lim; q++){
        if(*q == ' ') continue;
        key[n]     = (*q >= 'a' && *q <= 'z') ? (char)(*q - 32) : *q;
        nextraw[n] = q[1];
        n++;
    }
    int cnt = 0;
    for(int k=1; k<=n; k++){
        PatIdxNode *nd = patidx_node(ix, key, k, 0);
        if(!nd) continue;
        char nx = nextraw[k-1];
        int take_closed = !((nx>='A'&&nx<='Z')||(nx>='a'&&nx<='z')
                            ||(nx>='0'&&nx<='9')||nx=='_');
        int need = cnt + nd->open.n + (take_closed ? nd->closed.n : 0);
        if(need > ix->cand_cap){
            ix->cand_cap = need*2;
            ix->cand = realloc(ix->cand, (size_t)ix->cand_cap * sizeof(int));
            if(!ix->cand){ perror("realloc"); exit(1); }
        }
        for(int j=0;j<nd->open.n;j++) ix->cand[cnt++] = nd->open.rows[j];
        if(take_closed)
            for(int j=0;j<nd->closed.n;j++) ix->cand[cnt++] = nd->closed.rows[j];
    }
    if(cnt > 1) qsort(ix->cand, (size_t)cnt, sizeof(int), patidx_cmp_int);
    *out = ix->cand;
    return cnt;
}

/* パターン行が空か。 */
static int pat_row_blank(const PatEntry *e){
    for(int i=0;i<PAT_FIELDS;i++) if(e->f[i][0]) return 0;
    return 1;
}

/* 欄の中身がソース行ごとに変わりうるか。 */
static int pat_text_dynamic(const char *s){
    for(const char *p=s; *p; p++){
        if(*p=='!' || *p=='$' || *p=='#' || *p=='@' || *p=='\'') return 1;
        if(*p>='a' && *p<='z') return 1;
    }
    return 0;
}

/* 欄が「大文字の名前をカンマで並べたもの」か。 */
static int pat_is_name_list(const char *s){
    int comma = 0;
    for(const char *p=s; *p; p++){
        if(*p==','){ comma = 1; continue; }
        if(*p==' ' || *p=='\t') continue;
        if((*p>='A'&&*p<='Z')||(*p>='0'&&*p<='9')||*p=='_') continue;
        return 0;
    }
    return comma;
}

/* `.bits` の欄が定数か。 */
static int pat_bits_field_static(const char *f){
    if(strcasecmp(f,"big")==0 || strcasecmp(f,"little")==0) return 1;
    return const_setsym_text(f);
}

/* このディレクティブ行を、ソースを読む前に 1 回だけ処理してよいか。
   判断に迷うものは必ず偽を返す（持ち上げないだけで結果は変わらない）。 */
static int pat_dir_line_invariant(const PatEntry *e){
    switch(e->dir_kind){
    case PD_SETSYM: {
        const char *name = e->f[1][0] ? e->f[1] : e->f[2];
        const char *val  = e->f[1][0] ? e->f[2] : "";
        if(pat_text_dynamic(name)) return 0;
        if(!val[0]) return 1;
        { const char *q = val;
          while(*q==' '||*q=='\t') q++;
          if(*q=='"') return 1;
          if(*q=='[') return 0;
        }
        if(const_setsym_text(val)) return 1;
        return pat_is_name_list(val);
    }
    case PD_CHECK: case PD_CLRCHECK: case PD_RELOC: case PD_CLRRELOC:
    case PD_SYMBOLC: case PD_PASSTHRU: case PD_EOL: case PD_TEXTMODE:
    case PD_ELFMACHINE: case PD_ELFCLASS: case PD_ELFRELA: case PD_ELFWIDTH:
    case PD_ELFEXTERN: case PD_ELFDWARF: case PD_ELFHEADER:
    case PD_ELFSECTION: case PD_ELFFIELD: case PD_ELFPCGUESS: case PD_ELFBUILTIN:
    case PD_ELFEXTRA: case PD_ELFDIFF: case PD_ELFENCODE: case PD_ELFRINFO:
    case PD_ELFUNIT: case PD_ELFLINK: case PD_ELFGROUP: case PD_ELFCFI:
    case PD_ELFCFIINIT: case PD_ELFCFIREG:
        for(int i=1;i<PAT_FIELDS;i++)
            for(const char *q=e->f[i]; *q; q++)
                if(*q=='!' || *q=='$' || *q=='#' || *q=='@') return 0;
        return 1;
    case PD_BITS:
        for(int i=1;i<PAT_FIELDS;i++)
            if(e->f[i][0] && !pat_bits_field_static(e->f[i])) return 0;
        return 1;
    case PD_PADDING: case PD_VLIW:
        for(int i=1;i<PAT_FIELDS;i++)
            if(e->f[i][0] && !const_setsym_text(e->f[i])) return 0;
        return 1;
    case PD_ERRMSG: {
        if(!const_setsym_text(e->f[1])) return 0;
        const char *q = e->f[2];
        while(*q==' '||*q=='\t') q++;
        return *q=='"';
    }
    case PD_ELFTYPE:
        if(!e->f[1][0]) return 0;
        for(const char *q=e->f[1]; *q; q++)
            if(*q=='!' || *q=='$' || *q=='#' || *q=='@' || *q=='\'') return 0;
        for(int i=3;i<PAT_FIELDS;i++)
            if(e->f[i][0] && !const_setsym_text(e->f[i])) return 0;
        return const_setsym_text(e->f[2]);
    default:
        return 0;
    }
}

/* 先頭から何行を事前処理に持ち上げられるかを数える。
   持ち上げた範囲が読んでいる名前を、あとの行の `.setsym` / `.clearsym` /
   `.free` が書き換えている場合は、順序依存が壊れるので諦める。 */
static void pat_hoist_scan(PatVec *v){
    g_hoist_rows = 0;
    g_hoist_bits = g_hoist_padding = g_hoist_symbolc = g_hoist_vliw = 0;
    int h = 0;
    int f_bits=0, f_padding=0, f_symbolc=0, f_vliw=0;
    for(; h < v->len; h++){
        PatEntry *e = &v->data[h];
        if(pat_row_blank(e)) continue;
        if(!e->is_dir) break;
        if(!pat_dir_line_invariant(e)) break;
        switch(e->dir_kind){
        case PD_BITS:    f_bits = 1;    break;
        case PD_PADDING: f_padding = 1; break;
        case PD_SYMBOLC: f_symbolc = 1; break;
        case PD_VLIW:    f_vliw = 1;    break;
        default: break;
        }
    }
    if(h <= 0 || h >= v->len) return;

    StrVec reads; sv_init(&reads);
    for(int i = 0; i < h; i++){
        PatEntry *e = &v->data[i];
        for(int fi = 1; fi < PAT_FIELDS; fi++){
            const char *q = e->f[fi];
            while(*q){
                if((*q>='A'&&*q<='Z')||(*q>='0'&&*q<='9')||*q=='_'){
                    char tok[256]; int n = 0;
                    while(((*q>='A'&&*q<='Z')||(*q>='0'&&*q<='9')||*q=='_')
                          && n < (int)sizeof(tok)-1) tok[n++] = *q++;
                    tok[n] = '\0';
                    int dup = 0;
                    for(int k=0;k<reads.len;k++) if(strcmp(reads.data[k],tok)==0){ dup=1; break; }
                    if(!dup) sv_push(&reads, tok);
                } else q++;
            }
        }
    }

    int blocked = 0;
    for(int i = h; i < v->len && !blocked; i++){
        PatEntry *e = &v->data[i];
        if(!e->is_dir) continue;
        const char *wname = NULL;
        if(e->dir_kind == PD_SETSYM){
            if(!e->f[1][0]){ blocked = 1; break; }
            if(const_setsym_text(e->f[2])) continue;
            wname = e->f[1];
        } else if(e->dir_kind == PD_CLEARSYM){
            wname = e->f[2][0] ? e->f[2] : e->f[1];
            if(!wname[0]){ blocked = 1; break; }
        } else if(e->dir_kind == PD_FREE){
            wname = e->f[2][0] ? e->f[2] : e->f[1];
            if(!wname[0]){ blocked = 1; break; }
        } else continue;
        char up[256]; int un = 0;
        for(const char *q = wname; *q && un < (int)sizeof(up)-1; q++)
            up[un++] = (*q>='a'&&*q<='z') ? (char)(*q-32) : *q;
        up[un] = '\0';
        for(int k=0;k<reads.len;k++)
            if(strcmp(reads.data[k], up)==0){ blocked = 1; break; }
    }
    sv_free(&reads);
    if(blocked) return;
    g_hoist_rows    = h;
    g_hoist_bits    = f_bits;
    g_hoist_padding = f_padding;
    g_hoist_symbolc = f_symbolc;
    g_hoist_vliw    = f_vliw;
}

/* ---- `.unordered` --------------------------------------------------------
   宣言があれば、すべてのディレクティブがファイル全体に効くので、パターン
   より先に 1 度ずつ処理する。その順は
     1. 設定もの（.unordered .symbolc .bits .padding .vliw .passthru .eol
        .textmode と EPIC）
     2. .setsym — 値が別の .setsym の名前を読むなら、その定義を先に
     3. その他（.check .map .enum .reloc .error ELF の表など）
   で、各組の中は書かれた順。同じ名前・同じ変数への中身の違う定義と、
   位置の意味しか持たないディレクティブ（.clearsym .clrcheck .clrenum
   .clrreloc .free）はエラーにする。axx.py の _pat_unordered_plan() と
   同じ規則である。
   ------------------------------------------------------------------------ */
/* 欄の前後の空白を除いた写しを作る（呼び出し側が free する）。 */
static char *unord_trim_dup(const char *s){
    while(*s==' '||*s=='\t') s++;
    size_t n = strlen(s);
    while(n > 0 && (s[n-1]==' '||s[n-1]=='\t')) n--;
    char *r = malloc(n + 1);
    if(!r){ perror("malloc"); exit(1); }
    memcpy(r, s, n); r[n] = '\0';
    return r;
}

/* ASCII の小文字を大文字にする（その場で）。 */
static void unord_upper(char *s){
    for(; *s; s++) if(*s >= 'a' && *s <= 'z') *s = (char)(*s - 32);
}

/* `.setsym` が定義する名前（大文字、free する）。 */
static char *unord_setsym_name(const PatEntry *e){
    char *r = unord_trim_dup(e->f[1][0] ? e->f[1] : e->f[2]);
    unord_upper(r);
    return r;
}

/* 重複検査の鍵とエラーで名指す言い方を作る。鍵を持たなければ 0 を返す。 */
static int unord_key(const PatEntry *e, char *key, size_t ksz, char *label, size_t lsz){
    const char *name = e->f[0];
    switch(e->dir_kind){
    case PD_SETSYM: {
        char *up = unord_setsym_name(e);
        snprintf(key, ksz, ".setsym %s", up);
        snprintf(label, lsz, "symbol '%s'", up);
        free(up);
        return 1;
    }
    case PD_CHECK: case PD_MAP: case PD_ENUM: case PD_RELOC: {
        char *t1 = unord_trim_dup(e->f[1]);
        char *var = t1[0] ? t1 : unord_trim_dup(e->f[2]);
        for(char *q = var; *q; q++) *q = (char)tolower((unsigned char)*q);
        int chk = (e->dir_kind == PD_CHECK || e->dir_kind == PD_MAP);
        snprintf(key, ksz, "%s %s", chk ? "check" : name + 1, var);
        snprintf(label, lsz, "variable '%s' (%s)", var, chk ? ".check/.map" : name);
        if(var != t1) free(var);
        free(t1);
        return 1;
    }
    case PD_ERRMSG: {
        char *code = unord_trim_dup(e->f[1]);
        snprintf(key, ksz, ".error %s", code);
        snprintf(label, lsz, "error code %s", code);
        free(code);
        return 1;
    }
    case PD_SYMBOLC: case PD_BITS: case PD_PADDING: case PD_VLIW:
    case PD_PASSTHRU: case PD_EOL: case PD_TEXTMODE:
        snprintf(key, ksz, "%s", name);
        snprintf(label, lsz, "'%s'", name);
        return 1;
    case PD_EPIC:
        snprintf(key, ksz, "EPIC");
        snprintf(label, lsz, "'EPIC'");
        return 1;
    default:
        return 0;
    }
}

/* 重複検査で比べる中身。各欄の前後の空白を除いて `::` でつなぐ。 */
static char *unord_text(const PatEntry *e){
    size_t n = 1;
    for(int fi = 0; fi < PAT_FIELDS; fi++) n += strlen(e->f[fi]) + 2;
    char *r = malloc(n);
    if(!r){ perror("malloc"); exit(1); }
    r[0] = '\0';
    for(int fi = 0; fi < PAT_FIELDS; fi++){
        char *t = unord_trim_dup(e->f[fi]);
        if(fi) strcat(r, "::");
        strcat(r, t);
        free(t);
    }
    return r;
}

/* 行 pi の `.setsym` の値欄が、名前 nm（大文字）を読んでいるか。
   文字・数字・`_` の連なりを 1 語とし、`"..."` の中は読まない。 */
static int unord_reads(const PatEntry *e, const char *nm){
    const char *t = e->f[1][0] ? e->f[2] : "";
    size_t nl = strlen(nm);
    const char *q = t;
    while(*q){
        if(*q == '"'){
            q++;
            while(*q && *q != '"'){
                if(*q == '\\' && q[1]) q += 2; else q++;
            }
            if(*q) q++;
            continue;
        }
        unsigned char c = (unsigned char)*q;
        if(c < 128 && (isalnum(c) || c == '_')){
            const char *b = q;
            while(*q && (unsigned char)*q < 128
                  && (isalnum((unsigned char)*q) || *q == '_')) q++;
            if((size_t)(q - b) == nl){
                size_t k = 0;
                for(; k < nl; k++){
                    char ch = b[k];
                    if(ch >= 'a' && ch <= 'z') ch = (char)(ch - 32);
                    if(ch != nm[k]) break;
                }
                if(k == nl) return 1;
            }
            continue;
        }
        q++;
    }
    return 0;
}

/* `.unordered` の宣言があれば g_unordered を立て、g_dirorder を決める。 */
static void pat_unordered_plan(PatVec *v){
    g_unordered = 0;
    g_dirorder.n = 0;
    for(int pi = 0; pi < v->len; pi++)
        if(v->data[pi].is_dir && v->data[pi].dir_kind == PD_UNORDERED){ g_unordered = 1; break; }
    if(!g_unordered) return;

    PatRowList first = {0}, syms = {0}, rest = {0};
    StrVec keys; sv_init(&keys);
    StrVec texts; sv_init(&texts);
    PatRowList keyrows = {0};
    for(int pi = 0; pi < v->len; pi++){
        PatEntry *e = &v->data[pi];
        if(!e->is_dir) continue;
        int k = e->dir_kind;
        if(k == PD_CLEARSYM || k == PD_CLRCHECK || k == PD_CLRENUM
           || k == PD_CLRRELOC || k == PD_FREE)
            axx_diagf(1, 0, " error - %s: cannot be used in an .unordered pattern file "
                            "(pattern line %d); there every definition holds for the "
                            "whole file.\n", e->f[0], pi + 1);
        char key[600], label[600];
        if(unord_key(e, key, sizeof(key), label, sizeof(label))){
            char *text = unord_text(e);
            int found = -1;
            for(int j = 0; j < keys.len; j++)
                if(strcmp(keys.data[j], key) == 0){ found = j; break; }
            if(found < 0){
                sv_push(&keys, key);
                sv_push(&texts, text);
                prl_push(&keyrows, pi);
            } else if(strcmp(texts.data[found], text) != 0){
                axx_diagf(1, 0, " error - .unordered: pattern lines %d and %d "
                                "give %s two different definitions.\n",
                          keyrows.rows[found] + 1, pi + 1, label);
            }
            free(text);
        }
        if(k == PD_UNORDERED || k == PD_SYMBOLC || k == PD_BITS || k == PD_PADDING
           || k == PD_VLIW || k == PD_PASSTHRU || k == PD_EOL || k == PD_TEXTMODE
           || k == PD_EPIC)
            prl_push(&first, pi);
        else if(k == PD_SETSYM)
            prl_push(&syms, pi);
        else
            prl_push(&rest, pi);
    }
    for(int j = 0; j < keys.len; j++){ free(keys.data[j]); free(texts.data[j]); }
    free(keys.data); free(texts.data); free(keyrows.rows);

    /* .setsym の依存。deps[a*n+b] が真なら a は b の定義を先に要る。
       同じ名前の定義が複数あるときは最初のものを定義元とする。 */
    int n = syms.n;
    char **names = calloc((size_t)(n ? n : 1), sizeof(char*));
    unsigned char *deps = calloc((size_t)(n ? n : 1) * (size_t)(n ? n : 1), 1);
    unsigned char *done = calloc((size_t)(n ? n : 1), 1);
    if(!names || !deps || !done){ perror("calloc"); exit(1); }
    for(int a = 0; a < n; a++) names[a] = unord_setsym_name(&v->data[syms.rows[a]]);
    for(int b = 0; b < n; b++){
        int first_def = 1;
        for(int c = 0; c < b; c++) if(strcmp(names[c], names[b]) == 0){ first_def = 0; break; }
        if(!first_def) continue;
        for(int a = 0; a < n; a++)
            if(a != b && unord_reads(&v->data[syms.rows[a]], names[b]))
                deps[(size_t)a * (size_t)n + (size_t)b] = 1;
    }
    for(int r = 0; r < first.n; r++) prl_push(&g_dirorder, first.rows[r]);
    int left = n;
    while(left > 0){
        int nxt = -1;
        for(int a = 0; a < n && nxt < 0; a++){
            if(done[a]) continue;
            int ok = 1;
            for(int b = 0; b < n; b++)
                if(deps[(size_t)a * (size_t)n + (size_t)b] && !done[b]){ ok = 0; break; }
            if(ok) nxt = a;
        }
        if(nxt < 0){
            size_t cap = 64;
            for(int a = 0; a < n; a++) if(!done[a]) cap += strlen(names[a]) + 4;
            char *lst = malloc(cap);
            if(!lst){ perror("malloc"); exit(1); }
            lst[0] = '\0';
            int firstn = 1;
            for(int a = 0; a < n; a++){
                if(done[a]) continue;
                if(!firstn) strcat(lst, ", ");
                strcat(lst, "'"); strcat(lst, names[a]); strcat(lst, "'");
                firstn = 0;
            }
            axx_diagf(1, 0, " error - .unordered: the .setsym definitions of %s refer to "
                            "each other in a cycle.\n", lst);
            free(lst);
            for(int a = 0; a < n; a++)
                if(!done[a]){ prl_push(&g_dirorder, syms.rows[a]); done[a] = 1; }
            break;
        }
        prl_push(&g_dirorder, syms.rows[nxt]);
        done[nxt] = 1;
        left--;
    }
    for(int r = 0; r < rest.n; r++) prl_push(&g_dirorder, rest.rows[r]);
    for(int a = 0; a < n; a++) free(names[a]);
    free(names); free(deps); free(done);
    free(first.rows); free(syms.rows); free(rest.rows);

    g_hoist_rows = 0;
    g_hoist_bits = g_hoist_padding = g_hoist_symbolc = g_hoist_vliw = 0;
}

/* パターン表に空の行を 1 つ足す。 */
static PatEntry *pv_push_blank(PatVec*v){
    if(v->len>=v->cap){v->cap=v->cap?v->cap*2:32;v->data=realloc(v->data,v->cap*sizeof(PatEntry));if(!v->data){perror("realloc");exit(1);}}
    PatEntry *e=&v->data[v->len++];
    memset(e, 0, sizeof(*e));
    for(int i=0;i<PAT_FIELDS;i++) e->f[i]=strdup("");
    return e;
}
/* パターン表を解放する（現在は未使用）。 */
static AXX_UNUSED void pv_free(PatVec*v){
    for(int i=0;i<v->len;i++) for(int j=0;j<PAT_FIELDS;j++) free(v->data[i].f[j]);
    free(v->data); pv_init(v);
}
/* パターン行の idx 番目の欄を設定する。 */
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
/* `EPIC::` の宣言を解放する（現在は未使用）。 */
static AXX_UNUSED void vset_free(VliwSet*v){
    for(int i=0;i<v->len;i++){free(v->data[i].idxs);free(v->data[i].templ);}
    free(v->data);vset_init(v);
}
/* `EPIC::` の宣言を空にする。 */
static void vset_clear(VliwSet*v){
    for(int i=0;i<v->len;i++){free(v->data[i].idxs);free(v->data[i].templ);}
    v->len=0;
}
/* `EPIC::` の宣言を 1 つ足す。インデックスコードの並びとテンプレート。 */
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

typedef struct BufEntry { uint64_t pos; uint64_t val; struct BufEntry*next; } BufEntry;
#define BUFMAP_NB 4096
typedef struct { BufEntry *buckets[BUFMAP_NB]; } BufMap;

static void bufmap_init(BufMap*m){ memset(m->buckets,0,sizeof(m->buckets)); }
/* 出力ワードの置き場。連続した配列ではなく「位置 → ワード」の表なのは、
   `.org` でいくらでも飛べるため。隙間は書き出すときに `.padding` で埋める。 */
static void bufmap_set(BufMap*m, uint64_t pos, uint64_t val){
    uint32_t h=(uint32_t)(pos % BUFMAP_NB);
    for(BufEntry*e=m->buckets[h];e;e=e->next) if(e->pos==pos){e->val=val;return;}
    BufEntry*e=malloc(sizeof(BufEntry)); if(!e){perror("malloc");exit(1);} e->pos=pos; e->val=val;
    e->next=m->buckets[h]; m->buckets[h]=e;
}
/* 書かれた最大の位置。出力の大きさを決めるのに使う。 */
static uint64_t bufmap_max_key(BufMap*m, int *found_out){
    uint64_t mx=0; int found=0;
    for(int i=0;i<BUFMAP_NB;i++) for(BufEntry*e=m->buckets[i];e;e=e->next){
        if(!found||e->pos>mx){mx=e->pos;found=1;}
    }
    if(found_out) *found_out=found;
    return found?mx:0;
}
/* 出力バッファを解放する（現在は未使用）。 */
static AXX_UNUSED void bufmap_free(BufMap*m){
    for(int i=0;i<BUFMAP_NB;i++){BufEntry*e=m->buckets[i];while(e){BufEntry*n=e->next;free(e);e=n;}m->buckets[i]=NULL;}
}

#define OB_CHAR  ((char)0xFC)
#define CB_CHAR  ((char)0xFD)
/* `!S{{表}}変数` を展開したときに、差し込んだエントリのパターンの前後に置く
   印。どちらも直後の 1 文字が展開の段（'0' から）を表す。照合はこの印を
   読み飛ばしながら、ソース上の位置を覚えて変数の綴りにする。
   axx.py の SUB_OPEN / SUB_CLOSE と同じ。 */
#define SUB_OPEN_CHAR  ((char)0x1E)
#define SUB_CLOSE_CHAR ((char)0x1F)
#define VLIW_SEP_CHAR  ((char)0xFE)
#define VLIW_STOP_CHAR ((char)0xFF)
#define EXP_PAT  0
#define EXP_ASM  1

typedef struct {
    const char *name;
    int patvars;
    int vliw;
    int labels;
    int loc;
    int syms;
} ExprCaps;

static const ExprCaps CAPS_PAT  = { "pattern",       1, 1, 1, 1, 1 };
static const ExprCaps CAPS_ASM  = { "assembly",      0, 0, 1, 1, 1 };
static const ExprCaps CAPS_MINI = { "mini language", 0, 0, 1, 1, 1 };

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

typedef struct { char *file; long long *pcs; int len, cap; } MacroLinePcs;
typedef struct { MacroLinePcs *d; int len, cap; } MacroLinePcsVec;

/* マクロ層が読む「行ごとの PC」の記録。ソース側のマクロは `$` / `$$` を
   読めるが、見えるのは前回のリラクゼーション反復の値なので、反復ごとに
   ここへ記録して次の反復で引く。 */
static void mlp_vec_free(MacroLinePcsVec *v){
    for(int i=0;i<v->len;i++){ free(v->d[i].file); free(v->d[i].pcs); }
    free(v->d);
    v->d=NULL; v->len=v->cap=0;
}

/* そのファイルぶんの記録を始める。 */
static int mlp_begin(MacroLinePcsVec *v, const char *file){
    for(int i=0;i<v->len;i++){
        if(strcmp(v->d[i].file, file)==0){
            free(v->d[i].pcs);
            v->d[i].pcs=NULL; v->d[i].len=v->d[i].cap=0;
            return i;
        }
    }
    if(v->len >= v->cap){
        v->cap = v->cap ? v->cap*2 : 8;
        v->d = realloc(v->d, (size_t)v->cap * sizeof(v->d[0]));
        if(!v->d){ perror("realloc"); exit(1); }
    }
    MacroLinePcs *e = &v->d[v->len++];
    e->file = strdup(file ? file : "");
    if(!e->file){ perror("strdup"); exit(1); }
    e->pcs=NULL; e->len=e->cap=0;
    return v->len - 1;
}

/* 行 idx の PC を記録する。 */
static void mlp_push(MacroLinePcsVec *v, int idx, long long pc){
    if(idx < 0 || idx >= v->len) return;
    MacroLinePcs *e = &v->d[idx];
    if(e->len >= e->cap){
        e->cap = e->cap ? e->cap*2 : 64;
        e->pcs = realloc(e->pcs, (size_t)e->cap * sizeof(e->pcs[0]));
        if(!e->pcs){ perror("realloc"); exit(1); }
    }
    e->pcs[e->len++] = pc;
}

/* 記録した PC を引く。 */
static long long mlp_get(const MacroLinePcsVec *v, const char *file, int idx){
    if(!file || idx < 0) return 0;
    for(int i=0;i<v->len;i++)
        if(strcmp(v->d[i].file, file)==0)
            return (idx < v->d[i].len) ? v->d[i].pcs[idx] : 0;
    return 0;
}

enum { EHF_TYPE = 0, EHF_FLAGS, EHF_VERSION, EHF_ENTRY, EHF_OSABI,
       EHF_ABIVERSION, ELF_HDR_NFIELD };

/* ソースの `.cfi_*` 指令 1 つ（位置はセクション先頭からのワード数）と、
   `.cfi_startproc` から `.cfi_endproc` までの 1 関数ぶん。axx.py の
   ElfState.cfi_fdes の要素と同じ中身。 */
typedef struct { int64_t off; char op[64]; int nv; int64_t *v; } CfiOp;
typedef struct {
    char   *sec;
    int64_t start, end;
    int     simple;
    CfiOp  *ops; int nops, cops;
    int     ra;
    int     signal;
    int     pers_enc; char *pers_sym;
    int     lsda_enc; char *lsda_sym;
} CfiFde;

typedef struct {
    /* コマンド行で与えたファイル名（argv をそのまま指す。長さの制限はない）。 */
    const char *outfile;
    const char *expfile;
    const char *expfile_elf;
    const char *impfile;
    uint256_t pc_overflow_max;
    int       pc_overflow_set;
    int  osabi;

    uint256_t pc;
    uint256_t padding;

    char lwordchars[256];
    char swordchars[256];

    char      *current_section;
    size_t     current_section_cap;
    char *current_file;       /* 読んでいるファイルの名前（set_current_file で書く） */

    LabelMap   labels;
    SecMap     sections;
    SymMap     symbols;
    SymMap     patsymbols;
    StrVec     strsym_names;
    /* ミニ言語で「綴り間違いの疑い」とした名前（mini_tick() を参照）。 */
    StrVec     mini_suspects;
    StrVec     strsym_vals;

    struct ArrSym *arrsyms;
    int        arrsyms_len;
    int        arrsyms_cap;
    LabelMap   export_labels;
    StrVec     export_order;
    PatVec     pat;
    SubVec     subs;
    MiniFuncVec funcs;

    int        vliwinstbits;
    IntVec     vliwnop;
    int        vliwbits;
    VliwSet    vliwset;
    int        vliwflag;
    int        vliwtemplatebits;
    int        vliwstop;
    int        vcnt;

    int        expmode;
    const ExprCaps *expcaps;
    int        exp_typ_float;

    int        error_undefined_label;

    StrVec     reported_label_errors;

    int        had_error;

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
    int        text_output;

    char      *asmtext;
    char      *asmtext_disp;

    int        passthru;
    int        eol;
    int        textmode;

    char       captext[8192];
    int        captext_len;

    char       label_text[512];

    char      *comment_text;

    char       indent_text[512];

    char       cl[4096];
    int        ln;
    StrVec     fnstack;
    IStack     lnstack;

    PatVar     vars[NVARS];

    char deb1[4096];
    char deb2[4096];

    BufMap     buf;

    int        pass1_size_mode;

    char       stdin_tmp_path[512];

    const char *elf_objfile;
    int        elf_machine;
    int        elf_class;

    int        gen_debug;
    struct { char *section; uint64_t word_pc; char *file; int line; } *line_map;
    int        line_map_len;
    int        line_map_cap;

    int        elf_tracking;
    struct { char *name; uint64_t val; int word_idx;
             int rtype; int64_t addend; } *elf_refs;
    int        elf_refs_len;
    int        elf_refs_cap;
    int        elf_current_word_idx;
    struct {
        int      set;
        char    *label_name;
        uint64_t label_val;
    }          elf_var_to_label[NVARS];
    int        elf_capturing_var;
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

    ChkList   *check_constraints[NVARS];
    /* `.unordered` のときだけ使う、変数ごとの名前と値の表（`.map` が作る）。 */
    SymMap    *var_tables[NVARS];
    int        reloc_constraints[NVARS];
    char      *reloc_badname[32];
    int        reloc_badname_len;

    struct { char *name; int rtype; int width; int pcrel; } *elftypes;
    int        elftypes_len, elftypes_cap;

    int        elf_decl_machine;
    char       elf_decl_name[64];
    int        elf_decl_class;
    int        elf_decl_rela;
    int        elf_decl_pcguess;
    int        elf_decl_builtin;
    /* `.elfextra` / `.elfdiff` / `.elfencode` / `.elfrinfo` / `.elfunit` /
       `.elflink` / `.elfgroup`。axx.py の ElfState の decl_* と同じ中身。 */
    struct { char *type; char *comp; int sym; } *elf_extras;
    int        elf_extras_len, elf_extras_cap;
    char      *elf_diff_add[9];
    char      *elf_diff_sub[9];
    struct { char *type; char *add; char *sub; } *elf_diff_t;
    int        elf_diff_t_len, elf_diff_t_cap;
    struct { char *type; char *fn; } *elf_encodes;
    int        elf_encodes_len, elf_encodes_cap;
    char      *elf_decl_rinfo;
    int        elf_decl_unit;
    /* CFI: `.elfcfi` の欄、`.elfcfiinit` の命令、`.elfcfireg` の名前、
       ソースの `.cfi_*` から集めた関数。 */
    int        elf_cfi_set, elf_cfi_ra, elf_cfi_code, elf_cfi_data, elf_cfi_pad;
    char     **elf_cfiinit; int elf_cfiinit_len, elf_cfiinit_cap;
    struct { char *name; int num; } *elf_cfireg; int elf_cfireg_len, elf_cfireg_cap;
    CfiFde    *cfi_fdes; int cfi_fdes_len, cfi_fdes_cap;
    CfiFde     cfi_curf; int cfi_open;
    struct { char *sec; char *link; char *info; } *elf_links;
    int        elf_links_len, elf_links_cap;
    struct { char *name; char *sig; uint32_t flags; char **mem; int nmem; } *elf_groups;
    int        elf_groups_len, elf_groups_cap;
    char      *elf_decl_width[9];
    char      *elf_decl_extern;
    char      *elf_decl_dwarf;
    int        elf_hdr_set[ELF_HDR_NFIELD];
    uint64_t   elf_hdr_val[ELF_HDR_NFIELD];

    struct { char *name; uint32_t flags; int type_set; uint32_t type;
             int al_set; uint32_t al; int es_set; uint32_t es; } *elf_secs;
    int        elf_secs_len, elf_secs_cap;
    struct { char *name; int stype; int size_set; uint64_t size;
             int other; int weak; int common; uint64_t calign; } *sym_attrs;
    int        sym_attrs_len, sym_attrs_cap;
    struct { char *type; uint64_t mask; int off; int shift; long long bias; } *elf_fields;
    int        elf_fields_len, elf_fields_cap;
    char     **extern_untyped;
    int        extern_untyped_len, extern_untyped_cap;
    int        elf_machine_from_cli;
    long       elf_decl_gen;

    EnumDef    enum_defs[NVARS];

    const StrVec    *enum_bind_names;
    const uint256_t *enum_bind_vals;

    StrVec     errors;

    int        expr_depth;

    LabelMap  *relax_prev;

    int        relax_optimistic;

    LabelMap   macro_labels;
    int        macro_labels_valid;

    MacroLinePcsVec macro_line_pcs;
    MacroLinePcsVec macro_line_pcs_cur;

    char      *pat_include_chain[64];
    int        pat_include_depth;

    char      *combo_budget_warned_file[64];
    int        combo_budget_warned_line[64];
    int        combo_budget_warned_count;

    SecRangeVec section_ranges;

    int        equ_section_tracking;
    /* `.EQU` の式が触れたセクション名の集合（重複なし）。axx.py の
       _equ_sections_touched と同じ。 */
    char     **equ_secs;
    int        equ_nsecs, equ_secs_cap;

    char     **diag_pending;
    int       *diag_pending_seterr;
    int        diag_pending_len;
    int        diag_pending_cap;
    int        diag_capturing;
} AsmState;

/* いま診断を出してよいパスか。パス2と対話モードだけ真。パス1は推定値で
   動いているので、そこで出る「範囲外」は本物とは限らない。 */
static inline int should_report_errors(const AsmState *st) {
    return st->pas == 2 || st->pas == 0;
}


static AsmState *g_active_state = NULL;

/* 照合の試行中の診断を溜める。その試行が採択されるとは限らないため。 */
static void diag_pending_push(AsmState *st, const char *text, int set_error){
    if(st->diag_pending_len >= st->diag_pending_cap){
        int nc = st->diag_pending_cap ? st->diag_pending_cap*2 : 8;
        char **nt = realloc(st->diag_pending, (size_t)nc*sizeof(char*));
        if(nt) st->diag_pending = nt;
        int *ns = realloc(st->diag_pending_seterr, (size_t)nc*sizeof(int));
        if(ns) st->diag_pending_seterr = ns;
        if(!nt || !ns) return;
        st->diag_pending_cap = nc;
    }
    char *cp = strdup(text);
    if(!cp) return;
    st->diag_pending[st->diag_pending_len]        = cp;
    st->diag_pending_seterr[st->diag_pending_len] = set_error;
    st->diag_pending_len++;
}

/* 以降の診断を溜め始める。 */
static void diag_capture_begin(AsmState *st){
    for(int i=0;i<st->diag_pending_len;i++) free(st->diag_pending[i]);
    st->diag_pending_len = 0;
    st->diag_capturing   = 1;
}

/* 溜めた診断を取り出し、溜めるのをやめる。 */
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

typedef struct {
    char **texts; int *seterr; int n; int cap; int capturing; int in_match;
} DiagSuppress;

/* 診断を一時的に止める（現在は未使用）。 */
static AXX_UNUSED void diag_suppress_begin(AsmState *st, DiagSuppress *sv){
    sv->texts     = st->diag_pending;
    sv->seterr    = st->diag_pending_seterr;
    sv->n         = st->diag_pending_len;
    sv->cap       = st->diag_pending_cap;
    sv->capturing = st->diag_capturing;
    sv->in_match  = st->in_match_attempt;
    st->diag_pending        = NULL;
    st->diag_pending_seterr = NULL;
    st->diag_pending_len    = 0;
    st->diag_pending_cap    = 0;
    st->diag_capturing      = 1;
    st->in_match_attempt    = 1;
}

/* 診断の抑制を解く（現在は未使用）。 */
static AXX_UNUSED void diag_suppress_end(AsmState *st, DiagSuppress *sv){
    for(int i=0;i<st->diag_pending_len;i++) free(st->diag_pending[i]);
    free(st->diag_pending);
    free(st->diag_pending_seterr);
    st->diag_pending        = sv->texts;
    st->diag_pending_seterr = sv->seterr;
    st->diag_pending_len    = sv->n;
    st->diag_pending_cap    = sv->cap;
    st->diag_capturing      = sv->capturing;
    st->in_match_attempt    = sv->in_match;
}

/* 溜めた診断を出す。採択されたパターンのぶんだけ流す。 */
static void diag_replay(AsmState *st, char **texts, int *seterr, int n){
    for(int i=0;i<n;i++){
        if(should_report_errors(st)){
            fputs(texts[i], stderr);
            if(seterr[i]) st->had_error = 1;
        }
    }
}

static long long g_diag_count = 0;

/* 診断を 1 行出す。set_error で had_error を立て、force でパスと照合の
   状況を無視して必ず出す。 */
static void axx_diagf(int set_error, int force, const char *fmt, ...){
    AsmState *st = g_active_state;
    g_diag_count++;
    char stackbuf[2048];
    char *buf = stackbuf;
    va_list ap;
    va_start(ap, fmt);
    int need = vsnprintf(stackbuf, sizeof(stackbuf), fmt, ap);
    va_end(ap);
    if(need >= (int)sizeof(stackbuf)){
        char *heap = malloc((size_t)need + 1);
        if(heap){
            va_start(ap, fmt);
            vsnprintf(heap, (size_t)need + 1, fmt, ap);
            va_end(ap);
            buf = heap;
        }
    }

    if(st && !force){
        if(st->in_match_attempt){
            if(st->diag_capturing) diag_pending_push(st, buf, set_error);
            if(buf != stackbuf) free(buf);
            return;
        }
        if(!should_report_errors(st)){ if(buf != stackbuf) free(buf); return; }
    }
    fputs(buf, stderr);
    if(buf != stackbuf) free(buf);
    if(st && set_error) st->had_error = 1;
}

/* errno を、ファイル名を添えた文言にする。 */
static void axx_oserr_str(const char *fn, int err, char *out, size_t osz){
    char q[1024]; m_pyrepr(fn ? fn : "", q, sizeof(q));
    snprintf(out, osz, "[Errno %d] %s: %s", err, strerror(err), q);
}

/* errno を文言にする（ファイル名なし）。 */
static void axx_oserr_nopath(int err, char *out, size_t osz){
    snprintf(out, osz, "[Errno %d] %s", err, strerror(err));
}

/* 出力を閉じ、書き込みが成功したかを確かめる。 */
static int axx_close_out(FILE *fp, const char *path){
    int err = 0;
    errno = 0;
    if(fflush(fp) != 0 || ferror(fp)) err = errno ? errno : EIO;
    errno = 0;
    if(fclose(fp) != 0 && !err) err = errno ? errno : EIO;
    if(err){
        char eb[2*PATH_MAX + 256]; axx_oserr_nopath(err, eb, sizeof(eb));
        axx_diagf(1, 0, " error - cannot write '%s': %s\n", path, eb);
        return 1;
    }
    return 0;
}

/* 標準出力を流し、失敗を報告する。 */
static int axx_flush_stdout(const char *path){
    int err = 0;
    errno = 0;
    if(fflush(stdout) != 0 || ferror(stdout)) err = errno ? errno : EIO;
    if(err){
        char eb[2*PATH_MAX + 256]; axx_oserr_nopath(err, eb, sizeof(eb));
        axx_diagf(1, 0, " error - cannot write '%s': %s\n", path, eb);
        clearerr(stdout);
        return 1;
    }
    return 0;
}

/* 入力を開く。失敗したら文言を出して NULL を返す。 */
static FILE *axx_open_input(const char *fn, const char *what){
    char eb[2*PATH_MAX + 256];
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

/* 命令欄の記述 1 つ。`.elffield::<型>::<マスク>::<オフセット>::<シフト>::<補正>`
   と同じ形。 */
typedef struct { int rtype; uint64_t mask; int off; int shift; long long bias; } ElfFieldInfo;

/* 組み込みのマシン記述。どの項目もパターンファイルの宣言で同じものが
   書ける（.elfmachine / .elfclass / .elfrela / .elftype / .elfwidth /
   .elfextern / .elfdwarf / .elfpcguess / .elffield）。表は「宣言を
   あらかじめ書いておいたもの」にすぎず、コードのどこにも機種番号で
   分かれる処理は無い。axx.py の _ELF_MACHINE_RAW と同じ中身である。 */
typedef struct {
    int         machine;
    const char *name;
    int         elfclass;
    int         is_rela;
    int         extern_default;
    int         dwarf_abs;
    int         wg[9];
    const int  *pc_rel;
    int         pc_rel_n;
    const ElfNamedReloc *named;
    int         pcrel_guess;
    const ElfFieldInfo *field;
    int         field_n;
} ElfMachineInfo;

static const int _pcrel_i386[]    = {2, 4, 13, 21, 23};
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
    {"movw_uabs_g0", 263, 4}, {"movw_uabs_g0_nc", 264, 4},
    {"movw_uabs_g1", 265, 4}, {"movw_uabs_g1_nc", 266, 4},
    {"movw_uabs_g2", 267, 4}, {"movw_uabs_g2_nc", 268, 4},
    {"movw_uabs_g3", 269, 4},
    {"movw_prel_g0", 287, 4}, {"movw_prel_g0_nc", 288, 4},
    {"movw_prel_g1", 289, 4}, {"movw_prel_g1_nc", 290, 4},
    {"movw_prel_g2", 291, 4}, {"movw_prel_g2_nc", 292, 4},
    {"movw_prel_g3", 293, 4},
    {"ld_prel_lo19", 273, 4},
    {"adr_prel_lo21", 274, 4},
    {"adr_prel_pg_hi21", 275, 4}, {"adrp", 275, 4},
    {"adr_prel_pg_hi21_nc", 276, 4},
    {"add_abs_lo12_nc", 277, 4},
    {"ldst8_abs_lo12_nc", 278, 4},
    {"tstbr14", 279, 4}, {"condbr19", 280, 4},
    {"jump26", 282, 4}, {"call26", 283, 4},
    {"ldst16_abs_lo12_nc", 284, 4},
    {"ldst32_abs_lo12_nc", 285, 4},
    {"ldst64_abs_lo12_nc", 286, 4},
    {"ldst128_abs_lo12_nc", 299, 4},
    {"got_ld_prel19", 309, 4},
    {"got_page", 311, 4}, {"adr_got_page", 311, 4},
    {"got_lo12", 312, 4}, {"ld64_got_lo12_nc", 312, 4},
    {"ld64_gotpage_lo15", 313, 4},
    {NULL, 0, 0},
};

/* AArch64 の命令欄リロケーションが 32bit 命令語のどのビットに値を置くか。
   `.elffield::<型>::<マスク>` と同じ形で持つ。axx.py の _A64_FIELD_MASKS
   と同じ中身・同じ並びである。 */
#define A64_ADR_MASK  ((0x3ull << 29) | (0x7ffffull << 5))
#define A64_LO12_MASK (0xfffull << 10)
#define A64_MOVW_MASK (0xffffull << 5)
static const ElfFieldInfo _field_aarch64[] = {
    {263, A64_MOVW_MASK, 0, 0, 0}, {264, A64_MOVW_MASK, 0, 0, 0},
    {265, A64_MOVW_MASK, 0, 0, 0}, {266, A64_MOVW_MASK, 0, 0, 0},
    {267, A64_MOVW_MASK, 0, 0, 0}, {268, A64_MOVW_MASK, 0, 0, 0},
    {269, A64_MOVW_MASK, 0, 0, 0},
    {287, A64_MOVW_MASK, 0, 0, 0}, {288, A64_MOVW_MASK, 0, 0, 0},
    {289, A64_MOVW_MASK, 0, 0, 0}, {290, A64_MOVW_MASK, 0, 0, 0},
    {291, A64_MOVW_MASK, 0, 0, 0}, {292, A64_MOVW_MASK, 0, 0, 0},
    {293, A64_MOVW_MASK, 0, 0, 0},
    {274, A64_ADR_MASK, 0, 0, 0},
    {275, A64_ADR_MASK, 0, 0, 0}, {276, A64_ADR_MASK, 0, 0, 0},
    {277, A64_LO12_MASK, 0, 0, 0},
    {278, A64_LO12_MASK, 0, 0, 0},
    {273, 0x7ffffull << 5, 0, 0, 0},
    {279, 0x3fffull << 5, 0, 0, 0},
    {280, 0x7ffffull << 5, 0, 0, 0},
    {282, 0x3ffffffull, 0, 0, 0}, {283, 0x3ffffffull, 0, 0, 0},
    {284, A64_LO12_MASK, 0, 0, 0}, {285, A64_LO12_MASK, 0, 0, 0},
    {286, A64_LO12_MASK, 0, 0, 0}, {299, A64_LO12_MASK, 0, 0, 0},
    {309, 0x7ffffull << 5, 0, 0, 0},
    {311, A64_ADR_MASK, 0, 0, 0},
    {312, A64_LO12_MASK, 0, 0, 0},
    {313, A64_LO12_MASK, 0, 0, 0},
};
#define FIELD_AARCH64_N ((int)(sizeof(_field_aarch64)/sizeof(_field_aarch64[0])))

static const ElfNamedReloc _named_riscv[] = {
    {"abs64", 2, 8}, {"abs32", 1, 4}, {"abs16", 34, 2}, {"abs8", 33, 1},
    {NULL, 0, 0},
};

static const ElfMachineInfo ELF_MACHINES[] = {
    {3,   "i386",         1, 0, 2,   1,   {0, 22, 20,0,  2,0,0,0,  0}, _pcrel_i386,    5, _named_i386},
    {4,   "m68k",         1, 1, 4,   1,   {0,  3,  2,0,  4,0,0,0,  0}, _pcrel_m68k,    3, _named_m68k,
          1, NULL, 0},
    {20,  "PowerPC",      1, 1, 26,  1,   {0,  0,  4,0, 26,0,0,0,  0}, _pcrel_ppc32,   2, _named_ppc32},
    {21,  "PowerPC64",    2, 1, 26,  38,  {0,  0,  4,0, 26,0,0,0, 38}, _pcrel_ppc64,   3, _named_ppc64},
    {22,  "s390x",        2, 1, 5,   22,  {0,  1,  3,0,  5,0,0,0, 22}, _pcrel_s390x,   3, _named_s390x},
    {40,  "ARM",          1, 0, 3,   2,   {0,  8,  5,0,  3,0,0,0,  0}, _pcrel_arm,     2, _named_arm},
    {42,  "SuperH",       1, 1, 2,   1,   {0,  0,  0,0,  2,0,0,0,  0}, _pcrel_sh,      1, _named_sh},
    {43,  "SPARCV9",      2, 1, 6,   32,  {0,  1,  2,0,  6,0,0,0, 32}, _pcrel_sparcv9, 4, _named_sparcv9},
    {62,  "x86-64",       2, 1, 2,   1,   {0, 14, 12,0,  2,0,0,0,  1}, _pcrel_x86_64,  6, _named_x86_64},
    {183, "AArch64",      2, 1, 261, 257, {0,  0,262,0,261,0,0,0,257}, _pcrel_aarch64, 3, _named_aarch64,
          0, _field_aarch64, FIELD_AARCH64_N},
    {243, "RISC-V",       2, 1, 1,   2,   {0, 33, 34,0,  1,0,0,0,  2}, NULL,           0, _named_riscv},
};
#define ELF_MACHINES_N ((int)(sizeof(ELF_MACHINES)/sizeof(ELF_MACHINES[0])))

/* e_machine から組み込みのマシン記述を引く。 */
static const ElfMachineInfo *elf_machine_find(int machine){
    for(int i=0;i<ELF_MACHINES_N;i++)
        if(ELF_MACHINES[i].machine == machine) return &ELF_MACHINES[i];
    return NULL;
}

/* 組み込みの表で型名を番号にする。 */
static int elf_machine_named(const ElfMachineInfo *m, const char *name){
    if(!m) return -1;
    for(int i=0; m->named[i].name; i++)
        if(strcasecmp(m->named[i].name, name)==0) return m->named[i].rtype;
    return -1;
}

/* `.elftype` が宣言した型名を番号にする。 */
static int elftype_find(const AsmState *st, const char *name){
    for(int i=0;i<st->elftypes_len;i++)
        if(strcasecmp(st->elftypes[i].name, name)==0) return st->elftypes[i].rtype;
    return -1;
}

/* `.elftype` の宣言を登録する。 */
static void elftype_set(AsmState *st, const char *name, int rtype, int width, int pcrel){
    for(int i=0;i<st->elftypes_len;i++)
        if(strcasecmp(st->elftypes[i].name, name)==0){
            if(st->elftypes[i].rtype != rtype || st->elftypes[i].width != width
               || st->elftypes[i].pcrel != pcrel){
                st->elftypes[i].rtype = rtype;
                st->elftypes[i].width = width;
                st->elftypes[i].pcrel = pcrel;
                st->elf_decl_gen++;
            }
            return;
        }
    if(st->elftypes_len >= st->elftypes_cap){
        st->elftypes_cap = st->elftypes_cap ? st->elftypes_cap*2 : 8;
        st->elftypes = realloc(st->elftypes, (size_t)st->elftypes_cap*sizeof(*st->elftypes));
        if(!st->elftypes){ perror("realloc"); exit(1); }
    }
    st->elftypes[st->elftypes_len].name  = strdup(name);
    if(!st->elftypes[st->elftypes_len].name){ perror("strdup"); exit(1); }
    st->elftypes[st->elftypes_len].rtype = rtype;
    st->elftypes[st->elftypes_len].width = width;
    st->elftypes[st->elftypes_len].pcrel = pcrel;
    st->elftypes_len++;
    st->elf_decl_gen++;
}

/* 型名を番号にする。`.elftype` の宣言が組み込みの表に勝つ。 */
static int elf_reloc_named(const AsmState *st, const ElfMachineInfo *m, const char *name){
    if(!name || !name[0]) return -1;
    int t = elftype_find(st, name);
    if(t >= 0) return t;
    return elf_machine_named(m, name);
}

/* 組み込みの表で型番号を名前にする。 */
static const char *elf_machine_reverse(const ElfMachineInfo *m, int rtype){
    if(!m) return NULL;
    for(int i=0; m->named[i].name; i++)
        if(m->named[i].rtype == rtype) return m->named[i].name;
    return NULL;
}

/* 型番号を名前にする（診断とリスティング用）。 */
static const char *elf_reloc_reverse(const AsmState *st, const ElfMachineInfo *m, int rtype){
    const char *nm = elf_machine_reverse(m, rtype);
    if(nm) return nm;
    for(int i=0;i<st->elftypes_len;i++)
        if(st->elftypes[i].rtype == rtype) return st->elftypes[i].name;
    return NULL;
}

/* その型が使う欄の幅（バイト）。同じ型番号に名前が複数あるときは、幅を
   書いた最初のもの（axx.py の reloc_bytes の setdefault と同じ）。 */
static int elf_machine_reloc_bytes(const ElfMachineInfo *m, int rtype){
    if(!m) return 0;
    for(int i=0; m->named[i].name; i++)
        if(m->named[i].rtype == rtype && m->named[i].width) return m->named[i].width;
    return 0;
}

/* その型が PC 相対か。 */
static int elf_machine_is_pcrel(const ElfMachineInfo *m, int rtype){
    if(!m) return 0;
    for(int i=0;i<m->pc_rel_n;i++) if(m->pc_rel[i]==rtype) return 1;
    return 0;
}

/* 欄の幅と PC 相対かどうかが一致する型を 1 つ探す。 */
static int elf_reloc_same_width(const ElfMachineInfo *m, int nbytes, int want_pcrel){
    if(!m) return 0;
    for(int i=0; m->named[i].name; i++){
        if(m->named[i].width != nbytes) continue;
        if(elf_machine_is_pcrel(m, m->named[i].rtype) == (want_pcrel ? 1 : 0))
            return m->named[i].rtype;
    }
    return 0;
}

/* 欄の幅から型を推測する（優先順位は最も低い）。 */
static int elf_machine_width_guess(const ElfMachineInfo *m, int nbytes){
    if(!m || nbytes < 1 || nbytes > 8) return 0;
    return m->wg[nbytes];
}

typedef struct {
    ElfMachineInfo  info;
    ElfNamedReloc  *named;
    int            *pc_rel;
    char            name_buf[80];
    long            gen;
    int             machine;
    int             valid;
} ElfMachEff;

static ElfMachEff g_elf_mach_eff;

/* 宣言に書かれた型の綴りを番号にする。 */
static int elf_decl_type_in(const ElfNamedReloc *named, const char *text){
    if(!text) return -1;
    char buf[128]; size_t n = 0;
    for(const char *q = text; *q && n + 1 < sizeof(buf); q++){
        if(*q == ' ' || *q == '\t') continue;
        buf[n++] = *q;
    }
    buf[n] = '\0';
    if(!buf[0]) return -1;
    char *endp = NULL;
    long v = strtol(buf, &endp, 0);
    if(endp && *endp == '\0' && endp != buf) return (int)v;
    for(int i=0; named[i].name; i++)
        if(strcasecmp(named[i].name, buf)==0) return named[i].rtype;
    return -1;
}

/* `.elfbuiltin::0` でなければ、-m の番号の組み込みの表を返す。 */
static const ElfMachineInfo *elf_machine_base(const AsmState *st){
    if(st->elf_decl_builtin == 0) return NULL;
    return elf_machine_find(st->elf_machine);
}

/* いま有効な ELF マシン記述を組み立てて返す。
   組み込みの表を土台に、パターンファイルの宣言をかぶせたものがここで出来る。
   同じ名前なら宣言のほうが勝つ。`.elfbuiltin::0` なら土台は空の表で、
   宣言だけが残る。1 行ごとに作り直すと重いので、宣言の世代番号を鍵にして
   覚える。axx.py の elf_machine_table() と同じ規則である。 */
static const ElfMachineInfo *elf_machine_effective(const AsmState *st){
    if(g_elf_mach_eff.valid && g_elf_mach_eff.gen == st->elf_decl_gen
       && g_elf_mach_eff.machine == st->elf_machine)
        return &g_elf_mach_eff.info;

    const ElfMachineInfo *base = elf_machine_base(st);
    int base_n = 0;
    if(base) while(base->named[base_n].name) base_n++;

    ElfNamedReloc *nm = (ElfNamedReloc*)malloc(sizeof(*nm) *
                            (size_t)(base_n + st->elftypes_len + 1));
    if(!nm){ perror("malloc"); exit(1); }
    int n = 0;
    for(int i=0;i<base_n;i++){
        int overridden = 0;
        for(int k=0;k<st->elftypes_len;k++)
            if(strcasecmp(st->elftypes[k].name, base->named[i].name)==0){ overridden = 1; break; }
        if(!overridden) nm[n++] = base->named[i];
    }
    for(int k=0;k<st->elftypes_len;k++){
        nm[n].name  = st->elftypes[k].name;
        nm[n].rtype = st->elftypes[k].rtype;
        nm[n].width = st->elftypes[k].width;
        n++;
    }
    nm[n].name = NULL; nm[n].rtype = 0; nm[n].width = 0;

    int base_pr = base ? base->pc_rel_n : 0;
    int *pr = (int*)malloc(sizeof(int) * (size_t)(base_pr + st->elftypes_len + 1));
    if(!pr){ perror("malloc"); exit(1); }
    int prn = 0;
    for(int i=0;i<base_pr;i++) pr[prn++] = base->pc_rel[i];
    for(int k=0;k<st->elftypes_len;k++){
        if(!st->elftypes[k].pcrel) continue;
        int dup = 0;
        for(int i=0;i<prn;i++) if(pr[i]==st->elftypes[k].rtype){ dup=1; break; }
        if(!dup) pr[prn++] = st->elftypes[k].rtype;
    }

    ElfMachineInfo info;
    memset(&info, 0, sizeof(info));
    info.machine        = st->elf_machine;
    info.elfclass       = st->elf_decl_class ? st->elf_decl_class
                                             : (base ? base->elfclass : 2);
    info.is_rela        = st->elf_decl_rela >= 0 ? st->elf_decl_rela
                                                 : (base ? base->is_rela : 1);
    info.extern_default = base ? base->extern_default : 0;
    info.dwarf_abs      = base ? base->dwarf_abs : 0;
    info.pcrel_guess    = st->elf_decl_pcguess >= 0 ? st->elf_decl_pcguess
                                                    : (base ? base->pcrel_guess : 0);
    for(int w=0; w<9; w++) info.wg[w] = base ? base->wg[w] : 0;
    info.pc_rel   = pr;
    info.pc_rel_n = prn;
    info.named    = nm;

    for(int w=1; w<9; w++){
        if(!st->elf_decl_width[w]) continue;
        int rt = elf_decl_type_in(nm, st->elf_decl_width[w]);
        if(rt < 0) continue;
        info.wg[w] = rt;
    }
    { int rt = elf_decl_type_in(nm, st->elf_decl_extern);
      if(rt >= 0) info.extern_default = rt; }
    { int rt = elf_decl_type_in(nm, st->elf_decl_dwarf);
      if(rt >= 0) info.dwarf_abs = rt; }

    if(st->elf_decl_name[0]
       && (st->elf_decl_machine < 0 || st->elf_decl_machine == st->elf_machine))
        snprintf(g_elf_mach_eff.name_buf, sizeof(g_elf_mach_eff.name_buf), "%s",
                 st->elf_decl_name);
    else if(base)
        snprintf(g_elf_mach_eff.name_buf, sizeof(g_elf_mach_eff.name_buf), "%s", base->name);
    else
        snprintf(g_elf_mach_eff.name_buf, sizeof(g_elf_mach_eff.name_buf), "machine %d",
                 st->elf_machine);
    info.name = g_elf_mach_eff.name_buf;

    free(g_elf_mach_eff.named);
    free(g_elf_mach_eff.pc_rel);
    g_elf_mach_eff.named   = nm;
    g_elf_mach_eff.pc_rel  = pr;
    g_elf_mach_eff.info    = info;
    g_elf_mach_eff.gen     = st->elf_decl_gen;
    g_elf_mach_eff.machine = st->elf_machine;
    g_elf_mach_eff.valid   = 1;
    return &g_elf_mach_eff.info;
}

static struct { long gen; int machine; int valid; int n;
                ElfFieldInfo *f; } g_elf_field_eff;

/* いま有効な命令欄の記述の表を作る（宣言が先、組み込みの欄はその型の
   宣言が無いときだけ残る）。axx.py の elf_machine_table() の field と
   同じ規則である。 */
static void elf_field_effective(const AsmState *st){
    if(g_elf_field_eff.valid && g_elf_field_eff.gen == st->elf_decl_gen
       && g_elf_field_eff.machine == st->elf_machine)
        return;
    const ElfMachineInfo *m = elf_machine_effective(st);
    const ElfMachineInfo *base = elf_machine_base(st);
    int nb = base ? base->field_n : 0;
    free(g_elf_field_eff.f);
    g_elf_field_eff.f = (ElfFieldInfo*)malloc(sizeof(ElfFieldInfo)
                                              * (size_t)(st->elf_fields_len + nb + 1));
    if(!g_elf_field_eff.f){ perror("malloc"); exit(1); }
    int k = 0;
    for(int i = 0; i < st->elf_fields_len; i++){
        int rt = elf_decl_type_in(m->named, st->elf_fields[i].type);
        if(rt < 0) continue;
        int dup = 0;
        for(int j = 0; j < k; j++) if(g_elf_field_eff.f[j].rtype == rt){ dup = 1; break; }
        if(dup) continue;
        g_elf_field_eff.f[k].rtype = rt;
        g_elf_field_eff.f[k].mask  = st->elf_fields[i].mask;
        g_elf_field_eff.f[k].off   = st->elf_fields[i].off;
        g_elf_field_eff.f[k].shift = st->elf_fields[i].shift;
        g_elf_field_eff.f[k].bias  = st->elf_fields[i].bias;
        k++;
    }
    for(int i = 0; i < nb; i++){
        int dup = 0;
        for(int j = 0; j < k; j++)
            if(g_elf_field_eff.f[j].rtype == base->field[i].rtype){ dup = 1; break; }
        if(dup) continue;
        g_elf_field_eff.f[k++] = base->field[i];
    }
    g_elf_field_eff.n = k;
    g_elf_field_eff.gen = st->elf_decl_gen;
    g_elf_field_eff.machine = st->elf_machine;
    g_elf_field_eff.valid = 1;
}

/* 命令欄の記述を引く。無ければ NULL。axx.py の insn_reloc_field_decl()
   と同じ規則である。 */
static const ElfFieldInfo *insn_reloc_field_decl(const AsmState *st, int rtype){
    if(!st) return NULL;
    elf_field_effective(st);
    for(int j = 0; j < g_elf_field_eff.n; j++)
        if(g_elf_field_eff.f[j].rtype == rtype) return &g_elf_field_eff.f[j];
    return NULL;
}

/* その型が命令語のどのビットを使うかのマスク。命令欄の記述が無ければ 0
   （命令欄ではない、ふつうのデータリロケーション）。 */
static uint64_t insn_reloc_field_mask(const AsmState *st, int rtype){
    const ElfFieldInfo *f = insn_reloc_field_decl(st, rtype);
    return f ? f->mask : 0;
}

/* value の下位ビットから順に、mask の立っているビットへ下から詰める。
   REL で命令欄の型の加数を命令語へ書き戻すときに使う。axx.py の
   _field_deposit() と同じ規則である。 */
static uint64_t field_deposit(uint64_t mask, int64_t value){
    uint64_t out = 0;
    int bit = 0;
    while(mask){
        uint64_t low = mask & (~mask + 1);
        int64_t b = (bit < 63) ? ((value >> bit) & 1) : (value < 0 ? 1 : 0);
        if(b) out |= low;
        bit++;
        mask ^= low;
    }
    return out;
}

/* `.elfextra` の型の綴りが、その位置で初めて現れたものか。 */
static int elf_extra_first(const AsmState *st, int i){
    for(int j = 0; j < i; j++)
        if(strcmp(st->elf_extras[j].type, st->elf_extras[i].type) == 0) return 0;
    return 1;
}

/* rtype に添えるリロケーションを宣言の順に並べ、数を返す。axx.py の
   elf_machine_table() の extra と同じ並び（型の綴りの初出順、その中は
   添える型の宣言順）である。 */
static int elf_extras_of(const AsmState *st, int rtype, int *crt, int *csym, int max){
    if(st->elf_extras_len == 0) return 0;
    const ElfMachineInfo *m = elf_machine_effective(st);
    int n = 0;
    for(int i = 0; i < st->elf_extras_len; i++){
        if(!elf_extra_first(st, i)) continue;
        if(elf_decl_type_in(m->named, st->elf_extras[i].type) != rtype) continue;
        for(int k = i; k < st->elf_extras_len; k++){
            if(strcmp(st->elf_extras[k].type, st->elf_extras[i].type) != 0) continue;
            int c = elf_decl_type_in(m->named, st->elf_extras[k].comp);
            if(c < 0 || n >= max) continue;
            crt[n] = c; csym[n] = st->elf_extras[k].sym; n++;
        }
    }
    return n;
}

/* `.elfdiff` の幅 nbytes の対を引く。無ければ 0。 */
static int elf_diff_of(const AsmState *st, int nbytes, int *add, int *sub){
    if(nbytes < 1 || nbytes > 8 || !st->elf_diff_add[nbytes]) return 0;
    const ElfMachineInfo *m = elf_machine_effective(st);
    int a = elf_decl_type_in(m->named, st->elf_diff_add[nbytes]);
    int b = elf_decl_type_in(m->named, st->elf_diff_sub[nbytes]);
    if(a < 0 || b < 0) return 0;
    *add = a; *sub = b;
    return 1;
}

/* `.elfdiff` が 1 つでも宣言されているか。 */
static int elf_diff_any(const AsmState *st){
    for(int w = 1; w < 9; w++) if(st->elf_diff_add[w]) return 1;
    return st->elf_diff_t_len > 0;
}

/* 型付きの `.elfdiff`（`.reloc` がその型を付けた欄）の対を引く。最初に
   当たった宣言を使う。無ければ 0。 */
static int elf_diff_t_of(const AsmState *st, int rtype, int *add, int *sub){
    if(st->elf_diff_t_len == 0) return 0;
    const ElfMachineInfo *m = elf_machine_effective(st);
    for(int i = 0; i < st->elf_diff_t_len; i++){
        if(elf_decl_type_in(m->named, st->elf_diff_t[i].type) != rtype) continue;
        int a = elf_decl_type_in(m->named, st->elf_diff_t[i].add);
        int b = elf_decl_type_in(m->named, st->elf_diff_t[i].sub);
        if(a < 0 || b < 0) continue;
        *add = a; *sub = b;
        return 1;
    }
    return 0;
}

/* `.elfencode` の関数名を型番号で引く（最初に当たった宣言）。無ければ NULL。 */
static const char *elf_encode_of(const AsmState *st, int rtype){
    if(st->elf_encodes_len == 0) return NULL;
    const ElfMachineInfo *m = elf_machine_effective(st);
    for(int i = 0; i < st->elf_encodes_len; i++)
        if(elf_decl_type_in(m->named, st->elf_encodes[i].type) == rtype)
            return st->elf_encodes[i].fn;
    return NULL;
}

/* 型の付いていない外部シンボルとして登録されているか。 */
static int extern_untyped_has(const AsmState *st, const char *name){
    for(int i = 0; i < st->extern_untyped_len; i++)
        if(strcmp(st->extern_untyped[i], name) == 0) return 1;
    return 0;
}
/* その登録を付け外しする。 */
static void extern_untyped_set(AsmState *st, const char *name, int on){
    for(int i = 0; i < st->extern_untyped_len; i++)
        if(strcmp(st->extern_untyped[i], name) == 0){
            if(!on){
                free(st->extern_untyped[i]);
                st->extern_untyped[i] = st->extern_untyped[--st->extern_untyped_len];
            }
            return;
        }
    if(!on) return;
    if(st->extern_untyped_len >= st->extern_untyped_cap){
        st->extern_untyped_cap = st->extern_untyped_cap ? st->extern_untyped_cap * 2 : 16;
        st->extern_untyped = realloc(st->extern_untyped,
                                     sizeof(char*) * (size_t)st->extern_untyped_cap);
        if(!st->extern_untyped){ perror("realloc"); exit(1); }
    }
    st->extern_untyped[st->extern_untyped_len++] = strdup(name);
}

/* 欄の幅からリロケーション型を決める。ソースの `.reloctype` が上書きできる。 */
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


static const struct { const char *name; int v; } ELF_SYM_TYPES[] = {
    {"notype",0}, {"object",1}, {"func",2}, {"function",2},
    {"section",3}, {"file",4}, {"common",5}, {"tls",6}, {"tls_object",6},
    {"gnu_ifunc",10}, {"ifunc",10}, {NULL,0}
};

typedef struct { int stype; int size_set; uint64_t size;
                 int other; int weak; int common; uint64_t calign; } SymAttrView;
static const SymAttrView SYM_ATTR_DEFAULT = {0,0,0,0,0,0,0};

/* シンボルの属性を読む（無ければ既定値）。 */
static SymAttrView sym_attr_get(const AsmState *st, const char *name){
    for(int i=0;i<st->sym_attrs_len;i++)
        if(strcmp(st->sym_attrs[i].name, name)==0){
            SymAttrView v;
            v.stype    = st->sym_attrs[i].stype;
            v.size_set = st->sym_attrs[i].size_set;
            v.size     = st->sym_attrs[i].size;
            v.other    = st->sym_attrs[i].other;
            v.weak     = st->sym_attrs[i].weak;
            v.common   = st->sym_attrs[i].common;
            v.calign   = st->sym_attrs[i].calign;
            return v;
        }
    return SYM_ATTR_DEFAULT;
}

/* シンボルの属性を書くための枠を返す。読むだけの場合に枠を作らせないため、
   取得と分けてある。 */
static int sym_attr_slot(AsmState *st, const char *name){
    for(int i=0;i<st->sym_attrs_len;i++)
        if(strcmp(st->sym_attrs[i].name, name)==0) return i;
    if(st->sym_attrs_len >= st->sym_attrs_cap){
        st->sym_attrs_cap = st->sym_attrs_cap ? st->sym_attrs_cap*2 : 8;
        st->sym_attrs = realloc(st->sym_attrs,
                                (size_t)st->sym_attrs_cap*sizeof(*st->sym_attrs));
        if(!st->sym_attrs){ perror("realloc"); exit(1); }
    }
    int k = st->sym_attrs_len++;
    st->sym_attrs[k].name = strdup(name);
    if(!st->sym_attrs[k].name){ perror("strdup"); exit(1); }
    st->sym_attrs[k].stype = 0; st->sym_attrs[k].size_set = 0;
    st->sym_attrs[k].size = 0;  st->sym_attrs[k].other = 0;
    st->sym_attrs[k].weak = 0;  st->sym_attrs[k].common = 0;
    st->sym_attrs[k].calign = 0;
    return k;
}

/* st_info を組む。`.weak` があればバインドを STB_WEAK に差し替える。 */
static uint8_t weo_sym_info(const AsmState *st, const char *name, int bind){
    SymAttrView a = sym_attr_get(st, name);
    if(a.weak) bind = 2;
    return (uint8_t)(((bind & 0xF) << 4) | (a.stype & 0xF));
}

/* st_other を組む（`.other` は丸ごと置き換える）。 */
static uint8_t weo_sym_other(const AsmState *st, const char *name){
    return (uint8_t)(sym_attr_get(st, name).other & 0xFF);
}

/* st_size を組む。`.size` はワード数で書くので幅をかける。 */
static uint64_t weo_sym_size(const AsmState *st, const char *name, int bpw){
    SymAttrView a = sym_attr_get(st, name);
    if(!a.size_set) return 0;
    return a.size * (uint64_t)bpw;
}

static void weo_sym_common(const AsmState *st, const char *name, int bpw,
                           uint32_t *shndx, uint64_t *val, uint64_t *size){
    SymAttrView a = sym_attr_get(st, name);
    if(!a.common) return;
    *shndx = 0xfff2;
    *val   = a.calign;
    *size  = a.size * (uint64_t)bpw;
}

/* その名前を外部シンボルとして登録する。 */
static void sym_declare_extern(AsmState *st, const char *name){
    if(lmap_find(&st->labels, name)) return;
    const ElfMachineInfo *m = elf_machine_effective(st);
    extern_untyped_set(st, name, 1);
    lmap_set_imported(&st->labels, name, u256_zero(), ".text", m->extern_default);
}

/* いま開いているセクションの範囲を閉じて記録する。 */
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

/* セクション内のワードオフセットを出す。 */
static int64_t sec_word_offset(AsmState *st, const char *name, uint64_t word_pc){
    if(st->sections.count == 0) return (int64_t)word_pc;
    uint64_t cum = 0;
    int have_range = 0;
    for(int i=0;i<st->section_ranges.len;i++){
        if(strcmp(st->section_ranges.data[i].name,name)!=0) continue;
        have_range = 1;
        uint64_t rs = u256_to_u64(st->section_ranges.data[i].start);
        uint64_t rl = u256_to_u64(st->section_ranges.data[i].len);
        if(word_pc >= rs && word_pc <= rs+rl) return (int64_t)(cum + (word_pc-rs));
        cum += rl;
    }
    if(!have_range){
        SecEntry *e = secmap_find(&st->sections, name);
        if(e && !u256_is_zero(e->size)){
            uint64_t rs = u256_to_u64(e->start);
            uint64_t rl = u256_to_u64(e->size);
            if(word_pc >= rs && word_pc <= rs+rl) return (int64_t)(word_pc - rs);
        }
    }
    return -1;
}

/* DWARF に書くためのバイトオフセットを出す。 */
static uint64_t dwarf_word_offset(AsmState *st, const char *sec_name, uint64_t word_pc, int bpw){
    if(st->sections.count == 0) return word_pc * (uint64_t)bpw;
    int64_t o = sec_word_offset(st, sec_name, word_pc);
    return (uint64_t)(o >= 0 ? o : 0) * (uint64_t)bpw;
}

/* `.equ` の値をセクション相対に直す。 */
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

/* 現在のセクションを切り替える。 */
static void st_set_current_section(AsmState *st, const char *name){
    size_t n = strlen(name) + 1;
    if(n > st->current_section_cap){
        char *p = realloc(st->current_section, n);
        if(!p){ perror("realloc"); exit(1); }
        st->current_section = p;
        st->current_section_cap = n;
    }
    memcpy(st->current_section, name, n);
}

/* アセンブル状態をすべて初期値にする。 */
/* 読んでいるファイルの名前を書き換える。長さの制限はない。 */
static void set_current_file(AsmState *st, const char *fn){
    char *d = strdup(fn ? fn : "");
    if(!d){ perror("strdup"); exit(1); }
    free(st->current_file);
    st->current_file = d;
}

static void state_init(AsmState *st) {
    memset(st, 0, sizeof(*st));
    g_active_state = st;
    sv_init(&st->reported_label_errors);
    strcpy(st->lwordchars, "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz_.");
    strcpy(st->swordchars, "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz_%$-~&|");
    st_set_current_section(st, ".text");
    lmap_init(&st->labels);
    secmap_init(&st->sections);
    smap_init(&st->symbols);
    smap_init(&st->patsymbols);
    lmap_init(&st->export_labels);
    lmap_init(&st->macro_labels);
    sv_init(&st->export_order);
    pv_init(&st->pat);
    subv_init(&st->subs);
    mfv_init(&st->funcs);
    st->vliwinstbits = 41;
    iv_init(&st->vliwnop);
    st->vliwbits = 128;
    vset_init(&st->vliwset);
    st->vliwflag = 0;
    st->vliwtemplatebits = 0;
    st->vliwstop = 0;
    st->vcnt = 1;
    st->expmode = EXP_PAT;
    st->expcaps = &CAPS_PAT;
    st->exp_typ_float = 0;
    st->align = u256_from_u64(16);
    st->bts = 8;
    st->endian_big = 0;
    st->pas = 0;
    st->debug = 0;
    st->asmtext = NULL;
    st->asmtext_disp = NULL;
    st->passthru = 0;
    st->eol = 0;
    sv_init(&st->strsym_names);
    sv_init(&st->mini_suspects);
    sv_init(&st->strsym_vals);
    st->arrsyms = NULL; st->arrsyms_len = 0; st->arrsyms_cap = 0;
    st->osabi = 0;
    st->ln = 0;
    sv_init(&st->fnstack);
    is_init(&st->lnstack);
    for(int i=0;i<NVARS;i++){ st->vars[i].val=u256_zero(); st->vars[i].is_undef=0;
                              st->vars[i].text_off=-1; }
    st->textmode = 0;
    st->captext_len = 0;
    st->captext[0] = '\0';
    st->label_text[0] = '\0';
    st->comment_text = NULL;
    st->indent_text[0] = '\0';
    bufmap_init(&st->buf);
    st->pc = u256_zero();
    st->padding = u256_zero();
    st->pc_instr_start = u256_zero();
    st->pc_instr_end   = u256_zero();
    st->pass1_size_mode = 0;
    st->stdin_tmp_path[0] = '\0';
    st->current_file = strdup("");
    if(!st->current_file){ perror("strdup"); exit(1); }
    st->outfile = "";
    st->expfile = "";
    st->expfile_elf = "";
    st->impfile = "";
    st->elf_objfile = "";
    st->elf_machine = 62;
    st->elf_class = 0;
    st->gen_debug = 0;
    st->line_map = NULL;
    st->line_map_len = 0;
    st->line_map_cap = 0;
    st->elf_tracking = 0;
    st->elf_refs = NULL;
    st->elf_refs_len = 0;
    st->elf_refs_cap = 0;
    st->elf_current_word_idx = -1;
    for(int _vi=0;_vi<NVARS;_vi++){
        st->elf_var_to_label[_vi].set = 0;
        st->elf_var_to_label[_vi].label_name = NULL;
        st->elf_var_to_label[_vi].label_val = 0;
    }
    st->elf_capturing_var = -1;
    st->relocations = NULL;
    st->reloc_count = 0;
    st->reloc_cap = 0;
    for(int _rti=0; _rti<4; _rti++) st->reloctype_override[_rti] = -1;
    for(int _ci=0; _ci<NVARS; _ci++) st->check_constraints[_ci] = NULL;
    for(int _ci=0; _ci<NVARS; _ci++) st->var_tables[_ci] = NULL;
    for(int _ci=0; _ci<NVARS; _ci++) st->reloc_constraints[_ci] = 0;
    st->reloc_badname_len = 0;
    st->elftypes = NULL; st->elftypes_len = 0; st->elftypes_cap = 0;
    st->elf_decl_machine = -1;
    st->elf_decl_name[0] = '\0';
    st->elf_decl_class = 0;
    st->elf_decl_rela = -1;
    st->elf_decl_pcguess = -1;
    st->elf_decl_builtin = -1;
    st->elf_extras = NULL; st->elf_extras_len = 0; st->elf_extras_cap = 0;
    for(int _wi=0;_wi<9;_wi++){ st->elf_diff_add[_wi] = NULL; st->elf_diff_sub[_wi] = NULL; }
    st->elf_diff_t = NULL; st->elf_diff_t_len = 0; st->elf_diff_t_cap = 0;
    st->elf_encodes = NULL; st->elf_encodes_len = 0; st->elf_encodes_cap = 0;
    st->elf_decl_rinfo = NULL;
    st->elf_decl_unit = -1;
    st->elf_cfi_set = 0; st->elf_cfi_ra = 0; st->elf_cfi_code = 0; st->elf_cfi_data = 0; st->elf_cfi_pad = 0;
    st->elf_cfiinit = NULL; st->elf_cfiinit_len = 0; st->elf_cfiinit_cap = 0;
    st->elf_cfireg = NULL; st->elf_cfireg_len = 0; st->elf_cfireg_cap = 0;
    st->cfi_fdes = NULL; st->cfi_fdes_len = 0; st->cfi_fdes_cap = 0;
    memset(&st->cfi_curf, 0, sizeof(st->cfi_curf)); st->cfi_open = 0;
    st->elf_links = NULL; st->elf_links_len = 0; st->elf_links_cap = 0;
    st->elf_groups = NULL; st->elf_groups_len = 0; st->elf_groups_cap = 0;
    for(int _wi=0;_wi<9;_wi++) st->elf_decl_width[_wi] = NULL;
    st->elf_decl_extern = NULL;
    st->elf_decl_dwarf = NULL;
    for(int _hi=0;_hi<ELF_HDR_NFIELD;_hi++){ st->elf_hdr_set[_hi]=0; st->elf_hdr_val[_hi]=0; }
    st->elf_secs = NULL; st->elf_secs_len = 0; st->elf_secs_cap = 0;
    st->sym_attrs = NULL; st->sym_attrs_len = 0; st->sym_attrs_cap = 0;
    st->elf_fields = NULL; st->elf_fields_len = 0; st->elf_fields_cap = 0;
    st->extern_untyped = NULL; st->extern_untyped_len = 0; st->extern_untyped_cap = 0;
    st->elf_machine_from_cli = 0;
    st->elf_decl_gen = 0;
    for(int _ci=0; _ci<NVARS; _ci++) enumdef_init(&st->enum_defs[_ci]);
    st->enum_bind_names = NULL;
    st->enum_bind_vals  = NULL;
    sv_init(&st->errors);
    for(int _ei=0; _ei<ERRORS_COUNT; _ei++) sv_push(&st->errors, ERRORS_TABLE[_ei]);
}

/* ---- 行とトークンの文字列処理 -------------------------------------------
   大文字化は ASCII だけを畳む。locale 依存の toupper() に任せると axx.py 側の
   結果と食い違うため。文字列リテラル `"..."` と文字定数 `'c'` の中は触らない
   という規則を、この一群が共有している。
   ------------------------------------------------------------------------ */
static char axx_upper_char(char c) {
    if(c>='a'&&c<='z') return c-32;
    return c;
}
static int is_digit(char c){ return c>='0'&&c<='9'; }
/* 大文字の 16 進数字か。 */
static int is_xdigit_upper(char c){
    return (c>='0'&&c<='9')||(c>='A'&&c<='F');
}
static AXX_UNUSED int is_alpha(char c){ return (c>='A'&&c<='Z')||(c>='a'&&c<='z'); }

/* その場で ASCII 大文字化する。 */
static char *axx_strupr(char *s) {
    for(char*p=s;*p;p++) *p=axx_upper_char(*p);
    return s;
}
/* 大文字化して写す。 */
static void axx_strupr_to(char *dst, const char *src, size_t maxlen) {
    size_t i=0;
    for(;src[i]&&i<maxlen-1;i++) dst[i]=axx_upper_char(src[i]);
    dst[i]=0;
}

/* その位置にある `.enum` の要素名を最長一致で読む。名前の直後が英数字・
   下線なら語の途中なので一致とみなさない。 */
static int enum_name_at(const char *s, int idx, const StrVec *names, int *end_out){
    int best=-1, best_end=idx;
    for(int k=0;k<names->len;k++){
        const char *nm=names->data[k];
        int n=(int)strlen(nm);
        if(n <= best_end-idx) continue;
        int ok=1;
        for(int j=0;j<n;j++){
            char c=s[idx+j];
            if(c=='\0' || axx_upper_char(c)!=nm[j]){ ok=0; break; }
        }
        if(!ok) continue;
        char nx=s[idx+n];
        if((nx>='0'&&nx<='9')||(nx>='A'&&nx<='Z')||(nx>='a'&&nx<='z')||nx=='_') continue;
        best=k; best_end=idx+n;
    }
    *end_out=best_end;
    return best;
}

/* s の idx に t があるか（大文字小文字を区別しない）。 */
static int axx_q(const char *s, int slen, const char *t, int idx) {
    int tlen=(int)strlen(t);
    if(idx+tlen>slen) return 0;
    for(int i=0;i<tlen;i++)
        if(axx_upper_char(s[idx+i])!=axx_upper_char(t[i])) return 0;
    return 1;
}

/* 空白とタブを飛ばす。 */
static int axx_skipspc(const char *s, int idx) {
    while(s[idx]==' ') idx++;
    return idx;
}

/* 次の非空白が `{` か。 */
static int axx_next_nonspace_is_brace(const char *s, int slen, int idx) {
    int j = axx_skipspc(s, idx);
    return j < slen && s[j] == '{';
}

/* 空白の連なりを 1 個に潰す。ただし `"..."` と `'c'` の中は触らない。
   照合は空白の数を問わないので先に潰すが、テキストテンプレートが出す
   文字列は書いたままでなければならない。 */
static void axx_normalize_ws(char *l) {
    int in_str=0, in_ws=0;
    int i=0, w=0;
    while(l[i]){
        if(in_str){
            if(l[i]=='\\' && l[i+1]){ l[w++]=l[i++]; l[w++]=l[i++]; continue; }
            if(l[i]=='"') in_str=0;
            l[w++]=l[i++];
            continue;
        }
        if(l[i]=='"'){ in_str=1; in_ws=0; l[w++]=l[i++]; continue; }
        if(l[i]=='\''){
            int j=i+1;
            if(l[j]=='\\' && l[j+1] && l[j+2]=='\''){
                while(i<j+3) l[w++]=l[i++];
            } else if(l[j] && l[j+1]=='\''){
                while(i<j+2) l[w++]=l[i++];
            } else {
                l[w++]=l[i++];
            }
            in_ws=0;
            continue;
        }
        if(l[i]==' '||l[i]=='\t'||l[i]=='\n'||l[i]=='\r'){
            if(!in_ws){ l[w++]=' '; in_ws=1; }
            i++;
            continue;
        }
        l[w++]=l[i++];
        in_ws=0;
    }
    l[w]=0;
}

/* 空白の連なりを 1 個に潰す（リテラルの中も区別しない版）。 */
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

/* l[i] から始まる、文字列として読み飛ばす部分の長さ。無ければ 0。`"..."` は
   同じ行に閉じる `"` があるときだけ文字列で、中の `\` は次の 1 文字を逃がす。
   閉じない `"`、`\"`、文字定数 `'"'` は文字列を開かない。パターンファイルの
   コメントの開きと欄の区切り `::` を、文字列の中では効かせないために使う。
   axx.py の StringUtils.quoted_span() と同じ規則である。 */
static int axx_quoted_span(const char *l, int i){
    char c = l[i];
    if(c == '\\' && l[i+1] == '"') return 2;
    if(c == '\'' && l[i+1] == '"' && l[i+2] == '\'') return 3;
    if(c != '"') return 0;
    int j = i + 1;
    while(l[j]){
        if(l[j] == '\\' && l[j+1]){ j += 2; continue; }
        if(l[j] == '"') return j + 1 - i;
        j++;
    }
    return 0;
}

/* パターンファイルのブロックコメントを落とす。複数行にまたがるコメントは
   in_comment を次の行へ持ち越して続ける。古い書き方のための後方互換の
   判断（コメント行すべての頭に開きだけを書く流儀）は読み込み側にあり、
   ここは素の状態機械。`"..."` の中のコメントの開きはコメントにしない。 */
static void axx_remove_comment(char *l, int *in_comment) {
    int i=0, w=0;
    while(l[i]){
        if(*in_comment){
            if(l[i]=='*'&&l[i+1]=='/'){ *in_comment=0; i+=2; continue; }
            i++; continue;
        }
        int q = axx_quoted_span(l, i);
        if(q){ while(q-- > 0) l[w++]=l[i++]; continue; }
        if(l[i]=='/'&&l[i+1]=='*'){ *in_comment=1; i+=2; continue; }
        l[w++]=l[i++];
    }
    l[w]=0;
}

/* アセンブリ行を (コード, `;` コメント) に割る。`\;` は文字としての `;`。
   コメントを捨てずに返すのは、テキスト置換モードが綴りを残すため。 */
static void axx_split_comment_asm(char *l, char **cmt_out) {
    if(cmt_out) *cmt_out = NULL;
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
            if(cmt_out){
                char *c = strdup(l+i);
                if(!c){ perror("strdup"); exit(1); }
                size_t cn = strlen(c);
                while(cn>0 && (c[cn-1]==' '||c[cn-1]=='\t'
                               ||c[cn-1]=='\n'||c[cn-1]=='\r')) c[--cn]=0;
                *cmt_out = c;
            }
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

/* ソース行の `!!` と `!!!!` を 1 文字の内部表現に置き換える。
   `\!` は文字としての `!` なので先に開く。 */
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

/* 空白か VLIW スロット境界まで読む。 */
static int axx_get_param_to_spc(const char *s, int idx, char *t, size_t tsz) {
    idx=axx_skipspc(s,idx);
    size_t n=0;
    while(s[idx]&&n<tsz-1){
        if(s[idx]==' '||s[idx]==VLIW_SEP_CHAR||s[idx]==VLIW_STOP_CHAR) break;
        t[n++]=s[idx++];
    }
    t[n]=0;
    return idx;
}

/* VLIW スロット境界まで読む。 */
static int axx_get_param_to_eon(const char *s, int idx, char *t, size_t tsz) {
    idx=axx_skipspc(s,idx);
    size_t n=0;
    while(s[idx]&&n<tsz-1){
        if(s[idx]==VLIW_SEP_CHAR||s[idx]==VLIW_STOP_CHAR) break;
        t[n++]=s[idx++];
    }
    while(n>0&&(t[n-1]==' '||t[n-1]=='\t')) n--;
    t[n]=0;
    return idx;
}

/* ダブルクォートの文字列リテラルの中身を取る。エスケープは `\n` `\t` `\r`
   `\\` `\"` と `\xHH` `\uXXXX` `\UXXXXXXXX`。桁が足りない・多い場合は
   警告して書かれた文字をそのまま採る。 */
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
                if(l2[idx]&&is_xdigit_upper(axx_upper_char(l2[idx]))){
                    char r[600]; m_pyrepr(l2, r, sizeof(r));
                    axx_diagf(0, 0, " warning - '\\x' escape takes at most 2 hex digits; "
                                    "extra digit(s) treated as literal characters in: %s\n", r);
                }
                if(hn>0){
                    out[n++]=(char)(int)strtol(hex,NULL,16);
                } else {
                    char r[600]; m_pyrepr(l2, r, sizeof(r));
                    axx_diagf(0, 0, " warning - '\\x' escape requires at least one hex digit; "
                                    "treated as literal 'x' in: %s\n", r);
                    if(n<osz-1) out[n++]='x';
                }
            }
            else if(nc=='u'||nc=='U'){
                int want = (nc=='u') ? 4 : 8;
                idx+=2;
                char hex[9]; int hn=0;
                while(l2[idx]&&is_xdigit_upper(axx_upper_char(l2[idx]))&&hn<want)
                    hex[hn++]=l2[idx++];
                hex[hn]=0;
                unsigned long cp = (hn>0) ? strtoul(hex,NULL,16) : 0;
                if(hn!=want || cp>0x10FFFFul){
                    char r[600]; m_pyrepr(l2, r, sizeof(r));
                    if(hn!=want)
                        axx_diagf(0, 0, " warning - '\\%c' escape requires %d hex digits; "
                                        "treated as literal characters in: %s\n", nc, want, r);
                    else
                        axx_diagf(0, 0, " warning - invalid \\%c escape in: %s\n", nc, r);
                    if(n<osz-1) out[n++]=nc;
                    for(int hi=0; hi<hn && n<osz-1; hi++) out[n++]=hex[hi];
                } else {
                    char ub[4];
                    int ul = m_utf8(cp, ub);
                    for(int ui=0; ui<ul && n<osz-1; ui++) out[n++]=ub[ui];
                }
            }
            else              { out[n++]=nc;   idx+=2; }
        } else {
            out[n++]=l2[idx++];
        }
    }
    out[n]=0;
    if(!l2[idx]){
        char r[600]; m_pyrepr(l2, r, sizeof(r));
        axx_diagf(0, 0, " warning - unterminated string literal: %s\n", r);
    }
}

/* 文字が集合に含まれるか。 */
static int char_in(char c, const char *set){
    return strchr(set,c)!=NULL;
}

/* 続く 10 進数字を綴りのまま取る。 */
/* 浮動小数点の綴りを取る。`inf` / `-inf` / `nan` も読む。指数部は `e` の
   あとに数字が無ければ指数ではないので巻き戻す。 */
static int axx_get_floatstr(const char *s, int idx, char *fs, size_t fsz){
    if(strncmp(s+idx,"-inf",4)==0){strcpy(fs,"-inf");return idx+4;}
    if(strncmp(s+idx,"inf",3)==0){strcpy(fs,"inf");return idx+3;}
    if(strncmp(s+idx,"nan",3)==0){strcpy(fs,"nan");return idx+3;}
    size_t n=0;
    while(s[idx]&&(is_digit(s[idx])||s[idx]=='.')){
        if(n<fsz-1) fs[n++]=s[idx];
        idx++;
    }
    if(s[idx]=='e'||s[idx]=='E'){
        int saved_idx = idx;
        size_t saved_n = n;
        if(n<fsz-1) fs[n++]=s[idx];
        idx++;
        if(s[idx]=='+'||s[idx]=='-'){
            if(n<fsz-1) fs[n++]=s[idx];
            idx++;
        }
        int digits_start = idx;
        while(s[idx]&&is_digit(s[idx])){
            if(n<fsz-1) fs[n++]=s[idx];
            idx++;
        }
        if(idx == digits_start){
            idx = saved_idx;
            n   = saved_n;
        }
    }
    fs[n]=0;
    return idx;
}

/* `{ ... }` の中身を取る。 */
static int axx_get_curlb(AsmState *st, const char *s, int idx, int *f_out, char **t_out){
    idx=axx_skipspc(s,idx);
    *f_out=0; *t_out=NULL;
    if(s[idx]!='{') return idx;
    idx++;
    idx=axx_skipspc(s,idx);
    int start=idx;
    while(s[idx]&&s[idx]!='}') idx++;
    size_t n=(size_t)(idx-start);
    while(n>0&&s[start+n-1]==' ') n--;
    char *buf=malloc(n+1);
    if(!buf){ perror("malloc"); exit(1); }
    memcpy(buf,s+start,n);
    buf[n]=0;
    if(!s[idx]){
        if(should_report_errors(st)){
            axx_diagf(1, 0, " error - missing closing '}' in expression: '{%s'\n", buf);
        }
        free(buf);
        return (int)strlen(s);
    }
    idx++;
    *f_out=1;
    *t_out=buf;
    return idx;
}

/* シンボル名を 1 個取り、大文字化して返す。使える文字は `.symbolc` 次第。 */
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
        axx_diagf(0, 0, "warning - symbol name truncated to %zu characters\n", tsz-1);
    }
    return idx;
}

static char *axx_word_buf(const char *s, int idx, char *stackbuf, size_t stacksz,
                          size_t *szout){
    size_t rem = strlen(s + idx) + 1;
    if(rem <= stacksz){ *szout = stacksz; return stackbuf; }
    char *h = malloc(rem);
    if(!h){ perror("malloc"); exit(1); }
    *szout = rem;
    return h;
}

static int axx_get_label_word_ex(const char *s, int idx, const char *lwordchars,
                                 char *t_out, size_t tsz, int eat_colon){
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
        axx_diagf(0, 0, "warning - label name truncated to %zu characters\n", tsz-1);
    }
    if(eat_colon && s[idx]==':' && s[idx+1]!='=') idx++;
    return idx;
}

/* ラベル名を 1 個取る。大文字化はしない（ラベルは区別する）。 */
static int axx_get_label_word(const char *s, int idx, const char *lwordchars, char *t_out, size_t tsz){
    return axx_get_label_word_ex(s, idx, lwordchars, t_out, tsz, 1);
}

/* `::` までを 1 欄として取る。`"..."` の中の `::` では割らない
   （axx_quoted_span）。 */
static int axx_get_params1(const char *l, int idx, char *s_out, size_t ssz){
    idx=axx_skipspc(l,idx);
    if(!l[idx]){ s_out[0]=0; return idx; }
    size_t n=0;
    while(l[idx]){
        int q = axx_quoted_span(l, idx);
        if(q){
            while(q-- > 0){ if(n<ssz-1) s_out[n++]=l[idx]; idx++; }
            continue;
        }
        if(l[idx]==':'&&l[idx+1]==':'){idx+=2;break;}
        if(n<ssz-1) s_out[n++]=l[idx];
        idx++;
    }
    while(n>0&&(s_out[n-1]==' '||s_out[n-1]=='\t')) n--;
    s_out[n]=0;
    return idx;
}

/* ---- IEEE-754 変換 -----------------------------------------------------
   `!F` / `!D` / `!Q` と `.float` が通る。128bit は __float128 と
   strtoflt128 を使い、axx.py 側（Decimal で手組み）と同じビットになるよう
   inf / nan / -0.0 の形までそろえてある。
   ------------------------------------------------------------------------ */
static AXX_UNUSED uint32_t ieee754_32_from_str(const char *a){
    if(strcmp(a,"inf")==0) return 0x7F800000u;
    if(strcmp(a,"-inf")==0) return 0xFF800000u;
    if(strcmp(a,"nan")==0) return 0x7FC00000u;
    float f=(float)strtod(a,NULL);
    uint32_t r; memcpy(&r,&f,4); return r;
}
/* 64bit 倍精度のビットパターン（現在は未使用）。 */
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

#include <quadmath.h>

/* 10 進表記を __float128 にする。 */
static __float128 f128_from_decimal(const char *s)
{
    return strtoflt128(s, NULL);
}

typedef struct { __float128 val; const char *end; int ok; } F128R;

static F128R f128_expr_fn(const char *s);

/* 128bit 式の因子（数値・括弧・単項）。 */
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
        /* 綴りの終わりを先に測り、長さに上限を置かずに写す（以前は 78 文字で
           止まり、残りの桁が「読めない文字」になって倍精度の経路へ落ちていた）。 */
        const char *b=s;
        while((*s>='0'&&*s<='9')||*s=='.') s++;
        if(*s=='e'||*s=='E'){
            s++;
            if(*s=='+'||*s=='-') s++;
            while(*s>='0'&&*s<='9') s++;
        }
        size_t n=(size_t)(s-b);
        char *buf=malloc(n+1);
        if(!buf){ perror("malloc"); exit(1); }
        memcpy(buf,b,n); buf[n]='\0';
        r.val=f128_from_decimal(buf);
        free(buf);
        r.end=s;
        return r;
    }
    r.ok=0; return r;
}

/* 128bit 式の乗除。 */
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

/* 128bit 式の加減。`qad{...}` の中身がここを通る。 */
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

/* __float128 のビットパターンを 256bit 整数に移す。 */
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

/* 有限値か。 */
static int f128_is_finite(__float128 v)
{
    uint256_t u = f128_to_u256(v);
    uint64_t exp = (u.w[1] >> 48) & 0x7FFFu;
    return exp != 0x7FFFu;
}

/* 128bit 精度のまま式を評価し、ビットパターンを返す。 */
static uint256_t f128_eval_text(const char *text, int *ok_out)
{
    F128R r = f128_expr_fn(text);
    if(r.ok && r.end){
        const char *p = r.end;
        while(*p==' '||*p=='\t') p++;
        if(*p) r.ok = 0;
    }
    if(r.ok && !f128_is_finite(r.val)) r.ok = 0;
    if(ok_out) *ok_out = r.ok;
    if(!r.ok)  return u256_zero();
    return f128_to_u256(r.val);
}

#endif

/* `!Q` 用。128bit 四倍精度のビットパターン。 */
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
        uint256_t r = u256_zero();
        if(signbit(ld)) r.w[1] = (uint64_t)1ULL<<63;
        return r;
    }
    int sign = (ld < 0.0L) ? 1 : 0;
    if(ld < 0.0L) ld = -ld;
    int fe = 0;
    long double sig = frexpl(ld, &fe);
    sig *= 2.0L;
    int exp_unbiased = fe - 1;
    int biased_exp = exp_unbiased + 16383;
    int subnorm_shift = 0;
    if(biased_exp <= 0) { subnorm_shift = 1 - biased_exp; biased_exp = 0; }
    if(biased_exp >= 32767) {
        uint256_t r=u256_zero();
        r.w[1] = (uint64_t)(sign?1ULL:0ULL)<<63 | 0x7FFF000000000000ULL;
        return r;
    }
    long double frac_part = (subnorm_shift > 0) ? ldexpl(sig, -subnorm_shift) : (sig - 1.0L);
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

/* 32bit のビットパターンを float として読み直す。 */
static double enfloat_bits(uint64_t a){
    uint32_t u=(uint32_t)a; float f; memcpy(&f,&u,4); return (double)f;
}
/* 64bit のビットパターンを double として読み直す。 */
static double endouble_bits(uint64_t a){
    double d; memcpy(&d,&a,8); return d;
}

/* 256bit 整数のビットを double として読む。 */
static inline double u256_to_double(uint256_t v){
    double d; memcpy(&d, &v.w[0], 8); return d;
}
/* double のビットを 256bit 整数に移す。 */
static inline uint256_t double_to_u256(double d){
    uint256_t r = u256_zero(); memcpy(&r.w[0], &d, 8); return r;
}
static double u256_int_to_double(uint256_t v);
/* その位置から浮動小数点として読めるか。 */
static int axx_isfloatstr(const char *s, int idx){
    if(!s[idx]) return 0;
    if(strncmp(s+idx,"-inf",4)==0) return 1;
    if(strncmp(s+idx,"inf",3)==0) return 1;
    if(strncmp(s+idx,"nan",3)==0) return 1;
    if(is_digit(s[idx])) return 1;
    if(s[idx]=='.') return 1;
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

/* 部品をつないでアセンブラを組み立てる。 */
static void assembler_init(Assembler *a){
    state_init(&a->st);
    secrangevec_init(&a->imp_sections);
}

/* アドレスを現在の `.align` の倍数まで繰り上げる。 */
static uint256_t align_addr256(AsmState *st, uint256_t addr){
    if(u256_is_zero(st->align)) return addr;
    uint256_t q = u256_udiv(addr, st->align);
    uint256_t a = u256_sub(addr, u256_mul(q, st->align));
    if(u256_is_zero(a)) return addr;
    return u256_add(addr, u256_sub(st->align, a));
}

/* 出力ワードのビット数から下位マスクを作る。 */
static uint64_t axx_word_mask(int bts){
    if(bts <= 0)  return 0;
    if(bts >= 64) return (uint64_t)-1;
    return ((uint64_t)1 << bts) - 1;
}

/* 1 ワードを出力バッファに溜める。 */
static void outbin_store(AsmState *st, uint64_t position, uint256_t word_val){
    if(st->bts <= 0) return;
    uint64_t v = u256_to_u64(word_val) & axx_word_mask(st->bts);
    bufmap_set(&st->buf, position, v);
}

/* 1 ワードを溜め、prt ならリスティングにも 16 進で出す。 */
static void fwrite_word(AsmState *st, uint64_t position, uint256_t x, int prt){
    if(st->bts <= 0) return;
    uint64_t mask = axx_word_mask(st->bts);
    uint64_t val = u256_to_u64(x) & mask;
    if(prt){
        int colm=(st->bts+3)/4;
        printf(" 0x%0*llx",(int)colm,(unsigned long long)val);
    }
    outbin_store(st, position, u256_from_u64(val));
}

/* 1 ワードを溜め、`-v` のパス2か対話モードならリスティングにも出す。 */
static void outbin(AsmState *st, uint256_t a, uint256_t x){
    if(should_report_errors(st))
        fwrite_word(st, u256_to_u64(a), x, (st->pas==0)||st->verbose);
}
/* 1 ワードを溜める（リスティングには出さない）。 */
static void outbin2(AsmState *st, uint256_t a, uint256_t x){
    if(should_report_errors(st))
        fwrite_word(st, u256_to_u64(a), x, 0);
}

/* 溜めたワードを `-b` のファイルへ書き出す。隙間は `.padding` で埋め、
   各ワードは `.bits` のバイト数とバイト順で並べる。`.org` の飛び先が極端で
   出力が大きすぎるときは、書く代わりにそれを疑うよう促してやめる。
   `-o` と併用のときは、リンカのために 0 で残した命令欄があれば警告する。 */
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
    uint256_t _tot256 = u256_mul(u256_add(u256_from_u64(max_pos), u256_from_u64(1)),
                                  u256_from_u64((uint64_t)bytes_per_word));
    const uint64_t MAX_OUTPUT_BYTES = (uint64_t)1<<30;
    if(u256_gt_signed(_tot256, u256_from_u64(MAX_OUTPUT_BYTES))){
        char _tb[96]; u256_to_pydec(_tot256, _tb, sizeof(_tb));
        axx_diagf(1, 1, " error - output size %s bytes exceeds maximum %llu."
                        " Check for incorrect .ORG or address values.\n",
                  _tb, (unsigned long long)MAX_OUTPUT_BYTES);
        return;
    }
    uint64_t total_size = u256_to_u64(_tot256);
    if(total_size==0) return;
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
    if(!fp){
        char eb[2*PATH_MAX + 256]; axx_oserr_str(st->outfile, errno, eb, sizeof(eb));
        axx_diagf(1, 0, " error - cannot write '%s': %s\n", st->outfile, eb);
        free(data);
        return;
    }
    if(total_size) fwrite(data,1,(size_t)total_size,fp);
    if(axx_close_out(fp, st->outfile)){ free(data); return; }
    fprintf(stderr,"wrote raw binary %s (%llu bytes)\n",st->outfile,(unsigned long long)total_size);
    free(data);

    if(st->elf_objfile[0]){
        int _nz = 0;
        char _where[256]; size_t _wl = 0; _where[0] = '\0';
        for(int i = 0; i < st->reloc_count; i++){
            if(insn_reloc_field_mask(st, st->relocations[i].rtype) == 0) continue;
            _nz++;
            if(_nz <= 4){
                int _n = snprintf(_where + _wl, sizeof(_where) - _wl, "%s%s+0x%llx",
                                  _nz > 1 ? ", " : "",
                                  st->relocations[i].section,
                                  (unsigned long long)st->relocations[i].sec_offset);
                if(_n > 0 && (size_t)_n < sizeof(_where) - _wl) _wl += (size_t)_n;
            }
        }
        if(_nz > 0){
            if(_nz > 4) snprintf(_where + _wl, sizeof(_where) - _wl, ", ...");
            axx_diagf(0, 1, " warning - %d instruction field(s) were left 0 for the"
                            " linker (%s); this raw binary is only correct after linking"
                            " %s. Drop -o to have axx fill them in.\n",
                      _nz, _where, st->elf_objfile);
        }
    }
}

/* その変数が未定義ラベル由来の値を持っているか。 */
static int var_slot_is_undef(AsmState *st, int slot){
    if(slot>=0 && slot<NVARS) return st->vars[slot].is_undef;
    return 0;
}
/* 変数の値を、整数／浮動小数点どちらの読み方で返すか選ぶ。 */
static uint256_t var_slot_for_mode(AsmState *st, int slot, int want_float){
    if(slot<0||slot>=NVARS) return u256_zero();
    PatVar *pv = &st->vars[slot];
    if(want_float && !pv->is_float && !u256_is_undef(pv->val))
        return double_to_u256(u256_int_to_double(pv->val));
    return pv->val;
}
typedef struct { int slot; PatVar old; } VarUndo;
static VarUndo *g_vundo = NULL;
static int      g_vundo_len = 0, g_vundo_cap = 0;

static int g_vtouched[NVARS];
static int g_vtouched_list[NVARS];
static int g_vtouched_n = 0;

/* 変数を書き換えたことを記録する。照合の試行が失敗したときに、
   ここまで巻き戻すために使う。 */
static void var_note_write(AsmState *st, int slot){
    if(slot < 0 || slot >= NVARS) return;
    if(g_vundo_len >= g_vundo_cap){
        g_vundo_cap = g_vundo_cap ? g_vundo_cap * 2 : 64;
        g_vundo = realloc(g_vundo, (size_t)g_vundo_cap * sizeof(*g_vundo));
        if(!g_vundo){ perror("realloc"); exit(1); }
    }
    g_vundo[g_vundo_len].slot = slot;
    g_vundo[g_vundo_len].old  = st->vars[slot];
    g_vundo_len++;
    if(!g_vtouched[slot]){ g_vtouched[slot] = 1; g_vtouched_list[g_vtouched_n++] = slot; }
}

static int vars_mark(void){ return g_vundo_len; }

/* 変数の束縛を mark の時点まで巻き戻す。巻き戻さないと、当たらなかった
   試行の束縛が出力に化けて出る。 */
static void vars_rollback(AsmState *st, int mark){
    while(g_vundo_len > mark){
        g_vundo_len--;
        st->vars[g_vundo[g_vundo_len].slot] = g_vundo[g_vundo_len].old;
    }
}

/* すべての変数の束縛を消す。 */
static void vars_clear_all(AsmState *st){
    for(int i = 0; i < g_vtouched_n; i++){
        int sl = g_vtouched_list[i];
        st->vars[sl].val      = u256_zero();
        st->vars[sl].is_undef = 0;
        st->vars[sl].text_off = -1;
        g_vtouched[sl] = 0;
    }
    g_vtouched_n  = 0;
    g_vundo_len   = 0;
}

/* すべての変数を「書き換えた」ことにする。 */
static void vars_touch_all(void){
    g_vundo_len  = 0;
    g_vtouched_n = 0;
    for(int sl = 0; sl < g_nvars; sl++){ g_vtouched[sl] = 1; g_vtouched_list[g_vtouched_n++] = sl; }
}

typedef struct { int slot; int set; char *label_name; uint64_t label_val; } V2lUndo;
static V2lUndo *g_v2lundo = NULL;
static int      g_v2lundo_len = 0, g_v2lundo_cap = 0;

/* 変数 → ラベルの対応を書き換えたことを記録する（`-o` の追跡用）。 */
static void v2l_note_write(AsmState *st, int slot){
    if(slot < 0 || slot >= NVARS) return;
    if(g_v2lundo_len >= g_v2lundo_cap){
        g_v2lundo_cap = g_v2lundo_cap ? g_v2lundo_cap * 2 : 32;
        g_v2lundo = realloc(g_v2lundo, (size_t)g_v2lundo_cap * sizeof(*g_v2lundo));
        if(!g_v2lundo){ perror("realloc"); exit(1); }
    }
    g_v2lundo[g_v2lundo_len].slot       = slot;
    g_v2lundo[g_v2lundo_len].set        = st->elf_var_to_label[slot].set;
    g_v2lundo[g_v2lundo_len].label_val  = st->elf_var_to_label[slot].label_val;
    g_v2lundo[g_v2lundo_len].label_name = st->elf_var_to_label[slot].label_name;
    st->elf_var_to_label[slot].label_name = NULL;
    g_v2lundo_len++;
}

static int v2l_mark(void){ return g_v2lundo_len; }

/* その記録を捨てる。 */
static void v2l_forget(void){
    while(g_v2lundo_len > 0){
        g_v2lundo_len--;
        free(g_v2lundo[g_v2lundo_len].label_name);
    }
}

/* その記録を mark の時点まで巻き戻す。 */
static void v2l_rollback(AsmState *st, int mark){
    while(g_v2lundo_len > mark){
        g_v2lundo_len--;
        int sl = g_v2lundo[g_v2lundo_len].slot;
        free(st->elf_var_to_label[sl].label_name);
        st->elf_var_to_label[sl].set        = g_v2lundo[g_v2lundo_len].set;
        st->elf_var_to_label[sl].label_val  = g_v2lundo[g_v2lundo_len].label_val;
        st->elf_var_to_label[sl].label_name = g_v2lundo[g_v2lundo_len].label_name;
    }
}

/* 変数に値と「未定義由来か」の印を束縛する。 */
static void var_slot_put_tagged(AsmState *st, int slot, uint256_t v, int is_undef){
    if(slot<0||slot>=NVARS) return;
    var_note_write(st, slot);
    st->vars[slot].val=v; st->vars[slot].is_undef=is_undef; st->vars[slot].is_float=st->exp_typ_float;
}
/* 変数に値を束縛する。 */
static void var_slot_put(AsmState *st, int slot, uint256_t v){
    var_slot_put_tagged(st, slot, v, 0);
}

/* ラベル差の候補の 2 つ目以降のラベル。取り込み 1 回の間だけ使う。 */
static char   **g_v2l_pend_name[NVARS];
static uint64_t *g_v2l_pend_val[NVARS];
static int      g_v2l_pend_n[NVARS], g_v2l_pend_cap[NVARS];

static void elf_v2l_pend_clear(int vi){
    for(int i = 0; i < g_v2l_pend_n[vi]; i++) free(g_v2l_pend_name[vi][i]);
    g_v2l_pend_n[vi] = 0;
}
static void elf_v2l_pend_push(int vi, const char *k, uint64_t v){
    if(g_v2l_pend_n[vi] >= g_v2l_pend_cap[vi]){
        g_v2l_pend_cap[vi] = g_v2l_pend_cap[vi] ? g_v2l_pend_cap[vi] * 2 : 4;
        g_v2l_pend_name[vi] = realloc(g_v2l_pend_name[vi], sizeof(char*) * (size_t)g_v2l_pend_cap[vi]);
        g_v2l_pend_val[vi]  = realloc(g_v2l_pend_val[vi], sizeof(uint64_t) * (size_t)g_v2l_pend_cap[vi]);
        if(!g_v2l_pend_name[vi] || !g_v2l_pend_val[vi]){ perror("realloc"); exit(1); }
    }
    g_v2l_pend_name[vi][g_v2l_pend_n[vi]] = strdup(k);
    g_v2l_pend_val[vi][g_v2l_pend_n[vi]] = v;
    g_v2l_pend_n[vi]++;
}

static int elf_diff_wordch(int c){
    return isalnum(c) || c == '_' || c == '.' || c == '$';
}

/* 取り込んだ式の綴りから、ラベルの 1 次結合（ラベル差）を読み取る。式が
   `+` `-` `(` `)`、数、ラベルだけでできていて、どのラベルの係数も +1 か -1
   なら、項を「符号と名前」を \x01 で区切って並べた文字列を返し、Σ符号×値を
   *sum に置く。項は綴りに初めて現れた順。それ以外は NULL（曖昧）。
   axx.py の _elf_diff_resolve() と同じ規則である。 */
static char *elf_diff_resolve(const char *t, int L, char **names, const uint64_t *vals, int n,
                              uint64_t *sum){
    for(int a = 0; a < n; a++)
        for(int b = a + 1; b < n; b++)
            if(strcasecmp(names[a], names[b]) == 0) return NULL;
    int *coef = calloc((size_t)n, sizeof(int));
    int *ord = calloc((size_t)n, sizeof(int));
    int *seen = calloc((size_t)n, sizeof(int));
    int *stk = malloc(sizeof(int) * (size_t)(L + 2));
    if(!coef || !ord || !seen || !stk){ perror("alloc"); exit(1); }
    int nord = 0, sp = 0, sign = 1, expect = 1, ok = 1;
    stk[0] = 1;
    int i = 0;
    while(i < L && ok){
        char c = t[i];
        if(c == ' ' || c == '\t' || c == '\0'){ i++; continue; }
        if(c == '+' || c == '-'){
            int sg = c == '-' ? -1 : 1;
            if(expect) sign *= sg; else { sign = sg; expect = 1; }
            i++; continue;
        }
        if(c == '('){
            if(!expect){ ok = 0; break; }
            stk[sp + 1] = stk[sp] * sign; sp++;
            sign = 1; i++; continue;
        }
        if(c == ')'){
            if(sp == 0 || expect){ ok = 0; break; }
            sp--; i++; continue;
        }
        if(elf_diff_wordch((unsigned char)c) || c == '\''){
            if(!expect){ ok = 0; break; }
            int j;
            if(c == '\''){
                j = i + 1;
                while(j < L && t[j] != '\'') j++;
                if(j >= L){ ok = 0; break; }
                j++;
            } else {
                j = i;
                while(j < L && elf_diff_wordch((unsigned char)t[j])) j++;
                for(int k = 0; k < n; k++){
                    if((int)strlen(names[k]) == j - i && strncasecmp(names[k], t + i, (size_t)(j - i)) == 0){
                        if(!seen[k]){ seen[k] = 1; ord[nord++] = k; }
                        coef[k] += stk[sp] * sign;
                        break;
                    }
                }
            }
            expect = 0; sign = 1; i = j; continue;
        }
        ok = 0;
    }
    if(sp != 0 || expect || nord != n) ok = 0;
    for(int k = 0; ok && k < n; k++) if(coef[k] != 1 && coef[k] != -1) ok = 0;
    char *out = NULL;
    if(ok){
        size_t tot = 1;
        for(int k = 0; k < n; k++) tot += strlen(names[k]) + 2;
        out = malloc(tot);
        if(!out){ perror("malloc"); exit(1); }
        size_t p = 0;
        uint64_t sv = 0;
        for(int q = 0; q < nord; q++){
            int k = ord[q];
            if(q) out[p++] = '\x01';
            out[p++] = coef[k] > 0 ? '+' : '-';
            size_t l = strlen(names[k]);
            memcpy(out + p, names[k], l); p += l;
            sv += coef[k] > 0 ? vals[k] : (uint64_t)0 - vals[k];
        }
        out[p] = '\0';
        *sum = sv;
    }
    free(coef); free(ord); free(seen); free(stk);
    return out;
}

/* 変数の取り込みが終わったところで、ラベル差の候補を決める。決まれば名前を
   項の並び（elf_diff_resolve() の形）、値を Σ符号×値にして set を 3 にする。
   決まらなければ曖昧（-1）。 */
static void elf_v2l_finish(AsmState *st, int vi, const char *text, int len){
    if(!st->elf_tracking || vi < 0 || vi >= NVARS) return;
    if(st->elf_var_to_label[vi].set == 1){
        /* ラベルが 1 つでも符号が負（`-a+5` など）なら、`.elfdiff` があれば引く型
           だけのラベル差に、無ければ曖昧にする。axx.py の _elf_v2l_finish() と同じ。 */
        char *nm1[1] = { st->elf_var_to_label[vi].label_name };
        uint64_t v1[1] = { st->elf_var_to_label[vi].label_val };
        uint64_t sv1 = 0;
        char *c1 = elf_diff_resolve(text, len, nm1, v1, 1, &sv1);
        if(c1 && c1[0] == '-'){
            v2l_note_write(st, vi);
            if(elf_diff_any(st)){
                st->elf_var_to_label[vi].set = 3;
                st->elf_var_to_label[vi].label_name = c1;
                st->elf_var_to_label[vi].label_val = sv1;
                c1 = NULL;
            } else {
                st->elf_var_to_label[vi].set = -1;
                st->elf_var_to_label[vi].label_name = NULL;
            }
        }
        free(c1);
        return;
    }
    if(st->elf_var_to_label[vi].set != 2) return;
    int n = 1 + g_v2l_pend_n[vi];
    char **names = malloc(sizeof(char*) * (size_t)n);
    uint64_t *vals = malloc(sizeof(uint64_t) * (size_t)n);
    if(!names || !vals){ perror("malloc"); exit(1); }
    names[0] = st->elf_var_to_label[vi].label_name;
    vals[0] = st->elf_var_to_label[vi].label_val;
    for(int k = 1; k < n; k++){ names[k] = g_v2l_pend_name[vi][k-1]; vals[k] = g_v2l_pend_val[vi][k-1]; }
    uint64_t sv = 0;
    char *comb = elf_diff_resolve(text, len, names, vals, n, &sv);
    free(names); free(vals);
    v2l_note_write(st, vi);
    if(comb){
        st->elf_var_to_label[vi].set = 3;
        st->elf_var_to_label[vi].label_name = comb;
        st->elf_var_to_label[vi].label_val = sv;
    } else {
        st->elf_var_to_label[vi].set = -1;
        st->elf_var_to_label[vi].label_name = NULL;
    }
    elf_v2l_pend_clear(vi);
}

/* ラベルの値を読む。パスごとに「未確定」の扱いが変わる。
   パス1で前回の反復の値があればそれ、最初の反復なら現在の PC（楽観的に
   短い符号化から試す）、長さだけ見ている区間なら 0、それ以外は UNDEF。
   診断を出すのは照合の試行中でなく、かつ報告してよいパスのときだけ。
   `-o` の追跡中は、この参照がどの変数・どの出力ワードから来たかを記録する。 */
static uint256_t label_get_value(AsmState *st, const char *k){
    LabelEntry *e=lmap_find(&st->labels,k);
    if(e){
        uint256_t ret_val = e->value;
        const char *sec = e->section ? e->section : "";
        if(st->equ_section_tracking){
            int _seen = 0;
            for(int _i = 0; _i < st->equ_nsecs; _i++)
                if(strcmp(st->equ_secs[_i], sec) == 0){ _seen = 1; break; }
            if(!_seen){
                if(st->equ_nsecs >= st->equ_secs_cap){
                    st->equ_secs_cap = st->equ_secs_cap ? st->equ_secs_cap * 2 : 4;
                    st->equ_secs = realloc(st->equ_secs, (size_t)st->equ_secs_cap * sizeof(char*));
                    if(!st->equ_secs){ perror("realloc"); exit(1); }
                }
                st->equ_secs[st->equ_nsecs] = strdup(sec);
                if(!st->equ_secs[st->equ_nsecs]){ perror("strdup"); exit(1); }
                st->equ_nsecs++;
            }
            int64_t _adj = equ_section_relative_offset(st, sec, u256_to_u64(e->value));
            if(_adj >= 0) ret_val = u256_from_u64((uint64_t)_adj);
        } else if(st->in_binary_list && strcmp(sec, st->current_section) == 0){
            int64_t _adj = equ_section_relative_offset(st, sec, u256_to_u64(e->value));
            if(_adj >= 0) ret_val = u256_from_u64((uint64_t)_adj);
        }
        int _equ_has_reloc = e->is_equ && (e->reloc_type_override >= 0);
        if(st->elf_tracking && (!e->is_equ || _equ_has_reloc)){
            if(st->elf_capturing_var >= 0){
                int vi = st->elf_capturing_var;
                if(vi >= 0 && vi < g_nvars){
                    if(st->elf_var_to_label[vi].set == 0){
                        v2l_note_write(st, vi);
                        st->elf_var_to_label[vi].set = 1;
                        st->elf_var_to_label[vi].label_name = strdup(k);
                        st->elf_var_to_label[vi].label_val = u256_to_u64(e->value);
                    } else if(st->elf_var_to_label[vi].set == 1 && elf_diff_any(st)){
                        /* `.elfdiff` があればラベル差の候補にする。各ラベルの
                           符号は取り込みが終わってから elf_v2l_finish() が
                           決める。axx.py の _elf_v2l_second() と同じ規則。 */
                        char *first = strdup(st->elf_var_to_label[vi].label_name);
                        uint64_t fv = st->elf_var_to_label[vi].label_val;
                        v2l_note_write(st, vi);
                        st->elf_var_to_label[vi].set = 2;
                        st->elf_var_to_label[vi].label_name = first;
                        st->elf_var_to_label[vi].label_val = fv;
                        elf_v2l_pend_clear(vi);
                        elf_v2l_pend_push(vi, k, u256_to_u64(e->value));
                    } else if(st->elf_var_to_label[vi].set == 2){
                        elf_v2l_pend_push(vi, k, u256_to_u64(e->value));
                    } else {
                        v2l_note_write(st, vi);
                        st->elf_var_to_label[vi].set = -1;
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
                st->elf_refs[st->elf_refs_len].rtype    = 0;
                st->elf_refs[st->elf_refs_len].addend   = 0;
                st->elf_refs_len++;
            }
        }
        return ret_val;
    }
    if(st->pas == 1 && st->relax_prev){
        LabelEntry *pe = lmap_find(st->relax_prev, k);
        if(pe){
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
        axx_diagf(1, 0, " error - Label undefined: '%s'  [%s:%d]\n",
                   k, st->current_file, (int)st->ln);
    }
    return UNDEF_VAL();
}
/* ラベルが属するセクション名。 */
static const char *label_get_section(AsmState *st, const char *k){
    LabelEntry *e=lmap_find(&st->labels,k);
    if(e) return e->section;
    st->error_undefined_label=1;
    return "";
}
static void report_definition_error(AsmState *st, const char *kind, const char *key,
                                    const char *fmt, ...){
    st->had_error = 1;
    char tag[600];
    snprintf(tag, sizeof(tag), "%s:%s", kind, key);
    for(int i=0;i<st->reported_label_errors.len;i++)
        if(strcmp(st->reported_label_errors.data[i], tag)==0) return;
    sv_push(&st->reported_label_errors, tag);

    char body[1024];
    va_list ap; va_start(ap, fmt);
    vsnprintf(body, sizeof(body), fmt, ap);
    va_end(ap);
    axx_diagf(1, 1, " error - %s  [%s:%d]\n",
              body, st->current_file, (int)st->ln);
}

/* ラベルを定義する。二重定義、パス1に無くパス2で現れた名前、パターン
   ファイルのシンボルとの衝突を弾く。 */
static int label_put_value(AsmState *st, const char *k, uint256_t v, const char *sec, int is_equ, int reloc_type, int is_undef){
    if(st->pas==1||st->pas==0){
        LabelEntry *_existing = lmap_find(&st->labels,k);
        if(_existing && !_existing->is_imported){
            report_definition_error(st, "dup", k, "label '%s' is already defined.", k);
            return 0;
        }
    } else if(st->pas==2){
        if(!lmap_contains(&st->labels,k)){
            report_definition_error(st, "pass1", k, "label '%s' not defined in pass 1.", k);
            return 0;
        }
    }
    char uk_stackbuf[512]; size_t uk_sz;
    char *uk = axx_word_buf(k, 0, uk_stackbuf, sizeof(uk_stackbuf), &uk_sz);
    axx_strupr_to(uk,k,uk_sz);
    uint256_t dummy;
    if(smap_get(&st->patsymbols,uk,&dummy)){
        report_definition_error(st, "patsym", k, "'%s' is a pattern file symbol.", k);
        if(uk != uk_stackbuf) free(uk);
        return 0;
    }
    if(uk != uk_stackbuf) free(uk);
    lmap_set(&st->labels,k,v,sec,is_equ,is_undef);
    if(reloc_type >= 0)
        lmap_set_reloc_type(&st->labels, k, reloc_type);
    return 1;
}
#if defined(__GNUC__)
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wformat-truncation"
#endif
/* 256bit 整数を Python の hex() と同じ綴りにする。 */
static void u256_to_pyhex(uint256_t a, char *out, size_t outsz){
    char buf[96]; size_t n=0; int neg=0;
    if((a.w[3]>>63)&1ULL){ neg=1; a=u256_neg(a); }
    int hi=3; while(hi>0 && a.w[hi]==0) hi--;
    n += (size_t)snprintf(buf+n,sizeof(buf)-n,"%llx",(unsigned long long)a.w[hi]);
    for(int i=hi-1;i>=0;i--)
        n += (size_t)snprintf(buf+n,sizeof(buf)-n,"%016llx",(unsigned long long)a.w[i]);
    snprintf(out,outsz,"%s0x%s",neg?"-":"",buf);
}
#if defined(__GNUC__)
#pragma GCC diagnostic pop
#endif

/* 256bit 整数を 10 進の綴りにする。 */
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

/* ラベル名を並べるための比較関数。 */
static int label_key_cmp(const void *pa, const void *pb){
    const LabelEntry *a = *(const LabelEntry *const *)pa;
    const LabelEntry *b = *(const LabelEntry *const *)pb;
    return strcmp(a->key, b->key);
}

/* ラベル表を標準エラーへ並べる。プロンプトモードの `?` の中身。 */
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
        char val[96];
        if(v[i]->is_undef) snprintf(val,sizeof(val),"UNDEF");
        else u256_to_pyhex(v[i]->value,val,sizeof(val));
        fprintf(stderr,"  %-40s  %s  (%s)\n",v[i]->key,val,v[i]->section);
    }
    free(v);
}

static struct ArrSym *arrsym_get(AsmState *st, const char *upper_name);

/* シンボルの値を取る。 */
static int symbol_get(AsmState *st, const char *w, uint256_t *out){
    char uw[512]; axx_strupr_to(uw,w,sizeof(uw));
    return smap_get(&st->symbols,uw,out);
}

/* 変数 vi が捕らえるシンボルの値を引く。`.unordered` の `.map` が作った
   変数ごとの表があればそこから引く（axx.py の match() の _sget と同じ）。 */
static int cap_sym_get(AsmState *st, int vi, const char *w, uint256_t *out){
    SymMap *tb = (vi >= 0 && vi < NVARS) ? st->var_tables[vi] : NULL;
    if(!tb) return symbol_get(st, w, out);
    char uw[512]; axx_strupr_to(uw,w,sizeof(uw));
    return smap_get(tb,uw,out);
}

/* 256bit 整数のビットを long double として読む。 */
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

/* ---- long double での式評価 ---------------------------------------------
   浮動小数点のリテラルと部分式を、本体の 256bit 評価器とは別に long double で
   解くための小さな再帰下降。`!F` / `!D` / `!Q` の値を作るときに使う。
   ------------------------------------------------------------------------ */
static void xeval_skip(XEP *p){
    while(p->i<p->len && (p->s[p->i]==' '||p->s[p->i]=='\t')) p->i++;
}

/* 項そのもの（数値・括弧）。 */
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

/* `**`。 */
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

/* 単項 `-` `+` `~`。 */
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

/* `*` `/` `%`。 */
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

/* `+` `-`。 */
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

/* `<<` `>>`。 */
static long double xeval_shift(XEP *p){
    long double v = xeval_addsub(p);
    while(p->ok){
        xeval_skip(p);
        if(p->i+1<p->len && p->s[p->i]=='<' && p->s[p->i+1]=='<'){
            p->i+=2; long double t=xeval_addsub(p);
            int64_t sh=(int64_t)t;
            if(sh<0 || sh>63){ p->ok=0; break; }
            v = (long double)((int64_t)v << sh);
        } else if(p->i+1<p->len && p->s[p->i]=='>' && p->s[p->i+1]=='>'){
            p->i+=2; long double t=xeval_addsub(p);
            int64_t sh=(int64_t)t;
            if(sh<0 || sh>63){ p->ok=0; break; }
            v = (long double)((int64_t)v >> sh);
        } else break;
    }
    return v;
}

/* `&`。 */
static long double xeval_band(XEP *p){
    long double v = xeval_shift(p);
    while(p->ok){
        xeval_skip(p);
        if(p->i<p->len && p->s[p->i]=='&'){ p->i++; v = (long double)((int64_t)v & (int64_t)xeval_shift(p)); }
        else break;
    }
    return v;
}

/* `^`。 */
static long double xeval_bxor(XEP *p){
    long double v = xeval_band(p);
    while(p->ok){
        xeval_skip(p);
        if(p->i<p->len && p->s[p->i]=='^'){ p->i++; v = (long double)((int64_t)v ^ (int64_t)xeval_band(p)); }
        else break;
    }
    return v;
}

/* 式を 1 個解く。 */
static long double xeval_expr(XEP *p){
    long double v = xeval_bxor(p);
    while(p->ok){
        xeval_skip(p);
        if(p->i<p->len && p->s[p->i]=='|'){ p->i++; v = (long double)((int64_t)v | (int64_t)xeval_bxor(p)); }
        else break;
    }
    return v;
}

/* テキストを評価して double で返す。読めなければ 0 を返す。 */
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
static int expr_num_operand(Assembler *asmb, uint256_t v, uint256_t *out);
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

static const char *g_expr_slen_ptr = NULL;
static int         g_expr_slen_len = 0;
/* ---- 式評価器 -----------------------------------------------------------
   優先順位ごとに 1 関数の再帰下降。アセンブリ行・パターン行・ミニ言語・
   マクロ層がすべてこれを通るので、どの層でも同じ式が同じ値になる。
   使える項の違いは状態の expmode / expcaps だけで表し、評価器は呼び出し元を
   知らない。優先順位は Python に倣う。
   ------------------------------------------------------------------------ */
static inline int expr_slen(const char *s){
    if(s == g_expr_slen_ptr) return g_expr_slen_len;
    return (int)strlen(s);
}

/* 末尾に NUL を足して式の終わりを確定させる。 */
static char *expr_terminate(const char *s){
    size_t l = strlen(s);
    char *r = malloc(l + 2);
    if(!r){ perror("malloc"); exit(1); }
    memcpy(r, s, l);
    r[l]   = '\0';
    r[l+1] = '\0';
    return r;
}

/* パターン行の式として評価する（すべての項が使える）。 */
static uint256_t expr_expression_pat(Assembler *asmb, const char *s, int idx, int *idx_out){
    asmb->st.expmode=EXP_PAT;
    asmb->st.expcaps=&CAPS_PAT;
    if(s == g_expr_slen_ptr) return expr_expression(asmb,s,idx,idx_out);
    char *ts=expr_terminate(s);
    uint256_t r=expr_expression(asmb,ts,idx,idx_out);
    free(ts);
    return r;
}
static uint256_t expr_expression_caps(Assembler *asmb, const char *s, int idx,
                                       const ExprCaps *caps, int *idx_out){
    int prev_mode = asmb->st.expmode;
    const ExprCaps *prev_caps = asmb->st.expcaps;
    asmb->st.expmode=EXP_PAT;
    asmb->st.expcaps=caps;
    char *ts=expr_terminate(s);
    uint256_t r=expr_expression(asmb,ts,idx,idx_out);
    free(ts);
    asmb->st.expmode=prev_mode;
    asmb->st.expcaps=prev_caps;
    return r;
}
/* アセンブリ行の式として評価する（パターン変数と VLIW 計数は無い）。 */
static uint256_t expr_expression_asm(Assembler *asmb, const char *s, int idx, int *idx_out){
    asmb->st.expmode=EXP_ASM;
    asmb->st.expcaps=&CAPS_ASM;
    char *ts=expr_terminate(s);
    uint256_t r=expr_expression(asmb,ts,idx,idx_out);
    free(ts);
    return r;
}
/* 入れ子の外側にある stopchar までを 1 つの式として評価する。 */
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
            if(stkp > 0) stkp--;
            buf[i] = c;
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


/* 単項演算子と組み込み項（`*(x,y)`、`!!!`、`!!!!`）。 */
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
/* expr_factor の本体。 */
static uint256_t expr_factor_impl(Assembler *asmb, const char *s, int idx, int *idx_out){
    AsmState *st=&asmb->st;
    idx=axx_skipspc(s,idx);
    uint256_t x=u256_zero();
    int slen=expr_slen(s);

    if(idx+4<=slen && strncmp(s+idx,"!!!!",4)==0 && st->expcaps->vliw){
        x=u256_from_i64(st->vliwstop); idx+=4;
        if(asmb->st.exp_typ_float) x=double_to_u256((double)st->vliwstop);
    } else if(idx+3<=slen && strncmp(s+idx,"!!!",3)==0 && st->expcaps->vliw){
        x=u256_from_i64(st->vcnt); idx+=3;
        if(asmb->st.exp_typ_float) x=double_to_u256((double)st->vcnt);
    } else if(s[idx]=='-'){
        x=expr_factor(asmb,s,idx+1,&idx);
        if(u256_is_undef(x)){
            /* 未定義のまま */
        } else if(asmb->st.exp_typ_float){
            double d=u256_to_double(x);
            x=double_to_u256(-d);
        } else {
            x=u256_neg(x);
        }
    } else if(s[idx]=='~'){
        x=expr_factor(asmb,s,idx+1,&idx);
        if(!u256_is_undef(x))
            x=expr_bitwise_result(asmb,u256_not(expr_safe_bitwise_operand(asmb,x,"~")));
    } else if(s[idx]=='@'){
        x=expr_factor(asmb,s,idx+1,&idx);
        if(!u256_is_undef(x)){
            int nb = op_msb(expr_safe_bitwise_operand(asmb,x,"@"));
            if(asmb->st.exp_typ_float)
                x=double_to_u256((double)nb);
            else
                x=u256_from_i64(nb);
        }
    } else if(s[idx]=='*'){
        if(idx+1<slen && s[idx+1]=='('){
            int i2;
            x=expr_expression(asmb,s,idx+2,&i2); idx=i2;
            if(s[idx]==','){
                int i3;
                uint256_t x2=expr_expression(asmb,s,idx+1,&i3); idx=i3;
                if(s[idx]==')'){
                    idx++;
                    uint256_t _bv, _bi;
                    if(UNDEF2(x, x2)){
                        x = UNDEF_VAL();
                    } else if(!expr_num_operand(asmb, x2, &_bi)){
                        if(should_report_errors(st))
                            axx_diagf(1, 0, " error - non-finite byte-extract offset in *(expr, expr).\n");
                        x = expr_bitwise_result(asmb, u256_zero());
                    } else if(u256_is_neg256(_bi)){
                        if(should_report_errors(st))
                            axx_diagf(1, 0, " error - negative byte-extract offset in *(expr, expr).\n");
                        x = expr_bitwise_result(asmb, u256_zero());
                    } else if(!expr_num_operand(asmb, x, &_bv)){
                        if(should_report_errors(st))
                            axx_diagf(1, 0, " error - non-finite value in *(expr, expr) byte extract.\n");
                        x = expr_bitwise_result(asmb, u256_zero());
                    } else {
                        int neg = 0;
                        x = expr_bitwise_result(asmb, op_byte(_bv, _bi, &neg));
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
            idx++;
            x=u256_zero();
        }
    } else {
        int prev_idx = idx;
        x=expr_factor1(asmb,s,idx,&idx);
        if(idx == prev_idx && idx < slen){
            char c = s[idx];
            if(c!='\0' && c!=',' && c!=')' && c!=']' && c!=CB_CHAR && c!=' ' && c!='\t'
               && !st->in_match_attempt && should_report_errors(st)){
                /* axx.py の s[idx:idx + 8] と同じく 8 文字ぶん（UTF-8 の文字単位。
                   読めないバイトは 1 文字）を出す。終端の NUL も 1 文字に数える。 */
                size_t _n = utf8_prefix_bytes(s + idx, (size_t)(slen + 1 - idx), 8);
                char _tr[160]; m_pyrepr_n(s + idx, _n, _tr, sizeof(_tr));
                axx_diagf(0, 0, " warning - unrecognized token at position %d in expression: "
                                "%s (treated as 0)\n", idx, _tr);
            }
        }
    }
    idx=axx_skipspc(s,idx);
    *idx_out=idx;
    return x;
}

/* s の先頭 avail バイトのうち、UTF-8 で nchars 文字ぶんのバイト数。読めない
   バイトは 1 文字として数える（axx.py が surrogateescape で読むのと同じ）。 */
static size_t utf8_prefix_bytes(const char *s, size_t avail, int nchars){
    size_t i = 0;
    for(int c = 0; c < nchars && i < avail; c++){
        unsigned char b = (unsigned char)s[i];
        size_t len = b < 0x80 ? 1 : (b >= 0xC2 && b <= 0xDF) ? 2
                   : (b >= 0xE0 && b <= 0xEF) ? 3 : (b >= 0xF0 && b <= 0xF4) ? 4 : 1;
        if(len > 1){
            if(i + len > avail) len = 1;
            for(size_t k = 1; k < len; k++)
                if(((unsigned char)s[i+k] & 0xC0) != 0x80){ len = 1; break; }
        }
        i += len;
    }
    return i;
}

/* `'\xHH'` を読む。読めたかを返し、値と次の位置を書く。 */
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

/* 項そのものを 1 個読む。数値（10 進・16 進・2 進・浮動小数点）、文字定数、
   ラベル、`#シンボル`、パターン変数、`$$` / `$.`、`%%`、括弧、`:=` の代入、
   配列シンボルの添字引き、`.enum` や集合の項目など、式の葉になるものすべて。
   どれにも当たらなければ位置を動かさず 0 を返す。 */
static uint256_t expr_factor1(Assembler *asmb, const char *s, int idx, int *idx_out){
    AsmState *st=&asmb->st;
    uint256_t x=u256_zero();
    idx=axx_skipspc(s,idx);
    int slen=expr_slen(s);
    int _hexlit_val=0, _hexlit_end=idx;
    int _hexlit_ok = parse_hex_char_literal(s, idx, slen, &_hexlit_val, &_hexlit_end);
    int _en_k=-1, _en_end=idx;
    int _vnl=0;

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
            x=double_to_u256(u256_int_to_double(x));
    }
    else if(axx_q(s,slen,"$.",idx)){
        idx+=2;
        x = st->pc_instr_end;
        if(st->in_binary_list || st->equ_section_tracking){
            int64_t _adj = equ_section_relative_offset(st, st->current_section, u256_to_u64(x));
            if(_adj >= 0) x = u256_from_u64((uint64_t)_adj);
        }
        if(asmb->st.exp_typ_float)
            x=double_to_u256(u256_int_to_double(x));
    }
    else if(axx_q(s,slen,"#",idx)){
        idx++;
        char tbuf[512]; size_t tsz;
        char *t = axx_word_buf(s, idx, tbuf, sizeof(tbuf), &tsz);
        idx=axx_get_symbol_word(s,idx,st->swordchars,t,tsz);
        uint256_t sv;
        char akey[512]; axx_strupr_to(akey,t,sizeof(akey));
        struct ArrSym *ar = arrsym_get(st, akey);
        if(ar && idx < slen && s[idx]=='['){
            int io2;
            uint256_t ixv = expr_expression_pat(asmb, s, idx+1, &io2);
            idx = io2;
            if(idx < slen && s[idx]==']') idx++;
            else if(should_report_errors(st))
                axx_diagf(1, 0, " error - '#%s[': missing ']'.\n", akey);
            int64_t n = u256_to_i64(ixv);
            if(n < 0 || n >= ar->len){
                if(should_report_errors(st))
                    axx_diagf(1, 0, " error - index %lld is out of range for array "
                               "symbol '%s' (0..%d).\n", (long long)n, akey, ar->len-1);
                x = u256_zero();
            } else if(ar->items[n].is_str){
                if(should_report_errors(st))
                    axx_diagf(1, 0, " error - '#%s[%lld]' is a string item and has no "
                               "numeric value.\n", akey, (long long)n);
                x = u256_zero();
            } else {
                x = ar->items[n].v;
            }
        }
        else if(symbol_get(st,t,&sv)) x=sv;
        else {
            if(should_report_errors(st)){
                axx_diagf(1, 0, " error - undefined symbol: '#%s'\n", t);
            }
            x=u256_zero();
        }
        if(t!=tbuf) free(t);
        if(asmb->st.exp_typ_float)
            x=double_to_u256(u256_int_to_double(x));
    }
    else if(axx_q(s,slen,"0b",idx)){
        idx+=2;
        int _ovf=0;
        while(s[idx]=='0'||s[idx]=='1'){
            x=u256_muladd_small(x,2,(uint64_t)(s[idx]-'0'),&_ovf);
            idx++;
        }
        if(_ovf) warn_u256_wrap("literal");
        if(asmb->st.exp_typ_float)
            x=double_to_u256(u256_int_to_double(x));
    }
    else if(axx_q(s,slen,"0x",idx)){
        idx+=2;
        int _ovf=0;
        while(s[idx]&&is_xdigit_upper(axx_upper_char(s[idx]))){
            int d; char c=axx_upper_char(s[idx]);
            d=(c>='A')?(c-'A'+10):(c-'0');
            x=u256_muladd_small(x,16,(uint64_t)d,&_ovf);
            idx++;
        }
        if(_ovf) warn_u256_wrap("literal");
        if(asmb->st.exp_typ_float)
            x=double_to_u256(u256_int_to_double(x));
    }
    else if(idx+3<=slen && strncmp(s+idx,"qad",3)==0 &&
            axx_next_nonspace_is_brace(s, slen, idx+3)){
        idx+=3;
        idx=axx_skipspc(s,idx);
        if(s[idx]=='{'){
            idx++;
            int start=idx; int depth=0;
            while(s[idx]){
                if(s[idx]=='('||s[idx]=='[') depth++;
                else if((s[idx]==')'||s[idx]==']')&&depth>0) depth--;
                else if(s[idx]=='}'&&depth==0) break;
                idx++;
            }
            size_t en = (size_t)(idx-start);
            char *expr_buf = malloc(en+1);
            if(!expr_buf){ perror("malloc"); exit(1); }
            memcpy(expr_buf, s+start, en);
            expr_buf[en]='\0';
            if(s[idx]!='}'){
                if(should_report_errors(&asmb->st)){
                    axx_diagf(1, 0, " error - missing closing '}' in expression: '{%s'\n", expr_buf);
                }
                x=u256_zero();
                free(expr_buf);
            }
            else {
            idx++;
            if(en==0){
                if(should_report_errors(&asmb->st)){
                    axx_diagf(1, 0, " error - qad{}: cannot evaluate expression '%s'; using 0.\n", expr_buf);
                }
                x=u256_zero();
            }
            else if(strcmp(expr_buf,"inf")==0 || strcmp(expr_buf,"-inf")==0 ||
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
                if(xeval_eval(asmb, expr_buf, &xv) && isfinite(xv)){
                    char fstr[64]; snprintf(fstr,sizeof(fstr),"%.17g",xv);
                    x=ieee754_128_from_str(fstr);
                } else {
                    if(should_report_errors(&asmb->st)){
                        axx_diagf(1, 0, " error - qad{}: cannot evaluate expression '%s'; using 0.\n", expr_buf);
                    }
                    x=u256_zero();
                }
            }
            }
            free(expr_buf);
            }
        }
    }
    else if(idx+5<=slen && strncmp(s+idx,"enflt",5)==0 &&
            axx_next_nonspace_is_brace(s, slen, idx+5)){
        idx+=5;
        int f; char *t;
        idx=axx_get_curlb(&asmb->st,s,idx,&f,&t);
        if(f){
            int prev_flt=asmb->st.exp_typ_float;
            asmb->st.exp_typ_float=0;
            int _outer_undef = asmb->st.error_undefined_label;
            asmb->st.error_undefined_label = 0;
            int io2; uint256_t iv=expr_expression_caps(asmb,t,0,asmb->st.expcaps,&io2);
            int _inner_undef = asmb->st.error_undefined_label;
            asmb->st.error_undefined_label = _outer_undef || _inner_undef;
            asmb->st.exp_typ_float=prev_flt;
            if(_inner_undef){
                if(should_report_errors(&asmb->st)){
                    axx_diagf(1, 0, " error - enflt{}: expression contains undefined label.\n");
                }
                iv = u256_zero();
            }
            double fval=enfloat_bits(u256_to_u64(iv));
            x = asmb->st.exp_typ_float ? double_to_u256(fval)
                                       : (isfinite(fval) ? u256_from_i64((int64_t)fval)
                                                         : u256_zero());
            free(t);
        }
    }
    else if(idx+5<=slen && strncmp(s+idx,"endbl",5)==0 &&
            axx_next_nonspace_is_brace(s, slen, idx+5)){
        idx+=5;
        int f; char *t;
        idx=axx_get_curlb(&asmb->st,s,idx,&f,&t);
        if(f){
            int prev_flt=asmb->st.exp_typ_float;
            asmb->st.exp_typ_float=0;
            int _outer_undef = asmb->st.error_undefined_label;
            asmb->st.error_undefined_label = 0;
            int io2; uint256_t iv=expr_expression_caps(asmb,t,0,asmb->st.expcaps,&io2);
            int _inner_undef = asmb->st.error_undefined_label;
            asmb->st.error_undefined_label = _outer_undef || _inner_undef;
            asmb->st.exp_typ_float=prev_flt;
            if(_inner_undef){
                if(should_report_errors(&asmb->st)){
                    axx_diagf(1, 0, " error - endbl{}: expression contains undefined label.\n");
                }
                iv = u256_zero();
            }
            double fval=endouble_bits(u256_to_u64(iv));
            x = asmb->st.exp_typ_float ? double_to_u256(fval)
                                       : (isfinite(fval) ? u256_from_i64((int64_t)fval)
                                                         : u256_zero());
            free(t);
        }
    }
    else if(idx+3<=slen && strncmp(s+idx,"dbl",3)==0 &&
            axx_next_nonspace_is_brace(s, slen, idx+3)){
        idx+=3;
        int f; char *t;
        idx=axx_get_curlb(&asmb->st,s,idx,&f,&t);
        if(f){
            uint64_t bits;
            if(t[0]=='\0'){
                if(should_report_errors(&asmb->st)){
                    axx_diagf(1, 0, " error - dbl{}: cannot convert expression to float64; using 0.\n");
                }
                bits=0;
            }
            else if(strcmp(t,"nan")==0) bits=0x7ff8000000000000ULL;
            else if(strcmp(t,"inf")==0) bits=0x7ff0000000000000ULL;
            else if(strcmp(t,"-inf")==0) bits=0xfff0000000000000ULL;
            else {
                double xv;
                if(xeval_eval(asmb, t, &xv) && isfinite(xv)){
                    memcpy(&bits,&xv,8);
                } else {
                    if(should_report_errors(&asmb->st)){
                        axx_diagf(1, 0, " error - dbl{}: cannot convert expression to float64; using 0.\n");
                    }
                    bits = 0;
                }
            }
            x = asmb->st.exp_typ_float ? double_to_u256((double)bits) : u256_from_u64(bits);
            free(t);
        }
    }
    else if(idx+3<=slen && strncmp(s+idx,"flt",3)==0 &&
            axx_next_nonspace_is_brace(s, slen, idx+3)){
        idx+=3;
        int f; char *t;
        idx=axx_get_curlb(&asmb->st,s,idx,&f,&t);
        if(f){
            uint32_t bits;
            if(t[0]=='\0'){
                if(should_report_errors(&asmb->st)){
                    axx_diagf(1, 0, " error - flt{}: cannot convert expression to float32; using 0.\n");
                }
                bits=0;
            }
            else if(strcmp(t,"nan")==0) bits=0x7fc00000u;
            else if(strcmp(t,"inf")==0) bits=0x7f800000u;
            else if(strcmp(t,"-inf")==0) bits=0xff800000u;
            else {
                double xv;
                float v = 0;
                if(xeval_eval(asmb, t, &xv) && isfinite(xv)
                   && (v = (float)xv, isfinite(v))){
                    memcpy(&bits,&v,4);
                } else {
                    if(should_report_errors(&asmb->st)){
                        axx_diagf(1, 0, " error - flt{}: cannot convert expression to float32; using 0.\n");
                    }
                    bits = 0;
                }
            }
            x = asmb->st.exp_typ_float ? double_to_u256((double)bits) : u256_from_u64(bits);
            free(t);
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
        /* 綴りの長さに上限を置かない（以前は 95 文字で黙って切っていたので、
           桁の多いリテラルの値が変わった）。 */
        char fsb[96];
        size_t _need = (size_t)(slen > idx ? slen - idx : 0) + 8;
        char *fs = (_need <= sizeof(fsb)) ? fsb : malloc(_need);
        if(!fs){ perror("malloc"); exit(1); }
        idx=axx_get_floatstr(s,idx,fs,(_need <= sizeof(fsb)) ? sizeof(fsb) : _need);
        if(fs[0]){
            char *_fend = NULL;
            double _fv = strtod(fs, &_fend);
            if(_fend && *_fend) _fv = 0.0;
            x=double_to_u256(_fv);
        }
        if(fs != fsb) free(fs);
    }
    else if(is_digit(s[idx])){
        /* 桁数に上限を置かずに読む（以前は 127 桁で黙って切っていた）。 */
        x=u256_zero();
        int _ovf=0;
        while(s[idx]&&is_digit(s[idx])){
            x=u256_muladd_small(x,10,(uint64_t)(s[idx]-'0'),&_ovf);
            idx++;
        }
        if(_ovf) warn_u256_wrap("literal");
    }
    else if(st->enum_bind_names
            && (_en_k=enum_name_at(s, idx, st->enum_bind_names, &_en_end)) >= 0){
        x = st->enum_bind_vals[_en_k];
        idx = _en_end;
    }
    else if(st->expcaps->patvars
            && (_vnl = var_name_len(s+idx)) > 0
            && (s[idx+_vnl]=='\0' || !char_in(s[idx+_vnl], st->lwordchars))){
        int _is_assign = (idx+_vnl+2<=slen && s[idx+_vnl]==':' && s[idx+_vnl+1]=='=');
        int vslot = var_slot(s+idx, _vnl, _is_assign);
        if(_is_assign){
            int _assign_prior_eul = st->error_undefined_label;
            st->error_undefined_label = 0;
            x=expr_expression(asmb,s,idx+_vnl+2,&idx);
            int _assign_this_undef = st->error_undefined_label;
            st->error_undefined_label = _assign_prior_eul || _assign_this_undef;
            var_slot_put_tagged(st,vslot,x,_assign_this_undef);
        } else {
            x=var_slot_for_mode(st,vslot,asmb->st.exp_typ_float);
            idx+=_vnl;
            if(!st->in_match_attempt
               && !st->pass1_size_mode
               && should_report_errors(st)){
                if(var_slot_is_undef(st, vslot) || u256_is_undef_derived(x)){
                    st->error_undefined_label = 1;
                    axx_diagf(0, 0, " error - Label undefined: variable '%s' contains undefined value"
                               "  [%s:%d]\n",
                               var_slot_name(vslot), st->current_file, (int)st->ln);
                }
            }
            if(st->elf_tracking && st->elf_current_word_idx >= 0){
                int _vi = vslot;
                if(_vi >= 0 && _vi < g_nvars && (st->elf_var_to_label[_vi].set == 1
                                                 || st->elf_var_to_label[_vi].set == 3)){
                    /* set 3 はラベル差。名前は「足す\x01引く」で、型の指定は持たない。 */
                    int _isdiff = st->elf_var_to_label[_vi].set == 3;
                    if(st->elf_refs_len >= st->elf_refs_cap){
                        st->elf_refs_cap = st->elf_refs_cap ? st->elf_refs_cap*2 : 8;
                        st->elf_refs = realloc(st->elf_refs,
                            st->elf_refs_cap * sizeof(st->elf_refs[0]));
                        if(!st->elf_refs){ perror("realloc"); exit(1); }
                    }
                    st->elf_refs[st->elf_refs_len].name     = strdup(st->elf_var_to_label[_vi].label_name);
                    st->elf_refs[st->elf_refs_len].val      = st->elf_var_to_label[_vi].label_val;
                    st->elf_refs[st->elf_refs_len].word_idx = st->elf_current_word_idx;
                    /* ラベル差でも `.reloc` の型（型付きの差）と定数部を持たせる。 */
                    (void)_isdiff;
                    st->elf_refs[st->elf_refs_len].rtype    = st->reloc_constraints[_vi];
                    st->elf_refs[st->elf_refs_len].addend   =
                        u256_is_undef_derived(x) && _isdiff ? 0 :
                        (int64_t)(u256_to_u64(x) - st->elf_var_to_label[_vi].label_val);
                    st->elf_refs_len++;
                }
            }
        }
    }
    else if(s[idx]&&char_in(s[idx],st->lwordchars)){
        char wbuf[512]; size_t wsz;
        char *w = axx_word_buf(s, idx, wbuf, sizeof(wbuf), &wsz);
        int new_idx=axx_get_label_word_ex(s,idx,st->lwordchars,w,wsz,0);
        if(new_idx!=idx){
            idx=new_idx;
            x=label_get_value(st,w);
            /* 未定義のラベルは番兵のまま残す（浮動小数点にすると毒の判定が
               できなくなる）。行全体の印ではなく、この値そのもので決める。 */
            if(asmb->st.exp_typ_float && !u256_is_undef(x))
                x=double_to_u256(u256_int_to_double(x));
        }
        if(w!=wbuf) free(w);
    }

    idx=axx_skipspc(s,idx);
    *idx_out=idx;
    return x;
}

/* `**`。指数と結果のビット数に上限を置き、連鎖で爆発させない。エラーのあとも
   0 にして残りの `**` を読み進める（途中で抜けると残りが宙に浮き、行が
   パターンに当たらなくなる）。axx.py の term0_0() と同じ規則である。 */
static uint256_t expr_term0_0(Assembler *asmb, const char *s, int idx, int *idx_out){
    uint256_t x=expr_factor(asmb,s,idx,&idx);
    int slen=expr_slen(s);
    while(idx<slen && axx_q(s,slen,"**",idx)){
        uint256_t t=expr_factor(asmb,s,idx+2,&idx);
        if(UNDEF2(x, t)){ x = UNDEF_VAL(); continue; }
        if(asmb->st.exp_typ_float){
            double a=u256_to_double(x), b=u256_to_double(t);
            x=double_to_u256(pow(a,b));
        } else {
            const int64_t EXP_MAX = 1024;
            const int64_t EXP_RESULT_MAX_BITS = 256;
            if(u256_is_neg256(t)){
                if(should_report_errors(&asmb->st)){
                    axx_diagf(1, 0, " error - Negative exponent in ** expression; result set to 0.\n");
                }
                x = u256_zero();
                continue;
            }
            if(u256_nonneg_gt_i64(t, EXP_MAX)){
                if(should_report_errors(&asmb->st)){
                    char _ec[96]; u256_to_pydec(t, _ec, sizeof(_ec));
                    axx_diagf(1, 0, " error - Exponent %s exceeds maximum %lld in ** expression; result set to 0.\n", _ec, (long long)EXP_MAX);
                }
                x = u256_zero();
                continue;
            }
            int64_t t_int = u256_to_i64(t);
            int64_t base_bits = u256_nbit(x);
            int64_t exp_factor = t_int > 1 ? t_int : 1;
            if(base_bits * exp_factor > EXP_RESULT_MAX_BITS){
                if(should_report_errors(&asmb->st)){
                    axx_diagf(1, 0, " error - ** result would exceed %lld bits (chained exponentiation); result set to 0.\n",(long long)EXP_RESULT_MAX_BITS);
                }
                x = u256_zero();
                continue;
            }
            x=u256_pow(x,t);
        }
    }
    *idx_out=idx; return x;
}

/* `*` `/` `//` `%`。整数モードの `/` はゼロ方向へ切り捨て、`%` は結果が
   除数の符号に従う（Python と同じ）。 */
static uint256_t expr_term0(Assembler *asmb, const char *s, int idx, int *idx_out){
    uint256_t x=expr_term0_0(asmb,s,idx,&idx);
    int slen=expr_slen(s);
    while(idx<slen){
        int flt=asmb->st.exp_typ_float;
        if(s[idx]=='*'&&s[idx+1]!='*'){
            uint256_t t=expr_term0_0(asmb,s,idx+1,&idx);
            if(UNDEF2(x, t)) x = UNDEF_VAL();
            else if(flt) x=double_to_u256(u256_to_double(x)*u256_to_double(t));
            else {
                uint256_t r=u256_mul_signed(x,t);
                if(!u256_is_zero(x) && !u256_is_zero(t)
                   && !u256_in_undef_band(x) && !u256_in_undef_band(t)
                   && !u256_eq(u256_truncdiv(r,x), t))
                    warn_u256_wrap("*");
                x=r;
            }
        } else if(axx_q(s,slen,"//",idx)){
            uint256_t t=expr_term0_0(asmb,s,idx+2,&idx);
            if(UNDEF2(x, t)) x = UNDEF_VAL();
            else if(flt){
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
            if(UNDEF2(x, t)) x = UNDEF_VAL();
            else if(flt){
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
            if(UNDEF2(x, t)) x = UNDEF_VAL();
            else if(flt){
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

/* `+` `-`。 */
static uint256_t expr_term1(Assembler *asmb, const char *s, int idx, int *idx_out){
    uint256_t x=expr_term0(asmb,s,idx,&idx);
    int slen=expr_slen(s);
    while(idx<slen){
        int flt=asmb->st.exp_typ_float;
        if(s[idx]=='+'){
            uint256_t t=expr_term0(asmb,s,idx+1,&idx);
            if(UNDEF2(x, t)) x = UNDEF_VAL();
            else if(flt) x=double_to_u256(u256_to_double(x)+u256_to_double(t));
            else {
                uint256_t r=u256_add(x,t);
                if(u256_is_neg256(x)==u256_is_neg256(t)
                   && u256_is_neg256(r)!=u256_is_neg256(x)
                   && !u256_in_undef_band(x) && !u256_in_undef_band(t))
                    warn_u256_wrap("+");
                x=r;
            }
        } else if(s[idx]=='-'){
            uint256_t t=expr_term0(asmb,s,idx+1,&idx);
            if(UNDEF2(x, t)) x = UNDEF_VAL();
            else if(flt) x=double_to_u256(u256_to_double(x)-u256_to_double(t));
            else {
                uint256_t r=u256_sub(x,t);
                if(u256_is_neg256(x)!=u256_is_neg256(t)
                   && u256_is_neg256(r)!=u256_is_neg256(x)
                   && !u256_in_undef_band(x) && !u256_in_undef_band(t))
                    warn_u256_wrap("-");
                x=r;
            }
        } else break;
    }
    *idx_out=idx; return x;
}

/* `<<` `>>`。負のシフト量と大きすぎるシフト量はエラーにする。エラーのあとも
   0 にして残りのシフトを読み進める。axx.py の term2() と同じ規則である。 */
static uint256_t expr_term2(Assembler *asmb, const char *s, int idx, int *idx_out){
    uint256_t x=expr_term1(asmb,s,idx,&idx);
    int slen=expr_slen(s);
    const int64_t SHIFT_MAX = 65536;
    while(idx<slen){
        if(axx_q(s,slen,"<<",idx)){
            uint256_t t=expr_term1(asmb,s,idx+2,&idx);
            if(UNDEF2(x, t)){ x = UNDEF_VAL(); continue; }
            uint256_t sop=expr_safe_bitwise_operand(asmb,t,"<<");
            if(u256_is_neg256(sop)){
                char _sc[96]; u256_to_pydec(sop, _sc, sizeof(_sc));
                if(should_report_errors(&asmb->st)){
                    axx_diagf(1, 0, " error - negative shift count (%s) in << expression.\n", _sc);
                }
                x=u256_zero(); continue;
            } else if(u256_nonneg_gt_i64(sop,SHIFT_MAX)){
                char _sc[96]; u256_to_pydec(sop, _sc, sizeof(_sc));
                if(should_report_errors(&asmb->st)){
                    axx_diagf(1, 0, " error - shift count %s exceeds maximum %lld in << expression.\n", _sc, (long long)SHIFT_MAX);
                }
                x=u256_zero(); continue;
            } else {
                uint256_t _b=expr_safe_bitwise_operand(asmb,x,"<<");
                int _n=(int)u256_to_i64(sop);
                if(!u256_is_zero(_b) && !u256_in_undef_band(_b)
                   && (long long)u256_nbit(_b) + _n > 255)
                    warn_u256_wrap("<<");
                x=expr_bitwise_result(asmb,u256_shl(_b,_n));
            }
        } else if(axx_q(s,slen,">>",idx)){
            uint256_t t=expr_term1(asmb,s,idx+2,&idx);
            if(UNDEF2(x, t)){ x = UNDEF_VAL(); continue; }
            uint256_t sop=expr_safe_bitwise_operand(asmb,t,">>");
            if(u256_is_neg256(sop)){
                char _sc[96]; u256_to_pydec(sop, _sc, sizeof(_sc));
                if(should_report_errors(&asmb->st)){
                    axx_diagf(1, 0, " error - negative shift count (%s) in >> expression.\n", _sc);
                }
                x=u256_zero(); continue;
            } else if(u256_nonneg_gt_i64(sop,SHIFT_MAX)){
                char _sc[96]; u256_to_pydec(sop, _sc, sizeof(_sc));
                if(should_report_errors(&asmb->st)){
                    axx_diagf(1, 0, " error - shift count %s exceeds maximum %lld in >> expression.\n", _sc, (long long)SHIFT_MAX);
                }
                x=u256_zero(); continue;
            } else x=expr_bitwise_result(asmb,u256_sar(expr_safe_bitwise_operand(asmb,x,">>"),(int)u256_to_i64(sop)));
        } else break;
    }
    *idx_out=idx; return x;
}


/* double を整数に切り捨てて 256bit に入れる。 */
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

/* 256bit 整数を double の値にする。 */
static double u256_int_to_double(uint256_t v){
    const double LIMB = 18446744073709551616.0;
    int neg = (int)((v.w[3] >> 63) & 1u);
    uint256_t m = neg ? u256_neg(v) : v;
    double d = 0.0;
    for(int i = 3; i >= 0; i--) d = d * LIMB + (double)m.w[i];
    return neg ? -d : d;
}

/* ビット演算の前に整数へ落とす。非有限値は警告して 0 にする。 */
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

/* ビット演算の結果を、現在のモードに合う形に整える。 */
static uint256_t expr_bitwise_result(Assembler *asmb, uint256_t v){
    if(asmb->st.exp_typ_float) return double_to_u256(u256_int_to_double(v));
    return v;
}

/* 数値として扱えるオペランドか確かめる。 */
static int expr_num_operand(Assembler *asmb, uint256_t v, uint256_t *out){
    if(asmb->st.exp_typ_float){
        double d = u256_to_double(v);
        if(!isfinite(d)){ *out = u256_zero(); return 0; }
        *out = double_trunc_to_u256(d);
        return 1;
    }
    *out = v;
    return 1;
}

/* `&`。`&&` は論理積なので食べない。 */
static uint256_t expr_term3(Assembler *asmb, const char *s, int idx, int *idx_out){
    uint256_t x=expr_term2(asmb,s,idx,&idx);
    int slen=expr_slen(s);
    while(idx<slen && s[idx]=='&' && s[idx+1]!='&'){
        uint256_t t=expr_term2(asmb,s,idx+1,&idx);
        if(UNDEF2(x, t)){ x = UNDEF_VAL(); continue; }
        x=expr_bitwise_result(asmb,u256_and(expr_safe_bitwise_operand(asmb,x,"&"),expr_safe_bitwise_operand(asmb,t,"&")));
    }
    *idx_out=idx; return x;
}

/* `|`。`||` は論理和なので食べない。 */
static uint256_t expr_term4(Assembler *asmb, const char *s, int idx, int *idx_out){
    uint256_t x=expr_term3(asmb,s,idx,&idx);
    int slen=expr_slen(s);
    while(idx<slen && s[idx]=='|' && s[idx+1]!='|'){
        uint256_t t=expr_term3(asmb,s,idx+1,&idx);
        if(UNDEF2(x, t)){ x = UNDEF_VAL(); continue; }
        x=expr_bitwise_result(asmb,u256_or(expr_safe_bitwise_operand(asmb,x,"|"),expr_safe_bitwise_operand(asmb,t,"|")));
    }
    *idx_out=idx; return x;
}

/* `^`。 */
static uint256_t expr_term5(Assembler *asmb, const char *s, int idx, int *idx_out){
    uint256_t x=expr_term4(asmb,s,idx,&idx);
    int slen=expr_slen(s);
    while(idx<slen && s[idx]=='^'){
        uint256_t t=expr_term4(asmb,s,idx+1,&idx);
        if(UNDEF2(x, t)){ x = UNDEF_VAL(); continue; }
        x=expr_bitwise_result(asmb,u256_xor(expr_safe_bitwise_operand(asmb,x,"^"),expr_safe_bitwise_operand(asmb,t,"^")));
    }
    *idx_out=idx; return x;
}

/* `'` — 符号拡張。`'` は文字定数の引用符でもあるので、直後が数字か `(` の
   ときだけ演算子として読む。 */
static uint256_t expr_term6(Assembler *asmb, const char *s, int idx, int *idx_out){
    uint256_t x=expr_term5(asmb,s,idx,&idx);
    int slen=expr_slen(s);
    while(idx<slen && s[idx]=='\''){
        int ni=idx+1; ni=axx_skipspc(s,ni);
        if(ni>=slen||((s[ni]<'0'||s[ni]>'9')&&s[ni]!='(')) break;
        uint256_t t=expr_term5(asmb,s,idx+1,&idx);
        if(UNDEF2(x, t)){ x = UNDEF_VAL(); continue; }
        uint256_t _xv, _tv;
        if(!expr_num_operand(asmb, x, &_xv) || !expr_num_operand(asmb, t, &_tv)){
            x = expr_bitwise_result(asmb, u256_zero());
            break;
        }
        int warn = 0;
        uint256_t _sr = op_sext(_xv, _tv, &warn);
        if(warn && should_report_errors(&asmb->st)){
            char cb[96]; u256_to_pydec(_tv, cb, sizeof(cb));
            axx_diagf(0, 0, " warning - sign-extension bit width %s exceeds maximum %d, result set to 0.\n",
                       cb, SEXT_MAX_BITS);
        }
        x = expr_bitwise_result(asmb, _sr);
    }
    *idx_out=idx; return x;
}

/* 比較と論理演算の結果（1 か 0）を、今のモードの値にする。浮動小数点の文脈では
   1.0 / 0.0 の倍精度で持つ（axx.py は int の 1 / 0 を返し、そのまま浮動小数点と
   混ぜて計算できる）。整数のビットのままだと、倍精度として読んだときに
   4.9e-324 のような値になってしまう。 */
static uint256_t expr_bool(Assembler *asmb, int b){
    if(asmb->st.exp_typ_float) return double_to_u256(b ? 1.0 : 0.0);
    return u256_from_i64(b);
}

/* 値が偽か。浮動小数点の文脈では 0.0 と -0.0 が偽（axx.py の 0.0 / -0.0 と同じ）。 */
static int expr_is_false(Assembler *asmb, uint256_t v){
    if(asmb->st.exp_typ_float && !u256_is_undef(v)) return u256_to_double(v) == 0.0;
    return u256_is_zero(v);
}

/* 比較 `<=` `<` `>=` `>` `==` `!=`。結果は 1 か 0。 */
static uint256_t expr_term7(Assembler *asmb, const char *s, int idx, int *idx_out){
    uint256_t x=expr_term6(asmb,s,idx,&idx);
    int slen=expr_slen(s);
    while(idx<slen){
        int flt=asmb->st.exp_typ_float;
        if(axx_q(s,slen,"<=",idx)){
            uint256_t t=expr_term6(asmb,s,idx+2,&idx);
            if(UNDEF2(x, t)){ x = UNDEF_VAL(); continue; }
            x=expr_bool(asmb, flt ? (u256_to_double(x)<=u256_to_double(t)?1:0)
                                : (u256_le_signed(x,t)?1:0));
        } else if(s[idx]=='<'&&s[idx+1]!='<'){
            uint256_t t=expr_term6(asmb,s,idx+1,&idx);
            if(UNDEF2(x, t)){ x = UNDEF_VAL(); continue; }
            x=expr_bool(asmb, flt ? (u256_to_double(x)< u256_to_double(t)?1:0)
                                : (u256_lt_signed(x,t)?1:0));
        } else if(axx_q(s,slen,">=",idx)){
            uint256_t t=expr_term6(asmb,s,idx+2,&idx);
            if(UNDEF2(x, t)){ x = UNDEF_VAL(); continue; }
            x=expr_bool(asmb, flt ? (u256_to_double(x)>=u256_to_double(t)?1:0)
                                : (u256_ge_signed(x,t)?1:0));
        } else if(s[idx]=='>'&&s[idx+1]!='>'){
            uint256_t t=expr_term6(asmb,s,idx+1,&idx);
            if(UNDEF2(x, t)){ x = UNDEF_VAL(); continue; }
            x=expr_bool(asmb, flt ? (u256_to_double(x)> u256_to_double(t)?1:0)
                                : (u256_gt_signed(x,t)?1:0));
        } else if(axx_q(s,slen,"==",idx)){
            uint256_t t=expr_term6(asmb,s,idx+2,&idx);
            if(UNDEF2(x, t)){ x = UNDEF_VAL(); continue; }
            x=expr_bool(asmb, flt ? (u256_to_double(x)==u256_to_double(t)?1:0)
                                : (u256_eq(x,t)?1:0));
        } else if(axx_q(s,slen,"!=",idx)){
            uint256_t t=expr_term6(asmb,s,idx+2,&idx);
            if(UNDEF2(x, t)){ x = UNDEF_VAL(); continue; }
            x=expr_bool(asmb, flt ? (u256_to_double(x)!=u256_to_double(t)?1:0)
                                : (!u256_eq(x,t)?1:0));
        } else break;
    }
    *idx_out=idx; return x;
}

/* 空けてある段。下へ素通しする。axx.py と段の番号をそろえるために残してある。 */
static uint256_t expr_term8(Assembler *asmb, const char *s, int idx, int *idx_out){
    return expr_term7(asmb,s,idx,idx_out);
}

static int skip_subexpr(const char *s, int idx);

/* `&&`。 */
static uint256_t expr_term9(Assembler *asmb, const char *s, int idx, int *idx_out){
    uint256_t x=expr_term8(asmb,s,idx,&idx);
    int slen=expr_slen(s);
    while(idx<slen && axx_q(s,slen,"&&",idx)){
        uint256_t t=expr_term8(asmb,s,idx+2,&idx);
        if(UNDEF2(x, t)){ x = UNDEF_VAL(); continue; }
        x=expr_bool(asmb, (!expr_is_false(asmb,x) && !expr_is_false(asmb,t))?1:0);
    }
    *idx_out=idx; return x;
}

/* `||`。 */
static uint256_t expr_term10(Assembler *asmb, const char *s, int idx, int *idx_out){
    uint256_t x=expr_term9(asmb,s,idx,&idx);
    int slen=expr_slen(s);
    while(idx<slen && axx_q(s,slen,"||",idx)){
        uint256_t t=expr_term9(asmb,s,idx+2,&idx);
        if(UNDEF2(x, t)){ x = UNDEF_VAL(); continue; }
        x=expr_bool(asmb, (!expr_is_false(asmb,x) || !expr_is_false(asmb,t))?1:0);
    }
    *idx_out=idx; return x;
}


/* 括弧の対応を数えて部分式 1 個を読み飛ばす。 */
static int skip_subexpr(const char *s, int idx) {
    int slen = expr_slen(s);
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

/* 三項演算子の片側を読み飛ばす（深さ付き）。 */
static int skip_ternary_expr_d(const char *s, int idx, int depth) {
    if(depth > EXPR_MAX_DEPTH) return idx;
    int slen = expr_slen(s);
    idx = skip_subexpr(s, idx);
    if(idx < slen && s[idx] == '?' && s[idx+1] != '='){
        idx++;
        idx = axx_skipspc(s, idx);
        idx = skip_ternary_expr_d(s, idx, depth + 1);
        idx = axx_skipspc(s, idx);
        if(idx < slen && s[idx] == ':' && s[idx+1] != '='){
            idx++;
            idx = axx_skipspc(s, idx);
            idx = skip_ternary_expr_d(s, idx, depth + 1);
        }
    }
    return idx;
}
/* 三項演算子の、選ばれなかった側を読み飛ばす。 */
static int skip_ternary_expr(const char *s, int idx) {
    return skip_ternary_expr_d(s, idx, 0);
}

/* `?:` — 三項演算子。選ばれなかった側は評価せずに飛ばす。`:=` の代入が
   走らないようにするためで、`:` の直後が `=` なら区切りとは読まない。 */
static uint256_t expr_term11(Assembler *asmb, const char *s, int idx, int *idx_out){
    AsmState *st = &asmb->st;
    uint256_t x = expr_term10(asmb, s, idx, &idx);
    int slen = expr_slen(s);
    if(idx < slen && axx_q(s, slen, "?", idx)){
        if(st->expr_depth >= EXPR_MAX_DEPTH){
            if(should_report_errors(st)){
                axx_diagf(1, 0, " error - expression nesting too deep.\n");
            }
            idx++;
            idx = axx_skipspc(s, idx);
            idx = skip_ternary_expr(s, idx);
            idx = axx_skipspc(s, idx);
            if(axx_q(s, slen, ":", idx) && s[idx+1] != '='){
                idx = skip_ternary_expr(s, axx_skipspc(s, idx + 1));
            }
            *idx_out = idx;
            return u256_zero();
        }
        st->expr_depth++;
        idx++;
        idx = axx_skipspc(s, idx);
        if(expr_is_false(asmb, x)){
            /* 真の側が入れ子の三項（`0?a?b:c:d`）でも丸ごと飛ばす。
               axx.py の term11() と同じく _skip_ternary_expr 相当を使う。 */
            int skip_end = skip_ternary_expr(s, idx);
            if(axx_q(s, slen, ":", skip_end) && s[skip_end+1] != '='){
                int false_start = axx_skipspc(s, skip_end + 1);
                x = expr_term11(asmb, s, false_start, &idx);
            } else {
                idx = skip_end;
                x = u256_zero();
            }
        } else {
            x = expr_term11(asmb, s, idx, &idx);
            idx = axx_skipspc(s, idx);
            if(axx_q(s, slen, ":", idx) && s[idx+1] != '='){
                idx = skip_ternary_expr(s, axx_skipspc(s, idx + 1));
            }
        }
        st->expr_depth--;
    }
    *idx_out = idx;
    return x;
}

/* 式を 1 個評価する。優先順位の一番上から入る。 */
static uint256_t expr_expression(Assembler *asmb, const char *s, int idx, int *idx_out){
    idx=axx_skipspc(s,idx);
    return expr_term11(asmb,s,idx,idx_out);
}

static void        strsym_set(AsmState *st, const char *upper_name, const char *val);
static void        strsym_delete(AsmState *st, const char *upper_name);
static const char *strsym_get(AsmState *st, const char *upper_name);
static char       *txt_template_inner(const char *q);
static void        arrsym_set_from_text(Assembler *asmb, const char *upper_name, const char *q);
static void        arrsym_delete(AsmState *st, const char *upper_name);
static void        arrsym_clear_all(AsmState *st);
static int         symbol_copy_from_name(AsmState *st, const char *dst_upper, const char *value_field);
static int         symbol_set_from_text(AsmState *st, const char *dst_upper, const char *value_field);

/* ---- パターン側ディレクティブ -------------------------------------------
   各ハンドラは「自分の担当でなければ 0、処理したら 1」を返し、呼び出し側が
   順に試す。ディレクティブは書かれた位置から効くので、パターン行の照合と
   違って順序に依存する。
   ------------------------------------------------------------------------ */
/* `.setsym` — あらゆる種類のシンボルを定義する。どの種類になるかは値欄の
   見た目で決まる（文字列・配列・集合・集合式・コピー・数値式）。特殊形の
   判定が数値解釈より先に来るが、集合になりえない欄は必ず数値解釈へ譲る。 */
static int dir_set_symbol(Assembler *asmb, PatEntry *e){
    if(!e||strcmp(e->f[0],".setsym")!=0) return 0;
    if(e->setsym_plain){
        if(!e->setsym_done){
            int io;
            e->setsym_val  = expr_expression_pat(asmb, e->f[2], 0, &io);
            e->setsym_done = 1;
        }
        smap_set(&asmb->st.symbols, e->setsym_key, e->setsym_val);
        return 1;
    }
    if(!e->f[1][0] && !e->f[2][0]){
        /* axx.py の set_symbol() と同じく、名前の無い `.setsym` は誤り。 */
        axx_diagf(1, 0, " error - .setsym directive requires at least a symbol name\n");
        return 0;
    }
    const char *name_field = e->f[1][0] ? e->f[1] : e->f[2];
    const char *value_field = e->f[1][0] ? e->f[2] : "";
    char key[512]; axx_strupr_to(key,name_field,sizeof(key));
    {
        const char *q = value_field;
        while(*q==' '||*q=='\t') q++;
        if(*q=='"'){
            char *body = txt_template_inner(q);
            strsym_set(&asmb->st, key, body);
            free(body);
            return 1;
        }
        if(*q=='['){
            arrsym_set_from_text(asmb, key, q);
            return 1;
        }
        if(symbol_copy_from_name(&asmb->st, key, value_field)) return 1;
        if(symbol_set_from_text(&asmb->st, key, value_field)) return 1;
    }
    int io;
    uint256_t v;
    if(e->setsym_const){
        if(!e->setsym_done){ e->setsym_val = expr_expression_pat(asmb,value_field,0,&io);
                             e->setsym_done = 1; }
        v = e->setsym_val;
    } else {
        v = value_field[0] ? expr_expression_pat(asmb,value_field,0,&io) : u256_zero();
    }
    smap_set(&asmb->st.symbols,key,v);
    return 1;
}

/* `.clearsym` — 名前を 1 つ、または引数なしで全部消す。 */
static int dir_clear_symbol(Assembler *asmb, PatEntry *e){
    if(!e||strcmp(e->f[0],".clearsym")!=0) return 0;
    if(e->f[2][0]){
        char key[512]; axx_strupr_to(key,e->f[2],sizeof(key));
        smap_delete(&asmb->st.symbols,key);
        strsym_delete(&asmb->st, key);
        arrsym_delete(&asmb->st, key);
    } else {
        smap_clear(&asmb->st.symbols);
        sv_free(&asmb->st.strsym_names); sv_init(&asmb->st.strsym_names);
        sv_free(&asmb->st.strsym_vals);  sv_init(&asmb->st.strsym_vals);
        arrsym_clear_all(&asmb->st);
    }
    return 1;
}

/* `.bits` — 出力ワードのビット数とバイト順。 */
static int dir_bits(Assembler *asmb, PatEntry *e){
    if(!e||strcmp(e->f[0],".bits")!=0) return 0;

    const char *fields[2]; int nfields=0;
    if(e->f[1][0]) fields[nfields++] = e->f[1];
    if(e->f[2][0]) fields[nfields++] = e->f[2];

    const char *wf = "";
    for(int fi=0; fi<nfields; fi++){
        const char *f = fields[fi];
        if(strcasecmp(f,"big")==0){ asmb->st.endian_big=1; }
        else if(strcasecmp(f,"little")==0){ asmb->st.endian_big=0; }
        else if(!wf[0]){ wf = f; }
        else {
            axx_diagf(1, 0, " error - .bits: multiple word-width fields given ('%s' and '%s').\n", wf, f);
        }
    }

    if(wf[0]){
        int io;
        asmb->st.error_undefined_label = 0;
        uint256_t v = expr_expression_pat(asmb,wf,0,&io);
        int64_t nb = u256_to_i64(v);
        if(asmb->st.error_undefined_label || u256_is_undef_derived(v)
           || nb < 1 || nb > 64 || !u256_eq(v, u256_from_i64(nb))){
            { char _wr[600]; m_pyrepr(wf, _wr, sizeof(_wr));
              axx_diagf(1, 0, " error - .bits: word width must be an integer in 1..64, got %s.\n", _wr); }
        } else {
            asmb->st.bts = (int)nb;
        }
        asmb->st.error_undefined_label = 0;
    }
    return 1;
}

/* `.padding` — 隙間を埋める値。 */
static int dir_padding(Assembler *asmb, PatEntry *e){
    if(!e||strcmp(e->f[0],".padding")!=0) return 0;
    const char *pf = e->f[2][0] ? e->f[2] : (e->f[1][0] ? e->f[1] : "");
    int io;
    uint256_t v = pf[0] ? expr_expression_pat(asmb,pf,0,&io) : u256_zero();
    asmb->st.padding=v;
    return 1;
}

/* `.symbolc` — シンボルに使える文字を増やす。 */
static int dir_symbolc(Assembler *asmb, PatEntry *e){
    if(!e||strcmp(e->f[0],".symbolc")!=0) return 0;
    if(e->f[2][0]){
        snprintf(asmb->st.swordchars, sizeof(asmb->st.swordchars),
                 "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789%s",
                 e->f[2]);
    }
    return 1;
}

/* `.vliw` — バンドル幅・命令幅・テンプレート幅・NOP を宣言する。 */
static int dir_vliwp(Assembler *asmb, PatEntry *e){
    if(!e||strcmp(e->f[0],".vliw")!=0) return 0;
    int io;
    uint256_t v1=expr_expression_pat(asmb,e->f[1],0,&io);
    uint256_t v2=expr_expression_pat(asmb,e->f[2],0,&io);
    uint256_t v3=expr_expression_pat(asmb,e->f[3],0,&io);
    uint256_t v4=expr_expression_pat(asmb,e->f[4],0,&io);

    int64_t vb64 = u256_to_i64(v1);
    int64_t vi64 = u256_to_i64(v2);
    int64_t vt64 = u256_to_i64(v3);
    if(vb64 < -8192 || vb64 > 8192 || !u256_eq(v1, u256_from_i64(vb64))){
        axx_diagf(1, 0, " error - .vliw: vliwbits is out of range (must be -8192..8192).\n");
        return 1;
    }
    if(vi64 < 0 || vi64 > 8192 || !u256_eq(v2, u256_from_i64(vi64))){
        axx_diagf(1, 0, " error - .vliw: vliwinstbits %lld is out of range (must be 0-8192).\n",
                   (long long)vi64);
        return 1;
    }
    if(vt64 < -8192 || vt64 > 8192 || !u256_eq(v3, u256_from_i64(vt64))){
        axx_diagf(1, 0, " error - .vliw: vliwtemplatebits is out of range (must be -8192..8192).\n");
        return 1;
    }
    asmb->st.vliwbits=(int)vb64;
    asmb->st.vliwinstbits=(int)vi64;
    asmb->st.vliwtemplatebits=(int)vt64;
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

/* `EPIC::` — インデックスコードの組み合わせごとのテンプレートを宣言する。 */
static int dir_epic(Assembler *asmb, PatEntry *e){
    if(!e) return 0;
    char uf[16]; axx_strupr_to(uf,e->f[0],sizeof(uf));
    if(strcmp(uf,"EPIC")!=0) return 0;
    if(!e->f[1][0]) return 0;
    const char *s=e->f[1];
    int idx=0;
    int cap=1;
    for(const char *q=s; *q; q++) if(*q==',') cap++;
    int *idxs=malloc((size_t)cap*sizeof(int));
    if(!idxs){ perror("malloc"); exit(1); }
    int ni=0;
    while(1){
        int io;
        uint256_t v=expr_expression_pat(asmb,s,idx,&io);
        if(ni<cap) idxs[ni++]=(int)u256_to_i64(v);
        idx=io;
        if(s[idx]==','){idx++;continue;}
        break;
    }
    vset_add(&asmb->st.vliwset,idxs,ni,e->f[2]);
    free(idxs);
    return 1;
}

/* ディレクティブの変数名欄をスロット番号にする。 */
static int dir_var_slot(const char *field){
    const char *p = field;
    while(*p==' '||*p=='\t') p++;
    size_t cap = strlen(p) + 1;
    char *lower = malloc(cap);
    if(!lower){ perror("malloc"); exit(1); }
    int n = 0;
    while(*p && !(*p==' '||*p=='\t'))
        lower[n++] = (char)tolower((unsigned char)*p++);
    lower[n] = '\0';
    while(*p==' '||*p=='\t') p++;
    if(*p || n == 0){ free(lower); return -1; }
    if(var_name_len(lower) != n){ free(lower); return -1; }
    int slot = var_slot(lower, n, 1);
    free(lower);
    return slot;
}

/* 要素リストを展開する。配列シンボルの名前はその中身に開き、`""` は
   省略可能の印として空文字で残す。 */
static void elem_list_expand(AsmState *st, const char *text, StrVec *out){
    const char *p = text;
    size_t bufsz = strlen(text) + 1;
    char *buf = malloc(bufsz);
    if(!buf){ perror("malloc"); exit(1); }
    while(*p){
        while(*p == ' ' || *p == '\t') p++;
        int j = 0;
        while(*p && *p != ',') buf[j++] = axx_upper_char(*p++);
        buf[j] = '\0';
        while(j > 0 && (buf[j-1] == ' ' || buf[j-1] == '\t')) buf[--j] = '\0';

        if(j == 2 && ((buf[0]=='"' && buf[1]=='"') || (buf[0]=='\'' && buf[1]=='\''))) j = 0;
        if(j == 0){
            sv_push(out, "");
        } else {
            struct ArrSym *ar = arrsym_get(st, buf);
            if(ar){
                for(int k = 0; k < ar->len; k++){
                    if(ar->items[k].is_str){
                        size_t upsz = strlen(ar->items[k].s) + 1;
                        char *up = malloc(upsz);
                        if(!up){ perror("malloc"); exit(1); }
                        axx_strupr_to(up, ar->items[k].s, upsz);
                        sv_push(out, up);
                        free(up);
                    } else {
                        char num[96];
                        u256_to_pydec(ar->items[k].v, num, sizeof(num));
                        sv_push(out, num);
                    }
                }
            } else {
                sv_push(out, buf);
            }
        }
        if(*p == ',') p++;
        else break;
    }
    free(buf);
}

/* 欄が空白だけか。 */
static int fld_blank(const char *s){
    for(; *s; s++) if(!isspace((unsigned char)*s)) return 0;
    return 1;
}

/* `.check` — その変数が捕らえてよいシンボルを制限する。 */
static int dir_check(Assembler *asmb, PatEntry *e){
    if(!e || strcmp(e->f[0], ".check") != 0) return 0;
    const char *var_str  = !fld_blank(e->f[1]) ? e->f[1] : e->f[2];
    const char *syms_str = !fld_blank(e->f[1]) ? e->f[2] : "";
    if(fld_blank(var_str)){
        axx_diagf(1, 0, " error - .check: variable name is not specified.\n");
        return 1;
    }
    int idx = dir_var_slot(var_str);
    if(idx < 0){
        axx_diagf(1, 0, " error - .check: variable should be a lower case name ('%s').\n",
                   var_str);
        return 1;
    }
    if(e->chk_cache && e->chk_cache_gen == g_arrgen){
        chk_install(&asmb->st.check_constraints[idx], chk_ref((ChkList*)e->chk_cache));
        return 1;
    }

    ChkList *nl = chk_new();
    StrVec elems; sv_init(&elems);
    elem_list_expand(&asmb->st, syms_str, &elems);
    for(int ei = 0; ei < elems.len; ei++){
        const char *nm = elems.data[ei];
        if(!nm[0]){
            int dup = 0;
            for(int si = 0; si < nl->v.len; si++)
                if(nl->v.data[si][0] == '\0'){ dup = 1; break; }
            if(!dup) sv_push(&nl->v, "");
        } else {
            sv_push(&nl->v, nm);
        }
    }
    sv_free(&elems);
    chk_unref((ChkList*)e->chk_cache);
    e->chk_cache     = chk_ref(nl);
    e->chk_cache_gen = g_arrgen;
    chk_install(&asmb->st.check_constraints[idx], nl);
    return 1;
}

/* 解決できなかった型名を、同じ名前について一度だけ報告するための印。 */
static int reloc_badname_seen(AsmState *st, const char *name){
    for(int i = 0; i < st->reloc_badname_len; i++)
        if(strcmp(st->reloc_badname[i], name) == 0) return 1;
    if(st->reloc_badname_len < (int)(sizeof(st->reloc_badname)/sizeof(st->reloc_badname[0])))
        st->reloc_badname[st->reloc_badname_len++] = strdup(name);
    return 0;
}

/* ELF 宣言の数値欄の読み取り結果。同じ綴りが何度も現れるので覚えておく。
   axx.py の DirectiveProcessor._elfdecl_cache と同じく、鍵は (綴り, 下限, 上限)。
   2 回目からは式を評価しないので、式の中で出る警告も 1 回だけになる。 */
typedef struct { char *text; uint64_t lo, hi; int is_u64; int ok; uint64_t val; } ElfDeclMemo;
static ElfDeclMemo *g_elfdecl_memo = NULL;
static int g_elfdecl_memo_n = 0, g_elfdecl_memo_cap = 0;

/* 宣言の数値欄を lo..hi の整数として読む。is_u64 なら符号なし 64 ビット。
   axx.py の _elf_decl_num() と同じ規則である。 */
static int elf_decl_read(Assembler *asmb, const char *dname, const char *text_in,
                         uint64_t lo, uint64_t hi, int is_u64, uint64_t *out){
    AsmState *st = &asmb->st;
    while(*text_in==' '||*text_in=='\t') text_in++;
    size_t tl = strlen(text_in);
    while(tl > 0 && (text_in[tl-1]==' '||text_in[tl-1]=='\t')) tl--;
    if(tl == 0){
        axx_diagf(1, 0, " error - %s: a number is required.\n", dname);
        return 0;
    }
    char *text = malloc(tl + 1);
    if(!text){ perror("malloc"); exit(1); }
    memcpy(text, text_in, tl); text[tl] = '\0';
    char lob[32], hib[32];
    if(is_u64){
        snprintf(lob, sizeof(lob), "%llu", (unsigned long long)lo);
        snprintf(hib, sizeof(hib), "%llu", (unsigned long long)hi);
    } else {
        snprintf(lob, sizeof(lob), "%lld", (long long)lo);
        snprintf(hib, sizeof(hib), "%lld", (long long)hi);
    }
    for(int i = 0; i < g_elfdecl_memo_n; i++){
        ElfDeclMemo *m = &g_elfdecl_memo[i];
        if(m->lo == lo && m->hi == hi && m->is_u64 == is_u64 && strcmp(m->text, text) == 0){
            if(!m->ok)
                axx_diagf(1, 0, " error - %s: value must be an integer in %s..%s, "
                                "got '%s'.\n", dname, lob, hib, text);
            else *out = m->val;
            free(text);
            return m->ok;
        }
    }
    int io;
    st->error_undefined_label = 0;
    uint256_t v = expr_expression_pat(asmb, text, 0, &io);
    int ok;
    uint64_t val = 0;
    if(is_u64){
        uint64_t n = u256_to_u64(v);
        ok = !(st->error_undefined_label || u256_is_undef_derived(v)
               || !u256_eq(v, u256_from_u64(n)) || n < lo || n > hi);
        val = n;
    } else {
        int64_t n = u256_to_i64(v);
        ok = !(st->error_undefined_label || u256_is_undef_derived(v)
               || !u256_eq(v, u256_from_i64(n)) || n < (int64_t)lo || n > (int64_t)hi);
        val = (uint64_t)n;
    }
    if(!ok)
        axx_diagf(1, 0, " error - %s: value must be an integer in %s..%s, "
                        "got '%s'.\n", dname, lob, hib, text);
    st->error_undefined_label = 0;
    if(g_elfdecl_memo_n >= g_elfdecl_memo_cap){
        g_elfdecl_memo_cap = g_elfdecl_memo_cap ? g_elfdecl_memo_cap * 2 : 16;
        g_elfdecl_memo = realloc(g_elfdecl_memo, (size_t)g_elfdecl_memo_cap * sizeof(ElfDeclMemo));
        if(!g_elfdecl_memo){ perror("realloc"); exit(1); }
    }
    ElfDeclMemo *m = &g_elfdecl_memo[g_elfdecl_memo_n++];
    m->text = text; m->lo = lo; m->hi = hi; m->is_u64 = is_u64; m->ok = ok; m->val = val;
    if(ok) *out = val;
    return ok;
}

static int elf_decl_num(Assembler *asmb, const char *dname, const char *text,
                        long long lo, long long hi, long long *out){
    uint64_t v;
    if(!elf_decl_read(asmb, dname, text, (uint64_t)lo, (uint64_t)hi, 0, &v)) return 0;
    *out = (long long)v;
    return 1;
}

static int elf_decl_u64(Assembler *asmb, const char *dname, const char *text,
                        uint64_t lo, uint64_t hi, uint64_t *out){
    return elf_decl_read(asmb, dname, text, lo, hi, 1, out);
}

/* ELF 宣言の欄を取り出す（欄の詰め方の違いを吸収する）。 */
static void elf_decl_fields(const PatEntry *e, const char **f1, const char **f2){
    const char *q = e->f[1];
    while(*q==' '||*q=='\t') q++;
    if(*q){ *f1 = e->f[1]; *f2 = e->f[2]; }
    else  { *f1 = e->f[2]; *f2 = ""; }
}

/* ELF 宣言の文字列欄を差し替え、変わったら世代番号を進める。 */
static void elf_decl_set_str(AsmState *st, char **slot, const char *text){
    if(*slot && strcmp(*slot, text)==0) return;
    free(*slot);
    *slot = strdup(text);
    if(!*slot){ perror("strdup"); exit(1); }
    st->elf_decl_gen++;
}

/* ELF 宣言の欄から空白を落として写す。 */
static void elf_decl_trim(char *dst, size_t dsz, const char *src){
    while(*src==' '||*src=='\t') src++;
    size_t n = strlen(src);
    while(n > 0 && (src[n-1]==' '||src[n-1]=='\t'||src[n-1]=='\r'||src[n-1]=='\n')) n--;
    if(n >= dsz) n = dsz - 1;
    memcpy(dst, src, n);
    dst[n] = '\0';
}

/* 同じものを確保して返す。 */
static char *elf_decl_trim_dup(const char *src){
    if(!src) src = "";
    size_t n = strlen(src);
    char *d = malloc(n + 1);
    if(!d){ perror("malloc"); exit(1); }
    elf_decl_trim(d, n + 1, src);
    return d;
}

/* `.elftype` の宣言を登録する本体。 */
static int elftype_apply(Assembler *asmb, PatEntry *e){
    AsmState *st = &asmb->st;
    const char *name_str = e->f[1][0] ? e->f[1] : e->f[2];
    const char *val_str  = e->f[1][0] ? e->f[2] : "";

    char *nm = malloc(strlen(name_str) + 1);
    if(!nm){ perror("malloc"); exit(1); }
    size_t nn = 0;
    for(const char *q = name_str; *q; q++){
        if(*q == ' ' || *q == '\t') continue;
        nm[nn++] = (char)tolower((unsigned char)*q);
    }
    nm[nn] = '\0';
    if(!nm[0]){
        axx_diagf(1, 0, " error - .elftype: type name is not specified.\n");
        e->elftype_done = 1; e->elftype_val = 0;
        free(nm);
        return 1;
    }
    if(!val_str[0]){
        axx_diagf(1, 0, " error - .elftype: type number is not specified ('%s').\n", nm);
        e->elftype_done = 1; e->elftype_val = 0;
        free(nm);
        return 1;
    }

    if(!e->elftype_done){
        int io;
        st->error_undefined_label = 0;
        uint256_t v = expr_expression_pat(asmb, val_str, 0, &io);
        int64_t n = u256_to_i64(v);
        if(st->error_undefined_label || u256_is_undef_derived(v)
           || n < 1 || n > 2147483647 || !u256_eq(v, u256_from_i64(n))){
            axx_diagf(1, 0, " error - .elftype: type number must be an integer in "
                            "1..2147483647, got '%s'.\n", val_str);
            st->error_undefined_label = 0;
            e->elftype_done = 1; e->elftype_val = 0;
            free(nm);
            return 1;
        }
        st->error_undefined_label = 0;
        e->elftype_val  = (int)n;
        e->elftype_wid  = 0;
        e->elftype_pcr  = 0;
        long long _w = 0, _pc = 0;
        if(e->f[3][0]){
            if(!elf_decl_num(asmb, ".elftype", e->f[3], 1, 8, &_w)){
                e->elftype_done = 1; e->elftype_val = 0;
                free(nm);
                return 1;
            }
            e->elftype_wid = (int)_w;
        }
        if(e->f[4][0]){
            if(!elf_decl_num(asmb, ".elftype", e->f[4], 0, 1, &_pc)){
                e->elftype_done = 1; e->elftype_val = 0;
                free(nm);
                return 1;
            }
            e->elftype_pcr = (int)_pc;
        }
        e->elftype_done = 1;
    }
    if(e->elftype_val > 0)
        elftype_set(st, nm, e->elftype_val, e->elftype_wid, e->elftype_pcr);
    free(nm);
    return 1;
}

/* `.elftype` — リロケーション型の名前と番号を自分で決める。 */
static int dir_elftype(Assembler *asmb, PatEntry *e){
    if(!e || strcmp(e->f[0], ".elftype") != 0) return 0;
    return elftype_apply(asmb, e);
}


/* `.elfmachine` — e_machine の既定値（`-m` より弱い）。 */
static int dir_elfmachine(Assembler *asmb, PatEntry *e){
    if(!e || strcmp(e->f[0], ".elfmachine") != 0) return 0;
    AsmState *st = &asmb->st;
    const char *numf, *namef;
    elf_decl_fields(e, &numf, &namef);
    long long v;
    if(!elf_decl_num(asmb, ".elfmachine", numf, 0, 65535, &v)) return 1;
    char nm[64];
    elf_decl_trim(nm, sizeof(nm), namef);
    if(st->elf_decl_machine != (int)v || strcmp(st->elf_decl_name, nm) != 0){
        st->elf_decl_machine = (int)v;
        snprintf(st->elf_decl_name, sizeof(st->elf_decl_name), "%s", nm);
        st->elf_decl_gen++;
    }
    if(!st->elf_machine_from_cli && st->elf_machine != (int)v){
        st->elf_machine = (int)v;
        st->elf_decl_gen++;
    }
    return 1;
}

/* `.elfclass` — ELF32 / ELF64 の既定値（`-f` より弱い）。 */
static int dir_elfclass(Assembler *asmb, PatEntry *e){
    if(!e || strcmp(e->f[0], ".elfclass") != 0) return 0;
    AsmState *st = &asmb->st;
    const char *f1, *f2; elf_decl_fields(e, &f1, &f2);
    char *t = elf_decl_trim_dup(f1);
    int cls = 0;
    if(strcmp(t,"32")==0) cls = 1;
    else if(strcmp(t,"64")==0) cls = 2;
    else {
        axx_diagf(1, 0, " error - .elfclass: value must be 32 or 64, got '%s'.\n", t);
        free(t);
        return 1;
    }
    free(t);
    if(st->elf_decl_class != cls){ st->elf_decl_class = cls; st->elf_decl_gen++; }
    return 1;
}

/* `.elfrela` — .rela か .rel かを決める。 */
static int dir_elfrela(Assembler *asmb, PatEntry *e){
    if(!e || strcmp(e->f[0], ".elfrela") != 0) return 0;
    AsmState *st = &asmb->st;
    const char *f1, *f2; elf_decl_fields(e, &f1, &f2);
    char *t = elf_decl_trim_dup(f1);
    for(char *q=t; *q; q++) *q = (char)tolower((unsigned char)*q);
    int r;
    if(strcmp(t,"1")==0 || strcmp(t,"rela")==0) r = 1;
    else if(strcmp(t,"0")==0 || strcmp(t,"rel")==0) r = 0;
    else {
        axx_diagf(1, 0, " error - .elfrela: value must be 1/rela or 0/rel, got '%s'.\n", t);
        free(t);
        return 1;
    }
    free(t);
    if(st->elf_decl_rela != r){ st->elf_decl_rela = r; st->elf_decl_gen++; }
    return 1;
}

/* `.elfwidth` — 欄の幅から型を推測する対応を宣言する。幅は 2 のべき乗
   でなくてもよい。 */
static int dir_elfwidth(Assembler *asmb, PatEntry *e){
    if(!e || strcmp(e->f[0], ".elfwidth") != 0) return 0;
    AsmState *st = &asmb->st;
    const char *wf, *tf; elf_decl_fields(e, &wf, &tf);
    long long w;
    if(!elf_decl_num(asmb, ".elfwidth", wf, 1, 8, &w)) return 1;
    char *t = elf_decl_trim_dup(tf);
    if(!t[0]){
        axx_diagf(1, 0, " error - .elfwidth: relocation type is not specified.\n");
        free(t);
        return 1;
    }
    elf_decl_set_str(st, &st->elf_decl_width[(int)w], t);
    free(t);
    return 1;
}

/* `.elfextern` — 外部シンボル参照に使う既定の型。 */
static int dir_elfextern(Assembler *asmb, PatEntry *e){
    if(!e || strcmp(e->f[0], ".elfextern") != 0) return 0;
    AsmState *st = &asmb->st;
    const char *f1, *f2; elf_decl_fields(e, &f1, &f2);
    char *t = elf_decl_trim_dup(f1);
    if(!t[0]){
        axx_diagf(1, 0, " error - .elfextern: relocation type is not specified.\n");
        free(t);
        return 1;
    }
    elf_decl_set_str(st, &st->elf_decl_extern, t);
    free(t);
    return 1;
}

/* `.elfdwarf` — DWARF セクション内の絶対参照に使う型。 */
static int dir_elfdwarf(Assembler *asmb, PatEntry *e){
    if(!e || strcmp(e->f[0], ".elfdwarf") != 0) return 0;
    AsmState *st = &asmb->st;
    const char *f1, *f2; elf_decl_fields(e, &f1, &f2);
    char *t = elf_decl_trim_dup(f1);
    if(!t[0]){
        axx_diagf(1, 0, " error - .elfdwarf: relocation type is not specified.\n");
        free(t);
        return 1;
    }
    elf_decl_set_str(st, &st->elf_decl_dwarf, t);
    free(t);
    return 1;
}

static const struct { const char *name; int idx; long long lo, hi; } _elf_hdr_fields[] = {
    { "type",       EHF_TYPE,       0, 0xFFFFll },
    { "flags",      EHF_FLAGS,      0, 0xFFFFFFFFll },
    { "version",    EHF_VERSION,    0, 0xFFFFFFFFll },
    { "entry",      EHF_ENTRY,      0, 0x7FFFFFFFFFFFFFFFll },
    { "osabi",      EHF_OSABI,      0, 0xFFll },
    { "abiversion", EHF_ABIVERSION, 0, 0xFFll },
    { NULL, 0, 0, 0 }
};

/* `.elfheader` — ELF ヘッダの欄（e_flags など）を直接書く。 */
static int dir_elfheader(Assembler *asmb, PatEntry *e){
    if(!e || strcmp(e->f[0], ".elfheader") != 0) return 0;
    AsmState *st = &asmb->st;
    const char *ff, *vf; elf_decl_fields(e, &ff, &vf);
    char fld[32]; size_t fn = 0;
    for(const char *q = ff; *q && fn + 1 < sizeof(fld); q++){
        if(*q == ' ' || *q == '\t') continue;
        fld[fn++] = (char)tolower((unsigned char)*q);
    }
    fld[fn] = '\0';
    int k = 0;
    for(; _elf_hdr_fields[k].name; k++)
        if(strcmp(_elf_hdr_fields[k].name, fld)==0) break;
    if(!_elf_hdr_fields[k].name){
        axx_diagf(1, 0, " error - .elfheader: unknown field '%s' (type, flags, "
                        "version, entry, osabi, abiversion).\n", fld);
        return 1;
    }
    long long v;
    if(!elf_decl_num(asmb, ".elfheader", vf, _elf_hdr_fields[k].lo,
                     _elf_hdr_fields[k].hi, &v)) return 1;
    int ix = _elf_hdr_fields[k].idx;
    if(!st->elf_hdr_set[ix] || st->elf_hdr_val[ix] != (uint64_t)v){
        st->elf_hdr_set[ix] = 1;
        st->elf_hdr_val[ix] = (uint64_t)v;
        st->elf_decl_gen++;
    }
    return 1;
}

static void elf_sec_set(AsmState *st, const char *name, uint32_t flags,
                        int type_set, uint32_t type, int al_set, uint32_t al,
                        int es_set, uint32_t es){
    for(int i=0;i<st->elf_secs_len;i++)
        if(strcasecmp(st->elf_secs[i].name, name)==0){
            if(st->elf_secs[i].flags != flags
               || st->elf_secs[i].type_set != type_set
               || st->elf_secs[i].type != type
               || st->elf_secs[i].al_set != al_set
               || st->elf_secs[i].al != al
               || st->elf_secs[i].es_set != es_set
               || st->elf_secs[i].es != es){
                st->elf_secs[i].flags    = flags;
                st->elf_secs[i].type_set = type_set;
                st->elf_secs[i].type     = type;
                st->elf_secs[i].al_set   = al_set;
                st->elf_secs[i].al       = al;
                st->elf_secs[i].es_set   = es_set;
                st->elf_secs[i].es       = es;
                st->elf_decl_gen++;
            }
            return;
        }
    if(st->elf_secs_len >= st->elf_secs_cap){
        st->elf_secs_cap = st->elf_secs_cap ? st->elf_secs_cap*2 : 4;
        st->elf_secs = realloc(st->elf_secs,
                               (size_t)st->elf_secs_cap*sizeof(*st->elf_secs));
        if(!st->elf_secs){ perror("realloc"); exit(1); }
    }
    st->elf_secs[st->elf_secs_len].name = strdup(name);
    if(!st->elf_secs[st->elf_secs_len].name){ perror("strdup"); exit(1); }
    st->elf_secs[st->elf_secs_len].flags    = flags;
    st->elf_secs[st->elf_secs_len].type_set = type_set;
    st->elf_secs[st->elf_secs_len].type     = type;
    st->elf_secs[st->elf_secs_len].al_set   = al_set;
    st->elf_secs[st->elf_secs_len].al       = al;
    st->elf_secs[st->elf_secs_len].es_set   = es_set;
    st->elf_secs[st->elf_secs_len].es       = es;
    st->elf_secs_len++;
    st->elf_decl_gen++;
}

/* `.elfsection` の宣言を名前で引く。 */
static int elf_sec_find(const AsmState *st, const char *name){
    for(int i=0;i<st->elf_secs_len;i++)
        if(strcasecmp(st->elf_secs[i].name, name)==0) return i;
    return -1;
}

/* `.elffield` — 命令語のどのビットに値が入るかを宣言する。
   `.elffield::<型>::<マスク>[::<オフセット>[::<シフト>[::<補正>]]]`。
   シフトは REL のとき加数を欄へ書き戻す前に右へずらすビット数、補正は
   加数に足す定数。axx.py の elffield_processing() と同じ規則である。 */
static int dir_elffield(Assembler *asmb, PatEntry *e){
    if(!e || strcmp(e->f[0], ".elffield") != 0) return 0;
    AsmState *st = &asmb->st;
    const char *tf, *mf; elf_decl_fields(e, &tf, &mf);
    char *t = elf_decl_trim_dup(tf);
    if(!t[0]){
        axx_diagf(1, 0, " error - .elffield: relocation type is not specified.\n");
        free(t);
        return 1;
    }
    uint64_t m;
    if(!elf_decl_u64(asmb, ".elffield", mf, 1, 0xFFFFFFFFFFFFFFFFull, &m)){ free(t); return 1; }
    long long off = 0;
    {
        const char *q = e->f[3];
        while(*q==' '||*q=='\t') q++;
        if(*q && !elf_decl_num(asmb, ".elffield", e->f[3], 0, 255, &off)){ free(t); return 1; }
    }
    long long sh = 0;
    {
        const char *q = e->f[4];
        while(*q==' '||*q=='\t') q++;
        if(*q && !elf_decl_num(asmb, ".elffield", e->f[4], 0, 63, &sh)){ free(t); return 1; }
    }
    long long bias = 0;
    {
        const char *q = e->f[5];
        while(*q==' '||*q=='\t') q++;
        if(*q && !elf_decl_num(asmb, ".elffield", e->f[5], -0x7FFFFFFFll, 0x7FFFFFFFll, &bias)){
            free(t); return 1;
        }
    }
    for(int i = 0; i < st->elf_fields_len; i++){
        if(strcmp(st->elf_fields[i].type, t) == 0){
            if(st->elf_fields[i].mask != m || st->elf_fields[i].off != (int)off
               || st->elf_fields[i].shift != (int)sh || st->elf_fields[i].bias != bias){
                st->elf_fields[i].mask  = m;
                st->elf_fields[i].off   = (int)off;
                st->elf_fields[i].shift = (int)sh;
                st->elf_fields[i].bias  = bias;
                st->elf_decl_gen++;
            }
            free(t);
            return 1;
        }
    }
    if(st->elf_fields_len >= st->elf_fields_cap){
        st->elf_fields_cap = st->elf_fields_cap ? st->elf_fields_cap * 2 : 16;
        st->elf_fields = realloc(st->elf_fields,
                                 sizeof(st->elf_fields[0]) * (size_t)st->elf_fields_cap);
        if(!st->elf_fields){ perror("realloc"); exit(1); }
    }
    st->elf_fields[st->elf_fields_len].type  = t;
    st->elf_fields[st->elf_fields_len].mask  = m;
    st->elf_fields[st->elf_fields_len].off   = (int)off;
    st->elf_fields[st->elf_fields_len].shift = (int)sh;
    st->elf_fields[st->elf_fields_len].bias  = bias;
    st->elf_fields_len++;
    st->elf_decl_gen++;
    return 1;
}

/* `.elfpcguess` / `.elfbuiltin` の 0 / 1 を読む本体。 */
static int dir_elf_flag(Assembler *asmb, PatEntry *e, const char *dname, int *slot){
    AsmState *st = &asmb->st;
    const char *f1, *f2; elf_decl_fields(e, &f1, &f2);
    char *t = elf_decl_trim_dup(f1);
    int v;
    if(strcmp(t, "0") == 0) v = 0;
    else if(strcmp(t, "1") == 0) v = 1;
    else {
        axx_diagf(1, 0, " error - %s: value must be 0 or 1, got '%s'.\n", dname, t);
        free(t);
        return 1;
    }
    free(t);
    if(*slot != v){ *slot = v; st->elf_decl_gen++; }
    return 1;
}

/* `.elfpcguess` — 幅からの推定で絶対型を PC 相対型に取り替えるか。
   axx.py の elfpcguess_processing() と同じ規則である。 */
static int dir_elfpcguess(Assembler *asmb, PatEntry *e){
    if(!e || strcmp(e->f[0], ".elfpcguess") != 0) return 0;
    return dir_elf_flag(asmb, e, ".elfpcguess", &asmb->st.elf_decl_pcguess);
}

/* `.elfbuiltin` — 組み込みのマシン表を土台にするか。
   axx.py の elfbuiltin_processing() と同じ規則である。 */
static int dir_elfbuiltin(Assembler *asmb, PatEntry *e){
    if(!e || strcmp(e->f[0], ".elfbuiltin") != 0) return 0;
    return dir_elf_flag(asmb, e, ".elfbuiltin", &asmb->st.elf_decl_builtin);
}

/* 配列を 1 つ伸ばす（ELF 宣言の表に共通）。 */
static void *elf_decl_grow(void *p, int *cap, int len, size_t sz){
    if(len < *cap) return p;
    *cap = *cap ? *cap * 2 : 8;
    p = realloc(p, (size_t)*cap * sz);
    if(!p){ perror("realloc"); exit(1); }
    return p;
}

/* `.elfextra` — その型のリロケーションに、同じ位置へもう 1 つ添える。
   axx.py の elfextra_processing() と同じ規則である。 */
static int dir_elfextra(Assembler *asmb, PatEntry *e){
    if(!e || strcmp(e->f[0], ".elfextra") != 0) return 0;
    AsmState *st = &asmb->st;
    char *t = elf_decl_trim_dup(e->f[1]);
    char *c = elf_decl_trim_dup(e->f[2]);
    if(!t[0] || !c[0]){
        axx_diagf(1, 0, " error - .elfextra: two relocation types are required.\n");
        free(t); free(c);
        return 1;
    }
    long long sym = 0;
    {
        const char *q = e->f[3];
        while(*q==' '||*q=='\t') q++;
        if(*q && !elf_decl_num(asmb, ".elfextra", e->f[3], 0, 1, &sym)){ free(t); free(c); return 1; }
    }
    for(int i = 0; i < st->elf_extras_len; i++)
        if(strcmp(st->elf_extras[i].type, t) == 0 && strcmp(st->elf_extras[i].comp, c) == 0){
            if(st->elf_extras[i].sym != (int)sym){
                st->elf_extras[i].sym = (int)sym;
                st->elf_decl_gen++;
            }
            free(t); free(c);
            return 1;
        }
    st->elf_extras = elf_decl_grow(st->elf_extras, &st->elf_extras_cap,
                                   st->elf_extras_len, sizeof(st->elf_extras[0]));
    st->elf_extras[st->elf_extras_len].type = t;
    st->elf_extras[st->elf_extras_len].comp = c;
    st->elf_extras[st->elf_extras_len].sym  = (int)sym;
    st->elf_extras_len++;
    st->elf_decl_gen++;
    return 1;
}

/* `.elfdiff` — 2 つのラベルの差を、足す型と引く型の対で出す。
   axx.py の elfdiff_processing() と同じ規則である。 */
static int dir_elfdiff(Assembler *asmb, PatEntry *e){
    if(!e || strcmp(e->f[0], ".elfdiff") != 0) return 0;
    AsmState *st = &asmb->st;
    {
        /* 第 1 欄が数でなければ型名: 型付きの差。 */
        char *f1 = elf_decl_trim_dup(e->f[1]);
        int isnum = f1[0] != '\0';
        if(isnum){
            if(f1[0] == '0' && (f1[1] == 'x' || f1[1] == 'X') && f1[2]){
                for(const char *q = f1 + 2; *q; q++) if(!isxdigit((unsigned char)*q)){ isnum = 0; break; }
            } else {
                for(const char *q = f1; *q; q++) if(!isdigit((unsigned char)*q)){ isnum = 0; break; }
            }
        }
        if(f1[0] && !isnum){
            char *a = elf_decl_trim_dup(e->f[2]);
            char *b = elf_decl_trim_dup(e->f[3]);
            if(!a[0] || !b[0]){
                axx_diagf(1, 0, " error - .elfdiff: an add type and a subtract type are required.\n");
                free(f1); free(a); free(b);
                return 1;
            }
            for(int i = 0; i < st->elf_diff_t_len; i++)
                if(strcmp(st->elf_diff_t[i].type, f1) == 0){
                    if(strcmp(st->elf_diff_t[i].add, a) != 0 || strcmp(st->elf_diff_t[i].sub, b) != 0){
                        free(st->elf_diff_t[i].add); free(st->elf_diff_t[i].sub);
                        st->elf_diff_t[i].add = a; st->elf_diff_t[i].sub = b;
                        st->elf_decl_gen++;
                    } else { free(a); free(b); }
                    free(f1);
                    return 1;
                }
            st->elf_diff_t = elf_decl_grow(st->elf_diff_t, &st->elf_diff_t_cap,
                                           st->elf_diff_t_len, sizeof(st->elf_diff_t[0]));
            st->elf_diff_t[st->elf_diff_t_len].type = f1;
            st->elf_diff_t[st->elf_diff_t_len].add  = a;
            st->elf_diff_t[st->elf_diff_t_len].sub  = b;
            st->elf_diff_t_len++;
            st->elf_decl_gen++;
            return 1;
        }
        free(f1);
    }
    long long w;
    if(!elf_decl_num(asmb, ".elfdiff", e->f[1], 1, 8, &w)) return 1;
    char *a = elf_decl_trim_dup(e->f[2]);
    char *b = elf_decl_trim_dup(e->f[3]);
    if(!a[0] || !b[0]){
        axx_diagf(1, 0, " error - .elfdiff: an add type and a subtract type are required.\n");
        free(a); free(b);
        return 1;
    }
    if(!st->elf_diff_add[w] || strcmp(st->elf_diff_add[w], a) != 0
       || strcmp(st->elf_diff_sub[w], b) != 0){
        free(st->elf_diff_add[w]); free(st->elf_diff_sub[w]);
        st->elf_diff_add[w] = a;
        st->elf_diff_sub[w] = b;
        st->elf_decl_gen++;
    } else {
        free(a); free(b);
    }
    return 1;
}

/* `.elfencode` — REL で加数を欄へ書き戻す関数を型ごとに決める。
   axx.py の elfencode_processing() と同じ規則である。 */
static int dir_elfencode(Assembler *asmb, PatEntry *e){
    if(!e || strcmp(e->f[0], ".elfencode") != 0) return 0;
    AsmState *st = &asmb->st;
    char *t = elf_decl_trim_dup(e->f[1]);
    char *f = elf_decl_trim_dup(e->f[2]);
    if(!t[0] || !f[0]){
        axx_diagf(1, 0, " error - .elfencode: a relocation type and a function name are required.\n");
        free(t); free(f);
        return 1;
    }
    for(int i = 0; i < st->elf_encodes_len; i++)
        if(strcmp(st->elf_encodes[i].type, t) == 0){
            if(strcmp(st->elf_encodes[i].fn, f) != 0){
                free(st->elf_encodes[i].fn);
                st->elf_encodes[i].fn = f;
                st->elf_decl_gen++;
            } else free(f);
            free(t);
            return 1;
        }
    st->elf_encodes = elf_decl_grow(st->elf_encodes, &st->elf_encodes_cap,
                                    st->elf_encodes_len, sizeof(st->elf_encodes[0]));
    st->elf_encodes[st->elf_encodes_len].type = t;
    st->elf_encodes[st->elf_encodes_len].fn   = f;
    st->elf_encodes_len++;
    st->elf_decl_gen++;
    return 1;
}

/* `.elfrinfo` — r_info を組む関数を決める。
   axx.py の elfrinfo_processing() と同じ規則である。 */
static int dir_elfrinfo(Assembler *asmb, PatEntry *e){
    if(!e || strcmp(e->f[0], ".elfrinfo") != 0) return 0;
    AsmState *st = &asmb->st;
    const char *f1, *f2; elf_decl_fields(e, &f1, &f2);
    char *f = elf_decl_trim_dup(f1);
    if(!f[0]){
        axx_diagf(1, 0, " error - .elfrinfo: a function name is required.\n");
        free(f);
        return 1;
    }
    elf_decl_set_str(st, &st->elf_decl_rinfo, f);
    free(f);
    return 1;
}

/* `.elfunit` — 加数とシンボル値の単位（byte / word）。
   axx.py の elfunit_processing() と同じ規則である。 */
static int dir_elfunit(Assembler *asmb, PatEntry *e){
    if(!e || strcmp(e->f[0], ".elfunit") != 0) return 0;
    AsmState *st = &asmb->st;
    const char *f1, *f2; elf_decl_fields(e, &f1, &f2);
    char *t = elf_decl_trim_dup(f1);
    for(char *q = t; *q; q++) *q = (char)tolower((unsigned char)*q);
    int u;
    if(strcmp(t, "byte") == 0) u = 0;
    else if(strcmp(t, "word") == 0) u = 1;
    else {
        axx_diagf(1, 0, " error - .elfunit: value must be byte or word, got '%s'.\n", t);
        free(t);
        return 1;
    }
    free(t);
    if(st->elf_decl_unit != u){ st->elf_decl_unit = u; st->elf_decl_gen++; }
    return 1;
}

/* `.elflink` — セクションの sh_link と sh_info を決める。
   axx.py の elflink_processing() と同じ規則である。 */
static int dir_elflink(Assembler *asmb, PatEntry *e){
    if(!e || strcmp(e->f[0], ".elflink") != 0) return 0;
    AsmState *st = &asmb->st;
    char *nm  = elf_decl_trim_dup(e->f[1]);
    char *lk  = elf_decl_trim_dup(e->f[2]);
    char *inf = elf_decl_trim_dup(e->f[3]);
    if(!nm[0]){
        axx_diagf(1, 0, " error - .elflink: section name is not specified.\n");
        free(nm); free(lk); free(inf);
        return 1;
    }
    for(int i = 0; i < st->elf_links_len; i++)
        if(strcasecmp(st->elf_links[i].sec, nm) == 0){
            if(strcmp(st->elf_links[i].link, lk) != 0 || strcmp(st->elf_links[i].info, inf) != 0){
                free(st->elf_links[i].link); free(st->elf_links[i].info);
                st->elf_links[i].link = lk;
                st->elf_links[i].info = inf;
                st->elf_decl_gen++;
            } else { free(lk); free(inf); }
            free(nm);
            return 1;
        }
    for(char *q = nm; *q; q++) *q = (char)tolower((unsigned char)*q);
    st->elf_links = elf_decl_grow(st->elf_links, &st->elf_links_cap,
                                  st->elf_links_len, sizeof(st->elf_links[0]));
    st->elf_links[st->elf_links_len].sec  = nm;
    st->elf_links[st->elf_links_len].link = lk;
    st->elf_links[st->elf_links_len].info = inf;
    st->elf_links_len++;
    st->elf_decl_gen++;
    return 1;
}

/* `.elfcfi` — CFI（.eh_frame）の CIE の欄を決める。
   axx.py の elfcfi_processing() と同じ規則である。 */
static int dir_elfcfi(Assembler *asmb, PatEntry *e){
    if(!e || strcmp(e->f[0], ".elfcfi") != 0) return 0;
    AsmState *st = &asmb->st;
    long long ra, ca, da, pad = 0;
    if(!elf_decl_num(asmb, ".elfcfi", e->f[1], 0, 0xFFFF, &ra)) return 1;
    if(!elf_decl_num(asmb, ".elfcfi", e->f[2], 1, 0xFFFF, &ca)) return 1;
    if(!elf_decl_num(asmb, ".elfcfi", e->f[3], -0xFFFF, 0xFFFF, &da)) return 1;
    if(da == 0){
        axx_diagf(1, 0, " error - .elfcfi: the data alignment factor must not be 0.\n");
        return 1;
    }
    {
        const char *q = e->f[4];
        while(*q==' '||*q=='\t') q++;
        if(*q){
            if(!elf_decl_num(asmb, ".elfcfi", e->f[4], 1, 64, &pad)) return 1;
            if(pad & (pad - 1)){
                axx_diagf(1, 0, " error - .elfcfi: the padding alignment must be a power "
                                "of two, got '%lld'.\n", pad);
                return 1;
            }
        }
    }
    if(!st->elf_cfi_set || st->elf_cfi_ra != (int)ra || st->elf_cfi_code != (int)ca
       || st->elf_cfi_data != (int)da || st->elf_cfi_pad != (int)pad){
        st->elf_cfi_set = 1; st->elf_cfi_ra = (int)ra; st->elf_cfi_code = (int)ca;
        st->elf_cfi_data = (int)da; st->elf_cfi_pad = (int)pad;
        st->elf_decl_gen++;
    }
    return 1;
}

/* `.elfcfiinit` — CIE の初期命令を 1 つ足す。空白の並びは 1 つにそろえる。
   axx.py の elfcfiinit_processing() と同じ規則である。 */
static int dir_elfcfiinit(Assembler *asmb, PatEntry *e){
    if(!e || strcmp(e->f[0], ".elfcfiinit") != 0) return 0;
    AsmState *st = &asmb->st;
    const char *f1, *f2; elf_decl_fields(e, &f1, &f2);
    size_t n = strlen(f1);
    char *t = malloc(n + 1);
    if(!t){ perror("malloc"); exit(1); }
    size_t k = 0; int sp = 0;
    for(const char *q = f1; *q; q++){
        if(isspace((unsigned char)*q)){ sp = 1; continue; }
        if(sp && k){ t[k++] = ' '; }
        sp = 0;
        t[k++] = *q;
    }
    t[k] = '\0';
    if(!t[0]){
        axx_diagf(1, 0, " error - .elfcfiinit: an instruction is required.\n");
        free(t);
        return 1;
    }
    for(int i = 0; i < st->elf_cfiinit_len; i++)
        if(strcmp(st->elf_cfiinit[i], t) == 0){ free(t); return 1; }
    st->elf_cfiinit = elf_decl_grow(st->elf_cfiinit, &st->elf_cfiinit_cap,
                                    st->elf_cfiinit_len, sizeof(char*));
    st->elf_cfiinit[st->elf_cfiinit_len++] = t;
    st->elf_decl_gen++;
    return 1;
}

/* `.elfcfireg` — CFI の指令に書くレジスタ名と DWARF のレジスタ番号。
   axx.py の elfcfireg_processing() と同じ規則である。 */
static int dir_elfcfireg(Assembler *asmb, PatEntry *e){
    if(!e || strcmp(e->f[0], ".elfcfireg") != 0) return 0;
    AsmState *st = &asmb->st;
    char *nm = elf_decl_trim_dup(e->f[1]);
    for(char *q = nm; *q; q++) *q = (char)tolower((unsigned char)*q);
    if(!nm[0]){
        axx_diagf(1, 0, " error - .elfcfireg: a register name is required.\n");
        free(nm);
        return 1;
    }
    long long v;
    if(!elf_decl_num(asmb, ".elfcfireg", e->f[2], 0, 0xFFFF, &v)){ free(nm); return 1; }
    for(int i = 0; i < st->elf_cfireg_len; i++)
        if(strcmp(st->elf_cfireg[i].name, nm) == 0){
            if(st->elf_cfireg[i].num != (int)v){ st->elf_cfireg[i].num = (int)v; st->elf_decl_gen++; }
            free(nm);
            return 1;
        }
    st->elf_cfireg = elf_decl_grow(st->elf_cfireg, &st->elf_cfireg_cap,
                                   st->elf_cfireg_len, sizeof(st->elf_cfireg[0]));
    st->elf_cfireg[st->elf_cfireg_len].name = nm;
    st->elf_cfireg[st->elf_cfireg_len].num  = (int)v;
    st->elf_cfireg_len++;
    st->elf_decl_gen++;
    return 1;
}

/* `.elfcfireg` の名前を引く（大小を区別しない）。無ければ -1。 */
static int elf_cfireg_find(const AsmState *st, const char *name){
    for(int i = 0; i < st->elf_cfireg_len; i++)
        if(strcasecmp(st->elf_cfireg[i].name, name) == 0) return st->elf_cfireg[i].num;
    return -1;
}

/* `.elfgroup` — セクショングループ（SHT_GROUP）を宣言する。
   axx.py の elfgroup_processing() と同じ規則である。 */
static int dir_elfgroup(Assembler *asmb, PatEntry *e){
    if(!e || strcmp(e->f[0], ".elfgroup") != 0) return 0;
    AsmState *st = &asmb->st;
    char *gn  = elf_decl_trim_dup(e->f[1]);
    char *sig = elf_decl_trim_dup(e->f[2]);
    if(!gn[0] || !sig[0]){
        axx_diagf(1, 0, " error - .elfgroup: a group name and a signature symbol are required.\n");
        free(gn); free(sig);
        return 1;
    }
    long long fl;
    if(!elf_decl_num(asmb, ".elfgroup", e->f[3], 0, 0xFFFFFFFFll, &fl)){ free(gn); free(sig); return 1; }
    char **mem = NULL; int nmem = 0, cmem = 0;
    {
        const char *q = e->f[4];
        while(*q){
            const char *b = q;
            while(*q && *q != ',') q++;
            size_t n = (size_t)(q - b);
            char *tmp = malloc(n + 1);
            if(!tmp){ perror("malloc"); exit(1); }
            memcpy(tmp, b, n); tmp[n] = '\0';
            char *m = elf_decl_trim_dup(tmp);
            free(tmp);
            if(m[0]){
                mem = elf_decl_grow(mem, &cmem, nmem, sizeof(char*));
                mem[nmem++] = m;
            } else free(m);
            if(*q == ',') q++;
        }
    }
    if(nmem == 0){
        axx_diagf(1, 0, " error - .elfgroup: no member section is given.\n");
        free(gn); free(sig); free(mem);
        return 1;
    }
    for(int i = 0; i < st->elf_groups_len; i++)
        if(strcasecmp(st->elf_groups[i].name, gn) == 0 && strcmp(st->elf_groups[i].sig, sig) == 0){
            int same = strcmp(st->elf_groups[i].name, gn) == 0
                       && st->elf_groups[i].flags == (uint32_t)fl && st->elf_groups[i].nmem == nmem;
            for(int k = 0; same && k < nmem; k++)
                if(strcmp(st->elf_groups[i].mem[k], mem[k]) != 0) same = 0;
            if(!same){
                for(int k = 0; k < st->elf_groups[i].nmem; k++) free(st->elf_groups[i].mem[k]);
                free(st->elf_groups[i].mem);
                free(st->elf_groups[i].name);
                st->elf_groups[i].name  = gn;
                st->elf_groups[i].flags = (uint32_t)fl;
                st->elf_groups[i].mem   = mem;
                st->elf_groups[i].nmem  = nmem;
                st->elf_decl_gen++;
            } else {
                for(int k = 0; k < nmem; k++) free(mem[k]);
                free(mem); free(gn);
            }
            free(sig);
            return 1;
        }
    st->elf_groups = elf_decl_grow(st->elf_groups, &st->elf_groups_cap,
                                   st->elf_groups_len, sizeof(st->elf_groups[0]));
    st->elf_groups[st->elf_groups_len].name  = gn;
    st->elf_groups[st->elf_groups_len].sig   = sig;
    st->elf_groups[st->elf_groups_len].flags = (uint32_t)fl;
    st->elf_groups[st->elf_groups_len].mem   = mem;
    st->elf_groups[st->elf_groups_len].nmem  = nmem;
    st->elf_groups_len++;
    st->elf_decl_gen++;
    return 1;
}

/* `.elfsection` — 名前から推測できないセクションの属性を宣言する。
   sh_flags / sh_type / 整列 / 要素サイズ。 */
static int dir_elfsection(Assembler *asmb, PatEntry *e){
    if(!e || strcmp(e->f[0], ".elfsection") != 0) return 0;
    AsmState *st = &asmb->st;
    const char *name_str = e->f[1][0] ? e->f[1] : e->f[2];
    const char *flag_str = e->f[1][0] ? e->f[2] : "";
    char *nm = elf_decl_trim_dup(name_str);
    if(!nm[0]){
        axx_diagf(1, 0, " error - .elfsection: section name is not specified.\n");
        free(nm);
        return 1;
    }
    long long fl;
    if(!elf_decl_num(asmb, ".elfsection", flag_str, 0, 0xFFFFFFFFll, &fl)){
        free(nm);
        return 1;
    }
    int type_set = 0; long long ty = 0;
    if(e->f[3][0]){
        if(!elf_decl_num(asmb, ".elfsection", e->f[3], 0, 0xFFFFFFFFll, &ty)){
            free(nm);
            return 1;
        }
        type_set = 1;
    }
    int al_set = 0; long long al = 0;
    if(e->f[4][0]){
        if(!elf_decl_num(asmb, ".elfsection", e->f[4], 0, 0x40000000ll, &al)){
            free(nm);
            return 1;
        }
        if(al & (al - 1)){
            axx_diagf(1, 0, " error - .elfsection: alignment must be 0 or a "
                            "power of two, got '%lld'.\n", al);
            free(nm);
            return 1;
        }
        al_set = 1;
    }
    int es_set = 0; long long es = 0;
    if(e->f[5][0]){
        if(!elf_decl_num(asmb, ".elfsection", e->f[5], 0, 0xFFFFFFFFll, &es)){
            free(nm);
            return 1;
        }
        es_set = 1;
    }
    elf_sec_set(st, nm, (uint32_t)fl, type_set, (uint32_t)ty,
                al_set, (uint32_t)al, es_set, (uint32_t)es);
    free(nm);
    return 1;
}

/* 整列が書かれていないセクションの既定値。SHT_NOTE だけ 4、ほかは 16。
   is_elf64 は現在使っていないが、axx.py 側と呼び出し形をそろえて残してある。 */
static uint32_t weo_default_align(uint32_t sh_type, int is_elf64){
    (void)is_elf64;
    if(sh_type == 7u) return 4u;
    return 16u;
}

static void elf_section_attrs(const AsmState *st, const char *name,
                              uint64_t *flags, uint32_t *shtype,
                              int *al_set, uint32_t *al, uint32_t *entsize){
    char *un = malloc(strlen(name)+1);
    if(!un){ perror("malloc"); exit(1); }
    int ui=0;
    for(;name[ui];ui++) un[ui]=(char)axx_upper_char(name[ui]);
    un[ui]=0;
    uint64_t fl;
    if     (strncmp(un,".TEXT",5)==0)   fl=0x2|0x4;
    else if(strncmp(un,".DATA",5)==0)   fl=0x2|0x1;
    else if(strncmp(un,".RODATA",7)==0) fl=0x2;
    else if(strncmp(un,".BSS",4)==0)    fl=0x2|0x1;
    else                                fl=0x2;
    uint32_t sht = (strncmp(un,".BSS",4)==0) ? 8u : 1u;
    int a_set = 0; uint32_t a_val = 0; uint32_t es_val = 0;
    int k = elf_sec_find(st, name);
    if(k >= 0){
        fl = st->elf_secs[k].flags;
        if(st->elf_secs[k].type_set) sht = st->elf_secs[k].type;
        if(st->elf_secs[k].al_set){ a_set = 1; a_val = st->elf_secs[k].al; }
        if(st->elf_secs[k].es_set) es_val = st->elf_secs[k].es;
    }
    *flags = fl; *shtype = sht;
    if(al_set)  *al_set  = a_set;
    if(al)      *al      = a_val;
    if(entsize) *entsize = es_val;
    free(un);
}

/* `.reloc` — その変数が捕らえたラベル参照に使う型を宣言する。 */
static int dir_reloc(Assembler *asmb, PatEntry *e){
    if(!e || strcmp(e->f[0], ".reloc") != 0) return 0;
    const char *var_str  = e->f[1];
    const char *type_str = e->f[2];
    if(fld_blank(var_str)){
        axx_diagf(1, 0, " error - .reloc: variable name is not specified.\n");
        return 1;
    }
    int idx = dir_var_slot(var_str);
    if(idx < 0){
        axx_diagf(1, 0, " error - .reloc: variable should be a lower case name ('%s').\n",
                   var_str);
        return 1;
    }
    char *tname = malloc(strlen(type_str) + 1);
    if(!tname){ perror("malloc"); exit(1); }
    size_t tn = 0;
    for(const char *q = type_str; *q; q++){
        if(*q == ' ' || *q == '\t') continue;
        tname[tn++] = (char)tolower((unsigned char)*q);
    }
    tname[tn] = '\0';
    if(!tname[0]){
        axx_diagf(1, 0, " error - .reloc: relocation type is not specified.\n");
        free(tname);
        return 1;
    }
    if(!asmb->st.elf_objfile[0]){ free(tname); return 1; }
    const ElfMachineInfo *m = elf_machine_effective(&asmb->st);
    int rtype = elf_reloc_named(&asmb->st, m, tname);
    if(rtype < 0){
        if(!reloc_badname_seen(&asmb->st, tname))
            axx_diagf(1, 0, " error - .reloc: unknown relocation type '%s' for %s.\n",
                       tname, m->name);
        free(tname);
        return 1;
    }
    free(tname);
    asmb->st.reloc_constraints[idx] = rtype;
    return 1;
}

/* `.clrreloc` — `.reloc` の宣言を外す。 */
static int dir_clrreloc(Assembler *asmb, PatEntry *e){
    if(!e || strcmp(e->f[0], ".clrreloc") != 0) return 0;
    const char *var_str = e->f[2][0] ? e->f[2] : e->f[1];
    if(var_str[0]){
        int idx = dir_var_slot(var_str);
        if(idx < 0){
            axx_diagf(1, 0, " error - .clrreloc: variable should be a lower case name ('%s').\n",
                       var_str);
            return 1;
        }
        asmb->st.reloc_constraints[idx] = 0;
    } else {
        for(int i = 0; i < g_nvars; i++) asmb->st.reloc_constraints[i] = 0;
    }
    return 1;
}

/* `.clrcheck` — `.check` の制限を外す。 */
static int dir_clrcheck(Assembler *asmb, PatEntry *e){
    if(!e || strcmp(e->f[0], ".clrcheck") != 0) return 0;
    const char *var_str = e->f[2];
    if(var_str[0]){
        int idx = dir_var_slot(var_str);
        if(idx < 0){
            axx_diagf(1, 0, " error - .clrcheck: variable should be a lower case name ('%s').\n",
                       var_str);
            return 1;
        }
        chk_install(&asmb->st.check_constraints[idx], NULL);
    } else {
        for(int i = 0; i < g_nvars; i++){
            chk_install(&asmb->st.check_constraints[i], NULL);
        }
    }
    return 1;
}

/* `.free` の 1 名前ぶん。シンボル・サブ表・`.check` の候補、そして変数名と
   して読めるならその `.check` / `.enum` / `.reloc` をすべて外す。 */
static void free_one_name(Assembler *asmb, const char *name){
    AsmState *st = &asmb->st;
    if(!name[0]) return;
    char key[512]; axx_strupr_to(key,name,sizeof(key));

    smap_delete(&st->symbols, key);
    strsym_delete(st, key);
    arrsym_delete(st, key);
    subv_mark_freed(&st->subs, name);

    for(int vi=0; vi<g_nvars; vi++){
        ChkList *cv = st->check_constraints[vi];
        if(!cv) continue;
        int hit = 0;
        for(int k=0; k<cv->v.len; k++)
            if(strcmp(cv->v.data[k], key)==0){ hit = 1; break; }
        if(!hit) continue;
        ChkList *nl = chk_new();
        for(int k=0; k<cv->v.len; k++)
            if(strcmp(cv->v.data[k], key)!=0) sv_push(&nl->v, cv->v.data[k]);
        chk_install(&st->check_constraints[vi], nl);
    }

    {
        char lower[64]; int n = 0;
        for(const char *q = name; *q && n < (int)sizeof(lower)-1; q++)
            lower[n++] = (char)tolower((unsigned char)*q);
        lower[n] = '\0';
        if(var_name_len(lower) == n){
            int vi = var_slot(lower, n, 0);
            if(vi >= 0){
                chk_install(&st->check_constraints[vi], NULL);
                st->reloc_constraints[vi] = 0;
                enumdef_clear(&st->enum_defs[vi]);
            }
        }
    }
}

static char *pat_trim(char *s);
static char *map_subst_index(const char *expr, const char *var, int i);

/* トップレベルのカンマだけで割る。括弧の中では割らない。 */
static void split_top_commas(const char *text, StrVec *out){
    int depth = 0;
    const char *b = text;
    char item[1024];
    for(const char *p = text; ; p++){
        if(*p == '(' || *p == '[' || *p == '{') depth++;
        else if(*p == ')' || *p == ']' || *p == '}'){ if(depth > 0) depth--; }
        if(*p == '\0' || (*p == ',' && depth == 0)){
            const char *s0 = b, *s1 = p;
            while(s0 < s1 && (*s0==' '||*s0=='\t')) s0++;
            while(s1 > s0 && (s1[-1]==' '||s1[-1]=='\t')) s1--;
            int n = (int)(s1 - s0);
            if(n > (int)sizeof(item)-1) n = (int)sizeof(item)-1;
            memcpy(item, s0, (size_t)n); item[n] = '\0';
            sv_push(out, item);
            if(*p == '\0') break;
            b = p + 1;
        }
    }
}

/* `.map` の本体。名前の並びに値を与え、同時に `.check` も設定する。
   値欄は 1 つの式（変数はリスト中の位置に置き換わる）か、名前と 1 対 1 で
   対応する値のリスト。長さが違えば何も定義せずにエラーにする。 */
static void map_apply(Assembler *asmb, PatEntry *e, SymMap *into, int set_check){
    AsmState *st = &asmb->st;
    const char *var_str  = e->f[1][0] ? pat_trim(e->f[1]) : "";
    const char *syms_str = e->f[2];
    const char *expr_str = pat_trim(e->f[3])[0] ? e->f[3] : var_str;
    int vslot = dir_var_slot(var_str);
    if(vslot < 0) return;
    char vname[64];
    snprintf(vname, sizeof(vname), "%s", var_slot_name(vslot));

    StrVec elems; sv_init(&elems);
    elem_list_expand(st, syms_str, &elems);
    StrVec vals; sv_init(&vals);
    split_top_commas(expr_str, &vals);
    if(vals.len > 1 && vals.len != elems.len){
        axx_diagf(1, 0, " error - .map: the value list has %d items "
                        "but the name list has %d.\n", vals.len, elems.len);
        sv_free(&vals); sv_free(&elems);
        return;
    }
    for(int i = 0; i < elems.len; i++){
        if(!elems.data[i][0]) continue;
        const char *src = (vals.len > 1) ? vals.data[i] : expr_str;
        char *val = map_subst_index(src, vname, i);
        int io;
        uint256_t v = expr_expression_pat(asmb, val, 0, &io);
        free(val);
        smap_set(into ? into : &st->symbols, elems.data[i], v);
    }
    sv_free(&vals);
    if(set_check){
        int idx = vslot;
        ChkList *nl = chk_new();
        for(int i = 0; i < elems.len; i++){
            if(!elems.data[i][0]){
                int dup = 0;
                for(int si = 0; si < nl->v.len; si++)
                    if(nl->v.data[si][0] == '\0'){ dup = 1; break; }
                if(!dup) sv_push(&nl->v, "");
            } else {
                sv_push(&nl->v, elems.data[i]);
            }
        }
        chk_install(&st->check_constraints[idx], nl);
    }
    sv_free(&elems);
}

/* `.map` — シンボル表とそのチェックを 1 行で書く。 */
static int dir_map(Assembler *asmb, PatEntry *e){
    if(!e || strcmp(e->f[0], ".map") != 0) return 0;
    if(g_unordered){
        /* 名前と値はその変数だけの表に入れる。同じ名前を別の変数が別の値で
           持てるので、`.setsym` を書き直さずに Z80 の C（レジスタ）と
           C（キャリー）のような使い分けができる。 */
        int vslot = dir_var_slot(e->f[1]);
        if(vslot < 0) return 1;
        SymMap **tp = &asmb->st.var_tables[vslot];
        if(!*tp){
            *tp = malloc(sizeof(SymMap));
            if(!*tp){ perror("malloc"); exit(1); }
            smap_init(*tp);
        } else {
            smap_clear(*tp);
        }
        map_apply(asmb, e, *tp, 1);
        return 1;
    }
    map_apply(asmb, e, NULL, 1);
    return 1;
}

/* `.unordered` — 宣言だけ。中身は pat_unordered_plan() が読み込み時に扱う。 */
static int dir_unordered(Assembler *asmb, PatEntry *e){
    (void)asmb;
    return e && strcmp(e->f[0], ".unordered") == 0;
}

/* `.free` — 名前をすべての表から外す。位置依存。 */
static int dir_free(Assembler *asmb, PatEntry *e){
    if(!e || strcmp(e->f[0], ".free") != 0) return 0;
    const char *names = e->f[2][0] ? e->f[2] : e->f[1];
    if(!names[0]){
        axx_diagf(1, 0, " error - .free: needs '.free::<name,name,...>'.\n");
        return 1;
    }
    const char *p = names;
    while(*p){
        while(*p==' '||*p=='\t') p++;
        char nm[512]; int j = 0;
        while(*p && *p!=',' && j < (int)sizeof(nm)-1) nm[j++] = *p++;
        while(j > 0 && (nm[j-1]==' '||nm[j-1]=='\t')) j--;
        nm[j] = '\0';
        free_one_name(asmb, nm);
        if(*p==',') p++;
        else break;
    }
    return 1;
}

/* `.passthru` — 当たらない行をエラーにせず素通しする。 */
static int dir_passthru(Assembler *asmb, PatEntry *e){
    if(!e || strcmp(e->f[0], ".passthru") != 0) return 0;
    char arg[32]; arg[0] = '\0';
    for(int fi=1; fi<PAT_FIELDS; fi++){
        const char *p = e->f[fi];
        while(*p==' '||*p=='\t') p++;
        if(*p){ axx_strupr_to(arg, p, sizeof(arg)); break; }
    }
    { size_t n = strlen(arg);
      while(n > 0 && (arg[n-1]==' '||arg[n-1]=='\t')) arg[--n] = '\0'; }
    if(arg[0]=='\0' || strcmp(arg,"ON")==0)   asmb->st.passthru = 1;
    else if(strcmp(arg,"OFF")==0)             asmb->st.passthru = 0;
    else
        axx_diagf(1, 0, " error - .passthru: expected 'on' or 'off' ('%s').\n", arg);
    return 1;
}

/* `.eol` — 1 ソース行につき 1 行の改行を入れる。 */
static int dir_eol(Assembler *asmb, PatEntry *e){
    if(!e || strcmp(e->f[0], ".eol") != 0) return 0;
    char arg[32]; arg[0] = '\0';
    for(int fi=1; fi<PAT_FIELDS; fi++){
        const char *p = e->f[fi];
        while(*p==' '||*p=='\t') p++;
        if(*p){ axx_strupr_to(arg, p, sizeof(arg)); break; }
    }
    { size_t n = strlen(arg);
      while(n > 0 && (arg[n-1]==' '||arg[n-1]=='\t')) arg[--n] = '\0'; }
    if(arg[0]=='\0' || strcmp(arg,"ON")==0) asmb->st.eol = 1;
    else if(strcmp(arg,"OFF")==0)           asmb->st.eol = 0;
    else
        axx_diagf(1, 0, " error - .eol: expected 'on' or 'off' ('%s').\n", arg);
    return 1;
}

/* `.textmode` — テキスト置換モード。ラベル・式・コメント・字下げを
   書かれていたままの綴りで出力に残す。 */
static int dir_textmode(Assembler *asmb, PatEntry *e){
    if(!e || strcmp(e->f[0], ".textmode") != 0) return 0;
    char arg[32]; arg[0] = '\0';
    for(int fi=1; fi<PAT_FIELDS; fi++){
        const char *p = e->f[fi];
        while(*p==' '||*p=='\t') p++;
        if(*p){ axx_strupr_to(arg, p, sizeof(arg)); break; }
    }
    { size_t n = strlen(arg);
      while(n > 0 && (arg[n-1]==' '||arg[n-1]=='\t')) arg[--n] = '\0'; }
    if(arg[0]=='\0' || strcmp(arg,"ON")==0){
        asmb->st.textmode = 1;
        asmb->st.passthru = 1;
        asmb->st.eol      = 1;
    } else if(strcmp(arg,"OFF")==0){
        asmb->st.textmode = 0;
        asmb->st.passthru = 0;
        asmb->st.eol      = 0;
    } else
        axx_diagf(1, 0, " error - .textmode: expected 'on' or 'off' ('%s').\n", arg);
    return 1;
}

/* `.enum` — 要素のリストを取る位置を宣言する。 */
static int dir_enum(Assembler *asmb, PatEntry *e){
    if(!e || strcmp(e->f[0], ".enum") != 0) return 0;
    const char *var_str   = e->f[1];
    const char *names_str = e->f[2];
    const char *expr_str  = e->f[3];
    int idx = dir_var_slot(var_str);
    if(idx < 0){
        axx_diagf(1, 0, " error - .enum: variable should be a lower case name ('%s').\n",
                   var_str);
        return 1;
    }

    StrVec elems; sv_init(&elems);
    elem_list_expand(&asmb->st, names_str, &elems);
    StrVec names; sv_init(&names);
    for(int ei = 0; ei < elems.len; ei++){
        const char *nm = elems.data[ei];
        if(!nm[0]) continue;
        int dup = 0;
        for(int k = 0; k < names.len; k++)
            if(strcmp(names.data[k], nm) == 0){ dup = 1; break; }
        if(!dup) sv_push(&names, nm);
    }
    sv_free(&elems);
    if(names.len == 0){
        axx_diagf(1, 0, " error - .enum: no enumeration element is given.\n");
        sv_free(&names);
        return 1;
    }
    int expr_blank = 1;
    for(const char *q = expr_str; *q; q++)
        if(*q != ' ' && *q != '\t'){ expr_blank = 0; break; }
    if(expr_blank){
        axx_diagf(1, 0, " error - .enum: the value expression is missing.\n");
        sv_free(&names);
        return 1;
    }

    enumdef_clear(&asmb->st.enum_defs[idx]);
    asmb->st.enum_defs[idx].names = names;
    asmb->st.enum_defs[idx].expr  = strdup(expr_str);
    if(!asmb->st.enum_defs[idx].expr){ perror("strdup"); exit(1); }
    return 1;
}

/* `.clrenum` — `.enum` の宣言を外す。 */
static int dir_clrenum(Assembler *asmb, PatEntry *e){
    if(!e || strcmp(e->f[0], ".clrenum") != 0) return 0;
    const char *var_str = e->f[2];
    if(var_str[0]){
        int idx = dir_var_slot(var_str);
        if(idx < 0){
            axx_diagf(1, 0, " error - .clrenum: variable should be a lower case name ('%s').\n",
                       var_str);
            return 1;
        }
        enumdef_clear(&asmb->st.enum_defs[idx]);
    } else {
        for(int i = 0; i < g_nvars; i++) enumdef_clear(&asmb->st.enum_defs[i]);
    }
    return 1;
}

/* `.error` — エラーコードの文言を足す・上書きする。実装のソースを触らずに
   自分の文言を持てる。 */
static int dir_errmsg(Assembler *asmb, PatEntry *e){
    if(!e || strcmp(e->f[0], ".error") != 0) return 0;

    const char *n_field   = e->f[1];
    const char *msg_field = e->f[2];

    int n_blank = 1;
    for(const char *q = n_field; *q; q++)
        if(*q != ' ' && *q != '\t'){ n_blank = 0; break; }
    if(n_blank){
        axx_diagf(1, 0, " error - .error directive requires an error code (number).\n");
        return 1;
    }

    AsmState *st = &asmb->st;
    st->error_undefined_label = 0;
    int io;
    uint256_t n = expr_expression_pat(asmb, n_field, 0, &io);
    int64_t n_int = u256_to_i64(n);
    #define AXX_ERROR_CODE_MAX 1000000
    if(st->error_undefined_label || u256_is_undef_derived(n)
       || n_int < 0 || n_int > AXX_ERROR_CODE_MAX || !u256_eq(n, u256_from_i64(n_int))){
        { size_t _nsz = strlen(n_field)*4+8; char *_nr = malloc(_nsz);
          if(!_nr){ perror("malloc"); exit(1); }
          m_pyrepr(n_field, _nr, _nsz);
          axx_diagf(1, 0, " error - .error: error code must be a non-negative integer (0-%d), got %s.\n",
                    AXX_ERROR_CODE_MAX, _nr);
          free(_nr); }
        st->error_undefined_label = 0;
        return 1;
    }
    st->error_undefined_label = 0;

    int idx0 = axx_skipspc(msg_field, 0);
    if(msg_field[idx0] != '"'){
        { size_t _msz = strlen(msg_field)*4+8; char *_mr = malloc(_msz);
          if(!_mr){ perror("malloc"); exit(1); }
          m_pyrepr(msg_field, _mr, _msz);
          axx_diagf(1, 0, " error - .error: message must be a double-quoted string, got %s.\n", _mr);
          free(_mr); }
        return 1;
    }

    size_t mlen = strlen(msg_field);
    char stackbuf[512];
    char *msg = (mlen < sizeof(stackbuf)) ? stackbuf : malloc(mlen + 1);
    if(!msg){ perror("malloc"); exit(1); }
    axx_get_string(msg_field, msg, mlen + 1);

    sv_set(&st->errors, (int)n_int, msg);

    if(msg != stackbuf) free(msg);
    return 1;
}

/* `.echo` — 本文行から標準エラーへ印字する。ワードは出さない。 */
static int dir_echo(Assembler *asmb, PatEntry *e){
    if(!e || strcmp(e->f[0], ".echo") != 0) return 0;
    AsmState *st = &asmb->st;
    if(!should_report_errors(st) || st->pass1_size_mode) return 1;
    EchoItem *items = (EchoItem*)e->echo_items;
    int n = e->echo_nitems;
    if(n <= 0){ m_echo_write(NULL, 0); return 1; }
    char **parts = malloc((size_t)n * sizeof(char*));
    if(!parts){ perror("malloc"); exit(1); }
    for(int k = 0; k < n; k++){
        if(items[k].is_str){ parts[k] = items[k].text; continue; }
        int io = 0;
        uint256_t v = expr_expression_pat(asmb, items[k].text, 0, &io);
        char cb[96];
        /* 未定義は番兵の数字ではなく UNDEF と出す（axx.py と同じ）。 */
        if(u256_is_undef(v)) snprintf(cb, sizeof(cb), "UNDEF");
        else u256_to_pydec(v, cb, sizeof(cb));
        parts[k] = strdup(cb);
        if(!parts[k]){ perror("strdup"); exit(1); }
    }
    m_echo_write(parts, n);
    for(int k = 0; k < n; k++) if(!items[k].is_str) free(parts[k]);
    free(parts);
    return 1;
}

/* そのエラー条件が、リンカが埋める変数を見ているか。`-o` では命令欄の値を
   まだ 0 にしてあるので、その変数への範囲検査は意味を持たない。真になった
   条件は報告しない。そうしないとリンク後には正しいコードが落ちてしまう。 */
static int cond_tests_relocated_var(AsmState *st, const char *cond, size_t len){
    if(!st->elf_objfile[0]) return 0;
    for(int vi = 0; vi < g_nvars; vi++){
        int rtype = st->reloc_constraints[vi];
        if(rtype == 0 || insn_reloc_field_mask(st, rtype) == 0) continue;
        const char *nm = g_varnames[vi];
        if(!nm || !*nm) continue;
        size_t nl = strlen(nm);
        if(nl > len) continue;
        for(size_t b = 0; b + nl <= len; b++){
            if(memcmp(cond + b, nm, nl) != 0) continue;
            if(b > 0){
                char c = cond[b - 1];
                if(isalnum((unsigned char)c) || c == '_') continue;
            }
            if(b + nl < len){
                char c = cond[b + nl];
                if(isalnum((unsigned char)c) || c == '_') continue;
            }
            return 1;
        }
    }
    return 0;
}

/* error_patterns 欄を評価する。`条件;コード` をカンマで並べたものを順に見る。
   評価は浮動小数点モードで行う。 */
static int dir_error(Assembler *asmb, const char *s){
    AsmState *st=&asmb->st;
    int has_content=0;
    for(const char*p=s;*p;p++) if(*p!=' '){has_content=1;break;}
    if(!has_content) return 0;

    char stackbuf[4096];
    size_t l=strlen(s);
    char *buf = (l < sizeof(stackbuf)) ? stackbuf : malloc(l+1);
    if(!buf){ perror("malloc"); exit(1); }
    memcpy(buf,s,l); buf[l]='\0';

    int idx=0;
    int triggered=0;
    while(1){
        if(!buf[idx]) break;
        if(buf[idx]==','){idx++;continue;}
        int idx_before = idx;
        int io;
        int prev_flt = st->exp_typ_float;
        st->exp_typ_float = 1;
        /* 条件が未定義のラベル・変数に触れたら、その条件では判定しない。未定義は
           すでに報告済みで、番兵の値で範囲を判定しても意味がない。
           axx.py の DirectiveProcessor.error() と同じ規則である。 */
        int undef_prior = st->error_undefined_label;
        st->error_undefined_label = 0;
        uint256_t u=expr_expression_pat(asmb,buf,idx,&io);
        int cond_undef = st->error_undefined_label || u256_is_undef(u);
        int cond_false = expr_is_false(asmb, u);
        idx=io;
        int io_cond = io;
        if(buf[idx]==';') idx++;
        uint256_t t=expr_expression_pat(asmb,buf,idx,&io);
        st->exp_typ_float = prev_flt;
        st->error_undefined_label = undef_prior || st->error_undefined_label;
        idx=io;
        if(idx <= idx_before) break;
        if((should_report_errors(st))&&!cond_false&&!cond_undef
           && !cond_tests_relocated_var(st, buf + idx_before,
                                        (size_t)(io_cond - idx_before))){
            double _tdv = u256_to_double(t);
            int64_t tc = (isfinite(_tdv) && _tdv > -9223372036854775808.0
                          && _tdv < 9223372036854775808.0) ? (int64_t)_tdv : 0;
            fprintf(stderr,"Line %d Error code %lld ",(int)st->ln,(long long)tc);
            if(tc>=0&&tc<st->errors.len) fprintf(stderr,"%s",st->errors.data[tc]);
            fprintf(stderr,": \n");
            triggered=1;
            st->had_error=1;
        }
    }
    if(buf!=stackbuf) free(buf);
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


/* 指定した番号の省略可能部分を、中身ごと取り除いた文字列を作る。 */
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


/* その位置でパターンが式捕捉を待っているか。 */
static int pat_expects_expr(const char *t, int idx){
    while(t[idx]==' '||t[idx]=='\t'||t[idx]==SUB_OPEN_CHAR||t[idx]==SUB_CLOSE_CHAR)
        idx += (t[idx]==' '||t[idx]=='\t') ? 1 : 2;
    return t[idx]=='!';
}
static uint256_t enum_eval(Assembler *asmb, const EnumDef *ed,
                           const unsigned char *present, int *ok_out){
    AsmState *st=&asmb->st;
    int n = ed->names.len;
    uint256_t *vals = malloc((size_t)(n>0?n:1) * sizeof(uint256_t));
    if(!vals){ perror("malloc"); exit(1); }
    for(int k=0;k<n;k++){
        if(!present[k]){ vals[k]=u256_zero(); continue; }
        uint256_t sv;
        if(!smap_get(&st->symbols, ed->names.data[k], &sv)){
            free(vals);
            *ok_out = 0;
            return u256_zero();
        }
        vals[k]=sv;
    }
    const StrVec    *prev_names = st->enum_bind_names;
    const uint256_t *prev_vals  = st->enum_bind_vals;
    int prev_expmode = st->expmode;
    const ExprCaps *prev_expcaps = st->expcaps;
    st->enum_bind_names = &ed->names;
    st->enum_bind_vals  = vals;
    int io=0;
    uint256_t r = expr_expression_pat(asmb, ed->expr, 0, &io);
    st->expmode = prev_expmode;
    st->expcaps = prev_expcaps;
    st->enum_bind_names = prev_names;
    st->enum_bind_vals  = prev_vals;
    free(vals);
    *ok_out = 1;
    return r;
}

/* 捕捉した変数が覚えるソースの綴りを置き場に積み、その位置を返す。 */
static int captext_put(AsmState *st, const char *p, int n){
    if(n < 0) n = 0;
    if(st->captext_len + n + 1 > (int)sizeof(st->captext)) return -1;
    int off = st->captext_len;
    memcpy(st->captext + off, p, (size_t)n);
    st->captext[off + n] = '\0';
    st->captext_len = off + n + 1;
    return off;
}

/* 捕捉した範囲 s[b..e) の綴りを変数に覚えさせる。止め文字と前後の空白は
   落とす。`{{.exp(変数)}}` がこれを出す。
   axx.py の PatternMatcher._cap_text() と同じ規則である。 */
static void cap_text_set(AsmState *st, int slot, const char *s, int b, int e, char stopchar){
    if(slot < 0 || slot >= NVARS) return;
    if(e < b) e = b;
    if(stopchar && e > b && s[e-1] == stopchar) e--;
    while(b < e && (s[b]==' '||s[b]=='\t')) b++;
    while(e > b && (s[e-1]==' '||s[e-1]=='\t')) e--;
    var_note_write(st, slot);
    st->vars[slot].text_off = captext_put(st, s + b, e - b);
}

/* 変数の綴りを空にする。 */
static void cap_text_clear(AsmState *st, int slot){
    if(slot < 0 || slot >= NVARS) return;
    var_note_write(st, slot);
    st->vars[slot].text_off = -1;
}

enum { SUB_MAX_DEPTH = 8 };

/* `!S{{表}}` の開き印・閉じ印に当たったソース上の位置。段ごとに持つ。 */
static int g_sub_span[SUB_MAX_DEPTH][2];

/* 開き印・閉じ印に当たった位置を覚える。
   axx.py の PatternMatcher._sub_mark() と同じ規則である。 */
static void sub_span_mark(char m, char k, int idx_s){
    int i = (unsigned char)k - '0';
    if(i < 0 || i >= SUB_MAX_DEPTH) return;
    if(m == SUB_OPEN_CHAR || g_sub_span[i][0] < 0) g_sub_span[i][0] = idx_s;
    g_sub_span[i][1] = idx_s;
}

/* 変数名の後ろの `\c` 止め文字を読み、次の位置を返す。`!S{{表}}` の閉じ印
   が変数名と `\c` のあいだに入っても止め文字として読み、その閉じ印の段を
   closes に返す（式を読み終えた位置で閉じる）。止め文字が無ければ閉じ印は
   そのまま残し、照合の本体が読む。
   axx.py の PatternMatcher._var_stopchar() と同じ規則である。 */
static int pat_var_stopchar(const char *t, int tlen, int idx_t, char *stop,
                            char *closes, int *nclose){
    int j = axx_skipspc(t, idx_t);
    int nc = 0;
    while(j + 1 < tlen && t[j] == SUB_CLOSE_CHAR){
        if(nc < SUB_MAX_DEPTH) closes[nc++] = t[j+1];
        j = axx_skipspc(t, j + 2);
    }
    if(j < tlen && t[j] == '\\'){
        j++;
        *stop = (j < tlen) ? t[j] : '\0';
        *nclose = nc;
        return j + 1;
    }
    *stop = '\0';
    *nclose = 0;
    return axx_skipspc(t, idx_t);
}

/* 止め文字の前で閉じる閉じ印を、式を読み終えた位置で閉じる。 */
static void sub_span_close_all(const char *closes, int nclose, int idx_s){
    for(int i = 0; i < nclose; i++) sub_span_mark(SUB_CLOSE_CHAR, closes[i], idx_s);
}

static int enum_capture(Assembler *asmb, const EnumDef *ed, const char *s, int idx,
                        uint256_t *val_out, int *idx_out){
    const StrVec *names = &ed->names;
    int n = names->len;
    unsigned char *present = calloc((size_t)(n>0?n:1), 1);
    if(!present){ perror("calloc"); exit(1); }

    int e1=0;
    int k1 = enum_name_at(s, axx_skipspc(s, idx), names, &e1);
    if(k1 < 0){ free(present); return 0; }
    int pos = e1;
    for(;;){
        pos = e1;
        int pr = axx_skipspc(s, e1);
        if(s[pr] == '-'){
            int e2=0;
            int k2 = enum_name_at(s, axx_skipspc(s, pr+1), names, &e2);
            if(k2 >= k1){
                for(int k=k1;k<=k2;k++) present[k]=1;
                pos = e2;
            } else {
                present[k1]=1;
            }
        } else {
            present[k1]=1;
        }
        int ps = axx_skipspc(s, pos);
        if(s[ps]==',' || s[ps]=='/'){
            int e3=0;
            int k3 = enum_name_at(s, axx_skipspc(s, ps+1), names, &e3);
            if(k3 >= 0){ k1=k3; e1=e3; continue; }
        }
        break;
    }
    int ok=0;
    uint256_t v = enum_eval(asmb, ed, present, &ok);
    free(present);
    if(!ok) return 0;
    *val_out = v;
    *idx_out = pos;
    return 1;
}

/* その位置にある集合の項目名を最長一致で読む（`!Y` の照合）。数値の項目は
   名前を持たないので候補外。 */
static int symset_item_at(const char *s, int idx, const struct ArrSym *ar, int *end_out){
    int best=-1, best_end=idx;
    for(int k=0;k<ar->len;k++){
        if(!ar->items[k].is_str || !ar->items[k].s) continue;
        const char *nm = ar->items[k].s;
        int n = (int)strlen(nm);
        if(n <= best_end-idx) continue;
        int ok=1;
        for(int j=0;j<n;j++){
            char c=s[idx+j];
            if(c=='\0' || axx_upper_char(c)!=axx_upper_char(nm[j])){ ok=0; break; }
        }
        if(!ok) continue;
        char nx=s[idx+n];
        if((nx>='0'&&nx<='9')||(nx>='A'&&nx<='Z')||(nx>='a'&&nx<='z')||nx=='_') continue;
        best=k; best_end=idx+n;
    }
    *end_out=best_end;
    return best;
}

/* ソース行とパターンを 1 文字ずつ突き合わせる本体。
   トークナイザは無い。大文字・数字・記号は文字定数、小文字の名前はシンボル、
   `!x` は式、`!!x` は因子、`!F/!D/!Q` は浮動小数点、`!L` は式とその綴り、
   `!E` は列挙リスト、`!Y集合[変数]` は集合の項目番号。当たるたびに値を変数へ
   束縛し、同時に特異度スコア (n_expr, -n_lit, n_sym) を数える。 */
static int pat_match(Assembler *asmb, const char *s_orig, const char *t_orig){
    AsmState *st=&asmb->st;
    axx_copy_trunc(st->deb1, sizeof(st->deb1), s_orig);
    axx_copy_trunc(st->deb2, sizeof(st->deb2), t_orig);

    static ScratchBuf sb_s, sb_t;
    size_t s_len = strlen(s_orig), t_len = strlen(t_orig);
    char *s = sbuf_take(&sb_s, s_len + 2);
    memcpy(s, s_orig, s_len); s[s_len] = 0; s[s_len+1] = 0;
    char *t = sbuf_take(&sb_t, t_len + 2);
    { int n2=0;
      for(size_t i=0;i<t_len;i++)
          if(t_orig[i]!=OB_CHAR && t_orig[i]!=CB_CHAR) t[n2++]=t_orig[i];
      t[n2]=0; t[n2+1]=0; }

    int idx_s=0,idx_t=0;
    idx_s=axx_skipspc(s,idx_s);
    idx_t=axx_skipspc(t,idx_t);
    int tlen=(int)strlen(t);
    int result=0;

    int n_expr=0, n_sym=0, n_lit=0;

    int prev_alnum=0;

    /* 当たらなかったときは、この試行で積んだ綴りを置き場から下ろす。 */
    int captext_len0 = st->captext_len;
    for(int k=0;k<SUB_MAX_DEPTH;k++){ g_sub_span[k][0] = -1; g_sub_span[k][1] = -1; }
    char closes[SUB_MAX_DEPTH]; int nclose = 0;

    while(1){
        int s_sp = (s[idx_s]==' '||s[idx_s]=='\t');
        int t_sp = (t[idx_t]==' '||t[idx_t]=='\t');
        idx_s=axx_skipspc(s,idx_s);
        idx_t=axx_skipspc(t,idx_t);
        while(t[idx_t]==SUB_OPEN_CHAR || t[idx_t]==SUB_CLOSE_CHAR){
            sub_span_mark(t[idx_t], t[idx_t+1], idx_s);
            idx_t += 2;
            if(t[idx_t]==' '||t[idx_t]=='\t') t_sp = 1;
            idx_t=axx_skipspc(t,idx_t);
        }
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
            if(idx_t >= tlen){ result=0; break; }
            a=t[idx_t]; idx_t++;
            if(a=='\0'){ result=0; break; }
            if(a=='F' || a=='D' || a=='Q'){
                char ftype = a;
                if(idx_t >= tlen){ result=0; break; }
                int _nl = var_name_len(t+idx_t);
                if(_nl == 0){ result=0; break; }
                int vslot = var_slot(t+idx_t, _nl, 1);
                if(vslot < 0){ result=0; break; }
                char stopchar = '\0';
                idx_t = pat_var_stopchar(t, tlen, idx_t + _nl, &stopchar, closes, &nclose);
                int idx_s_q_start = idx_s;
                uint256_t fv = expr_expression_esc_float(asmb, s, idx_s, stopchar, &idx_s);
                /* 未定義は 0（未定義はすでに報告済み）。axx.py と同じ。 */
                int fv_undef = u256_is_undef(fv);
                if(fv_undef) fv = double_to_u256(0.0);
                sub_span_close_all(closes, nclose, idx_s);
                cap_text_set(st, vslot, s, idx_s_q_start, idx_s, stopchar);
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
                    var_slot_put(st, vslot, u256_from_u64((uint64_t)bits));
                } else if(ftype == 'D'){
                    uint64_t bits; memcpy(&bits, &dv, 8);
                    var_slot_put(st, vslot, u256_from_u64(bits));
                } else {
                    int raw_len = idx_s - idx_s_q_start;
                    if(stopchar && raw_len > 0 &&
                       s[idx_s_q_start + raw_len - 1] == stopchar)
                        raw_len--;
                    uint256_t qbits;
                    if(fv_undef){
                        qbits = u256_zero();
                    } else
#if defined(__GNUC__) && !defined(__STRICT_ANSI__) && \
    (defined(__x86_64__) || defined(__i386__) || defined(__aarch64__) || \
     defined(__arm__) || defined(__riscv))
                    if(raw_len > 0){
                        /* 綴りの長さに上限を置かない（以前は 1024 文字以上を倍精度へ
                           落としていた。axx.py の !Q 捕捉と同じ規則である）。 */
                        char *expr_text = malloc((size_t)raw_len + 1);
                        if(!expr_text){ perror("malloc"); exit(1); }
                        memcpy(expr_text, s + idx_s_q_start, (size_t)raw_len);
                        expr_text[raw_len] = '\0';
                        const char *f128_text = expr_text;
                        if(raw_len > 4 &&
                           strncmp(expr_text, "qad{", 4) == 0 &&
                           expr_text[raw_len-1] == '}'){
                            expr_text[raw_len-1] = '\0';
                            f128_text = expr_text + 4;
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
                        free(expr_text);
                    } else
#endif
                    {
                        char fstr[64];
                        snprintf(fstr, sizeof(fstr), "%.17g", dv);
                        qbits = ieee754_128_from_str(fstr);
                    }
                    var_slot_put(st, vslot, qbits);
                }
                continue;
            } else if(a=='L'){
                if(idx_t >= tlen){ result=0; break; }
                int _nl = var_name_len(t+idx_t);
                if(_nl == 0){ result=0; break; }
                int vslot = var_slot(t+idx_t, _nl, 1);
                if(vslot < 0){ result=0; break; }
                char stopchar = '\0';
                idx_t = pat_var_stopchar(t, tlen, idx_t + _nl, &stopchar, closes, &nclose);
                int idx_s_text_start = idx_s;
                st->elf_capturing_var = vslot;
                int _cap_prior_l = st->error_undefined_label;
                st->error_undefined_label = 0;
                uint256_t v = expr_expression_esc(asmb,s,idx_s,stopchar,&idx_s);
                int _cap_undef_l = st->error_undefined_label;
                st->elf_capturing_var = -1;
                sub_span_close_all(closes, nclose, idx_s);
                elf_v2l_finish(st, vslot, s + idx_s_text_start, idx_s - idx_s_text_start);
                cap_text_set(st, vslot, s, idx_s_text_start, idx_s, stopchar);
                if(st->textmode){
                    st->error_undefined_label = _cap_prior_l;
                    if(_cap_undef_l || u256_is_undef_derived(v)) v = u256_zero();
                    var_slot_put_tagged(st,vslot,v,0);
                } else {
                    st->error_undefined_label = _cap_prior_l || _cap_undef_l;
                    var_slot_put_tagged(st,vslot,v,_cap_undef_l);
                }
                if(stopchar && s[idx_s]==stopchar) idx_s++;
                continue;
            } else if(a=='E'){
                if(idx_t >= tlen){ result=0; break; }
                int _nl = var_name_len(t+idx_t);
                if(_nl == 0){ result=0; break; }
                int vslot = var_slot(t+idx_t, _nl, 1);
                if(vslot < 0){ result=0; break; }
                idx_t += _nl;
                const EnumDef *ed = &st->enum_defs[vslot];
                if(!ed->expr){ result=0; break; }
                uint256_t ev; int eend=idx_s;
                if(!enum_capture(asmb, ed, s, idx_s, &ev, &eend)){ result=0; break; }
                int _cap_start_e = idx_s;
                idx_s = eend;
                var_slot_put(st, vslot, ev);
                cap_text_set(st, vslot, s, _cap_start_e, idx_s, '\0');
                continue;
            } else if(a=='Y'){
                if(idx_t >= tlen){ result=0; break; }
                int _sl = var_name_len(t+idx_t);
                if(_sl == 0){ result=0; break; }
                char _setkey[512];
                if(_sl >= (int)sizeof(_setkey)){ result=0; break; }
                for(int _i=0;_i<_sl;_i++)
                    _setkey[_i] = (char)axx_upper_char(t[idx_t+_i]);
                _setkey[_sl] = '\0';
                idx_t += _sl;
                if(idx_t >= tlen || t[idx_t] != '['){ result=0; break; }
                idx_t++;
                int _nl = var_name_len(t+idx_t);
                if(_nl == 0){ result=0; break; }
                int vslot = var_slot(t+idx_t, _nl, 1);
                if(vslot < 0){ result=0; break; }
                idx_t += _nl;
                if(idx_t >= tlen || t[idx_t] != ']'){ result=0; break; }
                idx_t++;
                struct ArrSym *_ys = arrsym_get(st, _setkey);
                if(!_ys || _ys->len <= 0){ result=0; break; }
                int _yend = idx_s;
                int _yk = symset_item_at(s, idx_s, _ys, &_yend);
                if(_yk < 0){ result=0; break; }
                cap_text_set(st, vslot, s, idx_s, _yend, '\0');
                idx_s = _yend;
                var_slot_put(st, vslot, u256_from_u64((uint64_t)_yk));
                n_expr--; n_sym++;
                continue;
            } else if(a=='!'){
                if(idx_t >= tlen){ result=0; break; }
                int _nl = var_name_len(t+idx_t);
                if(_nl == 0){ result=0; break; }
                int vslot = var_slot(t+idx_t, _nl, 1);
                if(vslot < 0){ result=0; break; }
                idx_t += _nl;
                st->elf_capturing_var = vslot;
                int _cap_prior_eul = st->error_undefined_label;
                st->error_undefined_label = 0;
                int _cap_start = idx_s;
                uint256_t v=expr_factor(asmb,s,idx_s,&idx_s);
                int _cap_this_undef = st->error_undefined_label;
                st->error_undefined_label = _cap_prior_eul || _cap_this_undef;
                st->elf_capturing_var = -1;
                elf_v2l_finish(st, vslot, s + _cap_start, idx_s - _cap_start);
                cap_text_set(st, vslot, s, _cap_start, idx_s, '\0');
                var_slot_put_tagged(st,vslot,v,_cap_this_undef);
                continue;
            } else {
                int _nl = var_name_len(t+idx_t-1);
                if(_nl == 0){ result=0; break; }
                int vslot = var_slot(t+idx_t-1, _nl, 1);
                if(vslot < 0){ result=0; break; }
                char stopchar='\0';
                idx_t = pat_var_stopchar(t, tlen, idx_t - 1 + _nl, &stopchar, closes, &nclose);
                st->elf_capturing_var = vslot;
                int _cap_prior_eul2 = st->error_undefined_label;
                st->error_undefined_label = 0;
                int _cap_start2 = idx_s;
                uint256_t v=expr_expression_esc(asmb,s,idx_s,stopchar,&idx_s);
                int _cap_this_undef2 = st->error_undefined_label;
                st->error_undefined_label = _cap_prior_eul2 || _cap_this_undef2;
                st->elf_capturing_var = -1;
                sub_span_close_all(closes, nclose, idx_s);
                elf_v2l_finish(st, vslot, s + _cap_start2, idx_s - _cap_start2);
                cap_text_set(st, vslot, s, _cap_start2, idx_s, stopchar);
                var_slot_put_tagged(st,vslot,v,_cap_this_undef2);
                if(stopchar && s[idx_s]==stopchar) idx_s++;
                continue;
            }
        } else if(a>='a'&&a<='z'){
            prev_alnum=0;
            int _nl = var_name_len(t+idx_t);
            int vi = var_slot(t+idx_t, _nl, 1);
            if(vi < 0){ result=0; break; }
            idx_t += _nl;
            int prev_idx_s = idx_s;
            ChkList *cv = st->check_constraints[vi];
            int cv_len = chk_len(cv);
            int allow_omit = 0, n_named = 0;
            for(int si = 0; si < cv_len; si++){
                if(chk_at(cv, si)[0] == '\0') allow_omit = 1;
                else                           n_named++;
            }

            char wbuf[512]; size_t wsz;
            char *w = axx_word_buf(s, idx_s, wbuf, sizeof(wbuf), &wsz);
            idx_s=axx_get_symbol_word(s,idx_s,st->swordchars,w,wsz);
            uint256_t sv = u256_zero();
            int ok = 1;
            if(!cap_sym_get(st,vi,w,&sv)){
                int _wl = (int)strlen(w), _hit = 0;
                for(int _cut = _wl - 1; _cut > 0; _cut--){
                    unsigned char _ch = (unsigned char)w[_cut];
                    if(isalnum(_ch) || _ch=='_') continue;
                    char _save = w[_cut];
                    w[_cut] = '\0';
                    if(cap_sym_get(st,vi,w,&sv)){ idx_s = prev_idx_s + _cut; _hit = 1; break; }
                    w[_cut] = _save;
                }
                if(!_hit) ok = 0;
            }
            if(ok && idx_s == prev_idx_s) ok = 0;

            if(ok && cv_len > 0){
                int hit = 0;
                for(int si = 0; si < cv_len; si++){
                    if(chk_at(cv, si)[0] != '\0' && strcmp(chk_at(cv, si), w) == 0){
                        hit = 1;
                        break;
                    }
                }
                if(!hit) ok = 0;
            }

            if(!ok && n_named > 0){
                int best_len = 0, best_si = -1;
                for(int si = 0; si < cv_len; si++){
                    const char *nm = chk_at(cv, si);
                    int nl = (int)strlen(nm);
                    if(nl <= best_len) continue;
                    int k = 0;
                    while(k < nl && s[prev_idx_s + k]
                          && axx_upper_char(s[prev_idx_s + k]) == nm[k]) k++;
                    if(k == nl){ best_len = nl; best_si = si; }
                }
                if(best_si >= 0 && strlen(chk_at(cv, best_si)) < wsz
                   && cap_sym_get(st, vi, chk_at(cv, best_si), &sv)){
                    snprintf(w, wsz, "%s", chk_at(cv, best_si));
                    idx_s = prev_idx_s + best_len;
                    ok = 1;
                }
            }

            if(w!=wbuf) free(w);

            if(!ok){
                if(!allow_omit){ result=0; break; }
                idx_s = prev_idx_s;
                var_slot_put(st, vi, u256_zero());
                cap_text_clear(st, vi);
                n_sym++;
                continue;
            }

            var_slot_put(st,vi,sv);
            cap_text_set(st, vi, s, prev_idx_s, idx_s, '\0');
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
    if(!result) st->captext_len = captext_len0;
    sbuf_give(&sb_s, s); sbuf_give(&sb_t, t);
    return result;
}

/* 省略可能部分の組み合わせを変えて試す。取り除く数を 0 個から増やすので、
   省略可能部分は「できるだけ残す」方向から試される。群の数と組み合わせの
   総数に上限があり、超えたパターンは不一致として扱って一度だけ警告する。
   試行ごとに変数の束縛とラベル参照の記録を巻き戻す。 */
static int pat_match0_brackets(Assembler *asmb, const char *s, const char *t_orig){
    {
        int has_grp = 0;
        for(const char *q=t_orig; q[0]; q++)
            if((q[0]=='[' && q[1]=='[') || (q[0]==']' && q[1]==']')){ has_grp = 1; break; }
        if(!has_grp) return pat_match(asmb, s, t_orig);
    }

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
    int comb[MAX_OPT_GROUPS + 1];
    for(int size=0; size<=cnt && !found; size++){
      for(int k=0;k<size;k++) comb[k]=k;
      while(!found){
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
                    asmb->st.combo_budget_warned_file[_wi] = strdup(asmb->st.current_file);
                    if(!asmb->st.combo_budget_warned_file[_wi]){ perror("strdup"); exit(1); }
                    asmb->st.combo_budget_warned_line[_wi] = asmb->st.ln;
                }
                axx_diagf(0, 0, " warning - a pattern with %d optional group(s) exceeded the "
                           "%llu-combination match budget and was treated as non-matching; "
                           "consider splitting it into multiple explicit pattern entries.\n",
                           cnt, (unsigned long long)MAX_COMBINATIONS);
            }
            goto combo_done;
        }
        int ri[MAX_OPT_GROUPS + 1]; int nr=0;
        for(int k=0;k<size;k++) ri[nr++]=sl[comb[k]];
        char *lt=remove_brackets_str(t,ri,nr);

        int mark_v   = vars_mark();
        int mark_v2l = v2l_mark();
        int saved_elf_refs_len = asmb->st.elf_refs_len;

        if(pat_match(asmb,s,lt)){
            found=1;
        } else {
            vars_rollback(&asmb->st, mark_v);
            for(int ri2=saved_elf_refs_len; ri2<asmb->st.elf_refs_len; ri2++)
                free(asmb->st.elf_refs[ri2].name);
            asmb->st.elf_refs_len = saved_elf_refs_len;
            v2l_rollback(&asmb->st, mark_v2l);
        }
        free(lt);

        int k = size - 1;
        while(k >= 0 && comb[k] == cnt - size + k) k--;
        if(k < 0) break;
        comb[k]++;
        for(int j = k + 1; j < size; j++) comb[j] = comb[j-1] + 1;
      }
    }
combo_done:
    free(sl); free(t);
    return found;
}

/* パターン中の最初のサブ表参照を探す。逃がされたものは飛ばす。 */
static int pat_find_sub_ref(const char *t, int start, int *end, char *name, size_t nsz, int *var){
    for(int i=start; t[i]; i++){
        if(!(t[i]=='!' && t[i+1]=='S' && t[i+2]=='{' && t[i+3]=='{')) continue;
        if(i>0 && t[i-1]=='\\') continue;
        const char *cb = strstr(t+i+4, "}}");
        if(!cb) return -1;
        size_t n = (size_t)(cb - (t+i+4));
        if(n >= nsz) continue;
        memcpy(name, t+i+4, n); name[n]='\0';
        int vl = var_name_len(cb+2);
        if(is_sub_name(name) && vl > 0){
            int vs = var_slot(cb+2, vl, 1);
            if(vs < 0) continue;
            *var = vs;
            *end = (int)(cb + 2 + vl - t);
            return i;
        }
    }
    return -1;
}

/* サブ表エントリの値リストを 1 つの値にまとめる。2 要素以上なら最初が
   最上位になるよう `.bits` 幅ずつ詰める。 */
static uint256_t pat_sub_value(Assembler *asmb, const char *expr){
    AsmState *st=&asmb->st;
    int bts = st->bts > 0 ? st->bts : 8;
    uint256_t mask = u256_sub(u256_shl(u256_one(), bts), u256_one());
    uint256_t acc = u256_zero();
    uint256_t first = u256_zero();
    int count = 0;
    int idx = 0, slen = (int)strlen(expr);
    while(idx < slen){
        if(expr[idx]==','){ idx++; continue; }
        int io;
        uint256_t v = expr_expression_pat(asmb, expr, idx, &io);
        if(io <= idx) break;
        idx = io;
        if(count==0) first = v;
        acc = u256_or(u256_shl(acc, bts), u256_and(v, mask));
        count++;
        if(idx < slen && expr[idx]==','){ idx++; continue; }
        break;
    }
    if(count==0) return u256_zero();
    if(count==1) return first;
    return acc;
}

typedef struct { int var; const char *val; } SubBind;

static int pat_match0_subs(Assembler *asmb, const char *s, const char *t,
                           SubBind *binds, int nbinds, int depth){
    /* 表の名前は t の一部なので、t と同じ長さがあれば必ず入る。 */
    size_t name_sz = strlen(t) + 1;
    char *name = malloc(name_sz);
    if(!name){ perror("malloc"); exit(1); }
    int var; int end;
    int start = pat_find_sub_ref(t, 0, &end, name, name_sz, &var);
    if(start < 0){
        free(name);
        int mark_v   = vars_mark();
        int mark_v2l = v2l_mark();
        int saved_elf_refs_len = asmb->st.elf_refs_len;
        if(pat_match0_brackets(asmb, s, t)){
            int spans[SUB_MAX_DEPTH][2];
            memcpy(spans, g_sub_span, sizeof(spans));
            for(int k=nbinds-1;k>=0;k--)
                var_slot_put(&asmb->st, binds[k].var, pat_sub_value(asmb, binds[k].val));
            for(int k=0;k<nbinds;k++){
                if(spans[k][0] < 0) cap_text_clear(&asmb->st, binds[k].var);
                else cap_text_set(&asmb->st, binds[k].var, s, spans[k][0], spans[k][1], '\0');
            }
            return 1;
        }
        vars_rollback(&asmb->st, mark_v);
        for(int ri=saved_elf_refs_len; ri<asmb->st.elf_refs_len; ri++)
            free(asmb->st.elf_refs[ri].name);
        asmb->st.elf_refs_len = saved_elf_refs_len;
        v2l_rollback(&asmb->st, mark_v2l);
        return 0;
    }

    if(depth >= SUB_MAX_DEPTH){
        axx_diagf(1, 0, " error - !S{{%s}}: sub table expansion exceeds maximum "
                   "depth %d.\n", name, SUB_MAX_DEPTH);
        free(name);
        return 0;
    }
    SubDef *d = subv_find(&asmb->st.subs, name);
    if(d && d->freed) d = NULL;
    if(!d){
        axx_diagf(1, 0, " error - !S{{%s}}: no sub table named '%s' (define it with "
                   "'.sub::%s ... .return').\n", name, name, name);
        free(name);
        return 0;
    }
    free(name);
    if(nbinds >= SUB_MAX_DEPTH) return 0;

    /* 差し込んだ範囲を印ではさむ。印の後ろの 1 文字が段で、束縛の並び
       での位置と同じになる（段ごとに 1 つずつ前に足すため）。 */
    int tlen = (int)strlen(t);
    char open_mark[3]  = { SUB_OPEN_CHAR,  (char)('0' + depth), '\0' };
    char close_mark[3] = { SUB_CLOSE_CHAR, (char)('0' + depth), '\0' };
    for(int k=0; k<d->n; k++){
        size_t nl = (size_t)start + strlen(d->e[k].pat) + (size_t)(tlen-end) + 5;
        char *nt = malloc(nl);
        if(!nt){ perror("malloc"); exit(1); }
        memcpy(nt, t, (size_t)start);
        nt[start] = '\0';
        strcat(nt + start, open_mark);
        strcat(nt + start, d->e[k].pat);
        strcat(nt + start, close_mark);
        strcat(nt + start, t + end);
        binds[nbinds].var = var;
        binds[nbinds].val = d->e[k].val;
        int ok = pat_match0_subs(asmb, s, nt, binds, nbinds+1, depth+1);
        free(nt);
        if(ok) return 1;
    }
    return 0;
}

/* サブ表参照を実際の選択肢に展開して順に試す。エントリのパターンがさらに
   別の表を参照していれば再帰する。連鎖は 8 段まで。失敗した試行のぶんは
   すべて巻き戻す。 */
static int pat_match0(Assembler *asmb, const char *s, const char *t_orig){
    SubBind binds[SUB_MAX_DEPTH];
    return pat_match0_subs(asmb, s, t_orig, binds, 0, 0);
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

/* パスのディレクトリ部分を取る。 */
static void axx_dir_of(const char *path, char *out, size_t osz)
{
    snprintf(out, osz, "%s", path ? path : "");
    char *d = dirname(out);
    if(d != out) memmove(out, d, strlen(d) + 1);
}

/* パスのディレクトリ部分を絶対パスで取る。 */
static void axx_abs_dir_of(const char *path, char *out, size_t osz)
{
    char abs_buf[2*PATH_MAX + 2];
    if(path && path[0] == '/'){
        axx_copy_trunc(abs_buf, sizeof(abs_buf), path);
    } else {
        char cwd_buf[PATH_MAX];
        if(getcwd(cwd_buf, sizeof(cwd_buf))){
            size_t cl = strlen(cwd_buf);
            axx_copy_trunc(abs_buf, sizeof(abs_buf), cwd_buf);
            if(cl + 1 < sizeof(abs_buf)){
                abs_buf[cl] = '/';
                axx_copy_trunc(abs_buf + cl + 1, sizeof(abs_buf) - cl - 1,
                               path ? path : "");
            }
        } else {
            axx_copy_trunc(abs_buf, sizeof(abs_buf), path ? path : "");
        }
    }
    char *d = dirname(abs_buf);
    axx_copy_trunc(out, osz, d ? d : ".");
}

static void readpat(Assembler *asmb, const char *fn);
static void include_pat(Assembler *asmb, const char *l, const char *base_dir);

static char **pat_macro_expand(FILE *f, const char *display, int *nlines, int **lines_out);
static void pat_macro_expand_free(char **v, int n);
static void macro_reset_pass_pattern(void);

/* `.INCLUDE` を処理する。相対パスはそのファイルのある場所から解決し、
   入れ子の深さと循環を検査する。 */
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
            axx_diagf(1, 0, " error - .INCLUDE directive has no filename: %s\n", l);
            return;
        }
    }
    char resolved[1024];
    axx_resolve_path(base_dir, raw, resolved, sizeof(resolved));
    readpat(asmb, resolved);
}

/* 未知のサブ表名を報告する。 */
static void sub_check_unknown(Assembler *asmb, const char *where, const char *t){
    size_t name_sz = strlen(t) + 1;
    char *name = malloc(name_sz);
    if(!name){ perror("malloc"); exit(1); }
    int var; int end, i = 0;
    while((i = pat_find_sub_ref(t, i, &end, name, name_sz, &var)) >= 0){
        if(!subv_find(&asmb->st.subs, name))
            axx_diagf(1, 0, " error - !S{{%s}} in %s: no sub table named '%s' "
                       "(define it with '.sub::%s ... .return').\n",
                       name, where, name, name);
        i = end;
    }
    free(name);
}

/* サブ表参照の循環をたどって見つける。 */
static void sub_walk_cycle(Assembler *asmb, int idx, char *mark, int *stack, int nstack){
    SubVec *sv = &asmb->st.subs;
    if(mark[idx] == 2) return;
    if(mark[idx] == 1){
        size_t psz = strlen(sv->data[idx].name) + 1;
        for(int k = 0; k < nstack; k++) psz += strlen(sv->data[stack[k]].name) + 4;
        char *path = malloc(psz);
        if(!path){ perror("malloc"); exit(1); }
        size_t n = 0;
        for(int k = 0; k < nstack; k++)
            n += (size_t)snprintf(path+n, psz-n, "%s -> ", sv->data[stack[k]].name);
        snprintf(path+n, psz-n, "%s", sv->data[idx].name);
        axx_diagf(1, 0, " error - sub table '%s' is circular (%s); expansion would "
                   "not terminate.\n", sv->data[idx].name, path);
        free(path);
        return;
    }
    mark[idx] = 1;
    SubDef *d = &sv->data[idx];
    for(int k = 0; k < d->n; k++){
        size_t name_sz = strlen(d->e[k].pat) + 1;
        char *name = malloc(name_sz);
        if(!name){ perror("malloc"); exit(1); }
        int var; int end, i = 0;
        while((i = pat_find_sub_ref(d->e[k].pat, i, &end, name, name_sz, &var)) >= 0){
            SubDef *tgt = subv_find(sv, name);
            if(tgt && nstack < sv->len){
                stack[nstack] = idx;
                sub_walk_cycle(asmb, (int)(tgt - sv->data), mark, stack, nstack+1);
            }
            i = end;
        }
        free(name);
    }
    mark[idx] = 2;
}

/* サブ表参照が解決できるかを読み込み時に一度だけ検査する。表は使用箇所より
   後に定義してよいので、ファイル全体を読んでから見る。ここで報告しておけば
   照合中に毎行同じ診断が出ることはない。 */
static void check_sub_refs(Assembler *asmb){
    SubVec *sv = &asmb->st.subs;
    for(int i = 0; i < asmb->st.pat.len; i++){
        const char *p0 = asmb->st.pat.data[i].f[0];
        if(p0 && p0[0]) sub_check_unknown(asmb, "pattern", p0);
    }
    for(int i = 0; i < sv->len; i++){
        char where[128];
        snprintf(where, sizeof(where), "sub table '%s'", sv->data[i].name);
        for(int k = 0; k < sv->data[i].n; k++)
            sub_check_unknown(asmb, where, sv->data[i].e[k].pat);
    }
    if(sv->len == 0) return;
    char *mark = calloc((size_t)sv->len, 1);
    int  *stack = malloc((size_t)(sv->len+1) * sizeof(int));
    if(!mark || !stack){ perror("calloc"); exit(1); }
    for(int i = 0; i < sv->len; i++) sub_walk_cycle(asmb, i, mark, stack, 0);
    free(mark); free(stack);
}


enum {
    MINI_MAX_STEPS = 4000000,
    MINI_MAX_DEPTH = 128,
    MINI_MAX_EMIT  = 1 << 20,
    MINI_MAX_ARRAY = 1 << 20,
    MINI_MAX_TOK   = 1024
};

typedef enum { MT_END, MT_NUM, MT_NAME, MT_DOT, MT_OP, MT_STR, MT_CORE } MTKind;
typedef struct { MTKind k; uint256_t num; char *s; } MTok;

typedef struct { MTok *tok; int tcap; char *text; size_t tsz; } MiniLexBuf;

typedef struct {
    jmp_buf     jb;
    int         jb_active;
    char       *err;
    const char *file;
    int         line;
    int         pdepth;   /* 式の構文解析の入れ子の深さ（mxp_enter） */
} MiniCtx;

/* ---- ミニ言語 (.func / .call) -------------------------------------------
   `binary_list` から `.call` で呼ばれる小さな手続き型言語。チューリング完全
   なので、文の数・呼び出しの入れ子・出力ワード数・配列長に上限を置いて、
   バグのあるパターンファイルがアセンブラを止められなくするのを防ぐ。
   整数は 256bit で回り込む。パターン変数はここでは使えないので、必要なら
   `.call` の引数として渡す。
   ------------------------------------------------------------------------ */
/* ミニ言語の実行時エラー。行と桁を添える。 */
static void mini_fail(MiniCtx *c, const char *fmt, ...){
    va_list ap;
    char bodybuf[400];
    char *body = bodybuf;
    va_start(ap, fmt);
    int bneed = vsnprintf(bodybuf, sizeof(bodybuf), fmt, ap);
    va_end(ap);
    if(bneed >= (int)sizeof(bodybuf)){
        char *bh = malloc((size_t)bneed + 1);
        if(bh){
            va_start(ap, fmt);
            vsnprintf(bh, (size_t)bneed + 1, fmt, ap);
            va_end(ap);
            body = bh;
        }
    }
    size_t msz = strlen(body) + (c->file ? strlen(c->file) : 1) + 32;
    char *msg = malloc(msz);
    if(!msg){ perror("malloc"); exit(1); }
    snprintf(msg, msz, "%s:%d: %s", c->file ? c->file : "?", c->line, body);
    if(body != bodybuf) free(body);
    free(c->err);
    c->err = msg;
    if(c->jb_active) longjmp(c->jb, 1);
    fprintf(stderr, " error - %s\n", c->err);
    exit(1);
}

/* ミニ言語用の確保。失敗したら止まる。 */
static void *mini_alloc(size_t n){
    void *p = calloc(1, n);
    if(!p){ perror("calloc"); exit(1); }
    return p;
}

/* 文字列を複製する。 */
static char *mini_strdup(const char *s){
    char *p = strdup(s ? s : "");
    if(!p){ perror("strdup"); exit(1); }
    return p;
}


static char *mini_echo_text(MiniVal *v);

/* 値を解放する（配列・文字列なら中身ごと）。 */
static void mini_val_free(MiniVal *v){
    if(v->arr) free(v->arr);
    if(v->astr){
        for(int i = 0; i < v->n; i++) free(v->astr[i]);
        free(v->astr);
        free(v->alen);
    }
    v->astr = NULL; v->alen = NULL;
    v->arr = NULL; v->n = v->cap = 0; v->is_arr = 0;
    if(v->str) free(v->str);
    v->str = NULL; v->slen = 0; v->is_str = 0;
}

/* 数値の値を作る。 */
static MiniVal mini_num(uint256_t x){
    MiniVal v; memset(&v, 0, sizeof(v));
    v.num = x;
    return v;
}

/* 文字列の値を作る。p の n バイトを複製して持つ。 */
static MiniVal mini_strval(const void *p, int n){
    MiniVal v; memset(&v, 0, sizeof(v));
    v.is_str = 1;
    v.str = mini_alloc((size_t)n + 1);
    if(n > 0) memcpy(v.str, p, (size_t)n);
    v.slen = n;
    return v;
}

/* 値を複製する。配列と文字列はコピーとして渡る。 */
static MiniVal mini_val_copy(const MiniVal *src){
    MiniVal v; memset(&v, 0, sizeof(v));
    if(src->is_str) return mini_strval(src->str, src->slen);
    v.is_arr = src->is_arr;
    v.num = src->num;
    if(src->is_arr && src->n > 0){
        v.arr = mini_alloc((size_t)src->n * sizeof(uint256_t));
        memcpy(v.arr, src->arr, (size_t)src->n * sizeof(uint256_t));
        v.n = v.cap = src->n;
        if(src->astr){
            v.astr = mini_alloc((size_t)src->n * sizeof(unsigned char*));
            v.alen = mini_alloc((size_t)src->n * sizeof(int));
            for(int i = 0; i < src->n; i++){
                if(!src->astr[i]) continue;
                v.astr[i] = mini_alloc((size_t)src->alen[i] + 1);
                if(src->alen[i] > 0) memcpy(v.astr[i], src->astr[i], (size_t)src->alen[i]);
                v.alen[i] = src->alen[i];
            }
        }
    }
    return v;
}

/* 配列を必要な長さまで伸ばす（上限あり）。 */
static void mini_arr_reserve(MiniVal *v, int want){
    if(want <= v->cap) return;
    int cap = v->cap ? v->cap : 8;
    while(cap < want) cap *= 2;
    uint256_t *na = realloc(v->arr, (size_t)cap * sizeof(uint256_t));
    if(!na){ perror("realloc"); exit(1); }
    v->arr = na;
    if(v->astr){
        unsigned char **ns = realloc(v->astr, (size_t)cap * sizeof(unsigned char*));
        int *nl = realloc(v->alen, (size_t)cap * sizeof(int));
        if(!ns || !nl){ perror("realloc"); exit(1); }
        for(int i = v->cap; i < cap; i++){ ns[i] = NULL; nl[i] = 0; }
        v->astr = ns; v->alen = nl;
    }
    v->cap = cap;
}

/* 配列の i 番目に値を置く。e は消費する（文字列ならその中身を引き取る）。
   i は確保済みの範囲であること。 */
static void mini_arr_put(MiniVal *v, int i, MiniVal e){
    if(e.is_str){
        if(!v->astr){
            int c = v->cap > 0 ? v->cap : 1;
            v->astr = mini_alloc((size_t)c * sizeof(unsigned char*));
            v->alen = mini_alloc((size_t)c * sizeof(int));
        }
        free(v->astr[i]);
        v->astr[i] = e.str;
        v->alen[i] = e.slen;
        v->arr[i] = u256_zero();
        return;
    }
    if(v->astr){ free(v->astr[i]); v->astr[i] = NULL; v->alen[i] = 0; }
    v->arr[i] = e.num;
    mini_val_free(&e);
}

/* 配列の i 番目の値を複製して返す。 */
static MiniVal mini_arr_get(const MiniVal *v, int i){
    if(v->astr && v->astr[i]) return mini_strval(v->astr[i], v->alen[i]);
    return mini_num(v->arr[i]);
}

/* `.echo` に出す形に整える。文字列の NUL は `\0` と書いて出す。配列は
   `[1, "ab", 3]` の形で、文字列の要素だけ `"` で囲む。
   axx.py の MiniInterp._echo_value() と同じ体裁である。 */
static char *mini_echo_text(MiniVal *v){
    if(v->is_str){
        char *b = mini_alloc((size_t)v->slen * 2 + 1);
        size_t len = 0;
        for(int i = 0; i < v->slen; i++){
            if(v->str[i] == 0){ b[len++] = '\\'; b[len++] = '0'; }
            else b[len++] = (char)v->str[i];
        }
        b[len] = 0;
        return b;
    }
    if(!v->is_arr){
        char cb[96]; u256_to_pydec(v->num, cb, sizeof(cb));
        return mini_strdup(cb);
    }
    size_t cap = (size_t)v->n * 98 + 4;
    if(v->astr)
        for(int i = 0; i < v->n; i++)
            if(v->astr[i]) cap += (size_t)v->alen[i] * 2 + 2;
    char *b = mini_alloc(cap);
    size_t len = 0;
    b[len++] = '[';
    for(int i = 0; i < v->n; i++){
        if(i){ b[len++] = ','; b[len++] = ' '; }
        if(v->astr && v->astr[i]){
            b[len++] = '"';
            for(int q = 0; q < v->alen[i]; q++){
                if(v->astr[i][q] == 0){ b[len++] = '\\'; b[len++] = '0'; }
                else b[len++] = (char)v->astr[i][q];
            }
            b[len++] = '"';
            continue;
        }
        char cb[96]; u256_to_pydec(v->arr[i], cb, sizeof(cb));
        size_t l = strlen(cb);
        memcpy(b + len, cb, l); len += l;
    }
    b[len++] = ']';
    b[len] = 0;
    return b;
}


/* 数字の並びをその基数で読む。 */
static uint256_t mini_digits(const char *s, int from, int to, int base){
    uint256_t acc = u256_zero();
    uint256_t b = u256_from_u64((uint64_t)base);
    for(int i = from; i < to; i++){
        if(s[i] == '_') continue;
        int d;
        char ch = s[i];
        if(ch >= '0' && ch <= '9') d = ch - '0';
        else if(ch >= 'a' && ch <= 'f') d = ch - 'a' + 10;
        else d = ch - 'A' + 10;
        acc = u256_add(u256_mul(acc, b), u256_from_u64((uint64_t)d));
    }
    return acc;
}

/* 字句解析のバッファを確保する。 */
static void minilex_ensure(MiniLexBuf *b, int len){
    int need_tok = len + 2;
    if(b->tcap < need_tok){
        b->tcap = need_tok;
        b->tok = realloc(b->tok, (size_t)b->tcap * sizeof(MTok));
        if(!b->tok){ perror("realloc"); exit(1); }
    }
    size_t need_txt = (size_t)len * 2 + 8;
    if(b->tsz < need_txt){
        b->tsz = need_txt;
        b->text = realloc(b->text, b->tsz);
        if(!b->text){ perror("realloc"); exit(1); }
    }
}

/* ミニ言語の 1 行をトークンに割る。位置も覚える。 */
static int mini_lex(MiniCtx *c, const char *t, MiniLexBuf *b){
    static const char *ops2[] = { "**","<<",">>","<=",">=","==","!=","&&","||", NULL };
    int n = 0, i = 0;
    int len = (int)strlen(t);
    minilex_ensure(b, len);
    MTok *out = b->tok;
    char *txt = b->text;
    size_t off = 0;
    #define MLX_BEGIN() (out[n].s = txt + off)
    #define MLX_PUT(ch_) (txt[off++] = (ch_))
    #define MLX_END()    (txt[off++] = '\0')
    while(i < len){
        char ch = t[i];
        if(ch == ' ' || ch == '\t'){ i++; continue; }
        if(isdigit((unsigned char)ch)){
            int j;
            if(ch == '0' && i + 1 < len && (t[i+1] == 'x' || t[i+1] == 'X')){
                j = i + 2;
                while(j < len && (isxdigit((unsigned char)t[j]) || t[j] == '_')) j++;
                if(j == i + 2) mini_fail(c, "malformed hex number");
                out[n].k = MT_NUM; out[n].num = mini_digits(t, i + 2, j, 16);
            } else if(ch == '0' && i + 1 < len && (t[i+1] == 'b' || t[i+1] == 'B')){
                j = i + 2;
                while(j < len && (t[j] == '0' || t[j] == '1' || t[j] == '_')) j++;
                if(j == i + 2) mini_fail(c, "malformed binary number");
                out[n].k = MT_NUM; out[n].num = mini_digits(t, i + 2, j, 2);
            } else {
                j = i;
                while(j < len && (isdigit((unsigned char)t[j]) || t[j] == '_')) j++;
                out[n].k = MT_NUM; out[n].num = mini_digits(t, i, j, 10);
            }
            MLX_BEGIN(); MLX_END(); n++; i = j; continue;
        }
        if(isalpha((unsigned char)ch) || ch == '_'){
            int j = i;
            while(j < len && (isalnum((unsigned char)t[j]) || t[j] == '_')) j++;
            out[n].k = MT_NAME;
            MLX_BEGIN();
            for(int q = i; q < j; q++) MLX_PUT(t[q]);
            MLX_END();
            n++; i = j; continue;
        }
        if(ch == '$'){
            if(t[i+1] == '$' || t[i+1] == '.'){
                out[n].k = MT_CORE;
                MLX_BEGIN(); MLX_PUT(t[i]); MLX_PUT(t[i+1]); MLX_END();
                n++; i += 2; continue;
            }
            mini_fail(c, "'$' must be written '$$' (location counter) or '$.' "
                         "(start of the next instruction)");
        }
        if(ch == '#'){
            int j = i + 1;
            while(j < len && (isalnum((unsigned char)t[j]) || t[j] == '_'
                              || t[j] == '.' || t[j] == '$')) j++;
            if(j == i + 1) mini_fail(c, "'#' needs a symbol name");
            out[n].k = MT_CORE;
            MLX_BEGIN();
            for(int q = i; q < j; q++) MLX_PUT(t[q]);
            MLX_END();
            n++; i = j; continue;
        }
        if(ch == '"'){
            int j = i + 1;
            MLX_BEGIN();
            for(;;){
                if(j >= len) mini_fail(c, "unterminated string");
                char cc = t[j];
                if(cc == '"'){ j++; break; }
                if(cc == '\\'){
                    if(j + 1 >= len) mini_fail(c, "unterminated string");
                    char e = t[j+1];
                    char r;
                    if(e == '\\')      r = '\\';
                    else if(e == '"')  r = '"';
                    else if(e == 'n')  r = '\n';
                    else if(e == 't')  r = '\t';
                    else { mini_fail(c, "unknown escape '\\%c' in a string", e); r = 0; }
                    MLX_PUT(r);
                    j += 2;
                    continue;
                }
                MLX_PUT(cc);
                j++;
            }
            MLX_END();
            out[n].k = MT_STR;
            n++; i = j; continue;
        }
        if(ch == '.'){
            int j = i + 1;
            while(j < len && (isalnum((unsigned char)t[j]) || t[j] == '_')) j++;
            if(j == i + 1) mini_fail(c, "stray '.'");
            out[n].k = MT_DOT;
            MLX_BEGIN();
            for(int q = i; q < j; q++) MLX_PUT(axx_upper_char(t[q]));
            MLX_END();
            n++; i = j; continue;
        }
        {
            int hit = 0;
            for(int q = 0; ops2[q]; q++){
                if(t[i] == ops2[q][0] && i + 1 < len && t[i+1] == ops2[q][1]){
                    out[n].k = MT_OP;
                    MLX_BEGIN(); MLX_PUT(ops2[q][0]); MLX_PUT(ops2[q][1]); MLX_END();
                    n++; i += 2; hit = 1; break;
                }
            }
            if(hit) continue;
        }
        if(strchr("+-*/%&|^~<>!()[]:,=", ch)){
            out[n].k = MT_OP;
            MLX_BEGIN(); MLX_PUT(ch); MLX_END();
            n++; i++; continue;
        }
        { /* axx.py と同じく 1 文字（UTF-8）を repr の形で引用する。 */
          size_t _cl = utf8_prefix_bytes(t + i, (size_t)(len - i), 1);
          char _cr[32]; m_pyrepr_n(t + i, _cl, _cr, sizeof(_cr));
          mini_fail(c, "unexpected character %s", _cr); }
    }
    out[n].k = MT_END;
    MLX_BEGIN(); MLX_END();
    #undef MLX_BEGIN
    #undef MLX_PUT
    #undef MLX_END
    return n;
}


typedef struct { MTok *t; int n; int i; MiniCtx *c; } MXP;

static MExpr *mxp_or(MXP *p);

/* 式の入れ子を 1 段深くする。MINI_EXPR_MAX_DEPTH を超えたら構文エラー。
   C のスタックを使い切って落ちないための上限で、axx.py も同じ段数で止まる。 */
#define MINI_EXPR_MAX_DEPTH 1000
static void mxp_enter(MXP *p){
    if(++p->c->pdepth > MINI_EXPR_MAX_DEPTH)
        mini_fail(p->c, "expression nests too deeply (more than %d levels)",
                  MINI_EXPR_MAX_DEPTH);
}

/* 式の節を 1 つ作る。 */
static MExpr *mx_new(MXKind k){
    MExpr *e = mini_alloc(sizeof(MExpr));
    e->k = k;
    return e;
}

/* 次がその演算子か。 */
static int mxp_is_op(MXP *p, const char *op){
    return p->i < p->n && p->t[p->i].k == MT_OP && strcmp(p->t[p->i].s, op) == 0;
}

/* 次がその演算子なら消費して真。 */
static int mxp_eat(MXP *p, const char *op){
    if(mxp_is_op(p, op)){ p->i++; return 1; }
    return 0;
}

/* 診断に出すためにトークンを Python の repr の形で書く。数は 10 進、行末は
   'end of line'。axx.py の _mini_tok_repr() と同じ。返した文字列は解放すること。 */
static char *mxp_tokdesc(MXP *p){
    if(p->i >= p->n){
        char *b = mini_alloc(32);
        m_pyrepr("end of line", b, 32);
        return b;
    }
    const MTok *tk = &p->t[p->i];
    if(tk->k == MT_NUM){
        char *b = mini_alloc(96);
        u256_to_pydec(tk->num, b, 96);
        return b;
    }
    size_t sz = strlen(tk->s) * 4 + 8;
    char *b = mini_alloc(sz);
    m_pyrepr(tk->s, b, sz);
    return b;
}

/* その演算子を必ず消費する。 */
static void mxp_expect(MXP *p, const char *op){
    if(!mxp_eat(p, op)){
        char *d = mxp_tokdesc(p);
        char msg[64];
        snprintf(msg, sizeof(msg), "expected '%s', found ", op);
        mini_fail(p->c, "%s%s", msg, d);
    }
}

static int mxp_end(MXP *p){ return p->i >= p->n; }

/* 項そのもの。数値、名前、括弧、配列リテラル、`.call`、組み込み。 */
static MExpr *mxp_primary(MXP *p){
    if(mxp_end(p)){ char *d = mxp_tokdesc(p); mini_fail(p->c, "expected a value, found %s", d); }
    MTok *tk = &p->t[p->i];
    if(tk->k == MT_STR){ p->i++; MExpr *e = mx_new(MX_STR); e->name = mini_strdup(tk->s); return e; }
    if(tk->k == MT_CORE){ p->i++; MExpr *e = mx_new(MX_CORE); e->name = mini_strdup(tk->s); return e; }
    if(tk->k == MT_NUM){ p->i++; MExpr *e = mx_new(MX_NUM); e->num = tk->num; return e; }
    if(tk->k == MT_NAME){ p->i++; MExpr *e = mx_new(MX_VAR); e->name = mini_strdup(tk->s); return e; }
    if(tk->k == MT_DOT){
        if(strcmp(tk->s, ".LEN") == 0 || strcmp(tk->s, ".STR") == 0
           || strcmp(tk->s, ".CHR") == 0 || strcmp(tk->s, ".INT") == 0){
            MXKind bk = tk->s[1] == 'L' ? MX_LEN : tk->s[1] == 'S' ? MX_TOSTR
                      : tk->s[1] == 'C' ? MX_CHR : MX_TOINT;
            p->i++;
            mxp_expect(p, "(");
            MExpr *e = mx_new(bk);
            e->a = mxp_or(p);
            mxp_expect(p, ")");
            return e;
        }
        if(strcmp(tk->s, ".CALL") == 0){
            p->i++;
            if(p->i >= p->n || p->t[p->i].k != MT_NAME)
                mini_fail(p->c, "'.call' needs a function name");
            MExpr *e = mx_new(MX_CALL);
            e->name = mini_strdup(p->t[p->i].s);
            p->i++;
            mxp_expect(p, "(");
            int cap = 0;
            if(!mxp_is_op(p, ")")){
                do {
                    if(e->nitems >= cap){
                        cap = cap ? cap * 2 : 8;
                        e->items = realloc(e->items, (size_t)cap * sizeof(MExpr*));
                        if(!e->items){ perror("realloc"); exit(1); }
                    }
                    e->items[e->nitems++] = mxp_or(p);
                } while(mxp_eat(p, ","));
            }
            mxp_expect(p, ")");
            return e;
        }
        { size_t _n = strlen(tk->s);
          char *_lo = mini_alloc(_n + 1);
          for(size_t _i=0;_i<_n;_i++) _lo[_i] = (char)tolower((unsigned char)tk->s[_i]);
          _lo[_n] = '\0';
          char *_r = mini_alloc(_n * 4 + 8);
          m_pyrepr(_lo, _r, _n * 4 + 8);
          mini_fail(p->c, "%s cannot be used in an expression", _r); }
    }
    if(mxp_is_op(p, "(")){
        p->i++;
        MExpr *e = mxp_or(p);
        mxp_expect(p, ")");
        return e;
    }
    if(mxp_is_op(p, "[")){
        p->i++;
        MExpr *e = mx_new(MX_ARRLIT);
        int cap = 0;
        if(!mxp_is_op(p, "]")){
            do {
                if(e->nitems >= cap){
                    cap = cap ? cap * 2 : 8;
                    e->items = realloc(e->items, (size_t)cap * sizeof(MExpr*));
                    if(!e->items){ perror("realloc"); exit(1); }
                }
                e->items[e->nitems++] = mxp_or(p);
            } while(mxp_eat(p, ","));
        }
        mxp_expect(p, "]");
        return e;
    }
    { char *d = mxp_tokdesc(p); mini_fail(p->c, "expected a value, found %s", d); }
    return NULL;
}

/* 後置の添字 `名前[式]`。 */
static MExpr *mxp_postfix(MXP *p){
    MExpr *e = mxp_primary(p);
    while(mxp_is_op(p, "[")){
        p->i++;
        MExpr *lo = mxp_is_op(p, ":") ? NULL : mxp_or(p);
        if(mxp_eat(p, ":")){
            MExpr *hi = mxp_is_op(p, "]") ? NULL : mxp_or(p);
            mxp_expect(p, "]");
            MExpr *s = mx_new(MX_SLICE);
            s->a = e; s->b = lo; s->c = hi;
            e = s;
        } else {
            mxp_expect(p, "]");
            if(!lo) mini_fail(p->c, "empty subscript");
            MExpr *s = mx_new(MX_INDEX);
            s->a = e; s->b = lo;
            e = s;
        }
    }
    return e;
}

static MExpr *mxp_unary(MXP *p);

/* `**`。 */
static MExpr *mxp_power(MXP *p){
    MExpr *e = mxp_postfix(p);
    if(mxp_is_op(p, "**")){
        p->i++;
        MExpr *b = mx_new(MX_BIN);
        strcpy(b->op, "**"); b->a = e; b->b = mxp_unary(p);
        return b;
    }
    return e;
}

/* 単項 `-` `+` `~`。 */
static MExpr *mxp_unary(MXP *p){
    if(mxp_is_op(p, "-") || mxp_is_op(p, "+") || mxp_is_op(p, "~")){
        char op[3]; strcpy(op, p->t[p->i].s);
        p->i++;
        MExpr *e = mx_new(MX_UN);
        strcpy(e->op, op);
        mxp_enter(p);
        e->a = mxp_unary(p);
        p->c->pdepth--;
        return e;
    }
    return mxp_power(p);
}

/* 二項演算子の 1 段。表で優先順位を回す。 */
static MExpr *mxp_binlevel(MXP *p, int level){
    static const char *tbl[6][3] = {
        { "|",  NULL, NULL },
        { "^",  NULL, NULL },
        { "&",  NULL, NULL },
        { "<<", ">>", NULL },
        { "+",  "-",  NULL },
        { "*",  "/",  "%"  },
    };
    MExpr *e = (level == 5) ? mxp_unary(p) : mxp_binlevel(p, level + 1);
    for(;;){
        int hit = -1;
        for(int q = 0; q < 3 && tbl[level][q]; q++)
            if(mxp_is_op(p, tbl[level][q])){ hit = q; break; }
        if(hit < 0) break;
        char op[3]; strcpy(op, p->t[p->i].s);
        p->i++;
        MExpr *b = mx_new(MX_BIN);
        strcpy(b->op, op);
        b->a = e;
        b->b = (level == 5) ? mxp_unary(p) : mxp_binlevel(p, level + 1);
        e = b;
    }
    return e;
}

/* 比較。 */
static MExpr *mxp_cmp(MXP *p){
    static const char *ops[] = { "==","!=","<=",">=","<",">", NULL };
    MExpr *e = mxp_binlevel(p, 0);
    for(;;){
        int hit = -1;
        for(int q = 0; ops[q]; q++) if(mxp_is_op(p, ops[q])){ hit = q; break; }
        if(hit < 0) break;
        char op[3]; strcpy(op, p->t[p->i].s);
        p->i++;
        MExpr *b = mx_new(MX_BIN);
        strcpy(b->op, op); b->a = e; b->b = mxp_binlevel(p, 0);
        e = b;
    }
    return e;
}

/* 単項 `!`。 */
static MExpr *mxp_not(MXP *p){
    if(mxp_is_op(p, "!")){
        p->i++;
        MExpr *e = mx_new(MX_UN);
        strcpy(e->op, "!");
        mxp_enter(p);
        e->a = mxp_not(p);
        p->c->pdepth--;
        return e;
    }
    return mxp_cmp(p);
}

/* `&&`。 */
static MExpr *mxp_and(MXP *p){
    MExpr *e = mxp_not(p);
    while(mxp_is_op(p, "&&")){
        p->i++;
        MExpr *b = mx_new(MX_BIN);
        strcpy(b->op, "&&"); b->a = e; b->b = mxp_not(p);
        e = b;
    }
    return e;
}

/* `||`。 */
static MExpr *mxp_or(MXP *p){
    mxp_enter(p);
    MExpr *e = mxp_and(p);
    while(mxp_is_op(p, "||")){
        p->i++;
        MExpr *b = mx_new(MX_BIN);
        strcpy(b->op, "||"); b->a = e; b->b = mxp_and(p);
        e = b;
    }
    p->c->pdepth--;
    return e;
}

/* 式を 1 個解析する。 */
static MExpr *mxp_full(MXP *p){
    MExpr *e = mxp_or(p);
    if(!mxp_end(p)){ char *d = mxp_tokdesc(p); mini_fail(p->c, "unexpected %s in expression", d); }
    return e;
}

/* `.echo` の引数（文字列と式の混在）を解析する。 */
static void mxp_echo_arglist(MXP *p, MExpr ***outv, int *outn){
    mxp_expect(p, "(");
    int cap = 0;
    *outv = NULL; *outn = 0;
    if(!mxp_is_op(p, ")")){
        do {
            if(*outn >= cap){
                cap = cap ? cap * 2 : 8;
                *outv = realloc(*outv, (size_t)cap * sizeof(MExpr*));
                if(!*outv){ perror("realloc"); exit(1); }
            }
            (*outv)[(*outn)++] = mxp_or(p);
        } while(mxp_eat(p, ","));
    }
    mxp_expect(p, ")");
}

/* カンマ区切りの式の並びを解析する。 */
static void mxp_arglist(MXP *p, MExpr ***outv, int *outn){
    mxp_expect(p, "(");
    int cap = 0;
    *outv = NULL; *outn = 0;
    if(!mxp_is_op(p, ")")){
        do {
            if(*outn >= cap){
                cap = cap ? cap * 2 : 8;
                *outv = realloc(*outv, (size_t)cap * sizeof(MExpr*));
                if(!*outv){ perror("realloc"); exit(1); }
            }
            (*outv)[(*outn)++] = mxp_or(p);
        } while(mxp_eat(p, ","));
    }
    mxp_expect(p, ")");
}


typedef struct {
    MiniFunc *f;
    int       i;
    MiniCtx  *c;
    MiniLexBuf *tok;
    int       loopdepth;
    int       nest;       /* .if/.elif/.while/.for の入れ子（msp_nest） */
} MSP;

/* 文の入れ子を 1 段深くする。MINI_BLOCK_MAX_DEPTH を超えたら構文エラー。
   C のスタックを使い切って落ちないための上限で、axx.py も同じ段数で止まる。 */
#define MINI_BLOCK_MAX_DEPTH 1000
static void msp_nest(MSP *p){
    if(++p->nest > MINI_BLOCK_MAX_DEPTH)
        mini_fail(p->c, "'.if'/'.while'/'.for' blocks nest too deeply (more than %d levels)",
                  MINI_BLOCK_MAX_DEPTH);
}

/* 文の並びに 1 つ積む。 */
static void ms_push(MStmt ***v, int *n, int *cap, MStmt *s){
    if(*n >= *cap){
        *cap = *cap ? *cap * 2 : 8;
        *v = realloc(*v, (size_t)*cap * sizeof(MStmt*));
        if(!*v){ perror("realloc"); exit(1); }
    }
    (*v)[(*n)++] = s;
}

/* 文の節を 1 つ作る。 */
static MStmt *ms_new(MSKind k, MSP *p, int li){
    MStmt *s = mini_alloc(sizeof(MStmt));
    s->k = k;
    s->file = p->f->lfiles[li];
    s->line = p->f->llines[li];
    return s;
}

/* 行頭のドット付きキーワードを大文字で取り出す。 */
static void mini_dotkw(const char *s, char *out, size_t osz){
    int i = axx_skipspc(s, 0);
    out[0] = 0;
    if(s[i] != '.') return;
    size_t n = 0;
    out[n++] = '.';
    i++;
    while(s[i] && (isalnum((unsigned char)s[i]) || s[i] == '_') && n < osz - 1)
        out[n++] = axx_upper_char(s[i++]);
    out[n] = 0;
}

/* それがブロックを閉じるキーワードか。 */
static int mini_is_ender(const char *kw){
    return strcmp(kw, ".ELIF") == 0 || strcmp(kw, ".ELSE") == 0
        || strcmp(kw, ".ENDIF") == 0
        || strcmp(kw, ".NEXT") == 0 || strcmp(kw, ".ENDWHILE") == 0;
}

static void msp_block(MSP *p, const char *e1, const char *e2, const char *e3,
                      MStmt ***outv, int *outn);
static MStmt *msp_if_chain(MSP *p, int li);

static void ms_call_tail(MiniCtx *c, MTok *toks, int n, char **namep,
                         MExpr ***argv, int *argn){
    if(n < 2 || toks[1].k != MT_NAME) mini_fail(c, "'.call' needs a function name");
    *namep = mini_strdup(toks[1].s);
    MXP ep; ep.t = toks + 2; ep.n = n - 2; ep.i = 0; ep.c = c;
    mxp_arglist(&ep, argv, argn);
    if(!mxp_end(&ep)) mini_fail(c, "unexpected text after '.call'");
}

/* 単純文 1 個を解析する。代入、`.emit`、`.echo`、`.raise`、`.return` など。 */
static MStmt *msp_simple(MSP *p, int li){
    MiniCtx *c = p->c;
    const char *text = p->f->lines[li];
    c->file = p->f->lfiles[li];
    c->line = p->f->llines[li];
    int n = mini_lex(c, text, p->tok);
    MTok *toks = p->tok->tok;
    if(n == 0) mini_fail(c, "empty statement");

    if(toks[0].k == MT_DOT){
        const char *kw = toks[0].s;
        if(strcmp(kw, ".RETURN") == 0){
            MStmt *s = ms_new(MS_RETURN, p, li);
            if(n > 1){
                MXP ep; ep.t = toks + 1; ep.n = n - 1; ep.i = 0; ep.c = c;
                s->val = mxp_full(&ep);
            }
            return s;
        }
        if(strcmp(kw, ".RAISE") == 0){
            if(n <= 1) mini_fail(c, "'.raise' needs an error code");
            MStmt *s = ms_new(MS_RAISE, p, li);
            MXP ep; ep.t = toks + 1; ep.n = n - 1; ep.i = 0; ep.c = c;
            s->val = mxp_full(&ep);
            return s;
        }
        if(strcmp(kw, ".EMIT") == 0){
            MStmt *s = ms_new(MS_EMIT, p, li);
            MXP ep; ep.t = toks + 1; ep.n = n - 1; ep.i = 0; ep.c = c;
            mxp_arglist(&ep, &s->args, &s->nargs);
            if(!mxp_end(&ep)) mini_fail(c, "unexpected text after '.emit(...)'");
            if(s->nargs == 0) mini_fail(c, "'.emit' needs at least one value");
            return s;
        }
        if(strcmp(kw, ".ECHO") == 0){
            MStmt *s = ms_new(MS_ECHO, p, li);
            MXP ep; ep.t = toks + 1; ep.n = n - 1; ep.i = 0; ep.c = c;
            mxp_echo_arglist(&ep, &s->args, &s->nargs);
            if(!mxp_end(&ep)) mini_fail(c, "unexpected text after '.echo(...)'");
            return s;
        }
        if(strcmp(kw, ".BREAK") == 0 || strcmp(kw, ".CONTINUE") == 0){
            int isbrk = (strcmp(kw, ".BREAK") == 0);
            if(n != 1)
                mini_fail(c, "unexpected text after '%s'", isbrk ? ".break" : ".continue");
            if(p->loopdepth <= 0)
                mini_fail(c, "'%s' must be inside a '.while' or '.for' loop",
                          isbrk ? ".break" : ".continue");
            return ms_new(isbrk ? MS_BREAK : MS_CONTINUE, p, li);
        }
        if(strcmp(kw, ".CALL") == 0){
            MStmt *s = ms_new(MS_CALL, p, li);
            ms_call_tail(c, toks, n, &s->name, &s->args, &s->nargs);
            return s;
        }
        if(strcmp(kw, ".NONLOCAL") == 0){
            MStmt *s = ms_new(MS_NONLOCAL, p, li);
            int cap = 0, j = 1;
            while(j < n){
                if(toks[j].k != MT_NAME) mini_fail(c, "'.nonlocal' needs variable names");
                if(s->nnames >= cap){
                    cap = cap ? cap * 2 : 8;
                    s->names = realloc(s->names, (size_t)cap * sizeof(char*));
                    if(!s->names){ perror("realloc"); exit(1); }
                }
                s->names[s->nnames++] = mini_strdup(toks[j].s);
                j++;
                if(j < n){
                    if(!(toks[j].k == MT_OP && strcmp(toks[j].s, ",") == 0))
                        mini_fail(c, "'.nonlocal' names must be separated by ','");
                    j++;
                }
            }
            if(s->nnames == 0) mini_fail(c, "'.nonlocal' needs variable names");
            return s;
        }
        { char _kl[256]; size_t _ki = 0;
          for(; kw[_ki] && _ki + 1 < sizeof(_kl); _ki++)
              _kl[_ki] = (char)tolower((unsigned char)kw[_ki]);
          _kl[_ki] = '\0';
          char _kr[600]; m_pyrepr(_kl, _kr, sizeof(_kr));
          mini_fail(c, "unknown statement %s", _kr); }
    }
    if(toks[0].k != MT_NAME)
        mini_fail(c, "statement must be a directive or an assignment");
    {
        MStmt *s = ms_new(MS_ASSIGN, p, li);
        s->name = mini_strdup(toks[0].s);
        MXP ep; ep.t = toks + 1; ep.n = n - 1; ep.i = 0; ep.c = c;
        if(mxp_is_op(&ep, "[")){
            ep.i++;
            MExpr *lo = mxp_is_op(&ep, ":") ? NULL : mxp_or(&ep);
            if(mxp_eat(&ep, ":")){
                /* `名前[lo:hi] = 値` は範囲の置き換え。a が NULL の MX_SLICE で表す。 */
                MExpr *sl = mx_new(MX_SLICE);
                sl->b = lo;
                sl->c = mxp_is_op(&ep, "]") ? NULL : mxp_or(&ep);
                s->idx = sl;
            } else {
                s->idx = lo;
            }
            mxp_expect(&ep, "]");
        }
        mxp_expect(&ep, "=");
        MTok *rt = ep.t + ep.i;
        int rn = ep.n - ep.i;
        if(rn > 0 && rt[0].k == MT_DOT && strcmp(rt[0].s, ".CALL") == 0){
            s->k = MS_CALLASSIGN;
            ms_call_tail(c, rt, rn, &s->fname, &s->args, &s->nargs);
            return s;
        }
        MXP rp; rp.t = rt; rp.n = rn; rp.i = 0; rp.c = c;
        s->val = mxp_full(&rp);
        return s;
    }
}

/* `.if` / `.elif` / `.else` / `.endif` の連なりを解析する。 */
static MStmt *msp_if_chain(MSP *p, int li){
    MiniCtx *c = p->c;
    char kw[32];
    mini_dotkw(p->f->lines[li], kw, sizeof(kw));
    char low[32];
    snprintf(low, sizeof(low), "%s", kw);
    for(char *q = low; *q; q++) *q = (char)tolower((unsigned char)*q);
    c->file = p->f->lfiles[li];
    c->line = p->f->llines[li];
    msp_nest(p);
    int n = mini_lex(c, p->f->lines[li], p->tok);
    MTok *toks = p->tok->tok;
    if(n < 2 || toks[n-1].k != MT_DOT || strcmp(toks[n-1].s, ".THEN") != 0)
        mini_fail(c, "'%s' must end with '.then'", low);
    MStmt *s = ms_new(MS_IF, p, li);
    MXP ep; ep.t = toks + 1; ep.n = n - 2; ep.i = 0; ep.c = c;
    s->val = mxp_full(&ep);
    p->i = li + 1;
    msp_block(p, ".ELIF", ".ELSE", ".ENDIF", &s->body, &s->nbody);
    if(p->i >= p->f->nlines){
        c->file = s->file; c->line = s->line;
        mini_fail(c, "'.if' is never closed with '.endif'");
    }
    char kw2[32];
    mini_dotkw(p->f->lines[p->i], kw2, sizeof(kw2));
    if(strcmp(kw2, ".ELIF") == 0){
        MStmt *inner = msp_if_chain(p, p->i);
        int cap2 = 0;
        ms_push(&s->body2, &s->nbody2, &cap2, inner);
    } else if(strcmp(kw2, ".ELSE") == 0){
        c->file = p->f->lfiles[p->i]; c->line = p->f->llines[p->i];
        if(mini_lex(c, p->f->lines[p->i], p->tok) != 1)
            mini_fail(c, "unexpected text after '.else'");
        p->i++;
        msp_block(p, ".ENDIF", NULL, NULL, &s->body2, &s->nbody2);
        if(p->i >= p->f->nlines){
            c->file = s->file; c->line = s->line;
            mini_fail(c, "'.if' is never closed with '.endif'");
        }
    }
    p->nest--;
    return s;
}

static void msp_block(MSP *p, const char *e1, const char *e2, const char *e3,
                      MStmt ***outv, int *outn){
    MiniCtx *c = p->c;
    int cap = 0;
    *outv = NULL; *outn = 0;
    while(p->i < p->f->nlines){
        int li = p->i;
        char kw[32];
        mini_dotkw(p->f->lines[li], kw, sizeof(kw));
        c->file = p->f->lfiles[li];
        c->line = p->f->llines[li];
        if((e1 && strcmp(kw, e1) == 0) || (e2 && strcmp(kw, e2) == 0)
           || (e3 && strcmp(kw, e3) == 0)) return;
        if(mini_is_ender(kw)){
            char low[32];
            snprintf(low, sizeof(low), "%s", kw);
            for(char *q = low; *q; q++) *q = (char)tolower((unsigned char)*q);
            mini_fail(c, "'%s' without a matching opener", low);
        }
        if(strcmp(kw, ".IF") == 0){
            MStmt *s = msp_if_chain(p, li);
            p->i++;
            ms_push(outv, outn, &cap, s);
            continue;
        }
        if(strcmp(kw, ".WHILE") == 0){
            msp_nest(p);
            int n = mini_lex(c, p->f->lines[li], p->tok);
            MTok *toks = p->tok->tok;
            MStmt *s = ms_new(MS_WHILE, p, li);
            MXP ep; ep.t = toks + 1; ep.n = n - 1; ep.i = 0; ep.c = c;
            s->val = mxp_full(&ep);
            p->i = li + 1;
            p->loopdepth++;
            msp_block(p, ".ENDWHILE", NULL, NULL, &s->body, &s->nbody);
            p->loopdepth--;
            if(p->i >= p->f->nlines){
                c->file = s->file; c->line = s->line;
                mini_fail(c, "'.while' is never closed with '.endwhile'");
            }
            p->nest--;
            p->i++;
            ms_push(outv, outn, &cap, s);
            continue;
        }
        if(strcmp(kw, ".FOR") == 0){
            msp_nest(p);
            int n = mini_lex(c, p->f->lines[li], p->tok);
            MTok *toks = p->tok->tok;
            if(n < 4 || toks[1].k != MT_NAME)
                mini_fail(c, "'.for' needs 'variable in range(...)' or 'variable in array'");
            MStmt *s = ms_new(MS_FOR, p, li);
            s->name = mini_strdup(toks[1].s);
            if(!(toks[2].k == MT_NAME && strcmp(toks[2].s, "in") == 0))
                mini_fail(c, "'.for %s' must be followed by 'in range(...)' or 'in array'",
                          s->name);
            /* `in` の後ろが `range(` なら数の範囲、それ以外は配列の式（s->val）で、
               その要素を順に回す。axx.py の MiniParser._for_header() と同じ規則である。 */
            if(!(toks[3].k == MT_NAME && strcmp(toks[3].s, "range") == 0)
               || n < 5 || !(toks[4].k == MT_OP && strcmp(toks[4].s, "(") == 0)){
                MXP ep; ep.t = toks + 3; ep.n = n - 3; ep.i = 0; ep.c = c;
                s->val = mxp_full(&ep);
            } else {
                MXP ep; ep.t = toks + 4; ep.n = n - 4; ep.i = 0; ep.c = c;
                mxp_arglist(&ep, &s->args, &s->nargs);
                if(!mxp_end(&ep)) mini_fail(c, "unexpected text after 'range(...)'");
                if(s->nargs < 1 || s->nargs > 3)
                    mini_fail(c, "range() takes 1 to 3 arguments, got %d", s->nargs);
            }
            p->i = li + 1;
            p->loopdepth++;
            msp_block(p, ".NEXT", NULL, NULL, &s->body, &s->nbody);
            p->loopdepth--;
            if(p->i >= p->f->nlines){
                c->file = s->file; c->line = s->line;
                mini_fail(c, "'.for' is never closed with '.next'");
            }
            p->nest--;
            p->i++;
            ms_push(outv, outn, &cap, s);
            continue;
        }
        ms_push(outv, outn, &cap, msp_simple(p, li));
        p->i = li + 1;
    }
}

/* 字句解析のバッファを使い回すために 1 個だけ持つ。 */
static MiniLexBuf *mini_tokbuf(void){
    static MiniLexBuf buf;
    return &buf;
}

/* `.func` の本文を文の構文木にする。 */
static int mini_compile_func(MiniFunc *f, char **errout){
    MiniCtx c;
    MiniLexBuf *tokbuf = mini_tokbuf();
    memset(&c, 0, sizeof(c));
    c.file = f->file; c.line = f->line;
    c.jb_active = 1;
    if(setjmp(c.jb)){
        *errout = c.err;
        f->body = NULL; f->nbody = 0;
        return 0;
    }
    MSP p; p.f = f; p.i = 0; p.c = &c; p.tok = tokbuf; p.loopdepth = 0; p.nest = 0;
    msp_block(&p, NULL, NULL, NULL, &f->body, &f->nbody);
    if(p.i < f->nlines){
        c.file = f->lfiles[p.i]; c.line = f->llines[p.i];
        mini_fail(&c, "'%s' has no matching opener", f->lines[p.i]);
    }
    return 1;
}


typedef struct { char *name; MiniVal v; } MiniBind;

typedef struct {
    MiniBind  *vars;   int nvars, cvars;
    char     **nonloc; int nnonloc, cnonloc;
    MiniFunc  *func;
} MiniFrame;

typedef struct {
    Assembler *asmb;
    MiniCtx    c;
    IntVec     out;
    long       steps;
    MiniFrame *frames; int nframes, cframes;
    int        returning;
    int        loopctl;
    MiniVal    retval;
    /* この呼び出しが前方参照のラベルとして許した名前（式の節の名前を指す）。 */
    const char **fb; int nfb, cfb;
    int        has_ret;
} MiniRun;

static MiniVal mini_eval(MiniRun *r, MExpr *e);
static void mini_exec_block(MiniRun *r, MStmt **body, int n);
static MiniFunc *mini_lookup(MiniRun *r, const char *name);
static void mini_call_func(MiniRun *r, MiniFunc *f, MiniVal *args, int nargs);

static void mini_at(MiniRun *r, MStmt *s){ r->c.file = s->file; r->c.line = s->line; }

/* 256bit 値を long long に飽和させて落とす。 */
static long long mini_to_ll_sat(uint256_t v){
    if(u256_is_neg256(v)){
        uint256_t p = u256_neg(v);
        if(u256_nonneg_gt_i64(p, 0x7fffffffffffffffLL)) return -0x7fffffffffffffffLL - 1;
        return -(long long)u256_to_u64(p);
    }
    if(u256_nonneg_gt_i64(v, 0x7fffffffffffffffLL)) return 0x7fffffffffffffffLL;
    return (long long)u256_to_u64(v);
}

/* 256bit 値を long long にする。範囲外はエラーにする。 */
static long long mini_to_ll(MiniRun *r, uint256_t v){
    if(u256_is_neg256(v)){
        uint256_t p = u256_neg(v);
        if(u256_nonneg_gt_i64(p, 0x7fffffffffffffffLL))
            mini_fail(&r->c, "value is out of range for this use");
        return -(long long)u256_to_u64(p);
    }
    if(u256_nonneg_gt_i64(v, 0x7fffffffffffffffLL))
        mini_fail(&r->c, "value is out of range for this use");
    return (long long)u256_to_u64(v);
}

/* 数値を要求する。配列か文字列が来たらエラーにする。 */
static uint256_t mini_need_num(MiniRun *r, MiniVal v, const char *what){
    if(v.is_arr){
        mini_val_free(&v);
        mini_fail(&r->c, "%s must be a number, not an array", what);
    }
    if(v.is_str){
        mini_val_free(&v);
        mini_fail(&r->c, "%s must be a number, not a string", what);
    }
    return v.num;
}

static uint256_t mini_bool(int b){ return b ? u256_one() : u256_zero(); }

/* 作った文字列の長さを検査する。配列と同じ上限を使う。 */
static void mini_need_strlen(MiniRun *r, long long n){
    if(n > MINI_MAX_ARRAY)
        mini_fail(&r->c, "string longer than the maximum length %d", MINI_MAX_ARRAY);
}

/* 整数を符号付き 10 進の文字列にする。 */
static MiniVal mini_dec(uint256_t x){
    char cb[96]; u256_to_pydec(x, cb, sizeof(cb));
    return mini_strval(cb, (int)strlen(cb));
}

/* `+` で文字列とつなぐ側を文字列にする。v は消費する。 */
static MiniVal mini_text_of(MiniRun *r, MiniVal v){
    if(v.is_str) return v;
    return mini_dec(mini_need_num(r, v, "an operand"));
}

/* 2 つの文字列をバイト順の辞書式で比べる。 */
static int mini_str_cmp(const MiniVal *a, const MiniVal *b){
    int m = a->slen < b->slen ? a->slen : b->slen;
    int c = m > 0 ? memcmp(a->str, b->str, (size_t)m) : 0;
    if(c) return c;
    return (a->slen > b->slen) - (a->slen < b->slen);
}

/* 片方でも文字列のときの二項演算。a と b は消費する。`+` は連結（整数は
   符号付き 10 進にしてつなぐ）、`*` は繰り返し、`==` `!=` は種類も含めた
   一致、`<` などはバイト順の辞書式比較。
   axx.py の MiniInterp._str_binop() と同じ規則である。 */
static MiniVal mini_str_binop(MiniRun *r, const char *op, MiniVal a, MiniVal b){
    if(strcmp(op, "+") == 0){
        MiniVal ta = mini_text_of(r, a);
        MiniVal tb = mini_text_of(r, b);
        long long n = (long long)ta.slen + tb.slen;
        if(n > MINI_MAX_ARRAY){ mini_val_free(&ta); mini_val_free(&tb); }
        mini_need_strlen(r, n);
        MiniVal v = mini_strval(ta.str, ta.slen);
        v.str = realloc(v.str, (size_t)n + 1);
        if(!v.str){ perror("realloc"); exit(1); }
        if(tb.slen > 0) memcpy(v.str + ta.slen, tb.str, (size_t)tb.slen);
        v.slen = (int)n;
        mini_val_free(&ta); mini_val_free(&tb);
        return v;
    }
    if(strcmp(op, "*") == 0){
        if(a.is_str && b.is_str){
            mini_val_free(&a); mini_val_free(&b);
            mini_fail(&r->c, "a string can only be repeated by a number");
        }
        MiniVal t = a.is_str ? a : b;
        MiniVal nv = a.is_str ? b : a;
        if(nv.is_arr) mini_val_free(&t);
        uint256_t nn = mini_need_num(r, nv, "a repeat count");
        long long cnt = mini_to_ll_sat(nn);
        if(cnt <= 0){ mini_val_free(&t); return mini_strval("", 0); }
        if(t.slen > 0 && cnt > (long long)MINI_MAX_ARRAY / t.slen + 1){
            mini_val_free(&t);
            mini_need_strlen(r, (long long)MINI_MAX_ARRAY + 1);
        }
        long long n = (long long)t.slen * cnt;
        if(n > MINI_MAX_ARRAY) mini_val_free(&t);
        mini_need_strlen(r, n);
        MiniVal v; memset(&v, 0, sizeof(v));
        v.is_str = 1;
        v.str = mini_alloc((size_t)n + 1);
        for(long long i = 0; i < cnt; i++)
            memcpy(v.str + i * t.slen, t.str, (size_t)t.slen);
        v.slen = (int)n;
        mini_val_free(&t);
        return v;
    }
    if(strcmp(op, "==") == 0 || strcmp(op, "!=") == 0){
        if(a.is_arr || b.is_arr){
            mini_val_free(&a); mini_val_free(&b);
            mini_fail(&r->c, "an operand must be a number, not an array");
        }
        int eq = a.is_str && b.is_str && mini_str_cmp(&a, &b) == 0;
        mini_val_free(&a); mini_val_free(&b);
        return mini_num(mini_bool(eq == (op[0] == '=')));
    }
    if(strcmp(op, "<") == 0 || strcmp(op, "<=") == 0
       || strcmp(op, ">") == 0 || strcmp(op, ">=") == 0){
        if(!(a.is_str && b.is_str)){
            mini_val_free(&a); mini_val_free(&b);
            mini_fail(&r->c, "cannot order a string against a number");
        }
        int c = mini_str_cmp(&a, &b);
        mini_val_free(&a); mini_val_free(&b);
        int res = op[0] == '<' ? (op[1] == '=' ? c <= 0 : c < 0)
                               : (op[1] == '=' ? c >= 0 : c > 0);
        return mini_num(mini_bool(res));
    }
    mini_val_free(&a); mini_val_free(&b);
    mini_fail(&r->c, "an operand of '%s' must be a number, not a string", op);
    return mini_num(u256_zero());
}

/* `.int(文字列)` — 文字列を整数として読む。前後の空白、符号、`0x` / `0b`、
   桁区切りの `_` を受け付ける。v は消費する。
   axx.py の MiniInterp._to_int() と同じ規則である。 */
static uint256_t mini_str_to_int(MiniRun *r, MiniVal v){
    if(v.is_arr){
        mini_val_free(&v);
        mini_fail(&r->c, "'.int' needs a number or a string");
    }
    if(!v.is_str) return v.num;
    int b = 0, e = v.slen;
    const unsigned char *t = v.str;
    while(b < e && (t[b] == ' ' || t[b] == '\t')) b++;
    while(e > b && (t[e-1] == ' ' || t[e-1] == '\t')) e--;
    int neg = 0;
    if(b < e && (t[b] == '+' || t[b] == '-')){ neg = t[b] == '-'; b++; }
    int base = 10;
    if(e - b >= 2 && t[b] == '0' && (t[b+1] == 'x' || t[b+1] == 'X')){ base = 16; b += 2; }
    else if(e - b >= 2 && t[b] == '0' && (t[b+1] == 'b' || t[b+1] == 'B')){ base = 2; b += 2; }
    int ok = b < e, ndig = 0;
    for(int i = b; i < e && ok; i++){
        int c = t[i];
        if(c == '_') continue;
        int d = (base == 16) ? isxdigit(c) : (base == 2) ? (c == '0' || c == '1')
                                                         : (c >= '0' && c <= '9');
        if(d) ndig++; else ok = 0;
    }
    if(!ok || ndig == 0){
        mini_val_free(&v);
        mini_fail(&r->c, "'.int' cannot read the string as a number");
    }
    uint256_t x = mini_digits((const char *)t, b, e, base);
    mini_val_free(&v);
    return neg ? u256_neg(x) : x;
}

/* その名前を持つスコープを探す。 */
static MiniFrame *mini_frame_for(MiniRun *r, const char *name, int *found){
    MiniFrame *top = &r->frames[r->nframes - 1];
    *found = 1;
    int is_nl = 0;
    for(int i = 0; i < top->nnonloc; i++)
        if(strcmp(top->nonloc[i], name) == 0){ is_nl = 1; break; }
    if(!is_nl) return top;
    for(int fi = r->nframes - 2; fi >= 0; fi--)
        for(int i = 0; i < r->frames[fi].nvars; i++)
            if(strcmp(r->frames[fi].vars[i].name, name) == 0) return &r->frames[fi];
    *found = 0;
    return NULL;
}

/* スコープの中で名前を引く。 */
static MiniBind *mini_find(MiniFrame *fr, const char *name){
    for(int i = 0; i < fr->nvars; i++)
        if(strcmp(fr->vars[i].name, name) == 0) return &fr->vars[i];
    return NULL;
}

/* スコープに名前を 1 つ作る。 */
static MiniBind *mini_bind_new(MiniFrame *fr, const char *name){
    if(fr->nvars >= fr->cvars){
        fr->cvars = fr->cvars ? fr->cvars * 2 : 8;
        fr->vars = realloc(fr->vars, (size_t)fr->cvars * sizeof(MiniBind));
        if(!fr->vars){ perror("realloc"); exit(1); }
    }
    MiniBind *b = &fr->vars[fr->nvars++];
    memset(b, 0, sizeof(*b));
    b->name = mini_strdup(name);
    return b;
}

/* 本体の式評価器に委譲する（ラベル・`$$`・`#記号` を読むため）。未定義ラベル
   由来の値は 0 にして、巨大な番兵をミニ言語の演算へ流し込まない。 */
static uint256_t mini_core_eval(MiniRun *r, const char *text){
    if(!r->asmb) mini_fail(&r->c, "'%s' is not available here", text);
    int io = 0;
    uint256_t v = expr_expression_caps(r->asmb, text, 0, &CAPS_MINI, &io);
    if(u256_is_undef_derived(v)) return u256_zero();
    return v;
}

/* その名前が本体側（ラベル・シンボル・前回の反復の値）にあるか。 */
static int mini_core_name(MiniRun *r, const char *name){
    if(!r->asmb) return 0;
    AsmState *st = &r->asmb->st;
    if(lmap_find(&st->labels, name)) return 1;
    {
        char up[512];
        axx_strupr_to(up, name, sizeof(up));
        if(smap_find(&st->symbols, up)) return 1;
    }
    if(st->relax_prev && lmap_find(st->relax_prev, name)) return 1;
    return 0;
}

/* 変数を読む。無ければ本体側の名前として解決を試みる。パス2で本体側にも
   無い名前は「設定前に使われた」エラーにする。 */
static MiniVal mini_get(MiniRun *r, const char *name){
    int found;
    MiniFrame *fr = mini_frame_for(r, name, &found);
    if(!found)
        mini_fail(&r->c, "'.nonlocal %s' found no enclosing definition of '%s'", name, name);
    MiniBind *b = mini_find(fr, name);
    if(!b){
        /* 本体側に無い名前を前方参照のラベルとして許すのは、ラベルがまだ揃って
           いないパス 1 の最初の反復だけ。2 回目からは前回の反復の値が全部あるので、
           それでも無い名前は綴り間違いとしてすぐ止める（暴走の上限まで回らない）。
           axx.py の MiniInterp._get() と同じ。 */
        int permissive = r->asmb && r->asmb->st.pas != 2
                         && !(r->asmb->st.pas == 1 && !r->asmb->st.relax_optimistic);
        if(permissive && sv_contains(&r->asmb->st.mini_suspects, name)) permissive = 0;
        if(r->asmb && (mini_core_name(r, name) || permissive)){
            if(permissive && !mini_core_name(r, name)){
                int seen = 0;
                for(int i = 0; i < r->nfb; i++) if(strcmp(r->fb[i], name) == 0){ seen = 1; break; }
                if(!seen){
                    if(r->nfb >= r->cfb){
                        r->cfb = r->cfb ? r->cfb * 2 : 8;
                        r->fb = realloc(r->fb, (size_t)r->cfb * sizeof(char*));
                        if(!r->fb){ perror("realloc"); exit(1); }
                    }
                    r->fb[r->nfb++] = name;
                }
            }
            return mini_num(mini_core_eval(r, name));
        }
        mini_fail(&r->c, "'%s' is used before it is set", name);
    }
    return mini_val_copy(&b->v);
}

/* 変数へ代入する。 */
static void mini_set(MiniRun *r, const char *name, MiniVal v){
    int found;
    MiniFrame *fr = mini_frame_for(r, name, &found);
    if(!found){
        mini_val_free(&v);
        mini_fail(&r->c, "'.nonlocal %s' found no enclosing definition of '%s'", name, name);
    }
    MiniBind *b = mini_find(fr, name);
    if(!b) b = mini_bind_new(fr, name);
    else mini_val_free(&b->v);
    b->v = v;
}

/* 変数の枠を得る（無ければ作る）。 */
static MiniBind *mini_ref(MiniRun *r, const char *name){
    int found;
    MiniFrame *fr = mini_frame_for(r, name, &found);
    if(!found)
        mini_fail(&r->c, "'.nonlocal %s' found no enclosing definition of '%s'", name, name);
    MiniBind *b = mini_find(fr, name);
    if(!b) mini_fail(&r->c, "'%s' is used before it is set", name);
    return b;
}


/* 二項演算。`/` と `%` は C と同じゼロ方向の切り捨てで、本体の式評価器の
   `%`（除数の符号）とは違う。 */
static uint256_t mini_binop(MiniRun *r, const char *op, uint256_t a, uint256_t b){
    if(strcmp(op, "+") == 0) return u256_add(a, b);
    if(strcmp(op, "-") == 0) return u256_sub(a, b);
    if(strcmp(op, "*") == 0) return u256_mul(a, b);
    if(strcmp(op, "/") == 0){
        if(u256_is_zero(b)) mini_fail(&r->c, "division by zero");
        return u256_truncdiv(a, b);
    }
    if(strcmp(op, "%") == 0){
        if(u256_is_zero(b)) mini_fail(&r->c, "division by zero");
        return u256_sub(a, u256_mul(u256_truncdiv(a, b), b));
    }
    if(strcmp(op, "**") == 0){
        if(u256_is_neg256(b)) mini_fail(&r->c, "negative exponent");
        return u256_pow(a, b);
    }
    if(strcmp(op, "<<") == 0){
        if(u256_is_neg256(b)) return u256_zero();
        if(u256_nonneg_gt_i64(b, 255)) return u256_zero();
        return u256_shl(a, (int)u256_to_u64(b));
    }
    if(strcmp(op, ">>") == 0){
        if(u256_is_neg256(b)) return u256_zero();
        if(u256_nonneg_gt_i64(b, 255))
            return u256_is_neg256(a) ? u256_neg(u256_one()) : u256_zero();
        return u256_sar(a, (int)u256_to_u64(b));
    }
    if(strcmp(op, "&") == 0) return u256_and(a, b);
    if(strcmp(op, "|") == 0) return u256_or(a, b);
    if(strcmp(op, "^") == 0) return u256_xor(a, b);
    if(strcmp(op, "<") == 0)  return mini_bool(u256_lt_signed(a, b));
    if(strcmp(op, ">") == 0)  return mini_bool(u256_gt_signed(a, b));
    if(strcmp(op, "<=") == 0) return mini_bool(u256_le_signed(a, b));
    if(strcmp(op, ">=") == 0) return mini_bool(u256_ge_signed(a, b));
    if(strcmp(op, "==") == 0) return mini_bool(u256_eq(a, b));
    return mini_bool(!u256_eq(a, b));
}

/* 式の構文木を評価する。 */
static MiniVal mini_eval(MiniRun *r, MExpr *e){
    switch(e->k){
    case MX_STR:
        return mini_strval(e->name, (int)strlen(e->name));
    case MX_TOSTR: {
        MiniVal v = mini_eval(r, e->a);
        if(v.is_arr){ mini_val_free(&v); mini_fail(&r->c, "'.str' needs a number or a string"); }
        if(v.is_str) return v;
        return mini_dec(v.num);
    }
    case MX_CHR: {
        uint256_t c = mini_need_num(r, mini_eval(r, e->a), "'.chr' argument");
        if(u256_is_neg256(c) || u256_nonneg_gt_i64(c, 255))
            mini_fail(&r->c, "'.chr' needs a value from 0 to 255");
        unsigned char ch = (unsigned char)u256_to_u64(c);
        return mini_strval(&ch, 1);
    }
    case MX_TOINT:
        return mini_num(mini_str_to_int(r, mini_eval(r, e->a)));
    case MX_CORE: return mini_num(mini_core_eval(r, e->name));
    case MX_NUM: return mini_num(e->num);
    case MX_VAR: return mini_get(r, e->name);
    case MX_ARRLIT: {
        MiniVal v; memset(&v, 0, sizeof(v));
        v.is_arr = 1;
        mini_arr_reserve(&v, e->nitems > 0 ? e->nitems : 1);
        for(int i = 0; i < e->nitems; i++){
            MiniVal ev = mini_eval(r, e->items[i]);
            if(ev.is_arr){
                mini_val_free(&ev); mini_val_free(&v);
                mini_fail(&r->c, "an array element must be a number or a string, "
                          "not an array");
            }
            v.n++;
            mini_arr_put(&v, v.n - 1, ev);
        }
        return v;
    }
    case MX_CALL: {
        MiniFunc *f = mini_lookup(r, e->name);
        MiniVal *vals = e->nitems ? mini_alloc((size_t)e->nitems * sizeof(MiniVal)) : NULL;
        for(int i = 0; i < e->nitems; i++) vals[i] = mini_eval(r, e->items[i]);
        const char *sfile = r->c.file;
        int sline = r->c.line;
        mini_call_func(r, f, vals, e->nitems);
        for(int i = 0; i < e->nitems; i++) mini_val_free(&vals[i]);
        free(vals);
        r->c.file = sfile; r->c.line = sline;
        if(!r->has_ret)
            mini_fail(&r->c, "'%s' returned no value; give it a "
                      "'.return <expression>'", e->name);
        MiniVal ret = r->retval;
        memset(&r->retval, 0, sizeof(r->retval));
        r->has_ret = 0;
        return ret;
    }
    case MX_LEN: {
        MiniVal b = mini_eval(r, e->a);
        if(!b.is_arr && !b.is_str){
            mini_val_free(&b);
            mini_fail(&r->c, "'.len' needs an array or a string");
        }
        int n = b.is_str ? b.slen : b.n;
        mini_val_free(&b);
        return mini_num(u256_from_u64((uint64_t)n));
    }
    case MX_INDEX: {
        MiniVal b = mini_eval(r, e->a);
        if(!b.is_arr && !b.is_str){
            mini_val_free(&b);
            mini_fail(&r->c, "only an array or a string can be indexed");
        }
        uint256_t iv = mini_need_num(r, mini_eval(r, e->b), "an index");
        long long i = mini_to_ll_sat(iv);
        MiniVal out;
        if(b.is_str)
            out = mini_num((i < 0 || i >= b.slen) ? u256_zero() : u256_from_u64(b.str[i]));
        else
            out = (i < 0 || i >= b.n) ? mini_num(u256_zero()) : mini_arr_get(&b, (int)i);
        mini_val_free(&b);
        return out;
    }
    case MX_SLICE: {
        MiniVal b = mini_eval(r, e->a);
        if(!b.is_arr && !b.is_str){
            mini_val_free(&b);
            mini_fail(&r->c, "only an array or a string can be sliced");
        }
        long long n = b.is_str ? b.slen : b.n;
        long long lo = 0, hi = n;
        if(e->b) lo = mini_to_ll_sat(mini_need_num(r, mini_eval(r, e->b), "a slice bound"));
        if(e->c) hi = mini_to_ll_sat(mini_need_num(r, mini_eval(r, e->c), "a slice bound"));
        if(lo < 0) lo = 0;
        if(lo > n) lo = n;
        if(hi < lo) hi = lo;
        if(hi > n) hi = n;
        if(b.is_str){
            MiniVal sv = mini_strval(b.str + lo, (int)(hi - lo));
            mini_val_free(&b);
            return sv;
        }
        MiniVal v; memset(&v, 0, sizeof(v));
        v.is_arr = 1;
        if(hi > lo){
            mini_arr_reserve(&v, (int)(hi - lo));
            for(long long i = lo; i < hi; i++){
                v.n++;
                mini_arr_put(&v, v.n - 1, mini_arr_get(&b, (int)i));
            }
        }
        mini_val_free(&b);
        return v;
    }
    case MX_UN: {
        uint256_t a = mini_need_num(r, mini_eval(r, e->a), "an operand");
        if(strcmp(e->op, "-") == 0) return mini_num(u256_neg(a));
        if(strcmp(e->op, "+") == 0) return mini_num(a);
        if(strcmp(e->op, "~") == 0) return mini_num(u256_not(a));
        return mini_num(mini_bool(u256_is_zero(a)));
    }
    case MX_BIN: {
        if(strcmp(e->op, "&&") == 0){
            uint256_t a = mini_need_num(r, mini_eval(r, e->a), "an operand");
            if(u256_is_zero(a)) return mini_num(u256_zero());
            uint256_t b = mini_need_num(r, mini_eval(r, e->b), "an operand");
            return mini_num(mini_bool(!u256_is_zero(b)));
        }
        if(strcmp(e->op, "||") == 0){
            uint256_t a = mini_need_num(r, mini_eval(r, e->a), "an operand");
            if(!u256_is_zero(a)) return mini_num(u256_one());
            uint256_t b = mini_need_num(r, mini_eval(r, e->b), "an operand");
            return mini_num(mini_bool(!u256_is_zero(b)));
        }
        MiniVal av = mini_eval(r, e->a);
        MiniVal bv = mini_eval(r, e->b);
        if(av.is_str || bv.is_str) return mini_str_binop(r, e->op, av, bv);
        if(av.is_arr) mini_val_free(&bv);
        uint256_t a = mini_need_num(r, av, "an operand");
        uint256_t b = mini_need_num(r, bv, "an operand");
        return mini_num(mini_binop(r, e->op, a, b));
    }
    }
    mini_fail(&r->c, "bad expression");
    return mini_num(u256_zero());
}

/* 実行した文を 1 つ数える。上限を超えたらエラーにする。 */
static void mini_tick(MiniRun *r){
    if(++r->steps > MINI_MAX_STEPS){
        /* パス 1 の最初の反復で上限に達したら、この呼び出しが前方参照として許した
           名前を「綴り間違いの疑い」として覚える（mini_get がその名前ですぐ止める）。
           axx.py の MiniInterp._tick() と同じ。 */
        if(r->asmb && r->asmb->st.pas == 1 && r->asmb->st.relax_optimistic)
            for(int i = 0; i < r->nfb; i++)
                if(!sv_contains(&r->asmb->st.mini_suspects, r->fb[i]))
                    sv_push(&r->asmb->st.mini_suspects, r->fb[i]);
        mini_fail(&r->c, "mini language ran more than %d statements; "
                  "assuming a runaway loop", MINI_MAX_STEPS);
    }
}

/* 呼ぶ関数を名前で探す。内側の定義から外側へたどる。 */
static MiniFunc *mini_lookup(MiniRun *r, const char *name){
    MiniFunc *f = r->nframes ? r->frames[r->nframes - 1].func : NULL;
    while(f){
        for(int i = 0; i < f->nchildren; i++)
            if(strcmp(f->children[i]->name, name) == 0) return f->children[i];
        f = f->parent;
    }
    for(int i = 0; i < r->asmb->st.funcs.len; i++)
        if(strcmp(r->asmb->st.funcs.data[i]->name, name) == 0)
            return r->asmb->st.funcs.data[i];
    mini_fail(&r->c, "no function named '%s'", name);
    return NULL;
}

static void mini_call_func(MiniRun *r, MiniFunc *f, MiniVal *args, int nargs);

/* `名前[lo:hi] = 値` — lo から hi の手前までを値で置き換える。境界は読み出しの
   `[lo:hi]` と同じく範囲に切り詰め、`lo == hi` ならその位置への挿入になる。値の
   長さが違えば全体の長さが変わる。文字列には文字列を、配列には配列を書く。
   v は消費する。axx.py の MiniInterp._store_slice() と同じ規則である。 */
static void mini_store_slice(MiniRun *r, MStmt *s, MiniVal v){
    int has_lo = s->idx->b != NULL, has_hi = s->idx->c != NULL;
    long long lo = 0, hi = 0;
    if(has_lo){
        MiniVal bv = mini_eval(r, s->idx->b);
        if(bv.is_arr || bv.is_str) mini_val_free(&v);
        lo = mini_to_ll_sat(mini_need_num(r, bv, "a slice bound"));
    }
    if(has_hi){
        MiniVal bv = mini_eval(r, s->idx->c);
        if(bv.is_arr || bv.is_str) mini_val_free(&v);
        hi = mini_to_ll_sat(mini_need_num(r, bv, "a slice bound"));
    }
    MiniBind *b = mini_ref(r, s->name);
    if(!b->v.is_arr && !b->v.is_str){
        mini_val_free(&v);
        mini_fail(&r->c, "'%s' is not an array or a string", s->name);
    }
    long long n = b->v.is_str ? b->v.slen : b->v.n;
    if(!has_lo) lo = 0;
    if(lo < 0) lo = 0;
    if(lo > n) lo = n;
    if(!has_hi) hi = n;
    if(hi < lo) hi = lo;
    if(hi > n) hi = n;
    if(b->v.is_str){
        if(!v.is_str){
            mini_val_free(&v);
            mini_fail(&r->c, "a string slice can only be given a string");
        }
        long long nl = lo + v.slen + (n - hi);
        if(nl > MINI_MAX_ARRAY) mini_val_free(&v);
        mini_need_strlen(r, nl);
        unsigned char *ns = mini_alloc((size_t)nl + 1);
        memcpy(ns, b->v.str, (size_t)lo);
        if(v.slen > 0) memcpy(ns + lo, v.str, (size_t)v.slen);
        memcpy(ns + lo + v.slen, b->v.str + hi, (size_t)(n - hi));
        free(b->v.str);
        b->v.str = ns;
        b->v.slen = (int)nl;
        mini_val_free(&v);
        return;
    }
    if(!v.is_arr){
        mini_val_free(&v);
        mini_fail(&r->c, "an array slice can only be given an array");
    }
    long long nl = lo + v.n + (n - hi);
    if(nl > MINI_MAX_ARRAY){
        mini_val_free(&v);
        mini_fail(&r->c, "array longer than the maximum length %d", MINI_MAX_ARRAY);
    }
    MiniVal na; memset(&na, 0, sizeof(na));
    na.is_arr = 1;
    mini_arr_reserve(&na, nl > 0 ? (int)nl : 1);
    for(long long i = 0; i < lo; i++){ na.n++; mini_arr_put(&na, na.n - 1, mini_arr_get(&b->v, (int)i)); }
    for(int i = 0; i < v.n; i++){ na.n++; mini_arr_put(&na, na.n - 1, mini_arr_get(&v, i)); }
    for(long long i = hi; i < n; i++){ na.n++; mini_arr_put(&na, na.n - 1, mini_arr_get(&b->v, (int)i)); }
    mini_val_free(&v);
    mini_val_free(&b->v);
    b->v = na;
}

/* 変数か配列要素へ代入する。配列は必要なら伸ばす。 */
static void mini_store(MiniRun *r, MStmt *s, MiniVal v){
    if(!s->idx){ mini_set(r, s->name, v); return; }
    if(s->idx->k == MX_SLICE && !s->idx->a){ mini_store_slice(r, s, v); return; }
    uint256_t iv = mini_need_num(r, mini_eval(r, s->idx), "an index");
    if(u256_is_neg256(iv)){
        char nb[96]; u256_to_pydec(iv, nb, sizeof(nb));
        mini_val_free(&v);
        mini_fail(&r->c, "negative index %s in assignment", nb);
    }
    if(u256_nonneg_gt_i64(iv, (int64_t)MINI_MAX_ARRAY - 1)){
        char nb[96]; u256_to_pydec(iv, nb, sizeof(nb));
        mini_val_free(&v);
        mini_fail(&r->c, "array index %s exceeds the maximum length %d",
                  nb, MINI_MAX_ARRAY);
    }
    long long i = mini_to_ll(r, iv);
    if(v.is_arr){
        mini_val_free(&v);
        mini_fail(&r->c, "an array element must be a number or a string, not an array");
    }
    MiniBind *b = mini_ref(r, s->name);
    if(b->v.is_str){
        /* 文字列の 1 バイトを書き換える。値は 0〜255 の整数か 1 バイトの文字列で、
           末尾より先なら NUL で埋めて伸ばす。axx.py の MiniInterp._store() と同じ規則。 */
        int ok = 1;
        unsigned char byte = 0;
        if(v.is_str){
            if(v.slen == 1) byte = v.str[0]; else ok = 0;
        } else if(u256_is_neg256(v.num) || u256_nonneg_gt_i64(v.num, 255)){
            ok = 0;
        } else {
            byte = (unsigned char)u256_to_u64(v.num);
        }
        mini_val_free(&v);
        if(!ok)
            mini_fail(&r->c, "a byte of a string must be a value from 0 to 255 or "
                      "a one-byte string");
        if(i >= b->v.slen){
            unsigned char *ns = realloc(b->v.str, (size_t)i + 2);
            if(!ns){ perror("realloc"); exit(1); }
            memset(ns + b->v.slen, 0, (size_t)(i + 2 - b->v.slen));
            b->v.str = ns;
            b->v.slen = (int)i + 1;
        }
        b->v.str[i] = byte;
        return;
    }
    if(!b->v.is_arr){
        mini_val_free(&v);
        mini_fail(&r->c, "'%s' is not an array or a string", s->name);
    }
    if(i >= b->v.n){
        mini_arr_reserve(&b->v, (int)i + 1);
        for(int q = b->v.n; q <= (int)i; q++) b->v.arr[q] = u256_zero();
        b->v.n = (int)i + 1;
    }
    mini_arr_put(&b->v, (int)i, v);
}

/* 返り値を捨てる。 */
static void mini_drop_ret(MiniRun *r){
    if(r->has_ret){ mini_val_free(&r->retval); r->has_ret = 0; }
}

/* 文 1 個を実行する。 */
static void mini_exec(MiniRun *r, MStmt *s){
    mini_at(r, s);
    mini_tick(r);
    switch(s->k){
    case MS_ASSIGN:
        mini_store(r, s, mini_eval(r, s->val));
        return;
    case MS_EMIT:
        for(int i = 0; i < s->nargs; i++){
            MiniVal ev = mini_eval(r, s->args[i]);
            if(ev.is_arr){
                /* 配列は要素ごとに出し、文字列の要素は 1 バイト 1 ワード。
                   axx.py の MiniInterp._exec() の 'emit' と同じ。 */
                for(int k = 0; k < ev.n; k++){
                    int ns = (ev.astr && ev.astr[k]) ? ev.alen[k] : 1;
                    for(int q = 0; q < ns; q++){
                        if(r->out.len >= MINI_MAX_EMIT){
                            mini_val_free(&ev);
                            mini_fail(&r->c, "'.emit' produced more than %d words",
                                      MINI_MAX_EMIT);
                        }
                        iv_push(&r->out, (ev.astr && ev.astr[k])
                                         ? u256_from_u64(ev.astr[k][q]) : ev.arr[k]);
                    }
                }
                mini_val_free(&ev);
                continue;
            }
            if(ev.is_str){
                /* 文字列は 1 バイトを 1 ワードとして出す。 */
                for(int q = 0; q < ev.slen; q++){
                    if(r->out.len >= MINI_MAX_EMIT){
                        mini_val_free(&ev);
                        mini_fail(&r->c, "'.emit' produced more than %d words",
                                  MINI_MAX_EMIT);
                    }
                    iv_push(&r->out, u256_from_u64(ev.str[q]));
                }
                mini_val_free(&ev);
                continue;
            }
            uint256_t x = ev.num;
            if(r->out.len >= MINI_MAX_EMIT)
                mini_fail(&r->c, "'.emit' produced more than %d words", MINI_MAX_EMIT);
            iv_push(&r->out, x);
        }
        return;
    case MS_RAISE: {
        MiniVal ev = mini_eval(r, s->val);
        if(ev.is_arr){
            mini_val_free(&ev);
            mini_fail(&r->c, "'.raise' needs a number, not an array");
        }
        if(ev.is_str){
            mini_val_free(&ev);
            mini_fail(&r->c, "'.raise' needs a number, not a string");
        }
        if(r->asmb && should_report_errors(&r->asmb->st)
           && !r->asmb->st.pass1_size_mode){
            AsmState *st = &r->asmb->st;
            int64_t tc = u256_to_i64(ev.num);
            fprintf(stderr, "Line %d Error code %lld ", (int)st->ln, (long long)tc);
            if(tc >= 0 && tc < st->errors.len)
                fprintf(stderr, "%s", st->errors.data[tc]);
            fprintf(stderr, ": \n");
            st->had_error = 1;
        }
        return;
    }
    case MS_ECHO: {
        int show = r->asmb && should_report_errors(&r->asmb->st)
                   && !r->asmb->st.pass1_size_mode;
        char **items = s->nargs ? mini_alloc((size_t)s->nargs * sizeof(char*)) : NULL;
        for(int i = 0; i < s->nargs; i++){
            MiniVal ev = mini_eval(r, s->args[i]);
            if(show) items[i] = mini_echo_text(&ev);
            mini_val_free(&ev);
        }
        if(show) m_echo_write(items, s->nargs);
        for(int i = 0; i < s->nargs; i++) free(items[i]);
        free(items);
        return;
    }
    case MS_CALL: {
        MiniFunc *f = mini_lookup(r, s->name);
        MiniVal *vals = s->nargs ? mini_alloc((size_t)s->nargs * sizeof(MiniVal)) : NULL;
        for(int i = 0; i < s->nargs; i++) vals[i] = mini_eval(r, s->args[i]);
        mini_at(r, s);
        mini_call_func(r, f, vals, s->nargs);
        for(int i = 0; i < s->nargs; i++) mini_val_free(&vals[i]);
        free(vals);
        mini_drop_ret(r);
        return;
    }
    case MS_CALLASSIGN: {
        MiniFunc *f = mini_lookup(r, s->fname);
        MiniVal *vals = s->nargs ? mini_alloc((size_t)s->nargs * sizeof(MiniVal)) : NULL;
        for(int i = 0; i < s->nargs; i++) vals[i] = mini_eval(r, s->args[i]);
        mini_at(r, s);
        mini_call_func(r, f, vals, s->nargs);
        for(int i = 0; i < s->nargs; i++) mini_val_free(&vals[i]);
        free(vals);
        mini_at(r, s);
        if(!r->has_ret)
            mini_fail(&r->c, "'%s' returned no value; give it a "
                      "'.return <expression>'", s->fname);
        MiniVal ret = r->retval;
        memset(&r->retval, 0, sizeof(r->retval));
        r->has_ret = 0;
        mini_store(r, s, ret);
        return;
    }
    case MS_BREAK:
        r->loopctl = 1;
        return;
    case MS_CONTINUE:
        r->loopctl = 2;
        return;
    case MS_RETURN:
        mini_drop_ret(r);
        if(s->val){
            r->retval = mini_eval(r, s->val);
            r->has_ret = 1;
        }
        r->returning = 1;
        return;
    case MS_NONLOCAL: {
        MiniFrame *top = &r->frames[r->nframes - 1];
        for(int i = 0; i < s->nnames; i++){
            if(mini_find(top, s->names[i]))
                mini_fail(&r->c, "'%s' is already local; '.nonlocal' must come "
                          "before it is set", s->names[i]);
            if(top->nnonloc >= top->cnonloc){
                top->cnonloc = top->cnonloc ? top->cnonloc * 2 : 8;
                top->nonloc = realloc(top->nonloc, (size_t)top->cnonloc * sizeof(char*));
                if(!top->nonloc){ perror("realloc"); exit(1); }
            }
            top->nonloc[top->nnonloc++] = mini_strdup(s->names[i]);
        }
        return;
    }
    case MS_IF: {
        uint256_t cv = mini_need_num(r, mini_eval(r, s->val), "a condition");
        if(!u256_is_zero(cv)) mini_exec_block(r, s->body, s->nbody);
        else mini_exec_block(r, s->body2, s->nbody2);
        return;
    }
    case MS_WHILE:
        for(;;){
            mini_at(r, s);
            uint256_t cv = mini_need_num(r, mini_eval(r, s->val), "a condition");
            if(u256_is_zero(cv)) break;
            mini_tick(r);
            mini_exec_block(r, s->body, s->nbody);
            if(r->returning) return;
            if(r->loopctl){ int lc = r->loopctl; r->loopctl = 0; if(lc == 1) break; }
        }
        return;
    case MS_FOR: {
        if(s->val){
            MiniVal arr = mini_eval(r, s->val);
            if(!arr.is_arr){
                mini_val_free(&arr);
                mini_fail(&r->c, "'.for %s in' needs an array", s->name);
            }
            /* 回り始める前に写しを取る。本体で配列を書き換えても回る順番は変わらない。 */
            for(int i = 0; i < arr.n; i++){
                mini_at(r, s);
                mini_tick(r);
                mini_set(r, s->name, mini_arr_get(&arr, i));
                mini_exec_block(r, s->body, s->nbody);
                if(r->returning) break;
                if(r->loopctl){ int lc = r->loopctl; r->loopctl = 0; if(lc == 1) break; }
            }
            mini_val_free(&arr);
            return;
        }
        uint256_t v[3];
        v[0] = v[1] = v[2] = u256_zero();
        for(int i = 0; i < s->nargs; i++)
            v[i] = mini_need_num(r, mini_eval(r, s->args[i]), "a range bound");
        uint256_t start, stop, step;
        if(s->nargs == 1){ start = u256_zero(); stop = v[0]; step = u256_one(); }
        else if(s->nargs == 2){ start = v[0]; stop = v[1]; step = u256_one(); }
        else { start = v[0]; stop = v[1]; step = v[2]; }
        if(u256_is_zero(step)) mini_fail(&r->c, "range() step must not be zero");
        int up = !u256_is_neg256(step);
        uint256_t i = start;
        while(up ? u256_lt_signed(i, stop) : u256_gt_signed(i, stop)){
            mini_at(r, s);
            mini_tick(r);
            mini_set(r, s->name, mini_num(i));
            mini_exec_block(r, s->body, s->nbody);
            if(r->returning) return;
            if(r->loopctl){ int lc = r->loopctl; r->loopctl = 0; if(lc == 1) return; }
            uint256_t nx = u256_add(i, step);
            if(up ? (!u256_is_neg256(i) && u256_is_neg256(nx))
                  : (u256_is_neg256(i) && !u256_is_neg256(nx)))
                return;
            i = nx;
        }
        return;
    }
    }
}

/* 文の並びを順に実行する。 */
static void mini_exec_block(MiniRun *r, MStmt **body, int n){
    for(int i = 0; i < n; i++){
        mini_exec(r, body[i]);
        if(r->returning || r->loopctl) return;
    }
}

/* スコープを空にする。 */
static void mini_frame_clear(MiniFrame *fr){
    for(int i = 0; i < fr->nvars; i++){
        free(fr->vars[i].name);
        mini_val_free(&fr->vars[i].v);
    }
    free(fr->vars);
    for(int i = 0; i < fr->nnonloc; i++) free(fr->nonloc[i]);
    free(fr->nonloc);
    memset(fr, 0, sizeof(*fr));
}

/* 関数を 1 回呼ぶ。新しいスコープを積み、入れ子の深さを検査する。 */
static void mini_call_func(MiniRun *r, MiniFunc *f, MiniVal *args, int nargs){
    if(r->nframes >= MINI_MAX_DEPTH)
        mini_fail(&r->c, "call nesting deeper than %d; assuming runaway recursion",
                  MINI_MAX_DEPTH);
    if(nargs != f->nparams)
        mini_fail(&r->c, "'%s' takes %d argument(s), got %d", f->name, f->nparams, nargs);
    if(r->nframes >= r->cframes){
        r->cframes = r->cframes ? r->cframes * 2 : 16;
        r->frames = realloc(r->frames, (size_t)r->cframes * sizeof(MiniFrame));
        if(!r->frames){ perror("realloc"); exit(1); }
    }
    mini_drop_ret(r);
    MiniFrame *fr = &r->frames[r->nframes++];
    memset(fr, 0, sizeof(*fr));
    fr->func = f;
    for(int i = 0; i < nargs; i++){
        MiniBind *b = mini_bind_new(fr, f->params[i]);
        b->v = mini_val_copy(&args[i]);
    }
    mini_exec_block(r, f->body, f->nbody);
    r->returning = 0;
    r->loopctl = 0;
    mini_frame_clear(&r->frames[r->nframes - 1]);
    r->nframes--;
}


/* 式の構文木を解放する。 */
static void mini_expr_free(MExpr *e){
    if(!e) return;
    mini_expr_free(e->a); mini_expr_free(e->b); mini_expr_free(e->c);
    for(int i = 0; i < e->nitems; i++) mini_expr_free(e->items[i]);
    free(e->items);
    free(e->name);
    free(e);
}

/* 文の構文木を解放する。 */
static void mini_stmt_free(MStmt *s){
    if(!s) return;
    mini_expr_free(s->idx);
    mini_expr_free(s->val);
    for(int i = 0; i < s->nargs; i++) mini_expr_free(s->args[i]);
    free(s->args);
    for(int i = 0; i < s->nbody; i++) mini_stmt_free(s->body[i]);
    free(s->body);
    for(int i = 0; i < s->nbody2; i++) mini_stmt_free(s->body2[i]);
    free(s->body2);
    for(int i = 0; i < s->nnames; i++) free(s->names[i]);
    free(s->names);
    free(s->name);
    free(s->fname);
    free(s);
}

/* 関数定義を解放する。 */
static void mini_func_free(MiniFunc *f){
    if(!f) return;
    for(int i = 0; i < f->nchildren; i++) mini_func_free(f->children[i]);
    free(f->children);
    for(int i = 0; i < f->nbody; i++) mini_stmt_free(f->body[i]);
    free(f->body);
    for(int i = 0; i < f->nlines; i++){ free(f->lines[i]); free(f->lfiles[i]); }
    free(f->lines); free(f->lfiles); free(f->llines);
    for(int i = 0; i < f->nparams; i++) free(f->params[i]);
    free(f->params);
    free(f->name); free(f->file);
    free(f);
}

/* 関数定義の並びを解放する。 */
static void mfv_free(MiniFuncVec *v){
    for(int i = 0; i < v->len; i++) mini_func_free(v->data[i]);
    free(v->data);
    mfv_init(v);
}

/* 関数定義を名前で引く。 */
static MiniFunc *mfv_find(MiniFuncVec *v, const char *name){
    for(int i = 0; i < v->len; i++)
        if(strcmp(v->data[i]->name, name) == 0) return v->data[i];
    return NULL;
}

static MiniFunc *mini_func_new(Assembler *asmb, MiniFunc *parent, const char *name,
                               const char *file, int line){
    MiniFunc *f = mini_alloc(sizeof(MiniFunc));
    f->name = mini_strdup(name);
    f->file = mini_strdup(file);
    f->line = line;
    f->parent = parent;
    if(parent){
        for(int i = 0; i < parent->nchildren; i++){
            if(strcmp(parent->children[i]->name, name) == 0){
                mini_func_free(parent->children[i]);
                parent->children[i] = f;
                return f;
            }
        }
        if(parent->nchildren >= parent->cchildren){
            parent->cchildren = parent->cchildren ? parent->cchildren * 2 : 4;
            parent->children = realloc(parent->children,
                                       (size_t)parent->cchildren * sizeof(MiniFunc*));
            if(!parent->children){ perror("realloc"); exit(1); }
        }
        parent->children[parent->nchildren++] = f;
        return f;
    }
    {
        MiniFuncVec *v = &asmb->st.funcs;
        for(int i = 0; i < v->len; i++){
            if(strcmp(v->data[i]->name, name) == 0){
                mini_func_free(v->data[i]);
                v->data[i] = f;
                return f;
            }
        }
        if(v->len >= v->cap){
            v->cap = v->cap ? v->cap * 2 : 8;
            v->data = realloc(v->data, (size_t)v->cap * sizeof(MiniFunc*));
            if(!v->data){ perror("realloc"); exit(1); }
        }
        v->data[v->len++] = f;
    }
    return f;
}

/* 関数に引数名を 1 つ足す。 */
static void mini_func_addparam(MiniFunc *f, const char *p){
    f->params = realloc(f->params, (size_t)(f->nparams + 1) * sizeof(char*));
    if(!f->params){ perror("realloc"); exit(1); }
    f->params[f->nparams++] = mini_strdup(p);
}

/* 関数本体に行を 1 つ足す。 */
static void mini_func_addline(MiniFunc *f, const char *text, const char *file, int line){
    if(f->nlines >= f->clines){
        f->clines = f->clines ? f->clines * 2 : 16;
        f->lines  = realloc(f->lines,  (size_t)f->clines * sizeof(char*));
        f->lfiles = realloc(f->lfiles, (size_t)f->clines * sizeof(char*));
        f->llines = realloc(f->llines, (size_t)f->clines * sizeof(int));
        if(!f->lines || !f->lfiles || !f->llines){ perror("realloc"); exit(1); }
    }
    f->lines[f->nlines]  = mini_strdup(text);
    f->lfiles[f->nlines] = mini_strdup(file);
    f->llines[f->nlines] = line;
    f->nlines++;
}

/* 集めた関数すべてを構文木にする。 */
static void mini_compile_all(MiniFunc **v, int n){
    for(int i = 0; i < n; i++){
        char *err = NULL;
        if(!mini_compile_func(v[i], &err)){
            axx_diagf(1, 0, " error - %s\n", err ? err : "?");
            free(err);
        }
        mini_compile_all(v[i]->children, v[i]->nchildren);
    }
}


/* s[k] の `"` から始まる文字列リテラルの次の位置を返す。閉じていなければ
   行末の位置。axx.py の ObjectGenerator._mini_skip_str() と同じ。 */
static int mini_skip_str(const char *s, int k, int len){
    k++;
    while(k < len && s[k]){
        if(s[k] == '\\' && k + 1 < len){ k += 2; continue; }
        if(s[k] == '"') return k + 1;
        k++;
    }
    return k;
}

/* `"..."` と書かれた引数を文字列として読む。逃げ記号はミニ言語の文字列と
   同じ 4 つ。失敗したら *ok を 0 にして診断する。
   axx.py の ObjectGenerator._mini_arg_str() と同じ規則である。 */
static MiniVal mini_arg_str(const char *t, int a, int *out_i, int *ok,
                            const char *name, int quiet){
    int len = (int)strlen(t);
    char *buf = mini_alloc((size_t)len + 1);
    int n = 0, k = a + 1;
    *ok = 0;
    for(;;){
        if(k >= len){
            if(!quiet)
                axx_diagf(1, 0, " error - '.call %s': unterminated string in the "
                           "argument list.\n", name);
            free(buf);
            *out_i = len;
            return mini_num(u256_zero());
        }
        char c = t[k];
        if(c == '"') break;
        if(c == '\\'){
            char e = (k + 1 < len) ? t[k+1] : '\0';
            char r;
            if(e == '\\')      r = '\\';
            else if(e == '"')  r = '"';
            else if(e == 'n')  r = '\n';
            else if(e == 't')  r = '\t';
            else {
                if(!quiet)
                    axx_diagf(1, 0, " error - '.call %s': unknown escape in a string "
                               "in the argument list.\n", name);
                free(buf);
                *out_i = len;
                return mini_num(u256_zero());
            }
            buf[n++] = r;
            k += 2;
            continue;
        }
        buf[n++] = c;
        k++;
    }
    MiniVal v = mini_strval(buf, n);
    free(buf);
    *out_i = k + 1;
    *ok = 1;
    return v;
}

/* t[a] から `.exp(` が始まるか。`.expx` のような別の名前は除く。 */
static int mini_is_exp(const char *t, int a){
    static const char *w = ".EXP";
    for(int i = 0; i < 4; i++) if(axx_upper_char(t[a+i]) != w[i]) return 0;
    int k = a + 4;
    if(isalnum((unsigned char)t[k]) || t[k] == '_') return 0;
    k = axx_skipspc(t, k);
    return t[k] == '(';
}

/* `.exp(変数)` と書かれた引数を、その変数が捕捉した綴りの文字列にする。綴りは
   `{{.exp(変数)}}` が出すものと同じ。
   axx.py の ObjectGenerator._mini_arg_exp() と同じ規則である。 */
static MiniVal mini_arg_exp(Assembler *asmb, const char *t, int a, int *out_i, int *ok,
                            const char *name, int quiet){
    AsmState *st = &asmb->st;
    int len = (int)strlen(t);
    int k = axx_skipspc(t, a + 4) + 1;
    const char *cp = strchr(t + k, ')');
    *ok = 0;
    *out_i = len;
    int b = k, e = cp ? (int)(cp - t) : k;
    while(b < e && (t[b] == ' ' || t[b] == '\t')) b++;
    while(e > b && (t[e-1] == ' ' || t[e-1] == '\t')) e--;
    int nl = e - b;
    if(!cp || nl == 0 || var_name_len(t + b) != nl){
        if(!quiet)
            axx_diagf(1, 0, " error - '.call %s': '.exp' needs '.exp(variable)'.\n", name);
        return mini_num(u256_zero());
    }
    char nm[512];
    if(nl >= (int)sizeof(nm)) nl = (int)sizeof(nm) - 1;
    memcpy(nm, t + b, (size_t)nl); nm[nl] = 0;
    int slot = var_slot(nm, nl, 0);
    if(slot < 0){
        if(!quiet)
            axx_diagf(1, 0, " error - '%s' is not a pattern variable; '.exp(%s)' "
                       "needs '%s' captured in the instruction field.\n", nm, nm, nm);
        return mini_num(u256_zero());
    }
    int off = st->vars[slot].text_off;
    const char *txt = (off < 0 || off >= st->captext_len) ? "" : st->captext + off;
    *ok = 1;
    *out_i = (int)(cp - t) + 1;
    return mini_strval(txt, (int)strlen(txt));
}

/* t[a] からの引数が文字列シンボルの名前 1 つだけなら、その値を返して *out_i を
   次の位置にする。`.setsym::名前::"..."` の名前で、後ろが `,` か引数の終わりの
   ときだけ当たる。式の一部（`msg+1` など）は今までどおり式として読む。
   axx.py の ObjectGenerator._mini_strsym_at() と同じ規則である。 */
/* t[a] からの引数が名前 1 つだけなら、その名前を大文字で key に置き、次の位置を
   返す。後ろが `,` か引数の終わりでなければ -1。
   axx.py の ObjectGenerator._mini_symname_at() と同じ規則である。 */
static int mini_symname_at(const char *t, int a, char *key, size_t ksz){
    int k = a;
    while(isalnum((unsigned char)t[k]) || t[k] == '_') k++;
    if(k == a) return -1;
    int e = axx_skipspc(t, k);
    if(t[e] && t[e] != ',') return -1;
    int n = k - a;
    if(n >= (int)ksz) return -1;
    for(int i = 0; i < n; i++) key[i] = (char)axx_upper_char(t[a+i]);
    key[n] = 0;
    return e;
}

static const char *mini_strsym_at(AsmState *st, const char *t, int a, int *out_i){
    char key[512];
    int e = mini_symname_at(t, a, key, sizeof(key));
    if(e < 0) return NULL;
    const char *sv = strsym_get(st, key);
    if(sv) *out_i = e;
    return sv;
}

static MiniVal mini_arg_one(Assembler *asmb, char *t, int a, int *out_i, int *ok,
                            const char *name, int quiet, int in_array);

/* 配列シンボル（`.setsym::名前::[...]`）を引数の配列にする。数の項目は整数、
   `"..."` と裸の名前の項目は文字列（`{{名前[i]}}` が出すもの）で、文字列は
   `"..."` と直接書いたのと同じに逃げ記号を開く。失敗したら *ok を 0 にする。
   axx.py の ObjectGenerator._mini_arrsym_value() と同じ規則である。 */
static MiniVal mini_arrsym_value(const struct ArrSym *ar, int *ok, const char *name,
                                 int quiet){
    MiniVal v; memset(&v, 0, sizeof(v));
    v.is_arr = 1;
    *ok = 0;
    for(int k = 0; k < ar->len; k++){
        MiniVal e;
        if(ar->items[k].is_str){
            const char *sv = ar->items[k].s ? ar->items[k].s : "";
            size_t svl = strlen(sv);
            char *q = mini_alloc(svl + 3);
            q[0] = '"'; memcpy(q + 1, sv, svl); q[svl + 1] = '"'; q[svl + 2] = 0;
            int sio, eok;
            e = mini_arg_str(q, 0, &sio, &eok, name, quiet);
            free(q);
            if(!eok){ mini_val_free(&e); mini_val_free(&v); return v; }
        } else {
            uint256_t x = ar->items[k].v;
            if(u256_is_undef_derived(x)) x = u256_zero();
            e = mini_num(x);
        }
        mini_arr_reserve(&v, v.n + 1);
        v.n++;
        mini_arr_put(&v, v.n - 1, e);
    }
    *ok = 1;
    return v;
}

/* `[e1, e2, ...]` と書かれた引数を配列として評価する。要素は整数か文字列で、
   書き方は引数 1 つと同じ（mini_arg_one）。
   axx.py の ObjectGenerator._mini_arg_array() と同じ規則である。 */
static MiniVal mini_arg_array(Assembler *asmb, char *t, int a, int *out_i, int *ok,
                              const char *name, int quiet){
    MiniVal v; memset(&v, 0, sizeof(v));
    v.is_arr = 1;
    *ok = 0;
    int len = (int)strlen(t);
    int depth = 0, k = a;
    while(k < len){
        if(t[k] == '"'){ k = mini_skip_str(t, k, len); continue; }
        if(t[k] == '(' || t[k] == '[') depth++;
        else if(t[k] == ')' || t[k] == ']'){ depth--; if(depth == 0) break; }
        k++;
    }
    if(depth != 0 || k >= len || t[k] != ']'){
        if(!quiet)
            axx_diagf(1, 0, " error - '.call %s': unbalanced '[' in the "
                       "argument list.\n", name);
        *out_i = len;
        return v;
    }
    t[k] = 0;
    int i = a + 1;
    while(1){
        i = axx_skipspc(t, i);
        if(!t[i]) break;
        if(t[i] == ','){ i++; continue; }
        int io, eok;
        MiniVal e = mini_arg_one(asmb, t, i, &io, &eok, name, quiet, 1);
        if(!eok){
            mini_val_free(&e);
            mini_val_free(&v);
            t[k] = ']';
            *out_i = len;
            return v;
        }
        i = io;
        mini_arr_reserve(&v, v.n + 1);
        v.n++;
        mini_arr_put(&v, v.n - 1, e);
        i = axx_skipspc(t, i);
        if(t[i] == ','){ i++; continue; }
        break;
    }
    t[k] = ']';
    *out_i = k + 1;
    *ok = 1;
    return v;
}

/* `.call` の引数を 1 つ読む。`[...]` は配列、`"..."` は文字列、`.exp(変数)` は
   捕捉した綴り、文字列シンボルの名前 1 つはその文字列、それ以外はパターン層の
   式。配列の要素も同じ規則で読むが、配列の中に配列は書けない。失敗したら
   *ok を 0 にして診断する。
   axx.py の ObjectGenerator._mini_arg_one() と同じ規則である。 */
static MiniVal mini_arg_one(Assembler *asmb, char *t, int a, int *out_i, int *ok,
                            const char *name, int quiet, int in_array){
    AsmState *st = &asmb->st;
    *ok = 0;
    if(t[a] == '['){
        if(in_array){
            if(!quiet)
                axx_diagf(1, 0, " error - '.call %s': an array element cannot be "
                           "an array.\n", name);
            *out_i = (int)strlen(t);
            return mini_num(u256_zero());
        }
        return mini_arg_array(asmb, t, a, out_i, ok, name, quiet);
    }
    if(t[a] == '"') return mini_arg_str(t, a, out_i, ok, name, quiet);
    if(mini_is_exp(t, a)) return mini_arg_exp(asmb, t, a, out_i, ok, name, quiet);
    int e;
    const char *sv = mini_strsym_at(st, t, a, &e);
    if(sv){
        /* `.call f("…")` と書いたのと同じに読む。 */
        int sio;
        size_t svl = strlen(sv);
        char *q = mini_alloc(svl + 3);
        q[0] = '"'; memcpy(q + 1, sv, svl); q[svl + 1] = '"'; q[svl + 2] = 0;
        MiniVal v = mini_arg_str(q, 0, &sio, ok, name, quiet);
        free(q);
        *out_i = e;
        return v;
    }
    {
        char key[512];
        int e2 = mini_symname_at(t, a, key, sizeof(key));
        struct ArrSym *ar = e2 >= 0 ? arrsym_get(st, key) : NULL;
        if(ar){
            if(in_array){
                if(!quiet)
                    axx_diagf(1, 0, " error - '.call %s': an array element cannot be "
                               "an array.\n", name);
                *out_i = (int)strlen(t);
                return mini_num(u256_zero());
            }
            *out_i = e2;
            return mini_arrsym_value(ar, ok, name, quiet);
        }
    }
    int io;
    uint256_t v = expr_expression_pat(asmb, t, a, &io);
    if(u256_is_undef_derived(v)) v = u256_zero();
    *out_i = io;
    *ok = 1;
    return mini_num(v);
}

/* `.call 名前(引数, ...)` を実行し、生まれたワード列を積む。引数は呼び出し側の
   パターン式なので、ここでパターン変数が解決されてから関数へ渡る。 */
static int mini_call_binary(Assembler *asmb, const char *s, int idx_in, IntVec *objl){
    volatile int idx = idx_in;
    AsmState *st = &asmb->st;
    int slen = expr_slen(s);
    int quiet = st->pass1_size_mode;

    idx += 5;
    idx = axx_skipspc(s, idx);
    int j = idx;
    while(j < slen && (isalnum((unsigned char)s[j]) || s[j] == '_')) j++;
    int namelen = j - idx;
    if(namelen <= 0){
        if(!quiet) axx_diagf(1, 0, " error - '.call' needs 'name(argument, ...)'.\n");
        return slen;
    }
    char namestack[512];
    char *name = namestack;
    char *name_heap = NULL;
    if((size_t)namelen >= sizeof(namestack)){
        name_heap = malloc((size_t)namelen + 1);
        if(!name_heap){ perror("malloc"); exit(1); }
        name = name_heap;
    }
    memcpy(name, s + idx, (size_t)namelen); name[namelen] = 0;
    idx = axx_skipspc(s, j);
    if(idx >= slen || s[idx] != '('){
        if(!quiet) axx_diagf(1, 0, " error - '.call' needs 'name(argument, ...)'.\n");
        free(name_heap);
        return slen;
    }
    int depth = 0, k = idx;
    while(k < slen){
        if(s[k] == '"'){ k = mini_skip_str(s, k, slen); continue; }
        if(s[k] == '(' || s[k] == '[') depth++;
        else if(s[k] == ')' || s[k] == ']'){ depth--; if(depth == 0) break; }
        k++;
    }
    if(depth != 0 || k >= slen){
        if(!quiet) axx_diagf(1, 0, " error - '.call %s': unbalanced parentheses.\n", name);
        free(name_heap);
        return slen;
    }
    int arglen = k - idx - 1;
    char *argtext = mini_alloc((size_t)arglen + 2);
    memcpy(argtext, s + idx + 1, (size_t)arglen);
    argtext[arglen] = 0;
    idx = k + 1;

    MiniFunc *f = mfv_find(&st->funcs, name);
    if(!f){
        if(!quiet)
            axx_diagf(1, 0, " error - '.call': no function named '%s' (define it with "
                       "'.func::%s:: ... .endfunc').\n", name, name);
        free(argtext);
        free(name_heap);
        return idx;
    }

    MiniVal *args = NULL;
    int nargs = 0, cargs = 0;
    int a = 0, alen = (int)strlen(argtext);
    while(1){
        a = axx_skipspc(argtext, a);
        if(a >= alen || !argtext[a]) break;
        if(argtext[a] == ','){ a++; continue; }
        int io, aok;
        MiniVal av = mini_arg_one(asmb, argtext, a, &io, &aok, name, quiet, 0);
        if(!aok){
            mini_val_free(&av);
            for(int i = 0; i < nargs; i++) mini_val_free(&args[i]);
            free(args);
            free(argtext);
            free(name_heap);
            return idx;
        }
        a = io;
        if(nargs >= cargs){
            cargs = cargs ? cargs * 2 : 8;
            args = realloc(args, (size_t)cargs * sizeof(MiniVal));
            if(!args){ perror("realloc"); exit(1); }
        }
        args[nargs++] = av;
        a = axx_skipspc(argtext, a);
        if(a < alen && argtext[a] == ','){ a++; continue; }
        break;
    }
    free(argtext);

    MiniRun r;
    memset(&r, 0, sizeof(r));
    r.asmb = asmb;
    iv_init(&r.out);
    r.c.file = f->file;
    r.c.line = f->line;
    r.c.jb_active = 1;
    if(setjmp(r.c.jb) == 0){
        mini_call_func(&r, f, args, nargs);
        for(int i = 0; i < r.out.len; i++) iv_push(objl, r.out.data[i]);
        if(r.has_ret){
            /* 配列は要素ごとに、文字列の要素は 1 バイト 1 ワードで出す。 */
            if(r.retval.is_arr)
                for(int i = 0; i < r.retval.n; i++){
                    if(r.retval.astr && r.retval.astr[i])
                        for(int q = 0; q < r.retval.alen[i]; q++)
                            iv_push(objl, u256_from_u64(r.retval.astr[i][q]));
                    else
                        iv_push(objl, r.retval.arr[i]);
                }
            else if(r.retval.is_str)
                for(int i = 0; i < r.retval.slen; i++)
                    iv_push(objl, u256_from_u64(r.retval.str[i]));
            else
                iv_push(objl, r.retval.num);
        }
    } else {
        if(!quiet) axx_diagf(1, 0, " error - %s\n", r.c.err ? r.c.err : "?");
    }
    for(int i = 0; i < r.nframes; i++) mini_frame_clear(&r.frames[i]);
    free(r.frames);
    free(r.fb);
    free(r.c.err);
    mini_drop_ret(&r);
    free(r.out.data);
    for(int i = 0; i < nargs; i++) mini_val_free(&args[i]);
    free(args);
    free(name_heap);
    return idx;
}

/* パターン欄の前後の空白を落とす。 */
static char *pat_trim(char *s){
    char *p = s + axx_skipspc(s, 0);
    size_t n = strlen(p);
    while(n > 0 && isspace((unsigned char)p[n-1])) p[--n] = '\0';
    return p;
}

static int parse_func_header(const char *l, char *name, size_t nsz,
                             char *params, size_t psz, int npmax, int *np,
                             char *errbuf, size_t esz){
    name[0] = '\0';
    *np = 0;
    errbuf[0] = '\0';

    int b = axx_skipspc(l, 0);
    const char *t = l + b;
    int tlen = (int)strlen(t);
    while(tlen > 0 && isspace((unsigned char)t[tlen-1])) tlen--;

    int i = 1;
    while(i < tlen && (isalnum((unsigned char)t[i]) || t[i]=='_')) i++;
    i = axx_skipspc(t, i);

    if(t[i]==':' && t[i+1]==':'){
        size_t hsz = (size_t)tlen + 1;
        char *hbuf = malloc(3 * hsz);
        if(!hbuf){ perror("malloc"); exit(1); }
        char *hf[3];
        for(int q=0;q<3;q++){ hf[q] = hbuf + (size_t)q*hsz; hf[q][0] = '\0'; }
        int hn = 0, hi = 0;
        while(1){
            hi = axx_get_params1(t, hi, hf[hn], hsz);
            hn++;
            if(hi >= tlen || hn >= 3) break;
        }
        const char *nm = (hn > 1) ? pat_trim(hf[1]) : "";
        snprintf(name, nsz, "%s", nm);
        if(hn > 2){
            char *tok = strtok(hf[2], ",");
            while(tok){
                char *pn = pat_trim(tok);
                if(pn[0]){
                    if(*np >= npmax){
                        snprintf(errbuf, esz, " error - '.func': more than %d parameters.\n", npmax);
                        free(hbuf);
                        return 1;
                    }
                    snprintf(params + (size_t)(*np)*psz, psz, "%s", pn);
                    (*np)++;
                }
                tok = strtok(NULL, ",");
            }
        }
        free(hbuf);
        return 0;
    }

    int j = i;
    while(j < tlen && (isalnum((unsigned char)t[j]) || t[j]=='_')) j++;
    if((size_t)(j - i) >= nsz){
        snprintf(errbuf, esz, " error - '.func': name is too long.\n");
        return 1;
    }
    memcpy(name, t + i, (size_t)(j - i));
    name[j - i] = '\0';

    int k = axx_skipspc(t, j);
    if(k >= tlen) return 0;
    if(t[k] != '('){
        /* axx.py と同じく Python の repr の形で引用する（' を含めば "…"）。 */
        char gr[400]; m_pyrepr_n(t + k, (size_t)(tlen - k), gr, sizeof(gr));
        snprintf(errbuf, esz, " error - '.func': expected '(' or end of line after "
                 "the name, got %s\n", gr);
        return 1;
    }
    int e = -1;
    for(int q = tlen - 1; q > k; q--) if(t[q] == ')'){ e = q; break; }
    if(e < 0){
        snprintf(errbuf, esz, " error - '.func': missing closing ')' in the "
                 "parameter list.\n");
        return 1;
    }
    for(int q = e + 1; q < tlen; q++){
        if(!isspace((unsigned char)t[q])){
            int ts = e + 1, te = tlen;
            while(ts < te && isspace((unsigned char)t[ts])) ts++;
            while(te > ts && isspace((unsigned char)t[te-1])) te--;
            snprintf(errbuf, esz, " error - '.func': trailing text after ')': "
                     "'%.*s'\n", te - ts, t + ts);
            return 1;
        }
    }

    int q = k + 1;
    while(q < e){
        int st2 = q;
        while(q < e && t[q] != ',') q++;
        int en = q;
        while(st2 < en && isspace((unsigned char)t[st2])) st2++;
        while(en > st2 && isspace((unsigned char)t[en-1])) en--;
        if(en > st2){
            if(*np >= npmax){
                snprintf(errbuf, esz, " error - '.func': more than %d parameters.\n", npmax);
                return 1;
            }
            int plen = en - st2;
            if((size_t)plen >= psz){
                snprintf(errbuf, esz, " error - '.func': parameter name is too long.\n");
                return 1;
            }
            memcpy(params + (size_t)(*np)*psz, t + st2, (size_t)plen);
            params[(size_t)(*np)*psz + plen] = '\0';
            (*np)++;
        }
        if(q < e) q++;
    }
    return 0;
}

/* `.map` の式の中の変数を、その名前の位置 i に置き換える。括弧で包むので
   優先順位は変わらず、置き換えるのは単語として現れた箇所だけ。 */
static char *map_subst_index(const char *expr, const char *var, int i){
    char num[32];
    snprintf(num, sizeof(num), "(%d)", i);
    size_t nl = strlen(num);
    size_t vl = strlen(var);
    size_t cap = strlen(expr) * (nl > vl ? nl : 1) + nl + 16;
    char *out = malloc(cap);
    if(!out){ perror("malloc"); exit(1); }
    size_t w = 0;
    for(size_t k = 0; expr[k]; ){
        /* 一致したときだけ後ろの文字を見る。一致しなければ k+vl は文字列の
           終わりを越えうる。 */
        int is_var = (strncasecmp(expr+k, var, vl) == 0);
        int lsep = (k == 0) || !(isalnum((unsigned char)expr[k-1]) || expr[k-1]=='_');
        int rsep = is_var && !(isalnum((unsigned char)expr[k+vl]) || expr[k+vl]=='_');
        if(is_var && lsep && rsep){ memcpy(out+w, num, nl); w += nl; k += vl; }
        else out[w++] = expr[k++];
    }
    out[w] = '\0';
    return out;
}

/* パターンファイルを読み、各行をマクロ層に通してから `::` で欄に割る。
   `.sub` と `.func` のブロックは本文を集めて別に持つので、その中の行が
   普通のパターン行として照合されることはない。
   コメントには後方互換の規則がある。開きだけをコメント行の頭に並べる古い
   書き方のために、すぐ次の行も開きで始まるか、以降どこにも閉じが無いときは
   自分の行を超えて延長しない。 */
static void readpat(Assembler *asmb, const char *fn){
    if(!fn||!fn[0]) return;

    enum { MAX_PAT_DEPTH = 50 };
    if(asmb->st.pat_include_depth > MAX_PAT_DEPTH){
        axx_diagf(1, 0, " error - pattern .INCLUDE nesting exceeds %d: '%s'\n",
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
            axx_diagf(1, 0, " error - circular pattern .INCLUDE detected: '%s' "
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

    char this_dir[PATH_MAX];
    axx_abs_dir_of(fn, this_dir, sizeof(this_dir));

    if(asmb->st.pat_include_depth == 1){
        macro_reset_pass_pattern();
        subv_free(&asmb->st.subs);
        mfv_free(&asmb->st.funcs);
    }

    int nexp = 0;
    int *expln = NULL;
    char **exp = pat_macro_expand(f, fn, &nexp, &expln);
    fclose(f);
    f = NULL;

    int *rest_has_close = malloc(sizeof(int) * (size_t)(nexp + 1));
    if(!rest_has_close){ perror("malloc"); exit(1); }
    rest_has_close[nexp] = 0;
    for(int i = nexp - 1; i >= 0; i--){
        rest_has_close[i] = rest_has_close[i+1] || (strstr(exp[i], "*/") != NULL);
    }

    char *line = NULL; size_t lcap = 0;
    int in_block_comment = 0;
    int legacy_chain = 0;
    SubDef *cur_sub = NULL;
    MiniFunc *func_stack[64];
    int nfunc_stack = 0;
    for(int li = 0; li < nexp; li++){
        size_t need = strlen(exp[li]) + 1;
        if(need > lcap){
            char *nl = realloc(line, need);
            if(!nl){ perror("realloc"); exit(1); }
            line = nl; lcap = need;
        }
        memcpy(line, exp[li], need);
        int was_in_comment = in_block_comment;
        axx_remove_comment(line, &in_block_comment);
        if(!in_block_comment){
            legacy_chain = 0;
        } else if(!was_in_comment){
            int oi = axx_skipspc(exp[li], 0);
            int this_is_bare_open = (exp[li][oi]=='/' && exp[li][oi+1]=='*');
            int treat_as_legacy;
            if(legacy_chain && this_is_bare_open){
                treat_as_legacy = 1;
            } else {
                int next_looks_legacy = 0;
                if(li+1 < nexp){
                    int ni = axx_skipspc(exp[li+1], 0);
                    next_looks_legacy = (exp[li+1][ni]=='/' && exp[li+1][ni+1]=='*');
                }
                treat_as_legacy = next_looks_legacy || !rest_has_close[li+1];
            }
            if(treat_as_legacy){
                in_block_comment = 0;
                legacy_chain = this_is_bare_open;
            } else {
                legacy_chain = 0;
            }
        }
        for(char*p=line;*p;p++){ if(*p=='\t') *p=' '; if(*p=='\r') *p=' '; }
        int l=(int)strlen(line);
        while(l>0&&(line[l-1]=='\n'||line[l-1]=='\r')) line[--l]=0;
        axx_reduce_spaces(line);

        {
            char dk[32];
            mini_dotkw(line, dk, sizeof(dk));
            if(nfunc_stack > 0 || strcmp(dk, ".FUNC") == 0){
                if(strcmp(dk, ".FUNC") == 0){
                    if(nfunc_stack >= (int)(sizeof(func_stack)/sizeof(func_stack[0]))){
                        axx_diagf(1, 0, " error - '.func' nesting is deeper than %d.\n",
                                   (int)(sizeof(func_stack)/sizeof(func_stack[0])));
                        continue;
                    }
                    enum { FUNC_PARAM_MAX = 64 };
                    size_t FUNC_NAME_MAX = strlen(line) + 1;
                    char *nmbuf = malloc(FUNC_NAME_MAX);
                    if(!nmbuf){ perror("malloc"); exit(1); }
                    char *pbuf = malloc((size_t)FUNC_PARAM_MAX * FUNC_NAME_MAX);
                    if(!pbuf){ perror("malloc"); exit(1); }
                    char errbuf[512];
                    int nparam = 0;
                    int hdr_err = parse_func_header(line, nmbuf, FUNC_NAME_MAX,
                                                    pbuf, FUNC_NAME_MAX,
                                                    FUNC_PARAM_MAX, &nparam,
                                                    errbuf, sizeof(errbuf));
                    int ok = 1;
                    if(hdr_err){
                        axx_diagf(1, 0, "%s", errbuf);
                        ok = 0;
                    } else if(!is_sub_name(nmbuf)){
                        size_t _nrsz = 4 * strlen(nmbuf) + 16;
                        char *_nr = malloc(_nrsz); if(!_nr){ perror("malloc"); exit(1); }
                        m_pyrepr(nmbuf, _nr, _nrsz);
                        axx_diagf(1, 0, " error - '.func' needs a name made of letters, "
                                   "digits and '_': %s\n", _nr);
                        free(_nr);
                        ok = 0;
                    } else {
                        for(int q=0;q<nparam;q++){
                            char *pn = pbuf + (size_t)q*FUNC_NAME_MAX;
                            if(!is_sub_name(pn)){
                                char _pr[600]; m_pyrepr(pn, _pr, sizeof(_pr));
                                axx_diagf(1, 0, " error - '.func %s': bad parameter "
                                           "name %s\n", nmbuf, _pr);
                                ok = 0;
                                break;
                            }
                        }
                    }
                    MiniFunc *parent = nfunc_stack ? func_stack[nfunc_stack-1] : NULL;
                    MiniFunc *nf;
                    if(ok){
                        int _dup = 0;
                        if(parent){
                            for(int i=0;i<parent->nchildren;i++)
                                if(strcmp(parent->children[i]->name, nmbuf)==0){ _dup=1; break; }
                        } else {
                            MiniFuncVec *_v = &asmb->st.funcs;
                            for(int i=0;i<_v->len;i++)
                                if(strcmp(_v->data[i]->name, nmbuf)==0){ _dup=1; break; }
                        }
                        if(_dup){
                            char _nr[600]; m_pyrepr(nmbuf, _nr, sizeof(_nr));
                            axx_diagf(0, 0, " warning - function %s is defined more than "
                                       "once; the later definition wins.\n", _nr);
                        }
                        nf = mini_func_new(asmb, parent, nmbuf, fn, expln[li]);
                        for(int q=0;q<nparam;q++)
                            mini_func_addparam(nf, pbuf + (size_t)q*FUNC_NAME_MAX);
                    } else {
                        nf = mini_alloc(sizeof(MiniFunc));
                        nf->name = mini_strdup("?");
                        nf->file = mini_strdup(fn);
                        nf->line = expln[li];
                        nf->parent = parent;
                    }
                    free(pbuf);
                    free(nmbuf);
                    func_stack[nfunc_stack++] = nf;
                    continue;
                }
                MiniFunc *cur = func_stack[nfunc_stack-1];
                if(strcmp(dk, ".ENDFUNC") == 0){
                    if(cur->depth != 0){
                        axx_diagf(1, 0, " error - '.func %s': '.endfunc' while a block "
                                   "('.if'/'.while'/'.for') is still open.\n", cur->name);
                    }
                    nfunc_stack--;
                    continue;
                }
                if(strcmp(dk, ".IF") == 0 || strcmp(dk, ".FOR") == 0
                   || strcmp(dk, ".WHILE") == 0){
                    cur->depth++;
                } else if(strcmp(dk, ".ENDIF") == 0 || strcmp(dk, ".NEXT") == 0
                          || strcmp(dk, ".ENDWHILE") == 0){
                    cur->depth--;
                    if(cur->depth < 0){
                        char _dkl[32]; size_t _di = 0;
                        for(; dk[_di] && _di + 1 < sizeof(_dkl); _di++)
                            _dkl[_di] = (char)tolower((unsigned char)dk[_di]);
                        _dkl[_di] = '\0';
                        axx_diagf(1, 0, " error - '.func::%s': %s without a matching "
                                   "block opener.\n", cur->name, _dkl);
                        cur->depth = 0;
                    }
                }
                {
                    int nb = axx_skipspc(line, 0);
                    if(line[nb]) mini_func_addline(cur, line, fn, expln[li]);
                }
                continue;
            }
            if(strcmp(dk, ".ECHO") == 0){
                if(cur_sub){
                    axx_diagf(1, 0, " error - '.echo' cannot be written inside "
                               "'.sub::%s'.\n", cur_sub->name);
                    continue;
                }
                int ea = axx_skipspc(line, 0) + 5;
                EchoItem *eiv = NULL;
                int ein = 0;
                char ebuf[512];
                const char *eerr = echo_items_parse(line + ea, &eiv, &ein,
                                                    ebuf, sizeof(ebuf));
                if(eerr) axx_diagf(1, 0, " error - '.echo': %s\n", eerr);
                PatEntry *pe = pv_push_blank(&asmb->st.pat);
                pat_set(pe, 0, ".echo");
                pat_set(pe, 1, line + ea);
                pe->echo_items  = eiv;
                pe->echo_nitems = ein;
                continue;
            }
        }

        char uline[16]={0};
        int si=axx_skipspc(line,0);
        for(int i=0;i<8&&line[si+i];i++) uline[i]=axx_upper_char(line[si+i]);
        if(strcmp(uline,".INCLUDE")==0){ include_pat(asmb,line+si,this_dir); continue; }

        size_t fsz = strlen(line) + 1;
        int fmax = 1;
        for(const char *q = line; *q; q++)
            if(q[0]==':' && q[1]==':'){ fmax++; q++; }
        if(fmax < 8) fmax = 8;
        char *fbuf = malloc((size_t)fmax * fsz);
        if(!fbuf){ perror("malloc"); exit(1); }
        char **fields = malloc((size_t)fmax * sizeof(char*));
        if(!fields){ perror("malloc"); exit(1); }
        for(int i=0;i<fmax;i++){ fields[i] = fbuf + (size_t)i*fsz; fields[i][0]=0; }
        int nf=0;
        int idx=0;
        while(1){
            idx=axx_get_params1(line,idx,fields[nf],fsz);
            nf++;
            if(idx>=(int)strlen(line)||nf>=fmax) break;
        }

        {
            char kw[16]={0};
            {
                int a = axx_skipspc(fields[0], 0);
                int e = (int)strlen(fields[0]);
                while(e > a && isspace((unsigned char)fields[0][e-1])) e--;
                if(e - a < (int)sizeof(kw))
                    for(int k = a; k < e; k++) kw[k-a] = axx_upper_char(fields[0][k]);
            }
            if(strcmp(kw,".SUB")==0){
                char *nm = (nf>1) ? pat_trim(fields[1]) : (char*)"";
                if(cur_sub){
                    axx_diagf(1, 0, " error - '.sub' inside '.sub::%s': sub tables "
                               "cannot be nested.\n", cur_sub->name);
                } else if(!is_sub_name(nm)){
                    axx_diagf(1, 0, " error - '.sub' needs a table name made of "
                               "letters, digits and '_': '%s'\n", nm);
                } else {
                    if(subv_find(&asmb->st.subs, nm))
                        axx_diagf(0, 0, " warning - sub table '%s' is defined more "
                                   "than once; the later definition wins.\n", nm);
                    cur_sub = subv_new(&asmb->st.subs, nm);
                }
                free(fields); free(fbuf); continue;
            }
            if(strcmp(kw,".RETURN")==0 || strcmp(kw,".ENDSUB")==0){
                if(!cur_sub){
                    char _kwl[16];
                    for(size_t _i=0;_i<sizeof(_kwl);_i++)
                        _kwl[_i] = (char)tolower((unsigned char)kw[_i]);
                    _kwl[sizeof(_kwl)-1] = '\0';
                    axx_diagf(1, 0, " error - '%s' without a matching '.sub'.\n", _kwl);
                }
                cur_sub = NULL;
                free(fields); free(fbuf); continue;
            }
            if(cur_sub){
                if(nf<2){
                    if(pat_trim(fields[0])[0]){
                        size_t _esz = strlen(fields[0]) * 4 + 8;
                        char *_er = malloc(_esz);
                        char _nr[600];
                        if(!_er){ perror("malloc"); exit(1); }
                        m_pyrepr(fields[0], _er, _esz);
                        m_pyrepr(cur_sub->name, _nr, sizeof(_nr));
                        axx_diagf(1, 0, " error - sub table %s: entry has no '::' "
                                   "field separator: %s\n", _nr, _er);
                        free(_er);
                    }
                } else {
                    subdef_push(cur_sub, fields[0], fields[nf-1]);
                }
                free(fields); free(fbuf); continue;
            }
        }

        {
            char kw[16]={0};
            int a = axx_skipspc(fields[0], 0);
            int e = (int)strlen(fields[0]);
            while(e > a && isspace((unsigned char)fields[0][e-1])) e--;
            if(e - a < (int)sizeof(kw))
                for(int k = a; k < e; k++) kw[k-a] = axx_upper_char(fields[0][k]);
            if(strcmp(kw,".MAP")==0){
                const char *var_str = (nf>2) ? pat_trim(fields[1]) : "";
                if(!var_str[0] || nf<3){
                    axx_diagf(1, 0, " error - .map: needs '.map::<variable>::"
                               "<name,name,...>[::<expression in the variable>]'.\n");
                } else if(dir_var_slot(var_str) < 0){
                    axx_diagf(1, 0, " error - .map: variable should be a lower case "
                               "name ('%s').\n", var_str);
                }
            }
        }

        if(nf==1){
            int nonblank=0;
            for(const char*p=fields[0];*p;p++){ if(!isspace((unsigned char)*p)){ nonblank=1; break; } }
            char kw1[16]={0};
            {
                int a = axx_skipspc(fields[0], 0);
                int e = (int)strlen(fields[0]);
                while(e > a && isspace((unsigned char)fields[0][e-1])) e--;
                if(e - a < (int)sizeof(kw1))
                    for(int k = a; k < e; k++) kw1[k-a] = axx_upper_char(fields[0][k]);
            }
            if(nonblank && strcmp(kw1,".PASSTHRU")!=0 && strcmp(kw1,".EOL")!=0
                        && strcmp(kw1,".TEXTMODE")!=0 && strcmp(kw1,".UNORDERED")!=0){
                { size_t _fl = strlen(fields[0]);
                  size_t _rsz = _fl * 4 + 8;
                  char *_fr = malloc(_rsz);
                  if(!_fr){ perror("malloc"); exit(1); }
                  m_pyrepr(fields[0], _fr, _rsz);
                  axx_diagf(0, 0, " warning - pattern line has no '::' field separator "
                             "and can never match (a pattern file has no line-"
                             "continuation mechanism, so this is likely a stray "
                             "line left over from a multi-line comment, or a "
                             "binary_list/error_patterns that was continued onto "
                             "the next physical line): %s\n", _fr);
                  free(_fr); }
            }
        }
        PatEntry *pe=pv_push_blank(&asmb->st.pat);
        if(nf==1){ pat_set(pe,0,fields[0]); }
        else if(nf==2){ pat_set(pe,0,fields[0]); pat_set(pe,2,fields[1]); }
        else if(nf==3){ pat_set(pe,0,fields[0]); pat_set(pe,1,fields[1]); pat_set(pe,2,fields[2]); }
        else if(nf==4){ pat_set(pe,0,fields[0]); pat_set(pe,1,fields[1]); pat_set(pe,2,fields[2]); pat_set(pe,3,fields[3]); }
        else if(nf==5){ for(int i=0;i<5;i++) pat_set(pe,i,fields[i]); }
        else if(nf==6){ for(int i=0;i<6;i++) pat_set(pe,i,fields[i]); }
        else {
            size_t _wsz = 4;
            for(int i=6;i<nf;i++) _wsz += strlen(fields[i]) * 4 + 8;
            char *_w = malloc(_wsz);
            if(!_w){ perror("malloc"); exit(1); }
            size_t _o = 0;
            _w[_o++] = '[';
            for(int i=6;i<nf;i++){
                if(i>6){ _w[_o++]=','; _w[_o++]=' '; }
                m_pyrepr(fields[i], _w + _o, _wsz - _o);
                _o += strlen(_w + _o);
            }
            _w[_o++] = ']'; _w[_o] = '\0';
            axx_diagf(0, 0, " warning - pattern line has more than 6 fields "
                            "(extra fields ignored): %s\n", _w);
            free(_w);
            for(int i=0;i<6;i++) pat_set(pe,i,fields[i]);
        }
        free(fields);
        free(fbuf);
    }
    if(in_block_comment){
        axx_diagf(0, 0, " warning - pattern file '%s' ends while a /* ... */ comment "
                   "is still open (missing closing '*/').\n", fn);
    }
    if(cur_sub){
        axx_diagf(1, 0, " error - pattern file '%s' ends while sub table '%s' is "
                   "still open (missing '.return' or '.endsub').\n", fn, cur_sub->name);
    }
    while(nfunc_stack > 0){
        axx_diagf(1, 0, " error - pattern file '%s' ends while function '%s' is "
                   "still open (missing '.endfunc').\n",
                   fn, func_stack[--nfunc_stack]->name);
    }
    if(asmb->st.pat_include_depth == 1){
        check_sub_refs(asmb);
        mini_compile_all(asmb->st.funcs.data, asmb->st.funcs.len);
    }
    free(rest_has_close);
    free(line);
    pat_macro_expand_free(exp, nexp); free(expln);
    asmb->st.pat_include_depth--;
    if(asmb->st.pat_include_depth >= 0
       && asmb->st.pat_include_depth < (int)(sizeof(asmb->st.pat_include_chain)
                                             / sizeof(asmb->st.pat_include_chain[0]))){
        free(asmb->st.pat_include_chain[asmb->st.pat_include_depth]);
        asmb->st.pat_include_chain[asmb->st.pat_include_depth] = NULL;
    }
}

/* `%%` を繰り返しインデックスの値に、`%0` をその 0 復帰に置き換える。
   文字列リテラルの中は触らない。 */
static int replace_percent_with_index(const char *s, char *out, size_t osz){
    int count=0,i=0; size_t n=0; int truncated=0;
    while(s[i]){
        if(s[i]=='"'){
            if(n<osz-1) out[n++]=s[i]; else truncated=1;
            i++;
            while(s[i]){
                if(s[i]=='\\' && s[i+1]){
                    if(n<osz-1) out[n++]=s[i];   else truncated=1;
                    if(n<osz-1) out[n++]=s[i+1]; else truncated=1;
                    i+=2; continue;
                }
                char ch=s[i];
                if(n<osz-1) out[n++]=ch; else truncated=1;
                i++;
                if(ch=='"') break;
            }
            continue;
        }
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

/* `@@[n, 中身]` の繰り返しを展開する。入れ子と文字列リテラルを数えて
   対応する閉じを探す。 */
static void e_p(const char *pattern, char *out, size_t osz, int *is_empty, Assembler *asmb, int ep_depth){
    enum { MAX_EP_DEPTH = 200 };
    if(ep_depth > MAX_EP_DEPTH){
        if(should_report_errors(&asmb->st)){
            axx_diagf(1, 0, " error - @@[...]: nesting exceeds maximum depth %d.\n", MAX_EP_DEPTH);
        }
        out[0]=0; *is_empty=1;
        return;
    }
    size_t n=0; int has_content=0;
    int i=0; int plen=(int)strlen(pattern);
    while(i<plen&&n<osz-1){
        if(i+3<=plen && strncmp(pattern+i,"@@[",3)==0){
            i+=3;
            int depth=1, expr_start=i, comma_pos=-1;
            while(i<plen&&depth>0){
                if(pattern[i]=='"'){
                    i++;
                    while(i<plen){
                        if(pattern[i]=='\\' && i+1<plen){ i+=2; continue; }
                        if(pattern[i]=='"'){ i++; break; }
                        i++;
                    }
                    continue;
                }
                if(pattern[i]=='[') depth++;
                else if(pattern[i]==']'){ depth--; if(depth==0) break; }
                else if(pattern[i]==','&&depth==1&&comma_pos<0) comma_pos=i;
                i++;
            }
            if(comma_pos>0){
                int el=comma_pos-expr_start;
                int rl=i-comma_pos-1;
                if(el<0) el=0;
                if(rl<0) rl=0;
                char *expr_part = malloc((size_t)el+1);
                char *rep_pat   = malloc((size_t)rl+1);
                if(!expr_part||!rep_pat){ perror("malloc"); exit(1); }
                memcpy(expr_part,pattern+expr_start,(size_t)el); expr_part[el]=0;
                memcpy(rep_pat,pattern+comma_pos+1,(size_t)rl); rep_pat[rl]=0;
                int io;
                int _rep_prior = asmb->st.error_undefined_label;
                asmb->st.error_undefined_label = 0;
                uint256_t nv=expr_expression_pat(asmb,expr_part,0,&io);
                int _rep_undef = asmb->st.error_undefined_label;
                asmb->st.error_undefined_label = _rep_prior || _rep_undef;
                int64_t nrep=u256_to_i64(nv);
                const int64_t N_MAX = (int64_t)1 << 24;
                if(_rep_undef || u256_is_undef_derived(nv)) nrep = 0;
                else if(u256_gt_signed(nv, u256_from_i64(N_MAX))){
                    char cb[96]; u256_to_pydec(nv, cb, sizeof(cb));
                    axx_diagf(0, 0, " error - @@[n,...]: repeat count %s exceeds maximum %lld.\n",
                              cb, (long long)N_MAX);
                    asmb->st.had_error = 1;
                    nrep = 0;
                }
                if(nrep>0){
                    has_content=1;
                    char *exp_rep = malloc(osz);
                    if(!exp_rep){ perror("malloc"); exit(1); }
                    int rep_empty=0;
                    e_p(rep_pat, exp_rep, osz, &rep_empty, asmb, ep_depth+1);
                    for(int j=0;j<nrep;j++){
                        if(j>0&&n<osz-1) out[n++]=',';
                        for(const char*p=exp_rep;*p&&n<osz-1;) out[n++]=*p++;
                    }
                    free(exp_rep);
                }
                free(expr_part); free(rep_pat);
                i++;
            } else {
                if(should_report_errors(&asmb->st)){
                    axx_diagf(1, 0, " error - @@[...]: missing ',' separating count and pattern.\n");
                }
                if(n+3<osz){ out[n++]='@'; out[n++]='@'; out[n++]='['; has_content=1; }
            }
        } else if(pattern[i]=='"'){
            out[n++]=pattern[i++]; has_content=1;
            while(i<plen&&n<osz-1){
                if(pattern[i]=='\\' && i+1<plen && n+1<osz-1){
                    out[n++]=pattern[i++];
                    out[n++]=pattern[i++];
                    continue;
                }
                char ch=pattern[i];
                out[n++]=pattern[i++];
                if(ch=='"') break;
            }
        } else { out[n++]=pattern[i++]; has_content=1; }
    }
    out[n]=0;
    *is_empty=!has_content;
}

/* ---- 配列シンボルと集合 -------------------------------------------------
   `.setsym` の値欄が `[...]` なら配列シンボル、名前のカンマ並びなら集合。
   集合は名前を項目に持つ配列シンボルなので、同じ置き場を使う。
   ------------------------------------------------------------------------ */
static int arrsym_find(AsmState *st, const char *upper_name){
    for(int i=0;i<st->arrsyms_len;i++)
        if(strcmp(st->arrsyms[i].name, upper_name)==0) return i;
    return -1;
}
/* 配列シンボルを引く。 */
static struct ArrSym *arrsym_get(AsmState *st, const char *upper_name){
    int i = arrsym_find(st, upper_name);
    return (i < 0) ? NULL : &st->arrsyms[i];
}
/* 配列シンボル 1 個を解放する。 */
static void arrsym_free_one(struct ArrSym *a){
    for(int i=0;i<a->len;i++) free(a->items[i].s);
    free(a->items); free(a->name);
    a->items = NULL; a->name = NULL; a->len = 0;
}
/* 配列シンボルを消す。 */
static void arrsym_delete(AsmState *st, const char *upper_name){
    int i = arrsym_find(st, upper_name);
    if(i < 0) return;
    g_arrgen++;
    arrsym_free_one(&st->arrsyms[i]);
    for(int k=i+1;k<st->arrsyms_len;k++) st->arrsyms[k-1] = st->arrsyms[k];
    st->arrsyms_len--;
}
/* 配列シンボルをすべて消す。 */
static void arrsym_clear_all(AsmState *st){
    if(st->arrsyms_len) g_arrgen++;
    for(int i=0;i<st->arrsyms_len;i++) arrsym_free_one(&st->arrsyms[i]);
    free(st->arrsyms);
    st->arrsyms = NULL; st->arrsyms_len = 0; st->arrsyms_cap = 0;
}

/* 配列シンボルを登録する。中身が変わったときだけ世代番号を進める。
   `.check` の名前一覧がこれを参照するので、無駄に進めるとそのキャッシュが
   意味なく落ちる。 */
static void arrsym_install(AsmState *st, const char *dst_upper, SymItem *items, int n){
    {
        struct ArrSym *old = arrsym_get(st, dst_upper);
        if(old && old->len == n){
            int same = 1;
            for(int i=0;i<n;i++){
                if(old->items[i].is_str != items[i].is_str){ same = 0; break; }
                if(items[i].is_str){
                    const char *a = old->items[i].s ? old->items[i].s : "";
                    const char *b = items[i].s ? items[i].s : "";
                    if(strcmp(a,b) != 0){ same = 0; break; }
                } else if(!u256_eq(old->items[i].v, items[i].v)){ same = 0; break; }
            }
            if(same){
                for(int i=0;i<n;i++) free(items[i].s);
                free(items);
                return;
            }
        }
    }
    g_arrgen++;
    arrsym_delete(st, dst_upper);
    if(st->arrsyms_len >= st->arrsyms_cap){
        st->arrsyms_cap = st->arrsyms_cap ? st->arrsyms_cap*2 : 8;
        st->arrsyms = realloc(st->arrsyms, (size_t)st->arrsyms_cap*sizeof(*st->arrsyms));
        if(!st->arrsyms){ perror("realloc"); exit(1); }
    }
    struct ArrSym *a = &st->arrsyms[st->arrsyms_len++];
    a->name = strdup(dst_upper);
    a->items = items;
    a->len = n;
}

/* 配列シンボルを複製する。独立したコピーなので元を再定義しても変わらない。 */
static void arrsym_copy(AsmState *st, const char *dst_upper, const char *src_upper){
    struct ArrSym *src = arrsym_get(st, src_upper);
    if(!src) return;
    if(strcmp(dst_upper, src_upper)==0) return;
    int n = src->len;
    SymItem *items = n ? malloc((size_t)n*sizeof(SymItem)) : NULL;
    if(n && !items){ perror("malloc"); exit(1); }
    for(int i=0;i<n;i++){
        items[i].is_str = src->items[i].is_str;
        items[i].v      = src->items[i].v;
        items[i].s      = src->items[i].s ? strdup(src->items[i].s) : NULL;
    }
    arrsym_install(st, dst_upper, items, n);
}

/* 欄が「裸の名前」1 個だけなら、その綴りをそのまま返す。大文字化はしない。
   配列シンボルの項目が書かれたままの綴りで残るのはこれが理由。 */
static int bare_name_of(const char *text, char *out, size_t cap){
    const char *q = text ? text : "";
    while(*q==' '||*q=='\t') q++;
    const char *b = q;
    if(!(isalpha((unsigned char)*q) || *q=='_')) return 0;
    while(isalnum((unsigned char)*q) || *q=='_') q++;
    size_t n = (size_t)(q - b);
    while(*q==' '||*q=='\t') q++;
    if(*q) return 0;
    if(n >= cap) return 0;
    memcpy(out, b, n);
    out[n] = '\0';
    return 1;
}

/* 値欄が裸の名前のときの `.setsym`。配列か文字列シンボルならコピーし、
   どちらでもなければ「その名前を保持する文字列シンボル」にする。
   名前を持ち回って添字に使えるのはこれのため。 */
static int symbol_copy_from_name(AsmState *st, const char *dst_upper, const char *value_field){
    char name[512];
    if(!bare_name_of(value_field, name, sizeof(name))) return 0;
    char src[512];
    axx_strupr_to(src, name, sizeof(src));

    if(arrsym_get(st, src)){ arrsym_copy(st, dst_upper, src); return 1; }
    const char *sv = strsym_get(st, src);
    if(sv){
        if(strcmp(dst_upper, src)==0) return 1;
        char *dup = strdup(sv);
        if(!dup){ perror("strdup"); exit(1); }
        strsym_set(st, dst_upper, dup);
        free(dup);
        return 1;
    }
    strsym_set(st, dst_upper, name);
    return 1;
}


typedef struct { SymItem *data; int len, cap; } ItemVec;

static void itv_init(ItemVec *v){ v->data = NULL; v->len = 0; v->cap = 0; }
/* 項目の並びを解放する。 */
static void itv_free(ItemVec *v){
    for(int i=0;i<v->len;i++) free(v->data[i].s);
    free(v->data);
    itv_init(v);
}
/* 項目を 1 つ積む。 */
static void itv_push(ItemVec *v, const SymItem *it){
    if(v->len >= v->cap){
        v->cap = v->cap ? v->cap*2 : 8;
        v->data = realloc(v->data, (size_t)v->cap*sizeof(SymItem));
        if(!v->data){ perror("realloc"); exit(1); }
    }
    SymItem *d = &v->data[v->len++];
    d->is_str = it->is_str;
    d->v      = it->v;
    d->s      = it->s ? strdup(it->s) : NULL;
}
/* 項目が等しいか。 */
static int symitem_eq(const SymItem *a, const SymItem *b){
    if(a->is_str != b->is_str) return 0;
    if(a->is_str) return strcmp(a->s ? a->s : "", b->s ? b->s : "") == 0;
    return u256_eq(a->v, b->v);
}
/* 項目が既にあるか。 */
static int itv_has(const ItemVec *v, const SymItem *it){
    for(int i=0;i<v->len;i++) if(symitem_eq(&v->data[i], it)) return 1;
    return 0;
}
/* 重複しなければ項目を積む（順序は最初に現れた位置）。 */
static void itv_push_unique(ItemVec *v, const SymItem *it){
    if(!itv_has(v, it)) itv_push(v, it);
}

/* 集合演算 1 つを適用する。`&` 積、`|` と `+` 和、`^` 対称差、`-` 差。
   固有の優先順位は無く、左から右へ適用するので `a&b|c` は `(a&b)|c`。 */
static void set_op_apply(ItemVec *acc, const ItemVec *rhs, char op){
    ItemVec out; itv_init(&out);
    if(op == '&'){
        for(int i=0;i<acc->len;i++)
            if(itv_has(rhs, &acc->data[i])) itv_push_unique(&out, &acc->data[i]);
    } else if(op == '|' || op == '+'){
        for(int i=0;i<acc->len;i++) itv_push_unique(&out, &acc->data[i]);
        for(int i=0;i<rhs->len;i++) itv_push_unique(&out, &rhs->data[i]);
    } else if(op == '^'){
        for(int i=0;i<acc->len;i++)
            if(!itv_has(rhs, &acc->data[i])) itv_push_unique(&out, &acc->data[i]);
        for(int i=0;i<rhs->len;i++)
            if(!itv_has(acc, &rhs->data[i])) itv_push_unique(&out, &rhs->data[i]);
    } else {
        for(int i=0;i<acc->len;i++)
            if(!itv_has(rhs, &acc->data[i])) itv_push_unique(&out, &acc->data[i]);
    }
    itv_free(acc);
    *acc = out;
}

/* 集合リストの 1 項目として読める名前か。 */
static int set_name_token(const char *t, char *out, size_t outsz){
    while(*t==' '||*t=='\t') t++;
    const char *e = t + strlen(t);
    while(e > t && (e[-1]==' '||e[-1]=='\t')) e--;
    int n = (int)(e - t);
    if(n <= 0 || n >= (int)outsz) return 0;
    if(t[0] >= '0' && t[0] <= '9') return 0;
    for(int i=0;i<n;i++) if(t[i]==' '||t[i]=='\t') return 0;
    for(int i=0;i<n;i++) out[i] = (char)axx_upper_char(t[i]);
    out[n] = '\0';
    return 1;
}

/* 集合式のオペランドを読む。既存の集合を指す裸の識別子のみ。`-` `&` `|` は
   シンボル名にも現れうるので、文字・数字・下線だけの綴りに限る。 */
static int set_operand(AsmState *st, const char *b, int n, ItemVec *out){
    while(n > 0 && (*b==' '||*b=='\t')){ b++; n--; }
    while(n > 0 && (b[n-1]==' '||b[n-1]=='\t')) n--;
    if(n <= 0) return 0;
    if(!(isalpha((unsigned char)b[0]) || b[0]=='_')) return 0;
    for(int i=1;i<n;i++)
        if(!(isalnum((unsigned char)b[i]) || b[i]=='_')) return 0;
    char nm[512];
    if(n >= (int)sizeof(nm)) return 0;
    for(int i=0;i<n;i++) nm[i] = (char)axx_upper_char(b[i]);
    nm[n] = '\0';
    struct ArrSym *a = arrsym_get(st, nm);
    if(!a) return 0;
    itv_init(out);
    for(int i=0;i<a->len;i++) itv_push_unique(out, &a->items[i]);
    return 1;
}

/* 集合式を計算する。集合として読めなければ失敗を返し、数値解釈へ譲る。 */
static int set_expr_from_text(AsmState *st, const char *text, ItemVec *out){
    ItemVec acc; itv_init(&acc);
    int have = 0, nops = 0;
    char op = 0;
    const char *b = text;
    for(const char *p = text; ; p++){
        if(*p=='&' || *p=='|' || *p=='^' || *p=='+' || *p=='-' || *p=='\0'){
            ItemVec cur;
            if(!set_operand(st, b, (int)(p - b), &cur)){
                if(have) itv_free(&acc);
                return 0;
            }
            if(!have){ acc = cur; have = 1; }
            else { set_op_apply(&acc, &cur, op); itv_free(&cur); nops++; }
            if(*p == '\0') break;
            op = *p;
            b  = p + 1;
        }
    }
    if(nops == 0){ itv_free(&acc); return 0; }
    *out = acc;
    return 1;
}

/* 名前のカンマ並びを集合として読む。項目がそれ自体集合ならその場で展開する。
   2 項目以上ないと集合にしないので、単一の名前はコピーとして扱われる。 */
static int set_literal_from_text(AsmState *st, const char *text, ItemVec *out){
    StrVec parts; sv_init(&parts);
    split_top_commas(text, &parts);
    if(parts.len < 2){ sv_free(&parts); return 0; }
    ItemVec v; itv_init(&v);
    for(int i=0;i<parts.len;i++){
        char nm[512];
        if(!set_name_token(parts.data[i], nm, sizeof(nm))){
            itv_free(&v); sv_free(&parts); return 0;
        }
        struct ArrSym *a = arrsym_get(st, nm);
        if(a){
            for(int k=0;k<a->len;k++) itv_push_unique(&v, &a->items[k]);
        } else {
            SymItem it; it.is_str = 1; it.s = nm; it.v = u256_zero();
            itv_push_unique(&v, &it);
        }
    }
    sv_free(&parts);
    *out = v;
    return 1;
}

/* 値欄を集合として解釈し、配列シンボルとして登録する。 */
static int symbol_set_from_text(AsmState *st, const char *dst_upper, const char *value_field){
    ItemVec items;
    if(!set_expr_from_text(st, value_field, &items)
       && !set_literal_from_text(st, value_field, &items)) return 0;
    arrsym_install(st, dst_upper, items.data, items.len);
    return 1;
}

/* `[...]` の中身を配列シンボルとして登録する。文字列は文字列、裸の名前は
   綴りのままの文字列、ほかは式として評価した数値。 */
static void arrsym_set_from_text(Assembler *asmb, const char *upper_name, const char *q){
    AsmState *st = &asmb->st;
    g_arrgen++;
    arrsym_delete(st, upper_name);
    if(st->arrsyms_len >= st->arrsyms_cap){
        st->arrsyms_cap = st->arrsyms_cap ? st->arrsyms_cap*2 : 8;
        st->arrsyms = realloc(st->arrsyms, (size_t)st->arrsyms_cap*sizeof(*st->arrsyms));
        if(!st->arrsyms){ perror("realloc"); exit(1); }
    }
    struct ArrSym *a = &st->arrsyms[st->arrsyms_len++];
    a->name = strdup(upper_name);
    a->items = NULL; a->len = 0;
    int cap = 0;

    const char *p = q + 1;
    while(*p){
        while(*p==' '||*p=='\t') p++;
        if(*p==']' || !*p) break;
        const char *b = p;
        int depth = 0, inq = 0;
        while(*p){
            if(inq){
                if(*p=='\\' && p[1]) p++;
                else if(*p=='"') inq = 0;
            } else if(*p=='"') inq = 1;
            else if(*p=='[' || *p=='(') depth++;
            else if(*p==')') depth--;
            else if(*p==']'){ if(depth==0) break; depth--; }
            else if(*p==',' && depth==0) break;
            p++;
        }
        int n = (int)(p - b);
        while(n > 0 && (b[n-1]==' '||b[n-1]=='\t')) n--;
        char *item = malloc((size_t)n+1);
        if(!item){ perror("malloc"); exit(1); }
        memcpy(item, b, (size_t)n); item[n] = '\0';

        if(a->len >= cap){
            cap = cap ? cap*2 : 8;
            a->items = realloc(a->items, (size_t)cap*sizeof(SymItem));
            if(!a->items){ perror("realloc"); exit(1); }
        }
        SymItem *it = &a->items[a->len++];
        it->is_str = 0; it->s = NULL; it->v = u256_zero();
        char nm[512];
        if(item[0]=='"'){
            it->is_str = 1;
            it->s = txt_template_inner(item);
        } else if(bare_name_of(item, nm, sizeof(nm))){
            it->is_str = 1;
            it->s = strdup(nm);
            if(!it->s){ perror("strdup"); exit(1); }
        } else if(item[0]){
            int io;
            it->v = expr_expression_pat(asmb, item, 0, &io);
        }
        free(item);
        if(*p==',') p++;
        else break;
    }
}

/* 文字列シンボルを探す。 */
static int strsym_find(AsmState *st, const char *upper_name){
    for(int i=0;i<st->strsym_names.len;i++)
        if(strcmp(st->strsym_names.data[i], upper_name)==0) return i;
    return -1;
}
/* 文字列シンボルの中身。 */
static const char *strsym_get(AsmState *st, const char *upper_name){
    int i = strsym_find(st, upper_name);
    return (i < 0) ? NULL : st->strsym_vals.data[i];
}
/* 文字列シンボルを定義する。 */
static void strsym_set(AsmState *st, const char *upper_name, const char *val){
    int i = strsym_find(st, upper_name);
    if(i >= 0){ free(st->strsym_vals.data[i]); st->strsym_vals.data[i] = strdup(val); return; }
    sv_push(&st->strsym_names, upper_name);
    sv_push(&st->strsym_vals,  val);
}
/* 文字列シンボルを消す。 */
static void strsym_delete(AsmState *st, const char *upper_name){
    int i = strsym_find(st, upper_name);
    if(i < 0) return;
    free(st->strsym_names.data[i]);
    free(st->strsym_vals.data[i]);
    for(int k=i+1;k<st->strsym_names.len;k++){
        st->strsym_names.data[k-1] = st->strsym_names.data[k];
        st->strsym_vals.data[k-1]  = st->strsym_vals.data[k];
    }
    st->strsym_names.len--;
    st->strsym_vals.len--;
}


typedef struct { char *b; size_t len, cap; } TxtBuf;

static void txt_init(TxtBuf *t){ t->b=NULL; t->len=0; t->cap=0; }
/* ---- テキストテンプレート -----------------------------------------------
   出力欄の `"..."` を展開してテキストを作る。置き換えるのは二重波括弧の中
   だけで、それ以外はバックスラッシュエスケープを除いて書いたままの文字が出る。
   同じテキストは 1 バイト 1 ワードでバイナリにも出るので、1 つのパターン
   ファイルが翻訳とアセンブルの両方を果たす。
   ------------------------------------------------------------------------ */
static void txt_addn(TxtBuf *t, const char *s, size_t n){
    if(t->len + n + 1 > t->cap){
        size_t nc = t->cap ? t->cap : 64;
        while(t->len + n + 1 > nc) nc *= 2;
        char *nb = realloc(t->b, nc);
        if(!nb){ perror("realloc"); exit(1); }
        t->b = nb; t->cap = nc;
    }
    memcpy(t->b + t->len, s, n);
    t->len += n;
    t->b[t->len] = '\0';
}
static void txt_addc(TxtBuf *t, char c){ txt_addn(t, &c, 1); }
static void txt_adds(TxtBuf *t, const char *s){ txt_addn(t, s, strlen(s)); }

/* 診断に収まる形にエスケープして積む。 */
static void txt_add_escaped(TxtBuf *t, const char *s){
    for(const unsigned char *p=(const unsigned char *)s; *p; p++){
        switch(*p){
        case '\n': txt_adds(t, "\\n");  break;
        case '\t': txt_adds(t, "\\t");  break;
        case '\r': txt_adds(t, "\\r");  break;
        case '\\': txt_adds(t, "\\\\"); break;
        case '"':  txt_adds(t, "\\\""); break;
        default:   txt_addc(t, (char)*p); break;
        }
    }
}

/* 値をその基数の数字だけで書く（基数プレフィックスは付けない）。 */
static void txt_radix(TxtBuf *t, uint256_t v, int radix){
    /* 未定義は数字にせず UNDEF と書く。番兵の大きさは両実装で違うので、数字で
       出すと出力がそろわない。axx.py の _txt_radix() と同じ。 */
    if(u256_is_undef(v)){ txt_adds(t, "UNDEF"); return; }
    int neg = 0;
    if(u256_lt_signed(v, u256_zero())){ neg = 1; v = u256_sub(u256_zero(), v); }
    char tmp[300];
    int n = 0;
    uint256_t base = u256_from_u64((uint64_t)radix);
    if(u256_is_zero(v)) tmp[n++] = '0';
    while(!u256_is_zero(v) && n < (int)sizeof(tmp)){
        uint256_t q = u256_udiv(v, base);
        uint64_t  d = u256_to_u64(u256_sub(v, u256_mul(q, base)));
        tmp[n++] = "0123456789abcdef"[d & 15];
        v = q;
    }
    if(neg) txt_addc(t, '-');
    while(n > 0) txt_addc(t, tmp[--n]);
}

#define TXT_FLOAT_PREC 34

/* 符号・数字列・指数から浮動小数点の表記を組む。 */
static void txt_float_emit(TxtBuf *t, int neg, char *digits, int ndig, int exp10){
    while(ndig > 1 && digits[ndig-1] == '0') digits[--ndig] = '\0';
    if(neg) txt_addc(t, '-');
    if(exp10 >= -6 && exp10 < TXT_FLOAT_PREC){
        if(exp10 >= ndig-1){
            txt_addn(t, digits, (size_t)ndig);
            for(int i = 0; i < exp10-(ndig-1); i++) txt_addc(t, '0');
            txt_adds(t, ".0");
        } else if(exp10 >= 0){
            txt_addn(t, digits, (size_t)(exp10+1));
            txt_addc(t, '.');
            txt_adds(t, digits + exp10 + 1);
        } else {
            txt_adds(t, "0.");
            for(int i = 0; i < -exp10-1; i++) txt_addc(t, '0');
            txt_adds(t, digits);
        }
    } else {
        txt_addc(t, digits[0]);
        txt_addc(t, '.');
        txt_adds(t, ndig > 1 ? digits+1 : "0");
        char e[16];
        snprintf(e, sizeof(e), "e%c%02d", exp10 < 0 ? '-' : '+',
                 exp10 < 0 ? -exp10 : exp10);
        txt_adds(t, e);
    }
}

/* 整数を浮動小数点の表記で書く（`16` が `16.0` になる）。 */
static void txt_float_int(TxtBuf *t, uint256_t v){
    int neg = 0;
    if(u256_lt_signed(v, u256_zero())){ neg = 1; v = u256_sub(u256_zero(), v); }
    char rev[96];
    int n = 0;
    uint256_t ten = u256_from_u64(10);
    if(u256_is_zero(v)) rev[n++] = '0';
    while(!u256_is_zero(v) && n < (int)sizeof(rev)){
        uint256_t q = u256_udiv(v, ten);
        rev[n++] = (char)('0' + (int)u256_to_u64(u256_sub(v, u256_mul(q, ten))));
        v = q;
    }
    char all[128];
    for(int i = 0; i < n; i++) all[i] = rev[n-1-i];
    all[n] = '\0';
    int exp10 = n - 1;
    if(n > TXT_FLOAT_PREC){
        int round_up = (all[TXT_FLOAT_PREC] >= '5');
        all[TXT_FLOAT_PREC] = '\0';
        n = TXT_FLOAT_PREC;
        if(round_up){
            int i = n - 1;
            while(i >= 0){
                if(all[i] != '9'){ all[i]++; break; }
                all[i--] = '0';
            }
            if(i < 0){ memmove(all+1, all, (size_t)n+1); all[0] = '1'; exp10++; }
        }
    }
    txt_float_emit(t, neg, all, n, exp10);
}

/* double を浮動小数点の表記で書く。 */
static void txt_float_double(TxtBuf *t, double d){
    if(!(d == d) || d > 1.0e308*10 || d < -1.0e308*10){
        txt_adds(t, (d == d) ? (d > 0 ? "inf" : "-inf") : "nan");
        return;
    }
    char buf[64];
    snprintf(buf, sizeof(buf), "%.*e", TXT_FLOAT_PREC-1, d);
    int neg = 0, k = 0;
    if(buf[k] == '-'){ neg = 1; k++; }
    char digits[TXT_FLOAT_PREC+1];
    int n = 0;
    for(; buf[k] && buf[k] != 'e' && buf[k] != 'E'; k++)
        if(buf[k] != '.' && n < TXT_FLOAT_PREC) digits[n++] = buf[k];
    digits[n] = '\0';
    int exp10 = (buf[k] == 'e' || buf[k] == 'E') ? atoi(buf+k+1) : 0;
    txt_float_emit(t, neg, digits, n, exp10);
}

/* 対応する閉じ括弧の位置。 */
static int txt_close_paren(const char *s, int i){
    int depth = 0;
    for(; s[i]; i++){
        if(s[i]=='(') depth++;
        else if(s[i]==')'){ if(--depth == 0) return i; }
    }
    return -1;
}

/* 変換名（`.hex` `.dec` `.bin` `.float` など）を読む。 */
static int txt_conv_name(const char *s, int *kind){
    static const struct { const char *n; int k; } tbl[] = {
        {"float",3},{"hex",0},{"dec",1},{"bin",2},{NULL,0}
    };
    for(int i=0; tbl[i].n; i++){
        size_t l = strlen(tbl[i].n);
        size_t j = 0;
        while(j < l && s[j] && axx_upper_char(s[j]) == axx_upper_char(tbl[i].n[j])) j++;
        if(j == l && s[l]=='('){ *kind = tbl[i].k; return (int)l; }
    }
    return 0;
}

/* 式を評価してテキストとして積む。 */
static void txt_emit_expr(Assembler *asmb, TxtBuf *t, const char *expr, int kind){
    AsmState *st = &asmb->st;
    int io;
    int saved_undef = st->error_undefined_label;
    st->error_undefined_label = 0;
    uint256_t v = expr_expression_pat(asmb, expr, 0, &io);
    if(st->error_undefined_label) saved_undef = 1;
    st->error_undefined_label = saved_undef;

    if(u256_is_undef(v)){ txt_adds(t, "UNDEF"); return; }
    switch(kind){
    case 0: txt_radix(t, v, 16); break;
    case 2: txt_radix(t, v, 2);  break;
    case 3:
        if(st->exp_typ_float) txt_float_double(t, u256_to_double(v));
        else                  txt_float_int(t, v);
        break;
    default: txt_radix(t, v, 10); break;
    }
}

/* 単独の名前を解決して積む。順序は文字列シンボル、配列シンボル、式。
   数値シンボルは 1 番目では引かないので、ただの単語が黙って数値に化けない。 */
static void txt_emit_name(Assembler *asmb, TxtBuf *t, const char *name, int len){
    AsmState *st = &asmb->st;
    char key[512];
    if(len >= (int)sizeof(key)) len = (int)sizeof(key)-1;
    for(int k=0;k<len;k++) key[k] = (char)axx_upper_char(name[k]);
    key[len] = '\0';

    const char *sv = strsym_get(st, key);
    if(sv){ txt_adds(t, sv); return; }

    struct ArrSym *ar = arrsym_get(st, key);
    if(ar){
        for(int k=0;k<ar->len;k++){
            if(k) txt_addc(t, ',');
            if(ar->items[k].is_str) txt_adds(t, ar->items[k].s);
            else                    txt_radix(t, ar->items[k].v, 10);
        }
        return;
    }

    if(is_var_name_n(name, len)){
        int vs = var_slot(name, len, 0);
        if(vs >= 0){ txt_radix(t, st->vars[vs].val, 10); return; }
    }
    txt_addn(t, name, (size_t)len);
}

static int txt_arr_index_check(Assembler *asmb, struct ArrSym *ar, const char *key,
                               int64_t n, int64_t *out){
    if(n < 0 || n >= ar->len){
        if(should_report_errors(&asmb->st))
            axx_diagf(1, 0, " error - index %lld is out of range for array symbol "
                       "'%s' (0..%d).\n", (long long)n, key, ar->len-1);
        return 0;
    }
    *out = n;
    return 1;
}

/* 添字に書かれた文字列リテラルを中身に開く。これがあるので `arr["CX"]` は
   `arr[CX]` と同じに読まれる。 */
static int txt_quoted_text(const char *t, char *out, size_t cap){
    const char *delim;
    size_t dl;
    if(t[0]=='\\' && t[1]=='"'){ delim = "\\\""; dl = 2; }
    else if(t[0]=='"'){ delim = "\""; dl = 1; }
    else return 0;
    size_t w = 0;
    for(size_t i = dl; t[i]; ){
        if(strncmp(t+i, delim, dl)==0){
            const char *tail = t + i + dl;
            while(*tail==' '||*tail=='\t') tail++;
            if(*tail) return 0;
            out[w] = '\0';
            return 1;
        }
        char c = t[i];
        if(c=='\\' && t[i+1]){
            switch(t[i+1]){
            case 'n':  c = '\n';  break;
            case 't':  c = '\t';  break;
            case 'r':  c = '\r';  break;
            case '\\': c = '\\'; break;
            case '"':  c = '"';   break;
            default:   c = t[i+1]; break;
            }
            i += 2;
        } else i++;
        if(w + 1 >= cap) return 0;
        out[w++] = c;
    }
    return 0;
}

static int txt_arr_index_of(Assembler *asmb, struct ArrSym *ar, const char *key,
                            const char *idxtext, int64_t *out){
    AsmState *st = &asmb->st;
    char cur[1024], nm[512], up[512], qbuf[1024];
    snprintf(cur, sizeof(cur), "%s", idxtext ? idxtext : "");
    {
        const char *p = cur;
        while(*p==' '||*p=='\t') p++;
        if(txt_quoted_text(p, qbuf, sizeof(qbuf)))
            snprintf(cur, sizeof(cur), "%s", qbuf);
    }
    int have = bare_name_of(cur, nm, sizeof(nm));
    if(have){
        axx_strupr_to(up, nm, sizeof(up));
        const char *sv = strsym_get(st, up);
        if(sv){
            snprintf(cur, sizeof(cur), "%s", sv);
            have = bare_name_of(cur, nm, sizeof(nm));
            if(have) axx_strupr_to(up, nm, sizeof(up));
        }
    }
    int is_var = 0;
    if(have){
        int len = (int)strlen(nm);
        if(is_var_name_n(nm, len) && var_slot(nm, len, 0) >= 0) is_var = 1;
    }
    if(have && !is_var){
        for(int k=0;k<ar->len;k++){
            if(!ar->items[k].is_str) continue;
            char ib[512];
            axx_strupr_to(ib, ar->items[k].s, sizeof(ib));
            if(strcmp(ib, up)==0){ *out = k; return 1; }
        }
        uint256_t sv2;
        if(smap_get(&st->symbols, up, &sv2))
            return u256_is_undef(sv2) ? 0
                 : txt_arr_index_check(asmb, ar, key, u256_to_i64(sv2), out);
    }
    int io;
    int saved_undef = st->error_undefined_label;
    st->error_undefined_label = 0;
    uint256_t iv = expr_expression_pat(asmb, cur, 0, &io);
    if(st->error_undefined_label) saved_undef = 1;
    st->error_undefined_label = saved_undef;
    /* 添字が未定義なら、未定義はすでに報告済みなので、範囲外とは報告せずに
       引けなかったことにする。axx.py の _arr_index_check() と同じ。 */
    if(u256_is_undef(iv)) return 0;
    return txt_arr_index_check(asmb, ar, key, u256_to_i64(iv), out);
}

static void txt_emit_indexed(Assembler *asmb, TxtBuf *t,
                             const char *name, int len, const char *idxtext){
    AsmState *st = &asmb->st;
    char key[512];
    if(len >= (int)sizeof(key)) len = (int)sizeof(key)-1;
    for(int k=0;k<len;k++) key[k] = (char)axx_upper_char(name[k]);
    key[len] = '\0';

    struct ArrSym *ar = arrsym_get(st, key);
    if(!ar){
        if(should_report_errors(st))
            axx_diagf(1, 0, " error - '%s' is not an array symbol; '%s[...]' "
                       "needs '.setsym::%s::[...]'.\n", key, key, key);
        return;
    }
    int64_t n;
    if(!txt_arr_index_of(asmb, ar, key, idxtext, &n)) return;
    if(ar->items[n].is_str) txt_adds(t, ar->items[n].s);
    else                    txt_radix(t, ar->items[n].v, 10);
}

/* 対応する閉じブラケットの位置。 */
static int txt_close_bracket(const char *s, int i){
    int depth = 0;
    for(; s[i]; i++){
        if(s[i]=='[') depth++;
        else if(s[i]==']'){ if(--depth == 0) return i; }
    }
    return -1;
}

/* 単独の名前の長さ。 */
static int txt_bare_name_len(const char *s){
    int i = 0;
    while(s[i]==' '||s[i]=='\t') i++;
    int a = i;
    if(!((s[i]>='a'&&s[i]<='z')||(s[i]>='A'&&s[i]<='Z')||s[i]=='_')) return 0;
    while((s[i]>='a'&&s[i]<='z')||(s[i]>='A'&&s[i]<='Z')
          ||(s[i]>='0'&&s[i]<='9')||s[i]=='_') i++;
    int len = i - a;
    while(s[i]==' '||s[i]=='\t') i++;
    return s[i] ? 0 : len;
}

/* `.index` の 2 つの書き方の両方を読む。 */
static int txt_index_call(const char *s, char *name, size_t ncap, char **idx){
    static const char *w = "INDEX";
    int k = 0;
    for(; k < 5; k++) if(axx_upper_char(s[k]) != w[k]) return 0;
    if(!(s[k]==' ' || s[k]=='\t' || s[k]=='(')) return 0;
    char *body = strdup(s + k);
    if(!body){ perror("strdup"); exit(1); }
    char *b = body;
    while(*b==' '||*b=='\t') b++;
    size_t bl = strlen(b);
    while(bl > 0 && (b[bl-1]==' '||b[bl-1]=='\t')) b[--bl] = '\0';
    if(*b=='('){
        int cp = txt_close_paren(b, 0);
        if(cp < 0){ free(body); return 0; }
        const char *tail = b + cp + 1;
        while(*tail==' '||*tail=='\t') tail++;
        if(*tail){ free(body); return 0; }
        b[cp] = '\0';
        b++;
        while(*b==' '||*b=='\t') b++;
        bl = strlen(b);
        while(bl > 0 && (b[bl-1]==' '||b[bl-1]=='\t')) b[--bl] = '\0';
    }
    char *p = b;
    if(!(isalpha((unsigned char)*p) || *p=='_')){ free(body); return 0; }
    char *nb = p;
    while(isalnum((unsigned char)*p) || *p=='_') p++;
    size_t n = (size_t)(p - nb);
    char *q = p;
    while(*q==' '||*q=='\t') q++;
    if(*q != '['){ free(body); return 0; }
    int cb = txt_close_bracket(q, 0);
    if(cb < 0){ free(body); return 0; }
    const char *tail = q + cb + 1;
    while(*tail==' '||*tail=='\t') tail++;
    if(*tail || n >= ncap){ free(body); return 0; }
    q[cb] = '\0';
    memcpy(name, nb, n); name[n] = '\0';
    *idx = strdup(q + 1);
    if(!*idx){ perror("strdup"); exit(1); }
    free(body);
    return 1;
}

/* 項目ではなく添字そのものを 10 進で積む。名前から番号への引き当て。 */
static void txt_emit_index(Assembler *asmb, TxtBuf *t, const char *name, const char *idxtext){
    AsmState *st = &asmb->st;
    char key[512];
    axx_strupr_to(key, name, sizeof(key));
    struct ArrSym *ar = arrsym_get(st, key);
    if(!ar){
        if(should_report_errors(st))
            axx_diagf(1, 0, " error - '%s' is not an array symbol; '.index %s[...]' "
                       "needs '.setsym::%s::[...]'.\n", key, key, key);
        return;
    }
    int64_t n;
    if(!txt_arr_index_of(asmb, ar, key, idxtext, &n)) return;
    txt_radix(t, u256_from_i64(n), 10);
}

/* `.exp(変数)` の形を読む。 */
static int txt_exp_call(const char *s, char *name, size_t ncap){
    static const char *w = "EXP";
    int k = 0;
    for(; k < 3; k++) if(axx_upper_char(s[k]) != w[k]) return 0;
    if(!(s[k]==' ' || s[k]=='\t' || s[k]=='('))
        return 0;
    char *body = strdup(s + k);
    if(!body){ perror("strdup"); exit(1); }
    char *b = body;
    while(*b==' '||*b=='\t') b++;
    size_t bl = strlen(b);
    while(bl > 0 && (b[bl-1]==' '||b[bl-1]=='\t')) b[--bl] = '\0';
    if(*b != '('){ free(body); return 0; }
    int cb = txt_close_paren(b, 0);
    if(cb < 0){ free(body); return 0; }
    const char *tail = b + cb + 1;
    while(*tail==' '||*tail=='\t') tail++;
    if(*tail){ free(body); return 0; }
    b[cb] = '\0';
    char *nm = b + 1;
    while(*nm==' '||*nm=='\t') nm++;
    size_t nl2 = strlen(nm);
    while(nl2 > 0 && (nm[nl2-1]==' '||nm[nl2-1]=='\t')) nm[--nl2] = '\0';
    if(nl2 == 0 || (int)nl2 != var_name_len(nm) || nl2 >= ncap){
        free(body); return 0;
    }
    memcpy(name, nm, nl2 + 1);
    free(body);
    return 1;
}

/* 変数が捕捉した綴りを、ソースに書かれていたまま積む。 */
static void txt_emit_exp(Assembler *asmb, TxtBuf *t, const char *name){
    AsmState *st = &asmb->st;
    int slot = var_slot(name, (int)strlen(name), 0);
    if(slot < 0){
        if(should_report_errors(st))
            axx_diagf(1, 0, " error - '%s' is not a pattern variable; '.exp(%s)' "
                       "needs '%s' captured in the instruction field.\n", name, name, name);
        return;
    }
    int off = st->vars[slot].text_off;
    if(off < 0 || off >= st->captext_len) return;
    txt_adds(t, st->captext + off);
}

/* テンプレートを展開してテキストを作る。 */
static void txt_render(Assembler *asmb, TxtBuf *t, const char *s){
    AsmState *st = &asmb->st;
    for(int i = 0; s[i]; ){
        if(s[i]=='\\' && s[i+1]){
            switch(s[i+1]){
            case 'n':  txt_addc(t, '\n');  break;
            case 't':  txt_addc(t, '\t');  break;
            case 'r':  txt_addc(t, '\r');  break;
            case '\\': txt_addc(t, '\\'); break;
            case '"':  txt_addc(t, '"');   break;
            default:   txt_addc(t, s[i+1]); break;
            }
            i += 2; continue;
        }
        if(s[i]=='{' && s[i+1]=='{'){
            const char *e = strstr(s+i+2, "}}");
            if(!e){ txt_addc(t, s[i++]); continue; }
            int n = (int)(e - (s+i+2));
            char *inner = malloc((size_t)n + 1);
            if(!inner){ perror("malloc"); exit(1); }
            memcpy(inner, s+i+2, (size_t)n); inner[n] = '\0';
            int j = 0; while(inner[j]==' ') j++;
            int kind = -1, nl = 0;
            int done = 0;
            if(inner[j]=='.'){
                char enm[512];
                if(txt_exp_call(inner+j+1, enm, sizeof(enm))){
                    txt_emit_exp(asmb, t, enm);
                    done = 1;
                }
            }
            if(!done && inner[j]=='.'){
                char inm[512]; char *iex = NULL;
                if(txt_index_call(inner+j+1, inm, sizeof(inm), &iex)){
                    txt_emit_index(asmb, t, inm, iex);
                    free(iex);
                    done = 1;
                }
            }
            if(!done && inner[j]=='.') nl = txt_conv_name(inner+j+1, &kind);
            if(nl){
                int cp = txt_close_paren(inner, j+1+nl);
                if(cp > 0){
                    inner[cp] = '\0';
                    txt_emit_expr(asmb, t, inner + j + 1 + nl + 1, kind);
                    done = 1;
                }
            }
            if(!done){
                int bs = 0; while(inner[bs]==' '||inner[bs]=='\t') bs++;
                int be = bs;
                if((inner[be]>='a'&&inner[be]<='z')||(inner[be]>='A'&&inner[be]<='Z')
                   || inner[be]=='_'){
                    while((inner[be]>='a'&&inner[be]<='z')||(inner[be]>='A'&&inner[be]<='Z')
                          ||(inner[be]>='0'&&inner[be]<='9')||inner[be]=='_') be++;
                    int bq = be; while(inner[bq]==' '||inner[bq]=='\t') bq++;
                    if(inner[bq]=='['){
                        int cb = txt_close_bracket(inner, bq);
                        if(cb > 0){
                            int tail = cb+1;
                            while(inner[tail]==' '||inner[tail]=='\t') tail++;
                            if(!inner[tail]){
                                inner[cb] = '\0';
                                txt_emit_indexed(asmb, t, inner+bs, be-bs, inner+bq+1);
                                done = 1;
                            }
                        }
                    }
                }
            }
            if(!done){
                int bl = txt_bare_name_len(inner);
                if(bl > 0){
                    char bk[512];
                    int bs = 0; while(inner[bs]==' '||inner[bs]=='\t') bs++;
                    int bn = bl < (int)sizeof(bk) ? bl : (int)sizeof(bk)-1;
                    for(int k=0;k<bn;k++) bk[k] = (char)axx_upper_char(inner[bs+k]);
                    bk[bn] = '\0';
                    if(strsym_get(st, bk) || arrsym_get(st, bk)){
                        txt_emit_name(asmb, t, inner+bs, bn);
                        done = 1;
                    }
                }
            }
            if(!done) txt_emit_expr(asmb, t, inner, -1);
            free(inner);
            i += n + 4;
            continue;
        }
        txt_addc(t, s[i++]);
    }
}

/* テンプレートの外側の引用符を外す。 */
static char *txt_template_inner(const char *q){
    size_t n = strlen(q);
    char *r = malloc(n + 1);
    if(!r){ perror("malloc"); exit(1); }
    size_t w = 0;
    for(size_t i = 1; i < n; i++){
        if(q[i]=='\\' && q[i+1]){ r[w++]=q[i]; r[w++]=q[i+1]; i++; continue; }
        if(q[i]=='"') break;
        r[w++] = q[i];
    }
    r[w] = '\0';
    return r;
}

/* 出力欄を評価して、その行のワード列を作る。
   先に繰り返しと `%%` の添字を展開し、残りをカンマで 1 要素ずつ見る。要素は
   二重引用符ならテキストテンプレート（UTF-8 の 1 バイトが 1 ワード。ワード幅を
   超えるバイトは警告して切る）、`.call` ならミニ言語、空ならアラインメント、
   ほかは式。頭の `;` は値が 0 のとき飛ばし、`;;` は評価して捨てる。 */
static void makeobj(Assembler *asmb, const char *s_in, IntVec *objl){
    AsmState *st=&asmb->st;
    iv_clear(objl);

    TxtBuf txtacc;  txt_init(&txtacc);
    TxtBuf dispacc; txt_init(&dispacc);
    int have_text = 0;

    size_t ep_cap = 8192;
    char *ep_buf = NULL;
    int is_empty = 0;

    PatVar saved_vars[NVARS];
    memcpy(saved_vars, st->vars, sizeof(saved_vars));
    int saved_elf_refs_len = st->elf_refs_len;
    struct {int set; char *label_name; uint64_t label_val;} saved_vtl[NVARS];
    int saved_nvars = g_nvars;
    for(int vi=0;vi<saved_nvars;vi++){
        saved_vtl[vi].set       = st->elf_var_to_label[vi].set;
        saved_vtl[vi].label_val = st->elf_var_to_label[vi].label_val;
        saved_vtl[vi].label_name = st->elf_var_to_label[vi].label_name
                                   ? strdup(st->elf_var_to_label[vi].label_name)
                                   : NULL;
    }

    int first_try = 1;
    while(1){
        ep_buf = realloc(ep_buf, ep_cap);
        if(!ep_buf){ perror("realloc"); exit(1); }
        memset(ep_buf, 0, ep_cap);
        if(!first_try){
            memcpy(st->vars, saved_vars, sizeof(saved_vars));
            vars_touch_all();
            for(int ri2=saved_elf_refs_len; ri2<st->elf_refs_len; ri2++)
                free(st->elf_refs[ri2].name);
            st->elf_refs_len = saved_elf_refs_len;
            for(int vi=0;vi<saved_nvars;vi++){
                free(st->elf_var_to_label[vi].label_name);
                st->elf_var_to_label[vi].set       = saved_vtl[vi].set;
                st->elf_var_to_label[vi].label_val = saved_vtl[vi].label_val;
                st->elf_var_to_label[vi].label_name = saved_vtl[vi].label_name
                                                       ? strdup(saved_vtl[vi].label_name)
                                                       : NULL;
            }
        }
        first_try = 0;
        e_p(s_in, ep_buf, ep_cap, &is_empty, asmb, 0);
        size_t used = strlen(ep_buf);
        if(used < ep_cap - 16) break;
        ep_cap *= 2;
        if(ep_cap > (size_t)256*1024*1024){
            fprintf(stderr,"makeobj: expanded pattern too large (>256 MB), truncating.\n");
            break;
        }
    }
    for(int vi=0;vi<saved_nvars;vi++) free(saved_vtl[vi].label_name);
    if(is_empty){ free(ep_buf); free(txtacc.b); free(dispacc.b); return; }

    size_t s_cap = strlen(ep_buf) + 64;
    char *s = NULL;
    while(1){
        char *s_new = realloc(s, s_cap);
        if(!s_new){ perror("malloc"); free(s); free(ep_buf); free(txtacc.b); free(dispacc.b); return; }
        s = s_new;
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
    if((size_t)slen + 1 < s_cap) s[slen+1] = '\0';
    else { char *s2 = realloc(s, (size_t)slen + 2); if(s2){ s = s2; s_cap = (size_t)slen + 2; s[slen+1] = '\0'; } }
    const char *_prev_slen_ptr = g_expr_slen_ptr;
    int         _prev_slen_len = g_expr_slen_len;
    g_expr_slen_ptr = s;
    g_expr_slen_len = slen;

    st->in_binary_list = 1;
    int _prior_undef = st->error_undefined_label;
    st->error_undefined_label = 0;

    int idx=0;
    while(1){
        if(idx>=slen||s[idx]=='\0') break;
        if(s[idx]==','){
            idx++;
            continue;
        }
        int semicolon=0, drop=0;
        if(s[idx]==';'){
            semicolon=1; idx++;
            if(s[idx]==';'){ drop=1; idx++; }
        }
        {
            int qs = idx;
            while(s[qs]==' '||s[qs]=='\t') qs++;
            if(s[qs]=='"'){
                char *inner = txt_template_inner(s+qs);
                TxtBuf t; txt_init(&t);
                txt_render(asmb, &t, inner);
                free(inner);
                const char *txt = t.b ? t.b : "";
                if(!(drop || (semicolon && txt[0]=='\0'))){
                    uint64_t word_mask = (st->bts > 0) ? axx_word_mask(st->bts) : 0xFFu;
                    int trunc = 0;
                    for(const unsigned char *bp=(const unsigned char *)txt; *bp; bp++){
                        if((uint64_t)*bp > word_mask) trunc = 1;
                        iv_push(objl, u256_from_u64((uint64_t)*bp));
                    }
                    if(trunc && !st->pass1_size_mode && should_report_errors(st)){
                        char r[1024]; m_pyrepr(txt, r, sizeof(r));
                        axx_diagf(0, 0, " warning - text template: one or more bytes exceed the "
                                        "output word width (%d bit(s)) and were truncated "
                                        "(high bits discarded): %s\n", st->bts, r);
                    }
                    txt_adds(&txtacc, txt);
                    if(have_text) txt_addc(&dispacc, ',');
                    txt_addc(&dispacc, '"');
                    txt_add_escaped(&dispacc, txt);
                    txt_addc(&dispacc, '"');
                    have_text = 1;
                }
                free(t.b);
                int closed = 0;
                idx = qs + 1;
                while(s[idx]){
                    if(s[idx]=='\\' && s[idx+1]){ idx+=2; continue; }
                    if(s[idx]=='"'){ idx++; closed=1; break; }
                    idx++;
                }
                if(!closed && !st->pass1_size_mode && should_report_errors(st)){
                    char r[1024]; m_pyrepr(s+qs, r, sizeof(r));
                    axx_diagf(0, 0, " warning - unterminated string literal in pattern encoding "
                                    "field: %s\n", r);
                }
                while(s[idx]==' '||s[idx]=='\t') idx++;
                if(s[idx]==','){ idx++; continue; }
                break;
            }
        }
        if(s[idx]=='.' && axx_upper_char(s[idx+1])=='C' && axx_upper_char(s[idx+2])=='A'
           && axx_upper_char(s[idx+3])=='L' && axx_upper_char(s[idx+4])=='L'
           && !(isalnum((unsigned char)s[idx+5]) || s[idx+5]=='_')){
            IntVec callw; iv_init(&callw);
            int _call_widx = objl->len;
            st->elf_current_word_idx = _call_widx;
            idx = mini_call_binary(asmb, s, idx, &callw);
            if(!(drop || (semicolon && callw.len == 1 && u256_is_zero(callw.data[0])))){
                for(int q = 0; q < callw.len; q++) iv_push(objl, callw.data[q]);
            } else {
                int _wi3 = 0;
                for(int _ri3 = 0; _ri3 < st->elf_refs_len; _ri3++){
                    if(st->elf_refs[_ri3].word_idx != _call_widx)
                        st->elf_refs[_wi3++] = st->elf_refs[_ri3];
                    else
                        free(st->elf_refs[_ri3].name);
                }
                st->elf_refs_len = _wi3;
            }
            st->elf_current_word_idx = -1;
            iv_free(&callw);
            if(s[idx]==','){ idx++; continue; }
            break;
        }
        int cur_widx = objl->len;
        st->elf_current_word_idx = cur_widx;
        if(st->pas==1) st->pass1_size_mode=1;
        int io;
        uint256_t x=expr_expression_pat(asmb,s,idx,&io);
        if(st->pas==1){ st->pass1_size_mode=0; st->error_undefined_label=0; }
        idx=io;
        if(!drop && (semicolon ? !u256_is_zero(x) : 1)){
            iv_push(objl,x);
        } else {
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
    g_expr_slen_ptr = _prev_slen_ptr;
    g_expr_slen_len = _prev_slen_len;
    if(_prior_undef) st->error_undefined_label = 1;
    if(have_text){
        free(st->asmtext);
        st->asmtext = txtacc.b ? txtacc.b : strdup("");
        free(st->asmtext_disp);
        st->asmtext_disp = dispacc.b ? dispacc.b : strdup("");
    } else {
        free(txtacc.b);
        free(dispacc.b);
    }
    free(s);
}

typedef struct { IntVec *data; int len; int cap; } IVVec;
static void ivv_init(IVVec*v){v->data=NULL;v->len=0;v->cap=0;}
/* ワード列の並びに 1 本積む。 */
static void ivv_push(IVVec*v,IntVec*iv){
    if(v->len>=v->cap){
        v->cap=v->cap?v->cap*2:8;
        v->data=realloc(v->data,v->cap*sizeof(IntVec));
        if(!v->data){perror("realloc");exit(1);}
    }
    IntVec *dst=&v->data[v->len++]; iv_init(dst); iv_copy(dst,iv);
}
/* ワード列の並びを解放する。 */
static void ivv_free(IVVec*v){
    for(int i=0;i<v->len;i++) iv_free(&v->data[i]);
    free(v->data); ivv_init(v);
}

/* int の比較関数（現在は未使用）。 */
AXX_UNUSED static int int_cmp(const void*a,const void*b){
    int ia=*(const int*)a, ib=*(const int*)b;
    return (ia > ib) - (ia < ib);
}

static int vliwprocess(Assembler *asmb, const char *line, IntVec *idxs_in, IntVec *objl_in,
                       int idx, int *idx_out){
    AsmState *st=&asmb->st;
    IVVec objs; ivv_init(&objs);
    ivv_push(&objs,objl_in);

    int *idxlst=NULL; int nidxlst=0; int capidxlst=0;
    for(int i=0;i<idxs_in->len;i++)
        ilst_push(&idxlst,&nidxlst,&capidxlst,(int)u256_to_i64(idxs_in->data[i]));

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
            for(int i=0;i<new_idxs.len;i++)
                ilst_push(&idxlst,&nidxlst,&capidxlst,(int)u256_to_i64(new_idxs.data[i]));
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
        int match = (k->nidxs == nidxlst);
        if(match){
            for(int mi=0; mi<nidxlst; mi++)
                if(k->idxs[mi] != idxlst[mi]){ match = 0; break; }
        }
        if(!match && st->vliwtemplatebits!=0) continue;

        int io;
        int _tmpl_prior_undef = st->error_undefined_label;
        st->error_undefined_label = 0;
        uint256_t xv=expr_expression_pat(asmb,k->templ,0,&io);
        if(st->error_undefined_label && should_report_errors(st)){
            st->had_error = 1;
        }
        st->error_undefined_label = _tmpl_prior_undef || st->error_undefined_label;
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
            for(int pi=0;pi<needed;pi++){
                uint256_t nv = (st->vliwnop.len > 0)
                             ? st->vliwnop.data[pi % st->vliwnop.len]
                             : u256_zero();
                iv_push(&values, nv);
            }
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

/* ---- ソース側ディレクティブ ---------------------------------------------
   パターンファイルに関係なく常に使えるのはここにあるものだけ。`DB` のような
   バイト出力ニーモニックは組み込みではなく、パターンファイルが定義したときに
   だけ存在する。
   ------------------------------------------------------------------------ */
/* `.labelc` — ラベルに使える文字を増やす。 */
static int adir_labelc(AsmState *st, const char *l, const char *ll){
    char up[32]; axx_strupr_to(up,l,sizeof(up));
    if(strcmp(up,".LABELC")!=0) return 0;
    if(ll&&ll[0]){
        snprintf(st->lwordchars, sizeof(st->lwordchars),
                 "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789%s", ll);
    }
    return 1;
}

/* 行頭の `label:` と `.equ` を処理する。`.equ` のラベルは再配置情報を失い、
   定数として扱われる。 */
static int elf_sec_name_cmp(const void *a, const void *b);
static char *adir_label_processing(Assembler *asmb, const char *l, char *out, size_t osz){
    AsmState *st=&asmb->st;
    if(!l[0]){ out[0]=0; return out; }
    char lblbuf[512]; size_t lblsz;
    char *label = axx_word_buf(l, 0, lblbuf, sizeof(lblbuf), &lblsz);
    int idx;
    idx=axx_get_label_word(l,0,st->lwordchars,label,lblsz);
    int lidx=idx;
    if(label[0]&&lidx>0&&l[lidx-1]==':'){
        idx=axx_skipspc(l,idx);
        char e[256]; idx=axx_get_param_to_spc(l,idx,e,sizeof(e));
        char ue[256]; axx_strupr_to(ue,e,sizeof(ue));
        if(strcmp(ue,".EQU")==0){
            int io;
            /* 式の部分は前後の空白を落としてから評価する（axx.py の
               `l[idx:].strip()` と同じ）。診断に出す位置がそろう。 */
            const char *expr_tail = l + axx_skipspc(l, idx);
            int reloc_type = -1;
            const char *dcolon = strstr(expr_tail, "::");
            size_t elen = dcolon ? (size_t)(dcolon - expr_tail) : strlen(expr_tail);
            while(elen > 0 && (expr_tail[elen-1]==' ' || expr_tail[elen-1]=='\t')) elen--;
            char *expr_buf = malloc(elen + 1);
            if(!expr_buf){ perror("malloc"); exit(1); }
            memcpy(expr_buf, expr_tail, elen); expr_buf[elen] = '\0';
            expr_tail = expr_buf;
            if(dcolon){
                const char *rt_str = dcolon + 2;
                rt_str += axx_skipspc(rt_str, 0);
                char *rt_lc = malloc(strlen(rt_str) + 1);
                if(!rt_lc){ perror("malloc"); exit(1); }
                int ri=0;
                while(rt_str[ri]){ rt_lc[ri]=(char)tolower((unsigned char)rt_str[ri]); ri++; }
                while(ri > 0 && (rt_lc[ri-1]==' ' || rt_lc[ri-1]=='\t')) ri--;
                rt_lc[ri]='\0';
                reloc_type = elf_reloc_named(st, elf_machine_effective(st), rt_lc);
                if(reloc_type < 0)
                    axx_diagf(0, 0, " warning - unknown reloctype '%s' in .EQU for machine %d\n",
                               rt_lc, st->elf_machine);
                free(rt_lc);
            }

            uint256_t u;
            st->error_undefined_label = 0;
            int saved_mode = st->pass1_size_mode;
            if(st->pas == 1)
                st->pass1_size_mode = 1;
            int track_sections = (reloc_type < 0);
            if(track_sections){
                st->equ_section_tracking = 1;
                for(int _i = 0; _i < st->equ_nsecs; _i++) free(st->equ_secs[_i]);
                st->equ_nsecs = 0;
            }
            u = expr_expression_asm(asmb, expr_tail, 0, &io);
            st->pass1_size_mode = saved_mode;
            if(track_sections){
                st->equ_section_tracking = 0;
                if(st->equ_nsecs > 1 && should_report_errors(st)){
                    /* 名前を並べて ", " でつなぐ（axx.py の sorted() と同じ順）。 */
                    qsort(st->equ_secs, (size_t)st->equ_nsecs, sizeof(char*), elf_sec_name_cmp);
                    size_t _ln = 1;
                    for(int _i = 0; _i < st->equ_nsecs; _i++) _ln += strlen(st->equ_secs[_i]) + 2;
                    char *_lst = malloc(_ln);
                    if(!_lst){ perror("malloc"); exit(1); }
                    _lst[0] = '\0';
                    for(int _i = 0; _i < st->equ_nsecs; _i++){
                        if(_i) strcat(_lst, ", ");
                        strcat(_lst, st->equ_secs[_i]);
                    }
                    axx_diagf(0, 0, " warning - .EQU '%s': expression combines labels from "
                               "multiple sections (%s) without an explicit ::reloctype; the resulting "
                               "constant assumes a specific section layout and will NOT be "
                               "relocated by the linker.\n", label, _lst);
                    free(_lst);
                }
            }
            if(st->error_undefined_label && should_report_errors(st)){
                axx_diagf(1, 0, " error - .EQU '%s': expression contains undefined label.\n",
                           label);
            }

            label_put_value(st,label,u,st->current_section,1,reloc_type,st->error_undefined_label);
            free(expr_buf);
            if(label!=lblbuf) free(label);
            if(st->textmode){
                int _n = lidx;
                if(_n > (int)sizeof(st->label_text)-1) _n = (int)sizeof(st->label_text)-1;
                memcpy(st->label_text, l, (size_t)_n);
                st->label_text[_n] = '\0';
                strncpy(out,l+lidx,osz-1); out[osz-1]=0; return out;
            }
            out[0]=0; return out;
        } else {
            int _ok = label_put_value(st,label,st->pc,st->current_section,0,-1,0);
            if(label!=lblbuf) free(label);
            /* 定義できなかった行（二重定義・パターンファイルのシンボルとの衝突
               など）は残りも組まない。axx.py の label_processing() と同じ。 */
            if(!_ok){ out[0]=0; return out; }
            { int _n = lidx;
              if(_n > (int)sizeof(st->label_text)-1) _n = (int)sizeof(st->label_text)-1;
              memcpy(st->label_text, l, (size_t)_n);
              st->label_text[_n] = '\0';
            }
            strncpy(out,l+lidx,osz-1); out[osz-1]=0; return out;
        }
    }
    if(label!=lblbuf) free(label);
    strncpy(out,l,osz-1); out[osz-1]=0; return out;
}

/* `.ascii` / `.asciz` の文字列をバイト列にする。 */
static int asciistr(Assembler *asmb, const char *l2){
    AsmState *st=&asmb->st;
    if(!l2[0]||l2[0]!='"') return 0;
    int idx=1;
    uint64_t word_mask = (st->bts > 0) ? axx_word_mask(st->bts) : 0xFFu;
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

/* `.section` / `.segment` — セクションを切り替える。これが唯一の方法で、
   `.text` のような短縮形は組み込みではない。 */
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

        st_set_current_section(st, l2);

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
/* `.endsection` / `.endsegment` — セクションを閉じる。 */
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
    if(u256_lt_signed(delta, u256_zero())){
        char db[96]; u256_to_pydec(delta, db, sizeof(db));
        if(should_report_errors(st)){
            axx_diagf(0, 0, " warning - ENDSECTION: computed block size %s < 0 for "
                       "'%s'; keeping previous size.\n", db, st->current_section);
        }
        return 1;
    }
    e->size = u256_add(e->size, delta);
    if(!u256_is_zero(delta))
        secrangevec_push(&st->section_ranges, st->current_section, e->entry_pc, delta);
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
    if(u256_lt_signed(x, u256_zero())){
        if(should_report_errors(&asmb->st)){
            char cb[96]; u256_to_pydec(x, cb, sizeof(cb));
            axx_diagf(1, 0, " error - %s requires a non-negative count, got %s.\n",
                       directive, cb);
        }
        return 1;
    }
    {
        int64_t lim = (int64_t)(1 << 28) / (int64_t)mul;
        if(cnt > lim || u256_gt_signed(x, u256_from_i64(lim))){
            if(should_report_errors(&asmb->st)){
                char cb[96]; u256_to_pydec(x, cb, sizeof(cb));
                axx_diagf(1, 0, " error - %s count %s (x%llu) exceeds maximum %d words.\n",
                           directive, cb, (unsigned long long)mul, 1<<28);
            }
            return 1;
        }
    }
    int64_t total = cnt * (int64_t)mul;
    asmb->st.pc = u256_add(asmb->st.pc, u256_from_u64((uint64_t)total));
    return 1;
}

/* `.resb` — バイトを出さず n バイト予約する。 */
static int adir_resb(Assembler *asmb, const char *l, const char *l2){
    return adir_resX(asmb,l,l2,".RESB",1);
}
/* `.resw` — n ワード予約する。 */
static int adir_resw(Assembler *asmb, const char *l, const char *l2){
    return adir_resX(asmb,l,l2,".RESW",2);
}
/* `.resd` — n ダブルワード予約する。 */
static int adir_resd(Assembler *asmb, const char *l, const char *l2){
    return adir_resX(asmb,l,l2,".RESD",4);
}
/* `.resq` — n クワッドワード予約する。 */
static int adir_resq(Assembler *asmb, const char *l, const char *l2){
    return adir_resX(asmb,l,l2,".RESQ",8);
}
/* `.zero` — ゼロバイトを並べる。 */
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
    if(u256_lt_signed(x, u256_zero())){
        if(should_report_errors(&asmb->st)){
            char cb[96]; u256_to_pydec(x, cb, sizeof(cb));
            axx_diagf(1, 0, " error - .ZERO requires a non-negative count, got %s.\n", cb);
        }
        return 1;
    }
    {
        const int64_t ZERO_MAX = (int64_t)1 << 28;
        if(cnt > ZERO_MAX || u256_gt_signed(x, u256_from_i64(ZERO_MAX))){
            if(should_report_errors(&asmb->st)){
                char cb[96]; u256_to_pydec(x, cb, sizeof(cb));
                axx_diagf(1, 0, " error - .ZERO count %s exceeds maximum %lld.\n",
                          cb, (long long)ZERO_MAX);
            }
            return 1;
        }
    }
    for(int64_t i=0;i<cnt;i++){
        outbin2(&asmb->st,asmb->st.pc,u256_from_u64(0));
        asmb->st.pc=u256_add(asmb->st.pc,u256_one());
    }
    return 1;
}
/* `.ascii` — 文字列のバイト列を出す。 */
static int adir_ascii(Assembler *asmb, const char *l, const char *l2){
    char up[16]; axx_strupr_to(up,l,sizeof(up));
    if(strcmp(up,".ASCII")!=0) return 0;
    return asciistr(asmb,l2);
}
/* `.asciz` — 文字列のバイト列と末尾の 0 を出す。 */
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
/* `.align` — 整列する。引数なしなら前回の値を使う。 */
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
/* `.org` — ロケーションカウンタを設定する。`,p` を付けるとカウンタが目標より
   下にある場合その隙間を埋める。 */
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
/* ラベルのエクスポート指定を処理する。 */
static int adir_export(Assembler *asmb, const char *l, const char *l2){
    AsmState *st=&asmb->st;
    char up[16]; axx_strupr_to(up,l,sizeof(up));
    if(strcmp(up,".EXPORT")!=0 && strcmp(up,".GLOBAL")!=0) return 0;
    if(st->pas!=2&&st->pas!=0) return 1;
    const char *buf = l2;
    int idx=0; int blen=(int)strlen(buf);
    while(idx<blen&&buf[idx]){
        idx=axx_skipspc(buf,idx);
        char sbuf[512]; size_t ssz;
        char *s = axx_word_buf(buf, idx, sbuf, sizeof(sbuf), &ssz);
        idx=axx_get_label_word(buf,idx,st->lwordchars,s,ssz);
        if(!s[0]){ if(s!=sbuf) free(s); break; }
        if(idx > 0 && buf[idx-1]==':' && idx < blen && buf[idx]==':')
            idx--;
        if(idx+1 < blen && buf[idx]==':' && buf[idx+1]==':'){
            idx += 2;
            int rt_start = idx;
            while(idx < blen && buf[idx]!=' ' && buf[idx]!='\t'
                  && buf[idx]!=',' && buf[idx]!=':' && buf[idx]!='\0')
                idx++;
            int rt_len = idx - rt_start;
            if(rt_len > 0){
                char *rt_str = malloc((size_t)rt_len + 1);
                if(!rt_str){ perror("malloc"); exit(1); }
                memcpy(rt_str, buf+rt_start, (size_t)rt_len);
                rt_str[rt_len]=0;
                for(int _ci=0;rt_str[_ci];_ci++)
                    if(rt_str[_ci]>='A'&&rt_str[_ci]<='Z') rt_str[_ci]+=32;
                int rtype = elf_reloc_named(st, elf_machine_effective(st), rt_str);
                if(rtype < 0)
                    axx_diagf(0, 0, " warning - unknown reloc type '%s' in .GLOBAL for machine %d\n",
                               rt_str, st->elf_machine);
                else
                    lmap_set_reloc_type(&st->labels, s, rtype);
                free(rt_str);
            }
        }
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
        if(s!=sbuf) free(s);
        idx=axx_skipspc(buf,idx);
        if(buf[idx]==',') idx++;
    }
    return 1;
}

/* `.extern` / `.global` — シンボルを外部と結び付ける。 */
static int adir_extern(Assembler *asmb, const char *l, const char *l2){
    AsmState *st=&asmb->st;
    char up[16]; axx_strupr_to(up,l,sizeof(up));
    if(strcmp(up,".EXTERN")!=0) return 0;
    const char *buf = l2;
    int idx=0; int blen=(int)strlen(buf);
    while(idx<blen&&buf[idx]){
        idx=axx_skipspc(buf,idx);
        char sbuf[512]; size_t ssz;
        char *s = axx_word_buf(buf, idx, sbuf, sizeof(sbuf), &ssz);
        s[0]=0;
        idx=axx_get_label_word(buf,idx,st->lwordchars,s,ssz);
        if(!s[0]){ if(s!=sbuf) free(s); break; }
        if(idx > 0 && buf[idx-1]==':' && idx < blen && buf[idx]==':')
            idx--;
        const ElfMachineInfo *_mtbl_ext = elf_machine_effective(st);
        int reloc_type = _mtbl_ext->extern_default;
        int explicit_reloc_type = 0;
        if(idx+1 < blen && buf[idx]==':' && buf[idx+1]==':'){
            idx += 2;
            int rt_start = idx;
            while(idx < blen && buf[idx]!=' ' && buf[idx]!='\t'
                  && buf[idx]!=',' && buf[idx]!=':' && buf[idx]!='\0')
                idx++;
            int rt_len = idx - rt_start;
            if(rt_len > 0){
                char *rt_str = malloc((size_t)rt_len + 1);
                if(!rt_str){ perror("malloc"); exit(1); }
                memcpy(rt_str, buf+rt_start, (size_t)rt_len);
                rt_str[rt_len]=0;
                for(int _ci=0;rt_str[_ci];_ci++)
                    if(rt_str[_ci]>='A'&&rt_str[_ci]<='Z') rt_str[_ci]+=32;
                int rtype = elf_reloc_named(st, _mtbl_ext, rt_str);
                if(rtype < 0){
                    reloc_type = -1;
                    axx_diagf(0, 0, " warning - unknown reloc type '%s' in .EXTERN for machine %d\n",
                               rt_str, st->elf_machine);
                } else {
                    reloc_type = rtype;
                    explicit_reloc_type = 1;
                }
                free(rt_str);
            }
        }
        if(idx < blen && buf[idx]==':') idx++;
        LabelEntry *existing=lmap_find(&st->labels,s);
        if(explicit_reloc_type) extern_untyped_set(st, s, 0);
        else if(!existing) extern_untyped_set(st, s, 1);
        if(!existing){
            lmap_set_imported(&st->labels, s, u256_zero(), ".text", reloc_type);
        } else if(existing->is_imported){
            if(explicit_reloc_type && existing->reloc_type_override >= 0)
                existing->reloc_type_override = reloc_type;
        } else {
            /* axx.py の extern_processing() と同じく、ここで定義済みの名前は
               外部にしない。 */
            axx_diagf(0, 0, " warning - .EXTERN: '%s' is already defined locally; "
                            "ignoring extern declaration\n", s);
        }
        if(s!=sbuf) free(s);
        idx=axx_skipspc(buf,idx);
        if(buf[idx]==',') idx++;
    }
    return 1;
}


#define SYM_DECL_MAXF 2

static int sym_decl_next(const AsmState *st, const char *buf, int blen, int *pidx,
                         char **name_out, char **fields, int nfields){
    for(int i=0;i<nfields;i++) fields[i] = NULL;
    *name_out = NULL;
    int idx = *pidx;
    if(idx >= blen) return 0;
    idx = axx_skipspc(buf, idx);
    char sbuf[512]; size_t ssz;
    char *s = axx_word_buf(buf, idx, sbuf, sizeof(sbuf), &ssz);
    s[0] = 0;
    idx = axx_get_label_word(buf, idx, st->lwordchars, s, ssz);
    if(!s[0]){ if(s!=sbuf) free(s); *pidx = blen; return 0; }
    if(idx > 0 && buf[idx-1]==':' && idx < blen && buf[idx]==':') idx--;
    int nf = 0;
    while(nf < nfields && idx+1 < blen && buf[idx]==':' && buf[idx+1]==':'){
        idx += 2;
        int fs = idx;
        while(idx < blen && buf[idx]!=' ' && buf[idx]!='\t'
              && buf[idx]!=',' && buf[idx]!=':' && buf[idx]!='\0') idx++;
        int fl = idx - fs;
        char *fv = malloc((size_t)fl + 1);
        if(!fv){ perror("malloc"); exit(1); }
        memcpy(fv, buf+fs, (size_t)fl);
        fv[fl] = 0;
        char *b = fv; while(*b==' '||*b=='\t') b++;
        int bl = (int)strlen(b);
        while(bl>0 && (b[bl-1]==' '||b[bl-1]=='\t')) b[--bl]=0;
        if(b != fv) memmove(fv, b, (size_t)bl+1);
        fields[nf++] = fv;
    }
    if(idx < blen && buf[idx]==':') idx++;
    char *nm = strdup(s);
    if(!nm){ perror("strdup"); exit(1); }
    if(s != sbuf) free(s);
    idx = axx_skipspc(buf, idx);
    if(idx < blen && buf[idx]==',') idx++;
    *pidx = idx;
    *name_out = nm;
    return 1;
}

/* シンボル属性ディレクティブの作業領域を解放する。 */
static void sym_decl_free(char **name, char **fields, int nfields){
    free(*name); *name = NULL;
    for(int i=0;i<nfields;i++){ free(fields[i]); fields[i] = NULL; }
}

static int sym_decl_num(Assembler *asmb, const char *dname, const char *name,
                        const char *text, long long lo, long long hi,
                        long long *out){
    AsmState *st = &asmb->st;
    if(!text || !text[0]){
        axx_diagf(1, 0, " error - %s: a number is required for '%s'.\n", dname, name);
        return 0;
    }
    int io;
    st->error_undefined_label = 0;
    uint256_t v = expr_expression_asm(asmb, text, 0, &io);
    int64_t n = u256_to_i64(v);
    if(st->error_undefined_label || u256_is_undef_derived(v)
       || !u256_eq(v, u256_from_i64(n)) || n < lo || n > hi){
        axx_diagf(1, 0, " error - %s: value for '%s' must be an integer in "
                        "%lld..%lld, got '%s'.\n", dname, name, lo, hi, text);
        st->error_undefined_label = 0;
        return 0;
    }
    st->error_undefined_label = 0;
    *out = (long long)n;
    return 1;
}

/* ソースの `.cfi_*` 指令 → 引数の種類（r: レジスタ、n: 数、s: シンボル名、
   *: 1 つ以上のバイト）。axx.py の _CFI_OPS と同じ表。 */
static const struct { const char *op; const char *spec; } CFI_OPS[] = {
    {"startproc", ""}, {"endproc", ""}, {"sections", ""},
    {"def_cfa", "rn"}, {"def_cfa_offset", "n"}, {"def_cfa_register", "r"},
    {"adjust_cfa_offset", "n"}, {"offset", "rn"}, {"val_offset", "rn"},
    {"rel_offset", "rn"}, {"restore", "r"}, {"undefined", "r"}, {"same_value", "r"},
    {"register", "rr"}, {"remember_state", ""}, {"restore_state", ""},
    {"return_column", "r"}, {"signal_frame", ""}, {"window_save", ""},
    {"negate_ra_state", ""}, {"escape", "*"}, {"personality", "ns"}, {"lsda", "ns"},
    {NULL, NULL}
};
static const char *cfi_spec(const char *op){
    for(int i = 0; CFI_OPS[i].op; i++) if(strcmp(CFI_OPS[i].op, op) == 0) return CFI_OPS[i].spec;
    return NULL;
}

/* CFI 指令の数の引数を読む。定数でなければ診断して 0。 */
static int cfi_num(Assembler *asmb, const char *op, const char *text, int64_t *out){
    AsmState *st = &asmb->st;
    int io;
    st->error_undefined_label = 0;
    uint256_t v = expr_expression_asm(asmb, text, 0, &io);
    int und = st->error_undefined_label || u256_is_undef_derived(v);
    st->error_undefined_label = 0;
    if(und){
        axx_diagf(1, 0, " error - .cfi_%s: '%s' is not a constant.\n", op, text);
        return 0;
    }
    *out = u256_to_i64(v);
    return 1;
}

/* CFI 指令のレジスタの引数を読む。`.elfcfireg` の名前か、0 以上の数。 */
static int cfi_reg(Assembler *asmb, const char *op, const char *text, int64_t *out){
    int r = elf_cfireg_find(&asmb->st, text);
    if(r >= 0){ *out = r; return 1; }
    if(!cfi_num(asmb, op, text, out)) return 0;
    if(*out < 0){
        axx_diagf(1, 0, " error - .cfi_%s: '%s' is not a register.\n", op, text);
        return 0;
    }
    return 1;
}

/* `.cfi_*` — CFI の指令を、その位置（セクション先頭からのワード数）と一緒に
   記録する。記録するのはパス2で `-o` のときだけ。axx.py の cfi_processing()
   と同じ規則である。 */
static int adir_cfi(Assembler *asmb, const char *l, const char *l2){
    AsmState *st = &asmb->st;
    if(strncasecmp(l, ".cfi_", 5) != 0) return 0;
    if(!(should_report_errors(st) && st->elf_objfile[0])) return 1;
    char op[64];
    snprintf(op, sizeof(op), "%s", l + 5);
    for(char *q = op; *q; q++) *q = (char)tolower((unsigned char)*q);
    const char *spec = cfi_spec(op);
    if(!spec){
        axx_diagf(1, 0, " error - unknown CFI directive '%s'.\n", l);
        return 1;
    }
    if(strcmp(op, "sections") == 0) return 1;
    /* 引数をカンマで切る */
    char *args[64]; int na = 0;
    char *buf = strdup(l2 ? l2 : "");
    if(!buf){ perror("strdup"); exit(1); }
    {
        int allsp = 1;
        for(const char *q = buf; *q; q++) if(!isspace((unsigned char)*q)){ allsp = 0; break; }
        if(!allsp){
            char *q = buf;
            while(na < 64){
                char *c = strchr(q, ',');
                if(c) *c = '\0';
                char *b = q; while(isspace((unsigned char)*b)) b++;
                char *e2 = b + strlen(b); while(e2 > b && isspace((unsigned char)e2[-1])) *--e2 = '\0';
                args[na++] = b;
                if(!c) break;
                q = c + 1;
            }
        }
    }
    const char *sec = st->current_section;
    int64_t off = equ_section_relative_offset(st, sec, u256_to_u64(st->pc));
    if(off < 0) off = (int64_t)u256_to_u64(st->pc);
    char l2t[512];
    {
        const char *b = l2 ? l2 : ""; while(isspace((unsigned char)*b)) b++;
        snprintf(l2t, sizeof(l2t), "%s", b);
        size_t n = strlen(l2t); while(n > 0 && isspace((unsigned char)l2t[n-1])) l2t[--n] = '\0';
    }
    if(strcmp(op, "startproc") == 0){
        if(st->cfi_open){
            axx_diagf(1, 0, " error - .cfi_startproc: the previous .cfi_startproc has "
                            "no .cfi_endproc.\n");
            free(buf); return 1;
        }
        if(na > 0 && !(na == 1 && strcasecmp(args[0], "simple") == 0)){
            axx_diagf(1, 0, " error - .cfi_startproc: unknown argument '%s'.\n", l2t);
            free(buf); return 1;
        }
        memset(&st->cfi_curf, 0, sizeof(st->cfi_curf));
        st->cfi_curf.sec = strdup(sec);
        st->cfi_curf.start = off; st->cfi_curf.end = off;
        st->cfi_curf.simple = na > 0;
        st->cfi_curf.ra = -1; st->cfi_curf.pers_enc = -1; st->cfi_curf.lsda_enc = -1;
        st->cfi_open = 1;
        free(buf); return 1;
    }
    if(!st->cfi_open){
        axx_diagf(1, 0, " error - .cfi_%s: not inside .cfi_startproc.\n", op);
        free(buf); return 1;
    }
    CfiFde *cur = &st->cfi_curf;
    if(strcmp(sec, cur->sec) != 0){
        axx_diagf(1, 0, " error - .cfi_%s: the section changed inside the function.\n", op);
        free(buf); return 1;
    }
    int star = strcmp(spec, "*") == 0;
    if(star){
        if(na == 0){
            axx_diagf(1, 0, " error - .cfi_%s: at least one argument is required.\n", op);
            free(buf); return 1;
        }
    } else if(na != (int)strlen(spec)){
        axx_diagf(1, 0, " error - .cfi_%s: %d argument(s) expected.\n", op, (int)strlen(spec));
        free(buf); return 1;
    }
    int64_t vals[64];
    const char *symarg = NULL;
    for(int k = 0; k < na; k++){
        char kind = star ? '*' : spec[k];
        if(kind == 'r'){
            if(!cfi_reg(asmb, op, args[k], &vals[k])){ free(buf); return 1; }
        } else if(kind == 's'){
            symarg = args[k]; vals[k] = 0;
        } else {
            if(!cfi_num(asmb, op, args[k], &vals[k])){ free(buf); return 1; }
            if(kind == '*' && (vals[k] < 0 || vals[k] > 255)){
                axx_diagf(1, 0, " error - .cfi_%s: '%s' is not a byte.\n", op, args[k]);
                free(buf); return 1;
            }
        }
    }
    if(strcmp(op, "endproc") == 0){
        cur->end = off;
        st->cfi_fdes = elf_decl_grow(st->cfi_fdes, &st->cfi_fdes_cap, st->cfi_fdes_len, sizeof(CfiFde));
        st->cfi_fdes[st->cfi_fdes_len++] = *cur;
        memset(cur, 0, sizeof(*cur));
        st->cfi_open = 0;
    } else if(strcmp(op, "return_column") == 0){
        cur->ra = (int)vals[0];
    } else if(strcmp(op, "signal_frame") == 0){
        cur->signal = 1;
    } else if(strcmp(op, "personality") == 0 || strcmp(op, "lsda") == 0){
        if(vals[0] < 0 || vals[0] > 255){
            axx_diagf(1, 0, " error - .cfi_%s: '%s' is not an encoding byte.\n", op, args[0]);
            free(buf); return 1;
        }
        int isp = op[0] == 'p';
        int *enc = isp ? &cur->pers_enc : &cur->lsda_enc;
        char **sym = isp ? &cur->pers_sym : &cur->lsda_sym;
        free(*sym); *sym = NULL;
        *enc = -1;
        if(vals[0] != 0xff){ *enc = (int)vals[0]; *sym = strdup(symarg); }
    } else {
        cur->ops = elf_decl_grow(cur->ops, &cur->cops, cur->nops, sizeof(CfiOp));
        CfiOp *o = &cur->ops[cur->nops++];
        o->off = off;
        snprintf(o->op, sizeof(o->op), "%s", op);
        o->nv = na;
        o->v = malloc(sizeof(int64_t) * (size_t)(na ? na : 1));
        if(!o->v){ perror("malloc"); exit(1); }
        for(int k = 0; k < na; k++) o->v[k] = vals[k];
    }
    free(buf);
    return 1;
}

/* `.type` — ELF シンボルの種別を書く。 */
static int adir_type(Assembler *asmb, const char *l, const char *l2){
    AsmState *st=&asmb->st;
    char up[16]; axx_strupr_to(up,l,sizeof(up));
    if(strcmp(up,".TYPE")!=0) return 0;
    if(!should_report_errors(st)) return 1;
    const char *buf = l2; int blen=(int)strlen(buf); int idx=0;
    char *nm; char *fv[SYM_DECL_MAXF];
    while(sym_decl_next(st, buf, blen, &idx, &nm, fv, 1)){
        char *kind = fv[0];
        if(!kind || !kind[0]){
            axx_diagf(1, 0, " error - .TYPE: a symbol type is required for '%s'.\n", nm);
            sym_decl_free(&nm, fv, 1);
            continue;
        }
        for(char *q=kind; *q; q++) if(*q>='A'&&*q<='Z') *q = (char)(*q+32);
        int v = -1;
        for(int i=0; ELF_SYM_TYPES[i].name; i++)
            if(strcmp(ELF_SYM_TYPES[i].name, kind)==0){ v = ELF_SYM_TYPES[i].v; break; }
        if(v < 0){
            long long n;
            if(!sym_decl_num(asmb, ".TYPE", nm, kind, 0, 15, &n)){
                sym_decl_free(&nm, fv, 1);
                continue;
            }
            v = (int)n;
        }
        int k = sym_attr_slot(st, nm);
        st->sym_attrs[k].stype = v;
        sym_decl_free(&nm, fv, 1);
    }
    return 1;
}

/* `.size` — 大きさを書く。値はワード数で、出力時に幅をかける。 */
static int adir_size(Assembler *asmb, const char *l, const char *l2){
    AsmState *st=&asmb->st;
    char up[16]; axx_strupr_to(up,l,sizeof(up));
    if(strcmp(up,".SIZE")!=0) return 0;
    if(!should_report_errors(st)) return 1;
    const char *buf = l2; int blen=(int)strlen(buf); int idx=0;
    char *nm; char *fv[SYM_DECL_MAXF];
    while(sym_decl_next(st, buf, blen, &idx, &nm, fv, 1)){
        long long n;
        if(!sym_decl_num(asmb, ".SIZE", nm, fv[0], 0, 0x7FFFFFFFFFFFFFFFll, &n)){
            sym_decl_free(&nm, fv, 1);
            continue;
        }
        int k = sym_attr_slot(st, nm);
        st->sym_attrs[k].size_set = 1;
        st->sym_attrs[k].size = (uint64_t)n;
        sym_decl_free(&nm, fv, 1);
    }
    return 1;
}

/* `.weak` — 弱シンボルにする。 */
static int adir_weak(Assembler *asmb, const char *l, const char *l2){
    AsmState *st=&asmb->st;
    char up[16]; axx_strupr_to(up,l,sizeof(up));
    if(strcmp(up,".WEAK")!=0) return 0;
    int record = should_report_errors(st);
    const char *buf = l2; int blen=(int)strlen(buf); int idx=0;
    char *nm; char *fv[SYM_DECL_MAXF];
    while(sym_decl_next(st, buf, blen, &idx, &nm, fv, 0)){
        sym_declare_extern(st, nm);
        if(!record){ sym_decl_free(&nm, fv, 0); continue; }
        int k = sym_attr_slot(st, nm);
        st->sym_attrs[k].weak = 1;
        LabelEntry *le = lmap_find(&st->labels, nm);
        if(!(le && le->is_imported)){
            uint256_t v = label_get_value(st, nm);
            const char *sec = label_get_section(st, nm);
            int is_equ_v = le ? le->is_equ : 0;
            int is_undef_v = le ? le->is_undef : 0;
            if(!lmap_find(&st->export_labels, nm)) sv_push(&st->export_order, nm);
            lmap_set(&st->export_labels, nm, v, sec, is_equ_v, is_undef_v);
        }
        sym_decl_free(&nm, fv, 0);
    }
    return 1;
}

/* `.hidden` / `.protected` / `.internal` — 可視性を書く。 */
static int adir_visibility(Assembler *asmb, const char *l, const char *l2){
    AsmState *st=&asmb->st;
    char up[16]; axx_strupr_to(up,l,sizeof(up));
    int vis;
    if     (strcmp(up,".HIDDEN")==0)    vis = 2;
    else if(strcmp(up,".PROTECTED")==0) vis = 3;
    else if(strcmp(up,".INTERNAL")==0)  vis = 1;
    else return 0;
    if(!should_report_errors(st)) return 1;
    const char *buf = l2; int blen=(int)strlen(buf); int idx=0;
    char *nm; char *fv[SYM_DECL_MAXF];
    while(sym_decl_next(st, buf, blen, &idx, &nm, fv, 0)){
        int k = sym_attr_slot(st, nm);
        st->sym_attrs[k].other = (st->sym_attrs[k].other & ~0x03) | vis;
        sym_decl_free(&nm, fv, 0);
    }
    return 1;
}

/* `.other` — st_other バイトを丸ごと置き換える。 */
static int adir_other(Assembler *asmb, const char *l, const char *l2){
    AsmState *st=&asmb->st;
    char up[16]; axx_strupr_to(up,l,sizeof(up));
    if(strcmp(up,".OTHER")!=0) return 0;
    if(!should_report_errors(st)) return 1;
    const char *buf = l2; int blen=(int)strlen(buf); int idx=0;
    char *nm; char *fv[SYM_DECL_MAXF];
    while(sym_decl_next(st, buf, blen, &idx, &nm, fv, 1)){
        long long n;
        if(!sym_decl_num(asmb, ".OTHER", nm, fv[0], 0, 255, &n)){
            sym_decl_free(&nm, fv, 1);
            continue;
        }
        int k = sym_attr_slot(st, nm);
        st->sym_attrs[k].other = (int)n;
        sym_decl_free(&nm, fv, 1);
    }
    return 1;
}

/* `.comm` — 共通シンボルにする。 */
static int adir_comm(Assembler *asmb, const char *l, const char *l2){
    AsmState *st=&asmb->st;
    char up[16]; axx_strupr_to(up,l,sizeof(up));
    if(strcmp(up,".COMM")!=0) return 0;
    int record = should_report_errors(st);
    const char *buf = l2; int blen=(int)strlen(buf); int idx=0;
    char *nm; char *fv[SYM_DECL_MAXF];
    while(sym_decl_next(st, buf, blen, &idx, &nm, fv, 2)){
        sym_declare_extern(st, nm);
        if(!record){ sym_decl_free(&nm, fv, 2); continue; }
        long long sz;
        if(!sym_decl_num(asmb, ".COMM", nm, fv[0], 0, 0x7FFFFFFFFFFFFFFFll, &sz)){
            sym_decl_free(&nm, fv, 2);
            continue;
        }
        long long al = 1;
        if(fv[1] && fv[1][0]){
            if(!sym_decl_num(asmb, ".COMM", nm, fv[1], 0, 0x40000000ll, &al)){
                sym_decl_free(&nm, fv, 2);
                continue;
            }
            if(al & (al - 1)){
                axx_diagf(1, 0, " error - .COMM: alignment must be 0 or a power "
                                "of two, got '%lld' for '%s'.\n", al, nm);
                sym_decl_free(&nm, fv, 2);
                continue;
            }
        }
        int k = sym_attr_slot(st, nm);
        st->sym_attrs[k].common   = 1;
        st->sym_attrs[k].size_set = 1;
        st->sym_attrs[k].size     = (uint64_t)sz;
        st->sym_attrs[k].calign   = (uint64_t)al;
        if(st->sym_attrs[k].stype == 0) st->sym_attrs[k].stype = 1;
        sym_decl_free(&nm, fv, 2);
    }
    return 1;
}

/* `.reloctype` — 幅推測リロケーション型を上書きする。 */
static int adir_reloctype(Assembler *asmb, const char *l, const char *l2){
    AsmState *st=&asmb->st;
    char up[16]; axx_strupr_to(up,l,sizeof(up));
    if(strcmp(up,".RELOCTYPE")!=0) return 0;

    const ElfMachineInfo *_mtbl_rt = elf_machine_effective(st);
    if(!_mtbl_rt->named[0].name){
        axx_diagf(0, 0, " warning - .RELOCTYPE: no relocation type is known for machine "
                   "%d; declare them with .elftype\n", st->elf_machine);
        return 1;
    }
    static const int _widths[4] = {1, 2, 4, 8};

    const char *buf = l2;
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

        int a=tok_start, b=idx;
        while(a<b && (buf[a]==' '||buf[a]=='\t')) a++;
        while(b>a && (buf[b-1]==' '||buf[b-1]=='\t')) b--;
        int nlen = b - a;
        char *name = calloc((size_t)(nlen > 0 ? nlen : 0) + 1, 1);
        if(!name){ perror("calloc"); exit(1); }
        if(nlen > 0){
            memcpy(name, buf+a, (size_t)nlen);
            name[nlen]=0;
            for(int _ci=0; name[_ci]; _ci++)
                if(name[_ci]>='A' && name[_ci]<='Z') name[_ci]+=32;
        }

        if(name[0]){
            int rtype = elf_reloc_named(st, _mtbl_rt, name);
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
        free(name);

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
    PatVar    vars[NVARS];
    struct { char *name; uint64_t val; int word_idx;
             int rtype; int64_t addend; } *refs;
    int       refs_len;
    struct { int set; char *label_name; uint64_t label_val; } vtl[NVARS];
    SymMap    symbols;
    ChkList  *check_constraints[NVARS];
    int       reloc_constraints[NVARS];
    EnumDef   enum_defs[NVARS];
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

/* ---- 最良パターンの選択 -------------------------------------------------
   最初に当たったパターンで止めない。すべて試し、当たったものに特異度スコアを
   付けて最小のものを採る。これによりパターンファイル中の行の順序が結果に
   影響しないので、特殊形を一般形の前に並べる手作業が要らない。
   ------------------------------------------------------------------------ */
static void best_init(BestMatch *b){
    memset(b, 0, sizeof(*b));
}

/* 候補の記録を解放する。 */
static void best_free(BestMatch *b){
    for(int i=0;i<b->diags_len;i++) free(b->diags[i]);
    free(b->diags); free(b->diag_seterr);
    b->diags = NULL; b->diag_seterr = NULL; b->diags_len = 0;
    if(!b->valid){ memset(b, 0, sizeof(*b)); return; }
    for(int i=0;i<b->refs_len;i++) free(b->refs[i].name);
    free(b->refs);
    for(int i=0;i<g_nvars;i++) free(b->vtl[i].label_name);
    smap_free(&b->symbols);
    for(int i=0;i<g_nvars;i++) chk_unref(b->check_constraints[i]);
    for(int i=0;i<g_nvars;i++) enumdef_clear(&b->enum_defs[i]);
    iv_free(&b->vliwnop);
    vset_free(&b->vliwset);
    memset(b, 0, sizeof(*b));
}

/* 特異度スコアの比較。式捕捉が少ないほう、同点ならリテラル一致が多いほう、
   同点ならシンボル捕捉が少ないほうが勝つ。 */
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
            b->refs[i].rtype    = st->elf_refs[saved_refs_len+i].rtype;
            b->refs[i].addend   = st->elf_refs[saved_refs_len+i].addend;
        }
    }
    for(int i=0;i<g_nvars;i++){
        b->vtl[i].set       = st->elf_var_to_label[i].set;
        b->vtl[i].label_val = st->elf_var_to_label[i].label_val;
        b->vtl[i].label_name = st->elf_var_to_label[i].label_name
                               ? strdup(st->elf_var_to_label[i].label_name) : NULL;
    }
    smap_init(&b->symbols);
    for(int bi=0; bi<st->symbols.nb; bi++)
        for(SymEntry *e=st->symbols.buckets[bi]; e; e=e->next)
            smap_set(&b->symbols, e->key, e->val);
    for(int i=0;i<g_nvars;i++){
        b->check_constraints[i] = chk_ref(st->check_constraints[i]);
        b->reloc_constraints[i] = st->reloc_constraints[i];
        enumdef_init(&b->enum_defs[i]);
        enumdef_copy(&b->enum_defs[i], &st->enum_defs[i]);
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

/* 採択したパターンの時点のディレクティブ状態へ戻す。 */
static void best_restore_dirstate(AsmState *st, const BestMatch *b){
    smap_assign(&st->symbols, &b->symbols);
    for(int i=0;i<g_nvars;i++){
        chk_install(&st->check_constraints[i], chk_ref(b->check_constraints[i]));
        st->reloc_constraints[i] = b->reloc_constraints[i];
        enumdef_copy(&st->enum_defs[i], &b->enum_defs[i]);
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

typedef struct {
    int       valid;
    SymMap    symbols;
    ChkList  *check_constraints[NVARS];
    int       reloc_constraints[NVARS];
    EnumDef   enum_defs[NVARS];
    char      swordchars[256];
    uint256_t padding;
    int       bts, endian_big;
    int       vliwbits, vliwinstbits, vliwtemplatebits, vliwflag;
    IntVec    vliwnop;
} DirSnap;

static DirSnap g_hdrsnap;

/* 持ち上げ状態の写しを解放する。 */
static void hdrsnap_free(DirSnap *d){
    if(!d->valid) return;
    smap_free(&d->symbols);
    for(int i=0;i<NVARS;i++){ chk_unref(d->check_constraints[i]); d->check_constraints[i]=NULL; }
    for(int i=0;i<NVARS;i++) enumdef_clear(&d->enum_defs[i]);
    iv_free(&d->vliwnop);
    memset(d, 0, sizeof(*d));
}

/* 先頭の持ち上げたディレクティブを処理し終えた状態を写し取る。反復ごとに
   ここまで戻せば、先頭のディレクティブを読み直さずに済む。 */
static void hdrsnap_take(DirSnap *d, AsmState *st){
    hdrsnap_free(d);
    smap_init(&d->symbols);
    for(int bi=0; bi<st->symbols.nb; bi++)
        for(SymEntry *e=st->symbols.buckets[bi]; e; e=e->next)
            smap_set(&d->symbols, e->key, e->val);
    for(int i=0;i<g_nvars;i++){
        d->check_constraints[i] = chk_ref(st->check_constraints[i]);
        d->reloc_constraints[i] = st->reloc_constraints[i];
        enumdef_init(&d->enum_defs[i]);
        enumdef_copy(&d->enum_defs[i], &st->enum_defs[i]);
    }
    memcpy(d->swordchars, st->swordchars, sizeof(d->swordchars));
    d->padding          = st->padding;
    d->bts              = st->bts;
    d->endian_big       = st->endian_big;
    d->vliwbits         = st->vliwbits;
    d->vliwinstbits     = st->vliwinstbits;
    d->vliwtemplatebits = st->vliwtemplatebits;
    d->vliwflag         = st->vliwflag;
    iv_init(&d->vliwnop);
    iv_copy(&d->vliwnop, &st->vliwnop);
    d->valid = 1;
}

/* 写し取った状態へ戻す。 */
static void hdrsnap_restore(DirSnap *d, AsmState *st){
    smap_assign(&st->symbols, &d->symbols);
    for(int i=0;i<g_nvars;i++){
        chk_install(&st->check_constraints[i], chk_ref(d->check_constraints[i]));
        st->reloc_constraints[i] = d->reloc_constraints[i];
        enumdef_copy(&st->enum_defs[i], &d->enum_defs[i]);
    }
    if(g_hoist_symbolc) memcpy(st->swordchars, d->swordchars, sizeof(st->swordchars));
    if(g_hoist_padding) st->padding = d->padding;
    if(g_hoist_bits){ st->bts = d->bts; st->endian_big = d->endian_big; }
    if(g_hoist_vliw){
        st->vliwbits         = d->vliwbits;
        st->vliwinstbits     = d->vliwinstbits;
        st->vliwtemplatebits = d->vliwtemplatebits;
        st->vliwflag         = d->vliwflag;
        iv_copy(&st->vliwnop, &d->vliwnop);
    }
}

static void elf_refs_push_copy(AsmState *st, const char *name,
                               uint64_t val, int word_idx,
                               int rtype, int64_t addend){
    if(st->elf_refs_len >= st->elf_refs_cap){
        st->elf_refs_cap = st->elf_refs_cap ? st->elf_refs_cap*2 : 8;
        st->elf_refs = realloc(st->elf_refs,
            st->elf_refs_cap * sizeof(st->elf_refs[0]));
        if(!st->elf_refs){ perror("realloc"); exit(1); }
    }
    st->elf_refs[st->elf_refs_len].name     = name ? strdup(name) : NULL;
    st->elf_refs[st->elf_refs_len].val      = val;
    st->elf_refs[st->elf_refs_len].word_idx = word_idx;
    st->elf_refs[st->elf_refs_len].rtype    = rtype;
    st->elf_refs[st->elf_refs_len].addend   = addend;
    st->elf_refs_len++;
}

/* パターンの先頭がその行に当たりうるかの粗い前判定。 */
static int pat_prefix_matches(const char *pat, const char *lin){
    char pfx[64];
    int np = 0;
    const char *p = pat;
    for(; *p && np < (int)sizeof(pfx)-1; p++){
        if(*p >= 'A' && *p <= 'Z') pfx[np++] = *p;
        else if(*p == ' ') continue;
        else break;
    }
    if(np == 0) return 1;

    int closed = 1;
    if(np >= (int)sizeof(pfx)-1){
        closed = 0;
    } else if(*p){
        char c = *p;
        if((c >= 'a' && c <= 'z') || (c >= '0' && c <= '9')
           || c == '!' || c == '\\' || c == '[') closed = 0;
    }

    int k = 0;
    for(const char *q = lin; *q; q++){
        if(*q == ' ') continue;
        if(axx_upper_char(*q) != pfx[k]) return 0;
        k++;
        if(k == np){
            if(closed){
                char n = q[1];
                if((n >= 'A' && n <= 'Z') || (n >= 'a' && n <= 'z')
                   || (n >= '0' && n <= '9') || n == '_') return 0;
            }
            return 1;
        }
    }
    return 0;
}

/* テキストを出力ワードの並びにする。 */
static void text_words(AsmState *st, const char *txt, IntVec *objl_out){
    uint64_t word_mask = (st->bts > 0) ? axx_word_mask(st->bts) : 0xFFu;
    int trunc = 0;
    for(const unsigned char *bp=(const unsigned char *)txt; *bp; bp++){
        if((uint64_t)*bp > word_mask) trunc = 1;
        iv_push(objl_out, u256_from_u64((uint64_t)*bp));
    }
    if(trunc && !st->pass1_size_mode && should_report_errors(st)){
        char r[1024]; m_pyrepr(txt, r, sizeof(r));
        axx_diagf(0, 0, " warning - .passthru: one or more bytes exceed the "
                        "output word width (%d bit(s)) and were truncated "
                        "(high bits discarded): %s\n", st->bts, r);
    }
}

static void passthru_line(Assembler *asmb, const char *l, const char *l2,
                          IntVec *objl_out){
    AsmState *st = &asmb->st;
    TxtBuf t; txt_init(&t);
    txt_adds(&t, l);
    if(l2 && l2[0]){ txt_addc(&t, ' '); txt_adds(&t, l2); }
    const char *txt = t.b ? t.b : "";
    st->error_undefined_label = 0;
    text_words(st, txt, objl_out);
    free(st->asmtext);
    st->asmtext = strdup(txt);
    if(!st->asmtext){ perror("strdup"); exit(1); }
    TxtBuf d; txt_init(&d);
    txt_addc(&d, '"');
    txt_add_escaped(&d, txt);
    txt_addc(&d, '"');
    free(st->asmtext_disp);
    st->asmtext_disp = d.b ? d.b : strdup("");
    free(t.b);
}

/* テキスト置換モードで、バイトを出さずに綴りだけ通すべき組み込みディレクティブか。 */
static int textmode_text_only_dir(const char *l){
    static const char *tbl[] = { ".ORG", ".ALIGN", ".ZERO", ".ASCII", ".ASCIZ",
                                 ".RESB", ".RESW", ".RESD", ".RESQ", NULL };
    char up[16]; axx_strupr_to(up, l, sizeof(up));
    for(int i=0; tbl[i]; i++) if(strcmp(up, tbl[i]) == 0) return 1;
    return 0;
}

static int adir_done(Assembler *asmb, const char *l, const char *l2,
                     IntVec *objl_out, int idx, int *idx_out){
    if(asmb->st.textmode) passthru_line(asmb, l, l2, objl_out);
    *idx_out = idx;
    return 1;
}

#define PAT_VARS_CLEAR() vars_clear_all(st)

/* ディレクティブ行 1 行を処理する。処理したら 1 を返す。 */
static int pat_dir_exec(Assembler *asmb, PatEntry *i){
    int _dir_done = 0;
    switch(i->dir_kind){
    case PD_SETSYM:   _dir_done = dir_set_symbol(asmb,i);   break;
    case PD_CLEARSYM: _dir_done = dir_clear_symbol(asmb,i); break;
    case PD_PADDING:  _dir_done = dir_padding(asmb,i);      break;
    case PD_BITS:     _dir_done = dir_bits(asmb,i);         break;
    case PD_SYMBOLC:  _dir_done = dir_symbolc(asmb,i);      break;
    case PD_EPIC:     _dir_done = dir_epic(asmb,i);         break;
    case PD_VLIW:     _dir_done = dir_vliwp(asmb,i);        break;
    case PD_CHECK:    _dir_done = dir_check(asmb,i);        break;
    case PD_CLRCHECK: _dir_done = dir_clrcheck(asmb,i);     break;
    case PD_RELOC:    _dir_done = dir_reloc(asmb,i);        break;
    case PD_CLRRELOC: _dir_done = dir_clrreloc(asmb,i);     break;
    case PD_MAP:      _dir_done = dir_map(asmb,i);          break;
    case PD_FREE:     _dir_done = dir_free(asmb,i);         break;
    case PD_PASSTHRU: _dir_done = dir_passthru(asmb,i);     break;
    case PD_EOL:      _dir_done = dir_eol(asmb,i);          break;
    case PD_TEXTMODE: _dir_done = dir_textmode(asmb,i);     break;
    case PD_ENUM:     _dir_done = dir_enum(asmb,i);         break;
    case PD_CLRENUM:  _dir_done = dir_clrenum(asmb,i);      break;
    case PD_ERRMSG:   _dir_done = dir_errmsg(asmb,i);       break;
    case PD_ECHO:     _dir_done = dir_echo(asmb,i);         break;
    case PD_ELFTYPE:  _dir_done = dir_elftype(asmb,i);      break;
    case PD_ELFMACHINE: _dir_done = dir_elfmachine(asmb,i);  break;
    case PD_ELFCLASS: _dir_done = dir_elfclass(asmb,i);      break;
    case PD_ELFRELA:  _dir_done = dir_elfrela(asmb,i);       break;
    case PD_ELFWIDTH: _dir_done = dir_elfwidth(asmb,i);      break;
    case PD_ELFEXTERN:_dir_done = dir_elfextern(asmb,i);     break;
    case PD_ELFDWARF: _dir_done = dir_elfdwarf(asmb,i);      break;
    case PD_ELFHEADER:_dir_done = dir_elfheader(asmb,i);     break;
    case PD_ELFSECTION:_dir_done = dir_elfsection(asmb,i);    break;
    case PD_ELFFIELD: _dir_done = dir_elffield(asmb,i);      break;
    case PD_ELFPCGUESS:_dir_done = dir_elfpcguess(asmb,i);   break;
    case PD_ELFBUILTIN:_dir_done = dir_elfbuiltin(asmb,i);   break;
    case PD_ELFEXTRA: _dir_done = dir_elfextra(asmb,i);      break;
    case PD_ELFDIFF:  _dir_done = dir_elfdiff(asmb,i);       break;
    case PD_ELFENCODE:_dir_done = dir_elfencode(asmb,i);     break;
    case PD_ELFRINFO: _dir_done = dir_elfrinfo(asmb,i);      break;
    case PD_ELFUNIT:  _dir_done = dir_elfunit(asmb,i);       break;
    case PD_ELFLINK:  _dir_done = dir_elflink(asmb,i);       break;
    case PD_ELFGROUP: _dir_done = dir_elfgroup(asmb,i);      break;
    case PD_ELFCFI:   _dir_done = dir_elfcfi(asmb,i);        break;
    case PD_ELFCFIINIT:_dir_done = dir_elfcfiinit(asmb,i);   break;
    case PD_ELFCFIREG:_dir_done = dir_elfcfireg(asmb,i);     break;
    case PD_UNORDERED:_dir_done = dir_unordered(asmb,i);    break;
    default: break;
    }
    return _dir_done;
}

static int lineassemble2_impl(Assembler *asmb, const char *line, int idx,
                              IntVec *idxs_out, IntVec *objl_out, int *idx_out,
                              char *l, char *l2, char *l_nospace, size_t bufsz,
                              char *lin, size_t linsz){
    AsmState *st=&asmb->st;
    iv_clear(idxs_out); iv_clear(objl_out);

    l[0]=0; l2[0]=0;
    idx=axx_get_param_to_spc(line,idx,l,bufsz);
    idx=axx_get_param_to_eon(line,idx,l2,bufsz);
    int ll=(int)strlen(l); while(ll>0&&(l[ll-1]==' '||l[ll-1]=='\t')) l[--ll]=0;
    int nn=0;
    for(int i=0;l[i];i++) if(l[i]!=' ') l_nospace[nn++]=l[i];
    l_nospace[nn]=0;
    memcpy(l, l_nospace, (size_t)nn+1);

    /* 未定義ラベルの印はこの命令の評価だけのもの。前の行で立ったものを持ち越すと、
       照合を 1 回も試さない行が「未定義ラベル」と報告される。axx.py の
       lineassemble2() と同じ。 */
    st->error_undefined_label = 0;

    if(st->textmode && textmode_text_only_dir(l)){
        passthru_line(asmb, l, l2, objl_out);
        *idx_out=idx; return 1;
    }

    if(adir_section(st,l,l2)) return adir_done(asmb,l,l2,objl_out,idx,idx_out);
    if(adir_endsection(st,l)) return adir_done(asmb,l,l2,objl_out,idx,idx_out);
    if(adir_resb(asmb,l,l2)) return adir_done(asmb,l,l2,objl_out,idx,idx_out);
    if(adir_resw(asmb,l,l2)) return adir_done(asmb,l,l2,objl_out,idx,idx_out);
    if(adir_resd(asmb,l,l2)) return adir_done(asmb,l,l2,objl_out,idx,idx_out);
    if(adir_resq(asmb,l,l2)) return adir_done(asmb,l,l2,objl_out,idx,idx_out);
    if(adir_zero(asmb,l,l2)) return adir_done(asmb,l,l2,objl_out,idx,idx_out);
    {
        char _adup[16]; axx_strupr_to(_adup,l,sizeof(_adup));
        if(strcmp(_adup,".ASCII")==0){
            if(!adir_ascii(asmb,l,l2) && should_report_errors(&asmb->st)){
                char r[1024]; m_pyrepr(l2, r, sizeof(r));
                axx_diagf(1, 0, " error - .ASCII: failed to process string argument: %s\n", r);
            }
            *idx_out=idx; return 1;
        }
        if(strcmp(_adup,".ASCIZ")==0){
            if(!adir_asciiz(asmb,l,l2) && should_report_errors(&asmb->st)){
                char r[1024]; m_pyrepr(l2, r, sizeof(r));
                axx_diagf(1, 0, " error - .ASCIZ: failed to process string argument: %s\n", r);
            }
            *idx_out=idx; return 1;
        }
    }
    { char up[16]; axx_strupr_to(up,l,sizeof(up));
      if(strcmp(up,".INCLUDE")==0){
          char raw[512]; axx_get_string(l2,raw,sizeof(raw));
          if(!raw[0]){
              char trimmed[512]; size_t tn=0;
              { int ti=axx_skipspc(l2,0);
                while(l2[ti] && tn < sizeof(trimmed)-1) trimmed[tn++]=l2[ti++];
                while(tn>0 && (trimmed[tn-1]==' '||trimmed[tn-1]=='\t')) tn--;
                trimmed[tn]=0;
              }
              if(trimmed[0]){
                  char fallback[512];
                  axx_get_param_to_spc(trimmed,0,fallback,sizeof(fallback));
                  if(fallback[0]){
                      char r[600]; m_pyrepr(fallback, r, sizeof(r));
                      axx_diagf(0, 0, " warning - .INCLUDE filename not quoted: %s. "
                                      "Please use double quotes.\n", r);
                      strncpy(raw, fallback, sizeof(raw)-1);
                      raw[sizeof(raw)-1]='\0';
                  }
              }
              if(!raw[0]){
                  char r[600]; m_pyrepr(l2, r, sizeof(r));
                  axx_diagf(1, 0, " error - .INCLUDE directive has no filename: %s\n", r);
                  free(st->comment_text); st->comment_text = NULL;
                  *idx_out=idx; return 1;
              }
          }
          if(raw[0]){
              char resolved[2*PATH_MAX + 2];
              const char *cur = st->current_file;
              if(strcmp(raw,"stdin")==0){
                  strncpy(resolved, raw, sizeof(resolved)-1);
                  resolved[sizeof(resolved)-1]='\0';
              } else if(cur && cur[0] && strcmp(cur,"(stdin)")!=0 && strcmp(cur,"stdin")!=0){
                  char abs_buf[2*PATH_MAX + 2], dir_buf[2*PATH_MAX + 2];
                  if(cur[0]=='/'){
                      strncpy(abs_buf, cur, sizeof(abs_buf)-1);
                      abs_buf[sizeof(abs_buf)-1]='\0';
                  } else {
                      char cwd_buf[PATH_MAX];
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
          free(st->comment_text); st->comment_text = NULL;
          st->indent_text[0] = '\0';
          *idx_out=idx; return 1;
      }
    }
    if(adir_align(asmb,l,l2)) return adir_done(asmb,l,l2,objl_out,idx,idx_out);
    if(adir_org(asmb,l,l2)) return adir_done(asmb,l,l2,objl_out,idx,idx_out);
    if(adir_labelc(st,l,l2)) return adir_done(asmb,l,l2,objl_out,idx,idx_out);
    if(adir_extern(asmb,l,l2)) return adir_done(asmb,l,l2,objl_out,idx,idx_out);
    if(adir_reloctype(asmb,l,l2)) return adir_done(asmb,l,l2,objl_out,idx,idx_out);
    if(adir_export(asmb,l,l2)) return adir_done(asmb,l,l2,objl_out,idx,idx_out);
    if(adir_cfi(asmb,l,l2)) return adir_done(asmb,l,l2,objl_out,idx,idx_out);
    if(adir_type(asmb,l,l2)) return adir_done(asmb,l,l2,objl_out,idx,idx_out);
    if(adir_size(asmb,l,l2)) return adir_done(asmb,l,l2,objl_out,idx,idx_out);
    if(adir_weak(asmb,l,l2)) return adir_done(asmb,l,l2,objl_out,idx,idx_out);
    if(adir_visibility(asmb,l,l2)) return adir_done(asmb,l,l2,objl_out,idx,idx_out);
    if(adir_other(asmb,l,l2)) return adir_done(asmb,l,l2,objl_out,idx,idx_out);
    if(adir_comm(asmb,l,l2)) return adir_done(asmb,l,l2,objl_out,idx,idx_out);


    if(!l[0]){
        *idx_out=idx;
        return (st->textmode && (st->label_text[0]
                || (st->comment_text && st->comment_text[0]))) ? 1 : 0;
    }

    int se=0, oerr=0, pln=0;
    int idxs_val=0;
    int loopflag=1;
    PatEntry *oerr_entry=NULL;
    int hit_sentinel=0;
    BestMatch best;
    best_init(&best);

    if(l2[0]) snprintf(lin,linsz,"%s %s",l,l2);
    else      snprintf(lin,linsz,"%s",l);
    axx_reduce_spaces(lin);

    int *cand = NULL;
    int  ncand = patidx_candidates(&g_patidx, lin, &cand);
    int  ai = (g_hoist_rows && g_hdrsnap.valid) ? g_hoist_first_ai : 0;
    int  ci = 0;
    long long hoist_diag0 = g_diag_count;

    if(g_unordered){
        /* `.unordered` ではディレクティブ行は always に入っていない。
           決めておいた順にここで全部処理してから、パターンだけを試す。 */
        for(int _di = 0; _di < g_dirorder.n; _di++){
            PAT_VARS_CLEAR();
            pat_dir_exec(asmb, &st->pat.data[g_dirorder.rows[_di]]);
        }
    }

    for(;;){
        int pi, from_always;
        {
            int a = (ai < g_patidx.always.n) ? g_patidx.always.rows[ai] : INT_MAX;
            int c = (ci < ncand)             ? cand[ci]                 : INT_MAX;
            if(a == INT_MAX && c == INT_MAX) break;
            if(a <= c){ pi = a; ai++; from_always = 1; }
            else      { pi = c; ci++; from_always = 0; }
        }
        PatEntry *i=&st->pat.data[pi];
        pln = pi + 1;

        if(g_hoist_rows && !g_hdrsnap.valid && pi >= g_hoist_rows){
            if(g_diag_count != hoist_diag0) g_hoist_rows = 0;
            else                            hdrsnap_take(&g_hdrsnap, st);
        }

        if(i->is_dir){
        PAT_VARS_CLEAR();
        if(pat_dir_exec(asmb, i)) continue;
        }

        int lw=0; for(int fi=0;fi<PAT_FIELDS;fi++) if(i->f[fi][0]) lw++;
        if(lw==0) continue;

        if(!i->f[0][0]){
            hit_sentinel=1;
            if(!best.valid){
                int io2;
                PAT_VARS_CLEAR();
                uint256_t idxv2=expr_expression_pat(asmb,i->f[3],0,&io2);
                idxs_val=(int)u256_to_i64(idxv2);
            }
            break;
        }

        if(from_always && i->pfxlen && !pat_prefix_matches(i->f[0], lin)) continue;

        PAT_VARS_CLEAR();

        st->error_undefined_label=0;
        st->expmode=EXP_ASM;
        st->expcaps=&CAPS_ASM;

        int mark_v   = vars_mark();
        int mark_v2l = v2l_mark();
        int saved_refs_len = st->elf_refs_len;
        /* 選ばれなかった試行の綴りは置き場から下ろす。 */
        int captext_len_try = st->captext_len;

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
            } else {
                st->captext_len = captext_len_try;
            }
            for(int di=0; di<_cand_ndiag; di++) free(_cand_diags[di]);
            free(_cand_diags); free(_cand_seterr);
            _cand_diags = NULL; _cand_seterr = NULL; _cand_ndiag = 0;
            vars_rollback(st, mark_v);
            for(int ri2=saved_refs_len; ri2<st->elf_refs_len; ri2++)
                free(st->elf_refs[ri2].name);
            st->elf_refs_len = saved_refs_len;
            v2l_rollback(st, mark_v2l);
            st->error_undefined_label=0;

        } else {
            vars_rollback(st, mark_v);
            v2l_rollback(st, mark_v2l);
            st->error_undefined_label=0;
            st->captext_len = captext_len_try;
        }
    }

    if(best.valid){
        PatEntry *i = best.pat;
        pln = best.pln;
        loopflag = 0;

        best_restore_dirstate(st, &best);
        memcpy(st->vars, best.vars, sizeof(st->vars));
        vars_touch_all();
        for(int ri2=0; ri2<best.refs_len; ri2++)
            elf_refs_push_copy(st, best.refs[ri2].name,
                               best.refs[ri2].val, best.refs[ri2].word_idx,
                               best.refs[ri2].rtype, best.refs[ri2].addend);
        for(int vi=0;vi<g_nvars;vi++){
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
        st->expcaps = &CAPS_ASM;

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
        {
            /* 4 つ目の欄（EPIC の番号）は binary_list の結果に関係なく評価する。
               axx.py の lineassemble2() と同じで、ここに未定義のラベルがあれば
               それも報告される。 */
            int io;
            uint256_t idxv=expr_expression_pat(asmb,i->f[3],0,&io);
            idxs_val=(int)u256_to_i64(idxv);
        }
    } else if(hit_sentinel){
        loopflag=0;
    }
    best_free(&best);

    if(loopflag){ se=1; pln=0; }

    if(se && st->passthru){
        passthru_line(asmb, l, l2, objl_out);
        *idx_out=idx; return 1;
    }

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
            axx_diagf(1, 0, " error - Illegal syntax in assemble line or pattern line.  [%s:%d]\n",
                      st->current_file, (int)st->ln);
            if(st->debug){
                fprintf(stderr, "   (pattern %d: ['%s', '%s', '%s', '%s', '%s', '%s'])\n",
                       pln,
                       oerr_entry ? oerr_entry->f[0] : "",
                       oerr_entry ? oerr_entry->f[1] : "",
                       oerr_entry ? oerr_entry->f[2] : "",
                       oerr_entry ? oerr_entry->f[3] : "",
                       oerr_entry ? oerr_entry->f[4] : "",
                       oerr_entry ? oerr_entry->f[5] : "");
            }
            *idx_out=idx; return 0;
        }
    }

    iv_clear(idxs_out);
    iv_push(idxs_out, u256_from_i64(idxs_val));
    *idx_out=idx;
    return 1;
}

static int lineassemble2(Assembler *asmb, const char *line, int idx,
                         IntVec *idxs_out, IntVec *objl_out, int *idx_out){
    size_t n = strlen(line);
    size_t bufsz = n + 2;
    size_t linsz = 2*n + 4;
    char *blk = malloc(3*bufsz + linsz);
    if(!blk){ perror("malloc"); exit(1); }
    char *l  = blk;
    char *l2 = blk + bufsz;
    char *ns = blk + 2*bufsz;
    char *lin= blk + 3*bufsz;
    int r = lineassemble2_impl(asmb, line, idx, idxs_out, objl_out, idx_out,
                               l, l2, ns, bufsz, lin, linsz);
    free(blk);
    return r;
}

typedef struct { const char *name; uint64_t val; int word_idx; int ord;
                 int rtype; int64_t addend; } ElfRef;

/* ラベル参照を出力ワードの順に並べるための比較関数。 */
static int elf_ref_cmp(const void *a, const void *b){
    const ElfRef *x = (const ElfRef *)a, *y = (const ElfRef *)b;
    if(x->word_idx != y->word_idx) return (x->word_idx > y->word_idx) - (x->word_idx < y->word_idx);
    return (x->ord > y->ord) - (x->ord < y->ord);
}

/* ソース 1 行を処理する主ループ。
   ラベル定義とソース側ディレクティブを済ませ、`!!` があればバンドルに分け、
   候補のパターンを順に照合して特異度スコア最小のものを採り、error_patterns を
   評価してから出力欄でワード列を作る。テキスト置換モードのときは、綴りを
   保ったテキストを作る経路へ回す。 */
static int lineassemble(Assembler *asmb, const char *line_in){
    AsmState *st=&asmb->st;

    size_t lin_len = strlen(line_in);
    char *line = malloc(lin_len + 2);
    if(!line){ perror("malloc"); return 0; }
    memcpy(line, line_in, lin_len + 1);

    st->indent_text[0] = '\0';
    if(st->textmode){
        size_t _ni = 0;
        while(line[_ni]==' ' || line[_ni]=='\t') _ni++;
        if(_ni > sizeof(st->indent_text)-1) _ni = sizeof(st->indent_text)-1;
        memcpy(st->indent_text, line, _ni);
        st->indent_text[_ni] = '\0';
    }

    axx_normalize_ws(line);
    char *cmt = NULL;
    axx_split_comment_asm(line, &cmt);
    free(st->comment_text); st->comment_text = NULL;
    if(st->textmode) st->comment_text = cmt; else free(cmt);
    if(!line[0] && !(st->comment_text && st->comment_text[0])){
        free(line); return 0;
    }
    axx_resolve_vliw_escapes(line);

    v2l_forget();

    if(g_hoist_rows && g_hdrsnap.valid){
        hdrsnap_restore(&g_hdrsnap, &asmb->st);
        subv_unfreeze_all(&asmb->st.subs);
    } else {
        for(int _ci = 0; _ci < g_nvars; _ci++){
            chk_install(&asmb->st.check_constraints[_ci], NULL);
            asmb->st.reloc_constraints[_ci] = 0;
            enumdef_clear(&asmb->st.enum_defs[_ci]);
        }
        subv_unfreeze_all(&asmb->st.subs);

        smap_clear(&asmb->st.symbols);
        for(int pi=0; pi<asmb->st.patsymbols.nb; pi++)
            for(SymEntry *se=asmb->st.patsymbols.buckets[pi]; se; se=se->next)
                smap_set(&asmb->st.symbols, se->key, se->val);
    }

    char *processed = malloc(lin_len + 2);
    if(!processed){ perror("malloc"); free(line); return 0; }
    st->captext_len = 0;
    st->captext[0] = '\0';
    st->label_text[0] = '\0';
    adir_label_processing(asmb, line, processed, lin_len + 2);
    free(line);

    if(st->pc.w[1]||st->pc.w[2]||st->pc.w[3]){
        if(!st->pc_overflow_set || u256_gt_signed(st->pc, st->pc_overflow_max)){
            st->pc_overflow_max = st->pc;
            st->pc_overflow_set = 1;
        }
    }

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
        for(int _vi=0;_vi<NVARS;_vi++){
            st->elf_var_to_label[_vi].set = 0;
            free(st->elf_var_to_label[_vi].label_name);
            st->elf_var_to_label[_vi].label_name = NULL;
            st->elf_var_to_label[_vi].label_val = 0;
        }
        st->elf_capturing_var = -1;
    }

    IntVec idxs; iv_init(&idxs);
    IntVec objl; iv_init(&objl);
    int new_idx;
    int flag=lineassemble2(asmb,processed,0,&idxs,&objl,&new_idx);

    st->elf_tracking=0;

    if(!flag){ free(processed); iv_free(&idxs); iv_free(&objl); return 0; }

    if(st->textmode && st->label_text[0] && !st->vliwflag
       && (st->asmtext || objl.len == 0)){
        TxtBuf lp; txt_init(&lp);
        txt_adds(&lp, st->label_text);
        if(st->asmtext && st->asmtext[0]) txt_addc(&lp, ' ');
        const char *pfx = lp.b ? lp.b : "";
        int plen = (int)strlen(pfx);
        if(plen > 0){
            for(int k=0;k<plen;k++) iv_push(&objl, u256_zero());
            for(int k=objl.len-1-plen; k>=0; k--) objl.data[k+plen] = objl.data[k];
            for(int k=0;k<plen;k++)
                objl.data[k] = u256_from_u64((uint64_t)(unsigned char)pfx[k]);
        }
        TxtBuf nt; txt_init(&nt);
        txt_adds(&nt, pfx);
        if(st->asmtext) txt_adds(&nt, st->asmtext);
        free(st->asmtext);
        st->asmtext = nt.b ? nt.b : strdup("");
        if(!st->asmtext){ perror("strdup"); exit(1); }
        TxtBuf nd; txt_init(&nd);
        txt_addc(&nd, '"');
        txt_add_escaped(&nd, st->asmtext);
        txt_addc(&nd, '"');
        free(st->asmtext_disp);
        st->asmtext_disp = nd.b ? nd.b : strdup("");
        for(int ri=0; ri<st->elf_refs_len; ri++)
            if(st->elf_refs[ri].word_idx >= 0) st->elf_refs[ri].word_idx += plen;
        free(lp.b);
    }

    if(st->textmode && st->comment_text && st->comment_text[0] && !st->vliwflag
       && (st->asmtext || objl.len == 0)){
        TxtBuf cs; txt_init(&cs);
        if(st->asmtext && st->asmtext[0]) txt_addc(&cs, ' ');
        txt_adds(&cs, st->comment_text);
        const char *sfx = cs.b ? cs.b : "";
        text_words(st, sfx, &objl);
        TxtBuf nt; txt_init(&nt);
        if(st->asmtext) txt_adds(&nt, st->asmtext);
        txt_adds(&nt, sfx);
        free(st->asmtext);
        st->asmtext = nt.b ? nt.b : strdup("");
        if(!st->asmtext){ perror("strdup"); exit(1); }
        TxtBuf nd; txt_init(&nd);
        txt_addc(&nd, '"');
        txt_add_escaped(&nd, st->asmtext);
        txt_addc(&nd, '"');
        free(st->asmtext_disp);
        st->asmtext_disp = nd.b ? nd.b : strdup("");
        free(cs.b);
    }

    if(st->textmode && st->indent_text[0] && !st->vliwflag
       && st->asmtext && st->asmtext[0]){
        const char *ind = st->indent_text;
        int ilen = (int)strlen(ind);
        for(int k=0;k<ilen;k++) iv_push(&objl, u256_zero());
        for(int k=objl.len-1-ilen; k>=0; k--) objl.data[k+ilen] = objl.data[k];
        for(int k=0;k<ilen;k++)
            objl.data[k] = u256_from_u64((uint64_t)(unsigned char)ind[k]);
        TxtBuf nt; txt_init(&nt);
        txt_adds(&nt, ind);
        txt_adds(&nt, st->asmtext);
        free(st->asmtext);
        st->asmtext = nt.b ? nt.b : strdup("");
        if(!st->asmtext){ perror("strdup"); exit(1); }
        TxtBuf nd; txt_init(&nd);
        txt_addc(&nd, '"');
        txt_add_escaped(&nd, st->asmtext);
        txt_addc(&nd, '"');
        free(st->asmtext_disp);
        st->asmtext_disp = nd.b ? nd.b : strdup("");
        for(int ri=0; ri<st->elf_refs_len; ri++)
            if(st->elf_refs[ri].word_idx >= 0) st->elf_refs[ri].word_idx += ilen;
    }

    if(st->eol && objl.len > 0 && !st->vliwflag)
        iv_push(&objl, u256_from_u64((uint64_t)'\n'));

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

            const ElfMachineInfo *_mtbl_rm = elf_machine_effective(st);
            #define RTYPE_FOR(nb) reloctype_for(st, _mtbl_rm, (nb))

            ElfRef *_valid = (ElfRef*)malloc((size_t)st->elf_refs_len * sizeof(ElfRef));
            if(!_valid){perror("malloc");exit(1);}
            int _nvalid = 0;
            for(int _ri=0; _ri<st->elf_refs_len; _ri++){
                if(st->elf_refs[_ri].word_idx >= 0){
                    _valid[_nvalid] = (ElfRef){st->elf_refs[_ri].name,
                                              st->elf_refs[_ri].val,
                                              st->elf_refs[_ri].word_idx,
                                              _nvalid,
                                              st->elf_refs[_ri].rtype,
                                              st->elf_refs[_ri].addend};
                    _nvalid++;
                }
            }
            qsort(_valid, (size_t)_nvalid, sizeof(ElfRef), elf_ref_cmp);

            {
                int _w2 = 0;
                for(int _r2 = 0; _r2 < _nvalid; _r2++){
                    int _dup = 0;
                    for(int _k = 0; _k < _w2; _k++){
                        if(_valid[_k].word_idx == _valid[_r2].word_idx
                           && strcmp(_valid[_k].name, _valid[_r2].name) == 0){ _dup = 1; break; }
                    }
                    if(_dup) continue;
                    if(_w2 != _r2) _valid[_w2] = _valid[_r2];
                    _w2++;
                }
                _nvalid = _w2;
            }
            {
                int _w2 = 0;
                for(int _r2 = 0; _r2 < _nvalid; _r2++){
                    int _ambig = 0;
                    for(int _k = 0; _k < _nvalid; _k++){
                        if(_k != _r2
                           && _valid[_k].word_idx == _valid[_r2].word_idx
                           && strcmp(_valid[_k].name, _valid[_r2].name) != 0){ _ambig = 1; break; }
                    }
                    if(_ambig) continue;
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
                /* 加数の単位。byte なら 1 ワードのバイト数を掛け、word ならワードのまま。 */
                int64_t _scale = (st->elf_decl_unit == 1) ? 1 : (int64_t)bpw;

                {
                    /* ラベル差（名前が「±名前」を \x01 で区切った並び。ラベル名は
                       `+` `-` で始まらないので先頭の文字で見分ける）。足す項には
                       足す型、引く項には引く型を同じ位置に出す。axx.py の
                       lineassemble() のラベル差の処理と同じ規則。 */
                    if(_lname[0] == '+' || _lname[0] == '-'){
                        if(_widx >= objl.len){ _gi = _gj; continue; }
                        /* 項を取り出す */
                        int _nt = 1;
                        for(const char *q = _lname; *q; q++) if(*q == '\x01') _nt++;
                        char **_tn = malloc(sizeof(char*) * (size_t)_nt);
                        int *_ts = malloc(sizeof(int) * (size_t)_nt);
                        if(!_tn || !_ts){ perror("malloc"); exit(1); }
                        {
                            const char *q = _lname; int k = 0;
                            while(k < _nt){
                                const char *e2 = strchr(q, '\x01');
                                size_t l = e2 ? (size_t)(e2 - q) : strlen(q);
                                _ts[k] = q[0] == '-' ? -1 : 1;
                                _tn[k] = malloc(l);
                                if(!_tn[k]){ perror("malloc"); exit(1); }
                                memcpy(_tn[k], q + 1, l - 1); _tn[k][l-1] = '\0';
                                k++;
                                q = e2 ? e2 + 1 : q + l;
                            }
                        }
                        int _drt = _valid[_gi].rtype;
                        int _da = 0, _ds = 0, _okp;
                        const ElfFieldInfo *_dfd = NULL;
                        if(_drt > 0){
                            _okp = elf_diff_t_of(st, _drt, &_da, &_ds);
                            _dfd = insn_reloc_field_decl(st, _drt);
                        } else {
                            _okp = elf_diff_of(st, _nbytes, &_da, &_ds);
                        }
                        if(!_okp){
                            if(st->debug){
                                char _ex[1024]; size_t _ep = 0;
                                for(int k = 0; k < _nt; k++){
                                    int _w = snprintf(_ex + _ep, sizeof(_ex) - _ep, "%s%s",
                                                      (_ts[k] < 0) ? "-" : (k ? "+" : ""), _tn[k]);
                                    if(_w > 0 && (size_t)_w < sizeof(_ex) - _ep) _ep += (size_t)_w;
                                }
                                axx_diagf(0, 0, " warning - no .elfdiff pair for the difference "
                                           "'%s'; relocation omitted.\n", _ex);
                            }
                            for(int k = 0; k < _nt; k++) free(_tn[k]);
                            free(_tn); free(_ts);
                            _gi = _gj;
                            continue;
                        }
                        int64_t _dconst;
                        int _dw, _dnb;
                        if(_drt > 0){
                            /* 型付きの差: 欄は `.elffield` があればその位置と幅、
                               無ければこの参照のワード列そのもの。 */
                            _dconst = _valid[_gi].addend * _scale;
                            _dw = _widx + (_dfd ? _dfd->off / bpw : 0);
                            if(_dfd){
                                _dnb = elf_machine_reloc_bytes(_mtbl_rm, _drt);
                                if(_dnb <= 0) _dnb = _nbytes;
                            } else _dnb = _nbytes;
                            if(_dfd && _mtbl_rm->is_rela){
                                int _nw2 = _dnb / bpw; if(_nw2 < 1) _nw2 = 1;
                                if(_dw + _nw2 <= objl.len){
                                    uint64_t _wm = axx_word_mask(st->bts);
                                    for(int _k = 0; _k < _nw2; _k++){
                                        int _sh = st->endian_big ? st->bts * (_nw2 - 1 - _k) : st->bts * _k;
                                        uint64_t _clr = (_sh < 64) ? ((_dfd->mask >> _sh) & _wm) : 0;
                                        uint64_t _wv = u256_to_u64(objl.data[_dw + _k]);
                                        objl.data[_dw + _k] = u256_from_u64((_wv & ~_clr) & _wm);
                                    }
                                }
                            }
                        } else {
                            int _bts = st->bts;
                            uint64_t _wm = axx_word_mask(_bts);
                            uint64_t _rv = 0;
                            for(int _k = 0; _k < _nwords; _k++){
                                int _wk = _widx + _k;
                                if(_wk >= objl.len) continue;
                                uint64_t _wv = u256_to_u64(objl.data[_wk]) & _wm;
                                int _sh = st->endian_big ? _bts * (_nwords - 1 - _k) : _bts * _k;
                                if(_sh < 64) _rv |= _wv << _sh;
                            }
                            int _fb = _nwords * _bts;
                            if(_fb > 0 && _fb < 64 && _rv >= ((uint64_t)1 << (_fb - 1)))
                                _rv -= ((uint64_t)1 << _fb);
                            _dconst = ((int64_t)_rv - (int64_t)_valid[_gi].val) * _scale;
                            _dw = _widx;
                            _dnb = _nbytes;
                            if(_mtbl_rm->is_rela)
                                for(int _k = 0; _k < _nwords; _k++)
                                    if(_widx + _k < objl.len) objl.data[_widx + _k] = u256_zero();
                        }
                        int64_t _dsec = (int64_t)((sec_completed_words +
                                                   (cur_pc + (uint64_t)_dw - sec_entry_pc_cur))
                                                  * (uint64_t)bpw);
                        int _has_plus = 0;
                        for(int k = 0; k < _nt; k++) if(_ts[k] > 0){ _has_plus = 1; break; }
                        int _dput = 0;
                        /* 足す項を先に、引く項を後に並べる。 */
                        for(int _pass = 0; _pass < 2; _pass++)
                            for(int k = 0; k < _nt; k++){
                                if((_pass == 0) != (_ts[k] > 0)) continue;
                                int64_t _ad = 0;
                                if(!_dput && (_ts[k] > 0 || !_has_plus)){
                                    _ad = _ts[k] > 0 ? _dconst : -_dconst;
                                    _dput = 1;
                                }
                                if(st->reloc_count >= st->reloc_cap){
                                    st->reloc_cap = st->reloc_cap ? st->reloc_cap*2 : 16;
                                    st->relocations = realloc(st->relocations,
                                        (size_t)st->reloc_cap * sizeof(st->relocations[0]));
                                    if(!st->relocations){ perror("realloc"); exit(1); }
                                }
                                st->relocations[st->reloc_count].section    = strdup(sec_name);
                                st->relocations[st->reloc_count].sec_offset = _dsec;
                                st->relocations[st->reloc_count].sym        = strdup(_tn[k]);
                                st->relocations[st->reloc_count].rtype      = _ts[k] > 0 ? _da : _ds;
                                st->relocations[st->reloc_count].addend     = _ad;
                                st->relocations[st->reloc_count].nbytes     = _dnb;
                                st->reloc_count++;
                            }
                        for(int k = 0; k < _nt; k++) free(_tn[k]);
                        free(_tn); free(_ts);
                        _gi = _gj;
                        continue;
                    }
                }

                LabelEntry *_le_rt = lmap_find(&st->labels, _lname);
                int _src_rtype = (_le_rt && _le_rt->reloc_type_override >= 0)
                               ? _le_rt->reloc_type_override : -1;

                int _forced_rtype = 0;
                if(_valid[_gi].rtype > 0){
                    int _hint_rtype = (_src_rtype >= 0 && !extern_untyped_has(st, _lname))
                                    ? _src_rtype : _valid[_gi].rtype;
                    const ElfFieldInfo *_fdecl = insn_reloc_field_decl(st, _hint_rtype);
                    if(!_fdecl){
                        _forced_rtype = _hint_rtype;
                    } else {
                        uint64_t _fmask = _fdecl->mask;
                        int _foff = _fdecl->off;
                        int _ibytes = elf_machine_reloc_bytes(_mtbl_rm, _hint_rtype);
                        if(_ibytes <= 0) _ibytes = 4;
                        int _iwords = _ibytes / bpw;
                        if(_iwords < 1) _iwords = 1;
                        int _fw = _widx + _foff / bpw;
                        if(_fw + _iwords <= objl.len){
                            uint64_t _wmask_i = axx_word_mask(st->bts);
                            for(int _k = 0; _k < _iwords; _k++){
                                int _sh = st->endian_big
                                        ? st->bts * (_iwords - 1 - _k)
                                        : st->bts * _k;
                                uint64_t _clear = (_sh < 64)
                                                ? ((_fmask >> _sh) & _wmask_i) : 0;
                                uint64_t _wv = u256_to_u64(objl.data[_fw + _k]);
                                objl.data[_fw + _k] =
                                    u256_from_u64((_wv & ~_clear) & _wmask_i);
                            }
                        }
                        int64_t _sec_rel_h =
                            (int64_t)((sec_completed_words +
                                       (cur_pc + (uint64_t)_fw - sec_entry_pc_cur))
                                      * (uint64_t)bpw);
                        if(st->reloc_count >= st->reloc_cap){
                            st->reloc_cap = st->reloc_cap ? st->reloc_cap*2 : 16;
                            st->relocations = realloc(st->relocations,
                                (size_t)st->reloc_cap * sizeof(st->relocations[0]));
                            if(!st->relocations){ perror("realloc"); exit(1); }
                        }
                        st->relocations[st->reloc_count].section    = strdup(sec_name);
                        st->relocations[st->reloc_count].sec_offset = _sec_rel_h;
                        st->relocations[st->reloc_count].sym        = strdup(_lname);
                        st->relocations[st->reloc_count].rtype      = _hint_rtype;
                        /* 加数は「オペランドの値 − ラベルの値」に補正を足したもの。 */
                        st->relocations[st->reloc_count].addend     =
                            _valid[_gi].addend * _scale + (int64_t)_fdecl->bias;
                        st->relocations[st->reloc_count].nbytes     = _ibytes;
                        st->reloc_count++;
                        _gi = _gj;
                        continue;
                    }
                }

                int _rtype = 0;
                int _rtype_is_default_guess = 0;
                if(_forced_rtype > 0){
                    _rtype = _forced_rtype;
                } else {
                    if(_src_rtype >= 0){
                        int _rt_ov = _src_rtype;
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
                if(_rtype == 0 && _widx < objl.len && st->debug)
                    axx_diagf(0, 0, " warning - no relocation type available for a %d-byte "
                               "reference to '%s'; relocation omitted.\n", _nbytes, _lname);
                if(_rtype != 0 && _widx < objl.len){
                    int64_t _sec_rel = (int64_t)((sec_completed_words +
                                                   (cur_pc + (uint64_t)_widx - sec_entry_pc_cur))
                                                  * (uint64_t)bpw);
                    int _bts = st->bts;
                    uint64_t _wmask = axx_word_mask(_bts);
                    uint64_t _raw_val = 0;
                    if(!st->endian_big){
                        for(int _k = 0; _k < _nwords; _k++){
                            int _wk = _widx + _k;
                            if(_wk < objl.len){
                                uint64_t _wv = u256_to_u64(objl.data[_wk]) & _wmask;
                                int _sh = _bts * _k;
                                if(_sh < 64) _raw_val |= _wv << _sh;
                            }
                        }
                    } else {
                        for(int _k = 0; _k < _nwords; _k++){
                            int _wk = _widx + _k;
                            if(_wk < objl.len){
                                uint64_t _wv = u256_to_u64(objl.data[_wk]) & _wmask;
                                if(_bts < 64) _raw_val = (_raw_val << _bts) | _wv;
                                else _raw_val = _wv;
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
                    int64_t _abs_wi = (int64_t)_valid[_gi].val;

                    if(_rtype_is_default_guess
                       && elf_machine_is_pcrel(_mtbl_rm, _rtype)
                       && (int64_t)_raw_val == _abs_wi){
                        int _alt = elf_reloc_same_width(_mtbl_rm, _nbytes, 0);
                        if(_alt > 0) _rtype = _alt;
                    }

                    if(_rtype_is_default_guess && _mtbl_rm->pcrel_guess
                       && !elf_machine_is_pcrel(_mtbl_rm, _rtype)
                       && (int64_t)_raw_val != _abs_wi){
                        int _alt = elf_reloc_same_width(_mtbl_rm, _nbytes, 1);
                        if(_alt > 0) _rtype = _alt;
                    }

                    int64_t _addend;
                    {
                    /* 加数はワードで求めてから単位（.elfunit）に直す。 */
                    int _is_pcrel = elf_machine_is_pcrel(_mtbl_rm, _rtype);
                        if(_is_pcrel)
                            _addend = ((int64_t)_raw_val - _abs_wi + _sec_rel / (int64_t)bpw) * _scale;
                        else
                            _addend = ((int64_t)_raw_val - _abs_wi) * _scale;
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

/* 1 行を処理する外枠。行の前処理と診断の文脈を整える。 */
static int lineassemble0(Assembler *asmb, const char *line){
    AsmState *st=&asmb->st;

    size_t n = strlen(line);
    char *cleaned = malloc(n + 1);
    if(!cleaned){ perror("malloc"); exit(1); }
    size_t w = 0;
    for(size_t i = 0; i < n; i++)
        if(line[i] != '\n' && line[i] != '\r') cleaned[w++] = line[i];
    cleaned[w] = '\0';

    strncpy(st->cl, cleaned, sizeof(st->cl)-1);
    st->cl[sizeof(st->cl)-1] = '\0';

    int show = (st->pas==0) || ((st->pas==2) && st->verbose);
    if(show){
        printf("%016llx %s %d %s //",(unsigned long long)u256_to_u64(st->pc),
               st->current_file, st->ln, cleaned);
    }
    free(st->asmtext); st->asmtext=NULL;
    free(st->asmtext_disp); st->asmtext_disp=NULL;
    int f=lineassemble(asmb,cleaned);
    if(st->asmtext && (st->pas==0 || st->pas==2)){
        if(show)                printf(" %s", st->asmtext_disp ? st->asmtext_disp : "");
        else if(st->text_output) printf("%s\n", st->asmtext);
    }
    free(st->asmtext); st->asmtext=NULL;
    free(st->asmtext_disp); st->asmtext_disp=NULL;
    if(show) printf("\n");
    free(cleaned);
    st->ln++;
    return f;
}

/* プロンプトモードの 1 行入力。`?` でラベル表を出す。このモードでは
   マクロ層を通らない。 */
static char *file_input_from_stdin(void){
    size_t total=0, cap=4096;
    char *buf=malloc(cap);
    if(!buf){ perror("malloc"); exit(1); }
    char line[4096];
    while(fgets(line,sizeof(line),stdin)){
        size_t l=strlen(line);
        for(size_t i=0;i<l;i++) if(line[i]=='\r'){ memmove(line+i,line+i+1,l-i); l--; i--; }
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
typedef struct { const char*name; uint64_t bs,bsz,fl; uint8_t*data; uint32_t sht;
                 int al_set; uint32_t al; uint32_t es; } WCS;
typedef struct { uint32_t shndx; uint64_t sv; } WSR;
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

/* ---- ELF オブジェクト出力 -----------------------------------------------
   セクション・シンボル表・リロケーションを組み、必要なら DWARF も付ける。
   マシン記述は elf_machine_effective() が返す実表から取るので、組み込みの表に
   無い CPU でもパターンファイルの宣言だけでリンクできる .o を出せる。
   型の決まらない参照はリロケーションを出さない（当てずっぽうの型番号で
   リンカを騙さないため）。
   ------------------------------------------------------------------------ */
/* 16bit を指定のバイト順で書く。 */
static void weo_w2(uint8_t*p,uint16_t v,int is_le){
    if(is_le){ p[0]=v&0xff; p[1]=(v>>8)&0xff; }
    else     { p[1]=v&0xff; p[0]=(v>>8)&0xff; }
}
/* 32bit を指定のバイト順で書く。 */
static void weo_w4(uint8_t*p,uint32_t v,int is_le){
    if(is_le){ p[0]=v&0xff;p[1]=(v>>8)&0xff;p[2]=(v>>16)&0xff;p[3]=(v>>24)&0xff; }
    else     { p[3]=v&0xff;p[2]=(v>>8)&0xff;p[1]=(v>>16)&0xff;p[0]=(v>>24)&0xff; }
}
/* 64bit を指定のバイト順で書く。 */
static void weo_w8(uint8_t*p,uint64_t v,int is_le){
    if(is_le){ for(int j=0;j<8;j++){p[j]=(uint8_t)(v&0xff);v>>=8;} }
    else     { for(int j=7;j>=0;j--){p[j]=(uint8_t)(v&0xff);v>>=8;} }
}
static void weo_w8s(uint8_t*p,int64_t v,int is_le){ weo_w8(p,(uint64_t)v,is_le); }

static void wbb_init(WBB*w){ w->b=calloc(1,64); w->len=1; w->cap=64; }
/* 書き出しバッファを伸ばす。 */
static void wbb_grow(WBB*w, size_t need){
    while(w->len+need>w->cap){w->cap*=2;w->b=realloc(w->b,w->cap);if(!w->b){perror("realloc");exit(1);}}
}
/* 文字列表に 1 個足し、その添字を返す。 */
static uint32_t wbb_str(WBB*w, const char*s){
    size_t l=strlen(s)+1; uint32_t off=(uint32_t)w->len;
    wbb_grow(w,l); memcpy(w->b+w->len,s,l); w->len+=l; return off;
}
/* バッファにバイト列を足す。 */
static void wbb_app(WBB*w, const void*src, size_t n){
    wbb_grow(w,n); memcpy(w->b+w->len,src,n); w->len+=n;
}

/* 出力バッファの範囲を、セクションの中身として切り出す。 */
static uint8_t *weo_extract(AsmState*st,int bpw,uint64_t w0,uint64_t wn){
    uint64_t nb=wn*(uint64_t)bpw;
    if(!nb) return calloc(1,1);
    uint8_t *d=calloc(1,(size_t)nb); if(!d){perror("calloc");exit(1);}
    uint64_t pad=u256_to_u64(st->padding);
    if(pad){
        pad &= axx_word_mask(st->bts);
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

/* 同じ名前のセクションが何度も開かれている場合、その範囲を書かれた順に
   つないで 1 本の中身にする。 */
static uint8_t *weo_extract_ranges(AsmState*st, int bpw, const char*name, uint64_t *out_nb){
    uint64_t total_words = 0;
    int have_range = 0;
    for(int i=0;i<st->section_ranges.len;i++)
        if(strcmp(st->section_ranges.data[i].name,name)==0){
            have_range = 1;
            total_words += u256_to_u64(st->section_ranges.data[i].len);
        }
    if(!have_range){
        SecEntry *fe = secmap_find(&st->sections, name);
        if(fe && !u256_is_zero(fe->size)){
            uint64_t nb0 = u256_to_u64(fe->size)*(uint64_t)bpw;
            *out_nb = nb0;
            if(!nb0) return calloc(1,1);
            return weo_extract(st, bpw, u256_to_u64(fe->start), u256_to_u64(fe->size));
        }
    }
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

static WSR weo_shndx(AsmState*st,WCS*csecs,int ncs,uint64_t ba,const char*sec_name,
                      int bpw){
    uint64_t word_pc = bpw ? ba/(uint64_t)bpw : 0;
    if(sec_name){
        for(int i=0;i<ncs;i++){
            if(strcmp(csecs[i].name,sec_name)==0){
                int64_t woff = sec_word_offset(st, sec_name, word_pc);
                if(woff >= 0) return (WSR){(uint32_t)(i+1), (uint64_t)woff*(uint64_t)bpw};
            }
        }
    }
    for(int i=0;i<ncs;i++){
        int64_t woff = sec_word_offset(st, csecs[i].name, word_pc);
        if(woff >= 0) return (WSR){(uint32_t)(i+1), (uint64_t)woff*(uint64_t)bpw};
    }
    if(ncs>0){
        int best_i=0; uint64_t best_start=0; int found=0;
        for(int i=0;i<ncs;i++){
            if(csecs[i].bs<=ba && (!found || csecs[i].bs>=best_start)){ best_i=i; best_start=csecs[i].bs; found=1; }
        }
        uint64_t sv = ba - csecs[best_i].bs;
        if(!found || ba < csecs[best_i].bs) sv = 0;
        return (WSR){(uint32_t)(best_i+1), sv};
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

/* そのラベルが外部に出すものか。 */
static int weo_isexp(WLK*earr,int ne,const char*nm){
    for(int i=0;i<ne;i++) if(!strcmp(earr[i].name,nm)) return 1;
    return 0;
}

/* 名前からシンボル表の添字を引く。 */
static int weo_symof(WSNI*snimap,int snimap_len,const char*nm){
    if(!nm) return 0;
    for(int i=0;i<snimap_len;i++) if(!strcmp(snimap[i].name,nm)) return snimap[i].idx;
    return 0;
}

/* そのセクションが SHT_NOBITS（中身を持たない）か。 */
static int weo_isno(WCS*csecs,int i){
    return csecs[i].sht == 8u;
}

/* ファイル位置を目標まで 0 で詰める。 */
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
/* DWARF にアドレスを 1 個書く。 */
static void rb_waddr(RB*r,uint64_t v,int addr_sz,int is_le){
    if(addr_sz==8) rb_w8(r,v,is_le); else rb_w4(r,(uint32_t)v,is_le);
}
/* DWARF セクション用のリロケーションを 1 個積む。 */
static void drv_add(DRV*v,uint64_t off,int sym,int rtype,int64_t add){
    if(v->len>=v->cap){ v->cap=v->cap?v->cap*2:8; v->d=realloc(v->d,(size_t)v->cap*sizeof(DRE)); if(!v->d){perror("realloc");exit(1);} }
    v->d[v->len++]=(DRE){off,sym,rtype,add};
}
/* 積んだリロケーションを .rela/.rel の形に詰める。 */
/* `.elfencode` / `.elfrinfo` の関数を呼び、返した数を *out に置く（失敗は 0）。
   AsmState は Assembler の先頭にあるので、そこから Assembler を得る。
   axx.py の _elf_call_func() と同じ規則である。 */
static int elf_call_func(AsmState *st, const char *dname, const char *fname,
                         const uint256_t *args, int nargs, uint256_t *out){
    Assembler *asmb = (Assembler*)st;
    MiniFunc *f = mfv_find(&st->funcs, fname);
    if(!f) return 0;
    MiniVal av[4];
    for(int i = 0; i < nargs && i < 4; i++) av[i] = mini_num(args[i]);
    MiniRun r;
    memset(&r, 0, sizeof(r));
    r.asmb = asmb;
    iv_init(&r.out);
    r.c.file = f->file;
    r.c.line = f->line;
    r.c.jb_active = 1;
    volatile int ok = 0;   /* longjmp をまたぐので volatile */
    if(setjmp(r.c.jb) == 0){
        mini_call_func(&r, f, av, nargs);
        if(r.has_ret && !r.retval.is_arr && !r.retval.is_str){ *out = r.retval.num; ok = 1; }
        else axx_diagf(1, 0, " error - %s: function '%s' must return a number.\n", dname, fname);
    } else {
        axx_diagf(1, 0, " error - %s: %s\n", dname, r.c.err ? r.c.err : "?");
    }
    for(int i = 0; i < r.nframes; i++) mini_frame_clear(&r.frames[i]);
    free(r.frames);
    free(r.fb);
    free(r.c.err);
    mini_drop_ret(&r);
    free(r.out.data);
    for(int i = 0; i < nargs && i < 4; i++) mini_val_free(&av[i]);
    return ok;
}

/* 書き出し中の AsmState（r_info を組む関数を呼ぶため）。 */
static AsmState *g_weo_st = NULL;

/* r_info を組む。`.elfrinfo` があればその関数、無ければ ELF の決まりの形。
   axx.py の _elf_r_info() と同じ規則である。 */
static uint64_t weo_rinfo(int sym, int rtype, int is_elf64){
    if(g_weo_st && g_weo_st->elf_decl_rinfo){
        uint256_t a[2] = { u256_from_i64(sym), u256_from_i64(rtype) };
        uint256_t v = u256_zero();
        if(!elf_call_func(g_weo_st, ".elfrinfo", g_weo_st->elf_decl_rinfo, a, 2, &v)) v = u256_zero();
        uint64_t x = u256_to_u64(v);
        return is_elf64 ? x : (x & 0xFFFFFFFFu);
    }
    if(is_elf64) return ((uint64_t)sym<<32)|((uint32_t)rtype);
    return ((uint32_t)(sym&0xffffff)<<8)|((uint8_t)rtype);
}

static uint8_t* dwarf_pack_relocs(DRV*v,size_t*outlen,int is_le,int is_elf64,int is_rela){
    size_t entsz = is_elf64 ? (is_rela?24:16) : (is_rela?12:8);
    size_t n=(size_t)v->len*entsz; uint8_t*b=calloc(1,n?n:1);
    for(int i=0;i<v->len;i++){
        uint8_t*p=b+(size_t)i*entsz;
        if(is_elf64){
            uint64_t rinfo=weo_rinfo(v->d[i].sym, v->d[i].rtype, 1);
            weo_w8(p,v->d[i].off,is_le); weo_w8(p+8,rinfo,is_le);
            if(is_rela) weo_w8s(p+16,v->d[i].addend,is_le);
        } else {
            uint32_t rinfo=(uint32_t)weo_rinfo(v->d[i].sym, v->d[i].rtype, 0);
            weo_w4(p,(uint32_t)v->d[i].off,is_le); weo_w4(p+4,rinfo,is_le);
            if(is_rela) weo_w4(p+8,(uint32_t)v->d[i].addend,is_le);
        }
    }
    *outlen=n; return b;
}
static int lrow_cmp(const void*a,const void*b){ uint64_t x=((const LROW*)a)->wpc,y=((const LROW*)b)->wpc; return x<y?-1:(x>y?1:0); }

/* 欄の幅が nbytes の、PC 相対のデータ型（命令欄の型を除く）を 1 つ探す。
   axx.py の _reloc_data_pcrel() と同じ規則である。 */
static int elf_reloc_data_pcrel(const AsmState *st, const ElfMachineInfo *m, int nbytes){
    for(int i = 0; m->named[i].name; i++){
        int rt = m->named[i].rtype;
        if(elf_machine_reloc_bytes(m, rt) != nbytes || !elf_machine_is_pcrel(m, rt)) continue;
        if(insn_reloc_field_decl(st, rt)) continue;
        return rt;
    }
    return 0;
}

/* CFI の状態: CFA のレジスタとオフセット、remember_state の積み。 */
typedef struct { int64_t reg, off; int64_t *stk; int nstk, cstk; } CfiStt;

/* CFI の命令 1 つを DW_CFA_* のバイト列にする。誤りは err に書いて 0 を返す。
   axx.py の _cfi_op_bytes() と同じ規則である。 */
static int cfi_op_bytes(RB *out, const char *op, const int64_t *v, int nv, CfiStt *stt,
                        int64_t da, char *err, size_t esz){
    #define CFI_FAC(o_, f_) do { if((o_) % da != 0){ \
        snprintf(err, esz, "offset %lld is not a multiple of the data alignment factor %lld", \
                 (long long)(o_), (long long)da); return 0; } (f_) = (o_) / da; } while(0)
    int64_t f;
    if(strcmp(op, "def_cfa") == 0){
        stt->reg = v[0]; stt->off = v[1];
        if(v[1] >= 0){ rb_u8(out, 0x0c); rb_uleb(out, (uint64_t)v[0]); rb_uleb(out, (uint64_t)v[1]); return 1; }
        CFI_FAC(v[1], f);
        rb_u8(out, 0x12); rb_uleb(out, (uint64_t)v[0]); rb_sleb(out, f); return 1;
    }
    if(strcmp(op, "def_cfa_offset") == 0 || strcmp(op, "adjust_cfa_offset") == 0){
        int64_t o = op[0] == 'd' ? v[0] : stt->off + v[0];
        stt->off = o;
        if(o >= 0){ rb_u8(out, 0x0e); rb_uleb(out, (uint64_t)o); return 1; }
        CFI_FAC(o, f);
        rb_u8(out, 0x13); rb_sleb(out, f); return 1;
    }
    if(strcmp(op, "def_cfa_register") == 0){
        stt->reg = v[0];
        rb_u8(out, 0x0d); rb_uleb(out, (uint64_t)v[0]); return 1;
    }
    if(strcmp(op, "offset") == 0 || strcmp(op, "rel_offset") == 0 || strcmp(op, "val_offset") == 0){
        int64_t r = v[0], o = v[1];
        if(op[0] == 'r') o = o - stt->off;
        CFI_FAC(o, f);
        if(op[0] == 'v'){
            if(f >= 0){ rb_u8(out, 0x14); rb_uleb(out, (uint64_t)r); rb_uleb(out, (uint64_t)f); }
            else { rb_u8(out, 0x15); rb_uleb(out, (uint64_t)r); rb_sleb(out, f); }
            return 1;
        }
        if(f >= 0){
            if(r < 64){ rb_u8(out, (uint8_t)(0x80 | r)); rb_uleb(out, (uint64_t)f); }
            else { rb_u8(out, 0x05); rb_uleb(out, (uint64_t)r); rb_uleb(out, (uint64_t)f); }
            return 1;
        }
        rb_u8(out, 0x11); rb_uleb(out, (uint64_t)r); rb_sleb(out, f); return 1;
    }
    if(strcmp(op, "restore") == 0){
        if(v[0] < 64) rb_u8(out, (uint8_t)(0xc0 | v[0]));
        else { rb_u8(out, 0x06); rb_uleb(out, (uint64_t)v[0]); }
        return 1;
    }
    if(strcmp(op, "undefined") == 0){ rb_u8(out, 0x07); rb_uleb(out, (uint64_t)v[0]); return 1; }
    if(strcmp(op, "same_value") == 0){ rb_u8(out, 0x08); rb_uleb(out, (uint64_t)v[0]); return 1; }
    if(strcmp(op, "register") == 0){
        rb_u8(out, 0x09); rb_uleb(out, (uint64_t)v[0]); rb_uleb(out, (uint64_t)v[1]); return 1;
    }
    if(strcmp(op, "remember_state") == 0){
        if(stt->nstk + 2 > stt->cstk){
            stt->cstk = stt->cstk ? stt->cstk * 2 : 8;
            stt->stk = realloc(stt->stk, sizeof(int64_t) * (size_t)stt->cstk);
            if(!stt->stk){ perror("realloc"); exit(1); }
        }
        stt->stk[stt->nstk++] = stt->reg; stt->stk[stt->nstk++] = stt->off;
        rb_u8(out, 0x0a); return 1;
    }
    if(strcmp(op, "restore_state") == 0){
        if(stt->nstk < 2){ snprintf(err, esz, "restore_state without remember_state"); return 0; }
        stt->off = stt->stk[--stt->nstk]; stt->reg = stt->stk[--stt->nstk];
        rb_u8(out, 0x0b); return 1;
    }
    if(strcmp(op, "window_save") == 0 || strcmp(op, "negate_ra_state") == 0){ rb_u8(out, 0x2d); return 1; }
    if(strcmp(op, "escape") == 0){
        for(int i = 0; i < nv; i++) rb_u8(out, (uint8_t)v[i]);
        return 1;
    }
    snprintf(err, esz, "'%s' cannot be used here", op);
    return 0;
    #undef CFI_FAC
}

/* ポインタの符号化 enc の大きさ（バイト）。対応しないものは 0。 */
static int cfi_ptr_size(int enc, int psize){
    switch(enc & 0x0f){
    case 0x00: return psize;
    case 0x02: case 0x0a: return 2;
    case 0x03: case 0x0b: return 4;
    case 0x04: case 0x0c: return 8;
    default: return 0;
    }
}

/* リンカ緩和の機種で CFI が局所シンボルを要る位置の並び（初めて現れた順）。
   axx.py の _cfi_points() と同じ並び。 */
typedef struct { const char *sec; int64_t b; char *name; int sym; } CfiPt;
static int cfi_points(const AsmState *st, int bpw, CfiPt **out){
    CfiPt *p = NULL; int n = 0, c = 0;
    for(int i = 0; i < st->cfi_fdes_len; i++){
        const CfiFde *f = &st->cfi_fdes[i];
        int64_t cand[2048]; int nc = 0;
        int64_t *big = NULL;
        int64_t *pts = cand;
        int maxp = f->nops + 2;
        if(maxp > 2048){ big = malloc(sizeof(int64_t) * (size_t)maxp); if(!big){ perror("malloc"); exit(1); } pts = big; }
        int64_t cur = f->start * bpw;
        pts[nc++] = cur;
        for(int k = 0; k < f->nops; k++){
            int64_t ob = f->ops[k].off * bpw;
            if(ob > cur){ pts[nc++] = ob; cur = ob; }
        }
        pts[nc++] = f->end * bpw;
        for(int k = 0; k < nc; k++){
            int dup = 0;
            for(int j = 0; j < n; j++) if(p[j].b == pts[k] && strcmp(p[j].sec, f->sec) == 0){ dup = 1; break; }
            if(dup) continue;
            p = elf_decl_grow(p, &c, n, sizeof(CfiPt));
            p[n].sec = f->sec; p[n].b = pts[k]; p[n].name = NULL; p[n].sym = 0; n++;
        }
        free(big);
    }
    *out = p;
    return n;
}
static int cfi_pt_sym(const CfiPt *p, int n, const char *sec, int64_t b){
    for(int i = 0; i < n; i++) if(p[i].b == b && strcmp(p[i].sec, sec) == 0) return p[i].sym;
    return 0;
}

typedef struct { int64_t off; int sym; int rt; int64_t addend; } EhRel;
typedef struct { EhRel *d; int n, c; } EhRelV;
static void ehrel_push(EhRelV *v, int64_t off, int sym, int rt, int64_t addend){
    v->d = elf_decl_grow(v->d, &v->c, v->n, sizeof(EhRel));
    v->d[v->n++] = (EhRel){off, sym, rt, addend};
}

/* 符号化 enc のポインタのリロケーションを足す（欄は呼ぶ側が 0 で置く）。
   axx.py の _build_eh_frame() の ptr() と同じ規則である。 */
static void cfi_ptr_reloc(AsmState *st, const ElfMachineInfo *m, int enc, const char *sym,
                          int64_t at, int psize, WSNI *snimap, int snimap_len, EhRelV *rel){
    int n = cfi_ptr_size(enc, psize);
    int app = enc & 0x70;
    if(n == 0 || (app != 0x00 && app != 0x10)){
        axx_diagf(1, 0, " error - CFI: pointer encoding 0x%02x is not supported.\n", enc);
        return;
    }
    int rt = app == 0x10 ? elf_reloc_data_pcrel(st, m, n) : (n <= 8 ? m->wg[n] : 0);
    if(!rt){
        axx_diagf(1, 0, " error - CFI: no relocation type for a %d-byte pointer "
                        "(encoding 0x%02x).\n", n, enc);
        return;
    }
    int si = weo_symof(snimap, snimap_len, sym);
    if(!si){
        axx_diagf(1, 0, " error - CFI: unknown symbol '%s'.\n", sym);
        return;
    }
    ehrel_push(rel, at, si, rt, 0);
}

/* ソースの `.cfi_*` から `.eh_frame` の中身とリロケーションを組む。
   axx.py の _build_eh_frame() と同じ規則である。 */
static void build_eh_frame(AsmState *st, const ElfMachineInfo *m, int is_elf64, int is_rela,
                           int is_le, int bpw, WCS *csecs, int ncs, const CfiPt *pts, int npts,
                           WSNI *snimap, int snimap_len, RB *data, EhRelV *rel){
    if(st->cfi_fdes_len == 0) return;
    if(!st->elf_cfi_set){
        axx_diagf(1, 0, " error - CFI: the pattern file has no .elfcfi declaration.\n");
        return;
    }
    int64_t ra0 = st->elf_cfi_ra, code = st->elf_cfi_code, da = st->elf_cfi_data;
    int psize = is_elf64 ? 8 : 4;
    int pad = st->elf_cfi_pad ? st->elf_cfi_pad : psize;
    int pcrel4 = elf_reloc_data_pcrel(st, m, 4);
    if(!pcrel4){
        axx_diagf(1, 0, " error - CFI: no 4-byte PC-relative relocation type for the "
                        "FDE address; declare one with .elftype.\n");
        return;
    }
    int radd = 0, rsub = 0;
    int relax = elf_diff_of(st, 4, &radd, &rsub);
    if(relax && code != 1){
        axx_diagf(1, 0, " error - CFI: relocated advances need a code alignment factor of 1.\n");
        return;
    }
    /* 初期命令 */
    int ni = st->elf_cfiinit_len;
    CfiOp *init = calloc((size_t)(ni ? ni : 1), sizeof(CfiOp));
    if(!init){ perror("calloc"); exit(1); }
    for(int i = 0; i < ni; i++){
        const char *t = st->elf_cfiinit[i];
        const char *sp = strchr(t, ' ');
        size_t ol = sp ? (size_t)(sp - t) : strlen(t);
        char op[64]; if(ol >= sizeof(op)) ol = sizeof(op) - 1;
        memcpy(op, t, ol); op[ol] = '\0';
        for(char *q = op; *q; q++) *q = (char)tolower((unsigned char)*q);
        const char *spec = cfi_spec(op);
        static const char *bad[] = {"startproc","endproc","sections","return_column","signal_frame",
                                    "personality","lsda","adjust_cfa_offset","rel_offset",
                                    "remember_state","restore_state",NULL};
        int ok = spec != NULL;
        for(int k = 0; ok && bad[k]; k++) if(strcmp(op, bad[k]) == 0) ok = 0;
        char *args[64]; int na = 0;
        char *buf = strdup(sp ? sp + 1 : "");
        if(!buf){ perror("strdup"); exit(1); }
        {
            int allsp = 1;
            for(const char *q = buf; *q; q++) if(!isspace((unsigned char)*q)){ allsp = 0; break; }
            if(!allsp){
                char *q = buf;
                while(na < 64){
                    char *c2 = strchr(q, ',');
                    if(c2) *c2 = '\0';
                    char *b = q; while(isspace((unsigned char)*b)) b++;
                    char *e2 = b + strlen(b); while(e2 > b && isspace((unsigned char)e2[-1])) *--e2 = '\0';
                    args[na++] = b;
                    if(!c2) break;
                    q = c2 + 1;
                }
            }
        }
        if(ok && strcmp(spec, "*") != 0 && na != (int)strlen(spec)) ok = 0;
        int64_t vals[64];
        for(int k = 0; ok && k < na; k++){
            int r = elf_cfireg_find(st, args[k]);
            int64_t rv;
            if(r >= 0) rv = r;
            else {
                const char *a = args[k];
                int neg = 0;
                if(*a == '+' || *a == '-'){ neg = *a == '-'; a++; }
                if(a[0] == '0' && (a[1] == 'x' || a[1] == 'X') && a[2]){
                    for(const char *q = a + 2; *q; q++) if(!isxdigit((unsigned char)*q)){ ok = 0; break; }
                    if(ok) rv = (int64_t)strtoull(a + 2, NULL, 16);
                } else if(a[0]){
                    for(const char *q = a; *q; q++) if(!isdigit((unsigned char)*q)){ ok = 0; break; }
                    if(ok) rv = (int64_t)strtoull(a, NULL, 10);
                } else ok = 0;
                if(!ok) break;
                if(neg) rv = -rv;
            }
            if(strcmp(spec, "*") == 0 && (rv < 0 || rv > 255)){ ok = 0; break; }
            vals[k] = rv;
        }
        if(!ok){
            axx_diagf(1, 0, " error - .elfcfiinit: cannot use '%s'.\n", t);
            free(buf);
            for(int k = 0; k < i; k++) free(init[k].v);
            free(init);
            return;
        }
        snprintf(init[i].op, sizeof(init[i].op), "%s", op);
        init[i].nv = na;
        init[i].v = malloc(sizeof(int64_t) * (size_t)(na ? na : 1));
        if(!init[i].v){ perror("malloc"); exit(1); }
        for(int k = 0; k < na; k++) init[i].v[k] = vals[k];
        free(buf);
    }

    /* CIE の鍵ごとの位置 */
    typedef struct { int64_t ra; int signal, simple, penc; const char *psym; int lenc; int64_t off; } CieK;
    CieK *cies = NULL; int ncie = 0, ccie = 0;
    char err[256];

    #define EH_RUN(ops_, nops_, stt_, body_) do { \
        for(int _q = 0; _q < (nops_); _q++){ \
            if(!cfi_op_bytes((body_), (ops_)[_q].op, (ops_)[_q].v, (ops_)[_q].nv, (stt_), da, err, sizeof(err))) \
                axx_diagf(1, 0, " error - CFI: .cfi_%s: %s.\n", (ops_)[_q].op, err); \
        } } while(0)
    #define EH_EMIT(body_) do { \
        size_t _tot = 4 + (body_).len; \
        size_t _pd = (size_t)((pad - (int64_t)(_tot % (size_t)pad)) % pad); \
        for(size_t _z = 0; _z < _pd; _z++) rb_u8(&(body_), 0); \
        rb_w4(data, (uint32_t)(body_).len, is_le); rb_app(data, (body_).b, (body_).len); \
        free((body_).b); } while(0)

    for(int fi = 0; fi < st->cfi_fdes_len; fi++){
        const CfiFde *fd = &st->cfi_fdes[fi];
        int sidx = 0;
        for(int i = 0; i < ncs; i++) if(strcmp(csecs[i].name, fd->sec) == 0){ sidx = i + 1; break; }
        if(!sidx){
            axx_diagf(1, 0, " error - CFI: section '%s' of a function is not in the output.\n", fd->sec);
            continue;
        }
        int64_t ra = fd->ra >= 0 ? fd->ra : ra0;
        int ci = -1;
        for(int k = 0; k < ncie; k++)
            if(cies[k].ra == ra && cies[k].signal == fd->signal && cies[k].simple == fd->simple
               && cies[k].penc == fd->pers_enc && cies[k].lenc == fd->lsda_enc
               && (fd->pers_enc < 0 || strcmp(cies[k].psym, fd->pers_sym) == 0)){ ci = k; break; }
        if(ci < 0){
            int64_t c_off = (int64_t)data->len;
            cies = elf_decl_grow(cies, &ccie, ncie, sizeof(CieK));
            cies[ncie] = (CieK){ra, fd->signal, fd->simple, fd->pers_enc, fd->pers_sym, fd->lsda_enc, c_off};
            ci = ncie++;
            RB body; rb_init(&body);
            rb_w4(&body, 0, is_le);
            int ver = ra <= 255 ? 1 : 3;
            rb_u8(&body, (uint8_t)ver);
            char aug[8]; int al = 0;
            aug[al++] = 'z';
            if(fd->pers_enc >= 0) aug[al++] = 'P';
            if(fd->lsda_enc >= 0) aug[al++] = 'L';
            aug[al++] = 'R';
            if(fd->signal) aug[al++] = 'S';
            rb_app(&body, aug, (size_t)al); rb_u8(&body, 0);
            rb_uleb(&body, (uint64_t)code); rb_sleb(&body, da);
            if(ver == 1) rb_u8(&body, (uint8_t)ra); else rb_uleb(&body, (uint64_t)ra);
            RB augd; rb_init(&augd);
            int p_pos = -1, p_n = 0;
            if(fd->pers_enc >= 0){
                rb_u8(&augd, (uint8_t)fd->pers_enc);
                p_pos = (int)augd.len;
                p_n = cfi_ptr_size(fd->pers_enc, psize);
                for(int z = 0; z < p_n; z++) rb_u8(&augd, 0);
            }
            if(fd->lsda_enc >= 0) rb_u8(&augd, (uint8_t)fd->lsda_enc);
            rb_u8(&augd, 0x1b);
            RB lb; rb_init(&lb); rb_uleb(&lb, augd.len);
            if(p_pos >= 0){
                int64_t at = c_off + 4 + (int64_t)body.len + (int64_t)lb.len + p_pos;
                cfi_ptr_reloc(st, m, fd->pers_enc, fd->pers_sym, at, psize, snimap, snimap_len, rel);
            }
            rb_app(&body, lb.b, lb.len); rb_app(&body, augd.b, augd.len);
            free(lb.b); free(augd.b);
            if(!fd->simple){
                CfiStt s0; memset(&s0, 0, sizeof(s0));
                EH_RUN(init, ni, &s0, &body);
                free(s0.stk);
            }
            EH_EMIT(body);
        }
        int64_t c_off = cies[ci].off;
        int64_t f_off = (int64_t)data->len;
        CfiStt stt; memset(&stt, 0, sizeof(stt));
        if(!fd->simple){
            RB scratch; rb_init(&scratch);
            EH_RUN(init, ni, &stt, &scratch);
            free(scratch.b);
            stt.nstk = 0;
        }
        int64_t sb = fd->start * bpw, eb = fd->end * bpw;
        RB body; rb_init(&body);
        rb_w4(&body, (uint32_t)((f_off + 4) - c_off), is_le);
        int64_t at = f_off + 4 + (int64_t)body.len;
        if(relax){
            ehrel_push(rel, at, cfi_pt_sym(pts, npts, fd->sec, sb), pcrel4, 0);
            rb_w4(&body, 0, is_le);
        } else {
            ehrel_push(rel, at, sidx, pcrel4, sb);
            rb_w4(&body, is_rela ? 0 : (uint32_t)sb, is_le);
        }
        at = f_off + 4 + (int64_t)body.len;
        if(relax){
            ehrel_push(rel, at, cfi_pt_sym(pts, npts, fd->sec, eb), radd, 0);
            ehrel_push(rel, at, cfi_pt_sym(pts, npts, fd->sec, sb), rsub, 0);
            rb_w4(&body, 0, is_le);
        } else {
            rb_w4(&body, (uint32_t)(eb - sb), is_le);
        }
        if(fd->lsda_enc >= 0){
            int n = cfi_ptr_size(fd->lsda_enc, psize);
            rb_uleb(&body, (uint64_t)n);
            at = f_off + 4 + (int64_t)body.len;
            cfi_ptr_reloc(st, m, fd->lsda_enc, fd->lsda_sym, at, psize, snimap, snimap_len, rel);
            for(int z = 0; z < n; z++) rb_u8(&body, 0);
        } else rb_uleb(&body, 0);
        int64_t cur = sb;
        for(int k = 0; k < fd->nops; k++){
            const CfiOp *o = &fd->ops[k];
            int64_t ob = o->off * bpw;
            if(ob < cur){
                axx_diagf(1, 0, " error - CFI: a .cfi_%s is placed before the previous one.\n", o->op);
                continue;
            }
            if(ob > cur){
                if(relax){
                    at = f_off + 4 + (int64_t)body.len + 1;
                    ehrel_push(rel, at, cfi_pt_sym(pts, npts, fd->sec, ob), radd, 0);
                    ehrel_push(rel, at, cfi_pt_sym(pts, npts, fd->sec, cur), rsub, 0);
                    rb_u8(&body, 0x04); rb_w4(&body, 0, is_le);
                } else {
                    int64_t d = ob - cur;
                    if(d % code != 0)
                        axx_diagf(1, 0, " error - CFI: an advance of %lld bytes is not a multiple "
                                        "of the code alignment factor %lld.\n", (long long)d, (long long)code);
                    int64_t f = d / code;
                    if(f < 64) rb_u8(&body, (uint8_t)(0x40 | f));
                    else if(f <= 0xff){ rb_u8(&body, 0x02); rb_u8(&body, (uint8_t)f); }
                    else if(f <= 0xffff){ rb_u8(&body, 0x03); rb_w2(&body, (uint16_t)f, is_le); }
                    else { rb_u8(&body, 0x04); rb_w4(&body, (uint32_t)f, is_le); }
                }
                cur = ob;
            }
            EH_RUN(o, 1, &stt, &body);
        }
        free(stt.stk);
        EH_EMIT(body);
    }
    #undef EH_RUN
    #undef EH_EMIT
    free(cies);
    for(int k = 0; k < ni; k++) free(init[k].v);
    free(init);
}

/* `.elflink` の sh_link / sh_info の綴りをセクション番号にする。数（10 進か
   0x 付き 16 進）ならそのまま、名前なら出力するセクションから引く。
   axx.py の write_elf_obj() の _shidx_of() と同じ規則である。 */
static uint32_t weo_shidx_of(AsmState *st, const char *text, const char *sname, const char *what,
                             WCS *csecs, int ncs, const int *rs_idx, int nrela, int G,
                             int is_rela, int sym_shidx, int str_shidx, int shstrndx,
                             const DSEC *dbg_prog, int n_dbg_prog, int dbg_base){
    (void)st;
    if(!text || !text[0]) return 0;
    int alld = 1;
    for(const char *q = text; *q; q++) if(!isdigit((unsigned char)*q)){ alld = 0; break; }
    if(alld) return (uint32_t)strtoul(text, NULL, 10);
    if(text[0] == '0' && (text[1] == 'x' || text[1] == 'X') && text[2]){
        int allh = 1;
        for(const char *q = text + 2; *q; q++) if(!isxdigit((unsigned char)*q)){ allh = 0; break; }
        if(allh) return (uint32_t)strtoul(text + 2, NULL, 16);
    }
    for(int i = 0; i < ncs; i++)
        if(strcasecmp(csecs[i].name, text) == 0) return (uint32_t)(i + 1 + G);
    for(int ri = 0; ri < nrela; ri++){
        /* `.rel` / `.rela` に節の名前を続けた名前と比べる（長さの制限なし）。 */
        const char *pfx = is_rela ? ".rela" : ".rel";
        size_t pl = strlen(pfx);
        if(strncasecmp(text, pfx, pl) == 0
           && strcasecmp(text + pl, csecs[rs_idx[ri]].name) == 0)
            return (uint32_t)(ncs + 1 + ri + G);
    }
    if(strcasecmp(text, ".symtab") == 0) return (uint32_t)sym_shidx;
    if(strcasecmp(text, ".strtab") == 0) return (uint32_t)str_shidx;
    if(strcasecmp(text, ".shstrtab") == 0) return (uint32_t)shstrndx;
    for(int i = 0; i < n_dbg_prog; i++)
        if(strcasecmp(dbg_prog[i].name, text) == 0) return (uint32_t)(dbg_base + 1 + i);
    axx_diagf(0, 0, " warning - .elflink: %s of '%s': no section named '%s'; written as 0.\n",
               what, sname, text);
    return 0;
}

/* ELF 再配置可能オブジェクトを書く。 */
static void write_elf_obj(AsmState *st, const char *path, int machine){
    int bpw = (st->bts+7)/8; if(bpw<1) bpw=1;
    g_weo_st = st;

    int _is_le  = !st->endian_big;
    int _ei_data = _is_le ? 1 : 2;

    const ElfMachineInfo *_mtbl_w = elf_machine_effective(st);
    int _is_rela_w = _mtbl_w->is_rela;

    int _native_elfclass = _mtbl_w->elfclass;
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

    /* 中身の大きさに -b と同じ上限を置く。`.org` の誤りで巨大なファイルを
       書き始めないため。axx.py の write_elf_obj() と同じ数え方である。 */
    {
        uint256_t _tw = u256_zero();
        if(st->sections.count==0){
            if(st->pc_overflow_set) _tw = u256_add(st->pc_overflow_max, u256_from_u64(1));
            else if(have_w) _tw = u256_add(u256_from_u64(max_w), u256_from_u64(1));
        } else {
            for(int i=0;i<st->sections.count;i++){
                SecEntry *se=st->sections.order[i];
                int _hr=0;
                for(int k=0;k<st->section_ranges.len;k++)
                    if(strcmp(st->section_ranges.data[k].name,se->name)==0){
                        _hr=1; _tw=u256_add(_tw, st->section_ranges.data[k].len);
                    }
                if(!_hr && !u256_is_zero(se->size) && !u256_is_neg256(se->size))
                    _tw=u256_add(_tw, se->size);
            }
        }
        uint256_t _tot = u256_mul(_tw, u256_from_u64((uint64_t)bpw));
        const uint64_t MAX_OUTPUT_BYTES = (uint64_t)1<<30;
        if(u256_gt_signed(_tot, u256_from_u64(MAX_OUTPUT_BYTES))){
            char _tb[96]; u256_to_pydec(_tot, _tb, sizeof(_tb));
            axx_diagf(1, 1, " error - output size %s bytes exceeds maximum %llu."
                            " Check for incorrect .ORG or address values.\n",
                      _tb, (unsigned long long)MAX_OUTPUT_BYTES);
            g_weo_st = NULL;
            return;
        }
    }

    int ncs=0; WCS *csecs=NULL;
    if(st->sections.count==0){
        ncs=1; csecs=calloc(1,sizeof(WCS));
        uint64_t wn=have_w?max_w+1:0;
        uint64_t _fl0; uint32_t _sht0; int _as0; uint32_t _al0; uint32_t _es0;
        elf_section_attrs(st, ".text", &_fl0, &_sht0, &_as0, &_al0, &_es0);
        csecs[0]=(WCS){".text",0,wn*(uint64_t)bpw,_fl0,weo_extract(st,bpw,0,wn),
                       _sht0,_as0,_al0,_es0};
    } else {
        ncs=st->sections.count; csecs=calloc((size_t)ncs,sizeof(WCS));
        for(int i=0;i<ncs;i++){
            SecEntry *se=st->sections.order[i];
            uint64_t w0=u256_to_u64(se->start);
            uint64_t fl; uint32_t _sht; int _as; uint32_t _al; uint32_t _es;
            elf_section_attrs(st, se->name, &fl, &_sht, &_as, &_al, &_es);
            uint64_t _nb;
            uint8_t *_data = weo_extract_ranges(st, bpw, se->name, &_nb);
            csecs[i]=(WCS){se->name,w0*(uint64_t)bpw,_nb,fl,_data,_sht,_as,_al,_es};
        }
    }

    WRL *rela_lists=calloc((size_t)ncs,sizeof(WRL));
    for(int ri=0;ri<st->reloc_count;ri++){
        int sidx=-1;
        for(int i=0;i<ncs;i++) if(strcmp(st->relocations[ri].section,csecs[i].name)==0){sidx=i;break;}
        if(sidx<0){
            if(should_report_errors(st)){
                axx_diagf(1, 0, " error - relocation references unknown section '%s'; dropped from output.\n",
                           st->relocations[ri].section);
            }
            continue;
        }
        WRL *rl=&rela_lists[sidx];
        if(rl->len>=rl->cap){rl->cap=rl->cap?rl->cap*2:4;rl->data=realloc(rl->data,rl->cap*sizeof(WRE));if(!rl->data){perror("realloc");exit(1);}}
        rl->data[rl->len++]=(WRE){st->relocations[ri].sec_offset,st->relocations[ri].sym,
                                   st->relocations[ri].rtype,st->relocations[ri].addend,
                                   st->relocations[ri].nbytes};
        /* `.elfextra` の添えるリロケーション。同じ位置、加数 0。 */
        int _crt[64], _csym[64];
        int _nx = elf_extras_of(st, st->relocations[ri].rtype, _crt, _csym, 64);
        for(int _x = 0; _x < _nx; _x++){
            if(rl->len>=rl->cap){rl->cap=rl->cap?rl->cap*2:4;rl->data=realloc(rl->data,rl->cap*sizeof(WRE));if(!rl->data){perror("realloc");exit(1);}}
            rl->data[rl->len++]=(WRE){st->relocations[ri].sec_offset,
                                       _csym[_x] ? st->relocations[ri].sym : NULL,
                                       _crt[_x], 0, st->relocations[ri].nbytes};
        }
    }

    if(!_is_rela_w){
        uint64_t _wmask_r = axx_word_mask(st->bts);
        for(int i=0;i<ncs;i++){
            WRL *rl=&rela_lists[i];
            for(int ei=0;ei<rl->len;ei++){
                int64_t off = rl->data[ei].off;
                int nb = rl->data[ei].nbytes;
                /* 同じ位置に複数の項目があるとき（`.elfdiff` の対、`.elfextra`）は
                   最初の項目の加数だけを書き戻す。 */
                int _dup = 0;
                for(int ej=0;ej<ei;ej++) if(rl->data[ej].off == off){ _dup = 1; break; }
                if(_dup) continue;
                const ElfFieldInfo *_fd = insn_reloc_field_decl(st, rl->data[ei].rtype);
                const char *_enc = elf_encode_of(st, rl->data[ei].rtype);
                if(_enc){
                    /* `.elfencode` の関数が (欄の値, 加数) から新しい欄を作る。 */
                    int _nw = nb / bpw; if(_nw < 1) _nw = 1;
                    if(off < 0 || (uint64_t)(off + (int64_t)_nw * bpw) > csecs[i].bsz) continue;
                    uint8_t *dp = csecs[i].data + off;
                    uint64_t _iv = 0;
                    for(int k=0;k<_nw;k++){
                        uint64_t _wv = 0;
                        for(int j=0;j<bpw;j++){
                            int bj = _is_le ? (bpw - 1 - j) : j;
                            _wv = (_wv << 8) | dp[k*bpw + bj];
                        }
                        int _sh = st->bts * (_is_le ? k : (_nw - 1 - k));
                        if(_sh < 64) _iv |= (_wv & _wmask_r) << _sh;
                    }
                    uint256_t _a[2] = { u256_from_u64(_iv), u256_from_i64(rl->data[ei].addend) };
                    uint256_t _nv256;
                    if(!elf_call_func(st, ".elfencode", _enc, _a, 2, &_nv256)) continue;
                    uint64_t _nv = u256_to_u64(_nv256);
                    for(int k=0;k<_nw;k++){
                        int _sh = st->bts * (_is_le ? k : (_nw - 1 - k));
                        uint64_t _wv = (_sh < 64) ? ((_nv >> _sh) & _wmask_r) : 0;
                        for(int j=0;j<bpw;j++){
                            int bj = _is_le ? j : (bpw - 1 - j);
                            dp[k*bpw + bj] = (uint8_t)(_wv & 0xff);
                            _wv >>= 8;
                        }
                    }
                    continue;
                }
                if(_fd){
                    /* 命令欄の型。加数をシフトしてマスクのビットへ下から詰め、
                       欄の外（命令の残り）はそのまま残す。axx.py の
                       write_elf_obj() と同じ規則である。 */
                    int _nw = nb / bpw; if(_nw < 1) _nw = 1;
                    if(off < 0 || (uint64_t)(off + (int64_t)_nw * bpw) > csecs[i].bsz) continue;
                    uint8_t *dp = csecs[i].data + off;
                    uint64_t _iv = 0;
                    for(int k=0;k<_nw;k++){
                        uint64_t _wv = 0;
                        for(int j=0;j<bpw;j++){
                            int bj = _is_le ? (bpw - 1 - j) : j;
                            _wv = (_wv << 8) | dp[k*bpw + bj];
                        }
                        int _sh = st->bts * (_is_le ? k : (_nw - 1 - k));
                        if(_sh < 64) _iv |= (_wv & _wmask_r) << _sh;
                    }
                    int64_t _ad = rl->data[ei].addend;
                    int64_t _sv = (_fd->shift < 64) ? (_ad >> _fd->shift) : (_ad < 0 ? -1 : 0);
                    _iv = (_iv & ~_fd->mask) | field_deposit(_fd->mask, _sv);
                    for(int k=0;k<_nw;k++){
                        int _sh = st->bts * (_is_le ? k : (_nw - 1 - k));
                        uint64_t _wv = (_sh < 64) ? ((_iv >> _sh) & _wmask_r) : 0;
                        for(int j=0;j<bpw;j++){
                            int bj = _is_le ? j : (bpw - 1 - j);
                            dp[k*bpw + bj] = (uint8_t)(_wv & 0xff);
                            _wv >>= 8;
                        }
                    }
                    continue;
                }
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

    /* `.elfgroup` のセクショングループ。メンバーより前に来なければならない
       （gABI）ので、セクションヘッダ表の先頭に置き、残りの番号を G だけずらす。
       axx.py の write_elf_obj() と同じ規則である。 */
    int G = 0;
    int *grp_of = calloc((size_t)(st->elf_groups_len ? st->elf_groups_len : 1), sizeof(int));
    int **grp_nums = calloc((size_t)(st->elf_groups_len ? st->elf_groups_len : 1), sizeof(int*));
    int *grp_nnum = calloc((size_t)(st->elf_groups_len ? st->elf_groups_len : 1), sizeof(int));
    int *grp_member = calloc((size_t)(ncs ? ncs : 1), sizeof(int));
    if(!grp_of || !grp_nums || !grp_nnum || !grp_member){ perror("calloc"); exit(1); }
    for(int gi = 0; gi < st->elf_groups_len; gi++){
        int *nums = calloc((size_t)st->elf_groups[gi].nmem, sizeof(int));
        if(!nums){ perror("calloc"); exit(1); }
        int nn = 0;
        for(int k = 0; k < st->elf_groups[gi].nmem; k++){
            int found = 0;
            for(int i = 0; i < ncs; i++)
                if(strcasecmp(csecs[i].name, st->elf_groups[gi].mem[k]) == 0){ found = i + 1; break; }
            if(!found){
                axx_diagf(0, 0, " warning - .elfgroup: member section '%s' of group '%s' is not "
                           "in the output; ignored.\n", st->elf_groups[gi].mem[k], st->elf_groups[gi].name);
                continue;
            }
            int dup = 0;
            for(int j = 0; j < nn; j++) if(nums[j] == found){ dup = 1; break; }
            if(!dup) nums[nn++] = found;
        }
        if(nn){
            grp_of[G] = gi; grp_nums[G] = nums; grp_nnum[G] = nn; G++;
        } else {
            axx_diagf(0, 0, " warning - .elfgroup: group '%s' has no member in the output; "
                       "not written.\n", st->elf_groups[gi].name);
            free(nums);
        }
    }
    for(int g = 0; g < G; g++)
        for(int k = 0; k < grp_nnum[g]; k++){
            csecs[grp_nums[g][k] - 1].fl |= 0x200;
            grp_member[grp_nums[g][k] - 1] = 1;
        }
    /* `.elfunit::word` ならシンボルの値と大きさはワード単位で書く。 */
    int _word_unit = (st->elf_decl_unit == 1);
    int _bpw_sym = _word_unit ? 1 : bpw;

    WBB shstr; wbb_init(&shstr);
    WBB strtab_bb; wbb_init(&strtab_bb);

    uint32_t *sec_noff=calloc((size_t)ncs,sizeof(uint32_t));
    for(int i=0;i<ncs;i++) sec_noff[i]=wbb_str(&shstr,csecs[i].name);
    uint32_t *rela_noff=calloc((size_t)(nrela?nrela:1),sizeof(uint32_t));
    for(int ri2=0;ri2<nrela;ri2++){
        const char *_rpfx = _is_rela_w ? ".rela" : ".rel";
        size_t _rnsz = strlen(_rpfx) + strlen(csecs[rs_idx[ri2]].name) + 1;
        char *rn = malloc(_rnsz);
        if(!rn){ perror("malloc"); exit(1); }
        snprintf(rn, _rnsz, "%s%s", _rpfx, csecs[rs_idx[ri2]].name);
        rela_noff[ri2]=wbb_str(&shstr,rn);
        free(rn);
    }
    uint32_t sym_noff  =wbb_str(&shstr,".symtab");
    uint32_t str_noff  =wbb_str(&shstr,".strtab");
    uint32_t shstr_noff=wbb_str(&shstr,".shstrtab");

    int WEO_SYMSZ = _is_elf64 ? 24 : 16;
    WBB symtab_bb; symtab_bb.b=calloc(32,(size_t)WEO_SYMSZ); symtab_bb.len=0; symtab_bb.cap=32*WEO_SYMSZ;
    int nsyms=0;
    WSNI *snimap=calloc((size_t)(st->labels.count+st->export_labels.count+8),sizeof(WSNI));
    int snimap_len=0;

    /* 節番号が SHN_LORESERVE (0xff00) 以上のセクションがあれば、st_shndx に
       SHN_XINDEX (0xffff) を書き、本当の番号を `.symtab_shndx` に置く。
       axx.py の write_elf_obj() の _psym() と同じ規則である。 */
    int _need_xidx = (ncs + G) >= 0xff00;
    uint32_t *sym_xidx = NULL; int n_xidx = 0, c_xidx = 0;
    #define WEO_PSYM(nm_, info_, oth_, shx_, special_, val_, sz_) do { \
        uint32_t _s32 = (shx_); uint32_t _xv = 0; \
        if(!(special_) && _s32 >= 0xff00){ _xv = _s32; _s32 = 0xffff; } \
        sym_xidx = elf_decl_grow(sym_xidx, &c_xidx, n_xidx, sizeof(uint32_t)); \
        sym_xidx[n_xidx++] = _xv; \
        weo_sym(&symtab_bb,&nsyms,_is_le,_is_elf64,(nm_),(info_),(oth_),(uint16_t)_s32,(val_),(sz_)); \
    } while(0)
    WEO_PSYM(0,0,0,0,1,0,0);
    for(int i=0;i<ncs;i++) WEO_PSYM(0,0x03,0,(uint32_t)(i+1+G),0,0,0);

    /* リンカ緩和の機種の CFI が使う局所シンボル（.Lcfi<n>）。 */
    CfiPt *cfi_pts = NULL; int n_cfi_pts = 0;
    {
        int _ra, _rs;
        if(st->cfi_fdes_len > 0 && elf_diff_of(st, 4, &_ra, &_rs)){
            n_cfi_pts = cfi_points(st, bpw, &cfi_pts);
            for(int k = 0; k < n_cfi_pts; k++){
                char nm[64]; snprintf(nm, sizeof(nm), ".Lcfi%d", k);
                size_t L = strlen(nm);
                char *name = malloc(L + 64);
                if(!name){ perror("malloc"); exit(1); }
                memcpy(name, nm, L + 1);
                while(lmap_find(&st->labels, name) || lmap_find(&st->export_labels, name)){
                    name = realloc(name, strlen(name) + 2);
                    if(!name){ perror("realloc"); exit(1); }
                    strcat(name, "_");
                }
                cfi_pts[k].name = name;
            }
        }
    }

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
        int _via_sec = !(larr[i].is_equ && !_equ_has_reloc);
        WSR sr = !_via_sec
                 ? (WSR){0xfff1, larr[i].val}
                 : weo_shndx(st,csecs,ncs,larr[i].val*(uint64_t)bpw,larr[i].section,bpw);
        uint32_t _shx = sr.shndx; uint64_t _sval = sr.sv;
        int _special = !_via_sec || ncs == 0;
        if(_via_sec){
            if(ncs > 0) _shx = _shx + (uint32_t)G;
            if(_word_unit) _sval /= (uint64_t)bpw;
        }
        uint64_t _ssz = weo_sym_size(st, larr[i].name, _bpw_sym);
        if(sym_attr_get(st, larr[i].name).common) _special = 1;
        weo_sym_common(st, larr[i].name, _bpw_sym, &_shx, &_sval, &_ssz);
        uint32_t noff=wbb_str(&strtab_bb,larr[i].name);
        snimap[snimap_len++]=(WSNI){larr[i].name,nsyms};
        WEO_PSYM(noff, weo_sym_info(st,larr[i].name,0), weo_sym_other(st,larr[i].name),
                 _shx, _special, _sval, _ssz);
    }
    for(int k = 0; k < n_cfi_pts; k++){
        int _si = 0;
        for(int i = 0; i < ncs; i++) if(strcmp(csecs[i].name, cfi_pts[k].sec) == 0){ _si = i + 1; break; }
        if(!_si) continue;
        uint32_t noff = wbb_str(&strtab_bb, cfi_pts[k].name);
        cfi_pts[k].sym = nsyms;
        uint64_t _cv = _word_unit ? (uint64_t)cfi_pts[k].b / (uint64_t)bpw : (uint64_t)cfi_pts[k].b;
        WEO_PSYM(noff, 0, 0, (uint32_t)(_si + G), 0, _cv, 0);
    }
    int first_global=nsyms;
    for(int i=0;i<nl;i++){
        if(!larr[i].is_imported) continue;
        if(weo_isexp(earr,ne,larr[i].name)) continue;
        uint32_t _shx = 0; uint64_t _sval = 0;
        uint64_t _ssz = weo_sym_size(st, larr[i].name, _bpw_sym);
        weo_sym_common(st, larr[i].name, _bpw_sym, &_shx, &_sval, &_ssz);
        uint32_t noff=wbb_str(&strtab_bb,larr[i].name);
        snimap[snimap_len++]=(WSNI){larr[i].name,nsyms};
        WEO_PSYM(noff, weo_sym_info(st,larr[i].name,1), weo_sym_other(st,larr[i].name),
                 _shx, 1, _sval, _ssz);
    }
    for(int i=0;i<ne;i++){
        int _equ_has_reloc = earr[i].is_equ && (earr[i].reloc_type_override >= 0);
        int _via_sec = !(earr[i].is_equ && !_equ_has_reloc);
        WSR sr = !_via_sec
                 ? (WSR){0xfff1, earr[i].val}
                 : weo_shndx(st,csecs,ncs,earr[i].val*(uint64_t)bpw,earr[i].section,bpw);
        uint32_t _shx = sr.shndx; uint64_t _sval = sr.sv;
        int _special = !_via_sec || ncs == 0;
        if(_via_sec){
            if(ncs > 0) _shx = _shx + (uint32_t)G;
            if(_word_unit) _sval /= (uint64_t)bpw;
        }
        uint64_t _ssz = weo_sym_size(st, earr[i].name, _bpw_sym);
        if(sym_attr_get(st, earr[i].name).common) _special = 1;
        weo_sym_common(st, earr[i].name, _bpw_sym, &_shx, &_sval, &_ssz);
        uint32_t noff=wbb_str(&strtab_bb,earr[i].name);
        snimap[snimap_len++]=(WSNI){earr[i].name,nsyms};
        WEO_PSYM(noff, weo_sym_info(st,earr[i].name,1), weo_sym_other(st,earr[i].name),
                 _shx, _special, _sval, _ssz);
    }


    /* `.elfrinfo` が r_info の形を決めているときは、型欄の幅の警告は出さない。 */
    if(!_is_elf64 && !st->elf_decl_rinfo){
        int *warned = NULL; int nwarned = 0, cwarned = 0; int warned_sym = 0;
        for(int ri2=0;ri2<nrela;ri2++){
            WRL *rl=&rela_lists[rs_idx[ri2]];
            for(int ei=0;ei<rl->len;ei++){
                int rt = rl->data[ei].rtype;
                if(rt > 0xFF){
                    int seen = 0;
                    for(int k=0;k<nwarned;k++) if(warned[k]==rt){ seen=1; break; }
                    if(!seen){
                        if(nwarned >= cwarned){
                            cwarned = cwarned ? cwarned*2 : 8;
                            warned = realloc(warned, sizeof(int)*(size_t)cwarned);
                            if(!warned){ perror("realloc"); exit(1); }
                        }
                        warned[nwarned++] = rt;
                        axx_diagf(0, 0, " warning - relocation type %d does not fit the "
                                        "8-bit type field of an ELF32 r_info; it is "
                                        "written as %d.\n", rt, rt & 0xFF);
                    }
                }
                if(!warned_sym
                   && weo_symof(snimap,snimap_len,rl->data[ei].sym) > 0xFFFFFF){
                    warned_sym = 1;
                    axx_diagf(0, 0, " warning - more than 16777215 symbols: the symbol "
                                    "index does not fit the 24-bit field of an ELF32 "
                                    "r_info.\n");
                }
            }
        }
        free(warned);
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
                uint64_t rinfo=weo_rinfo(sym, rl->data[ei].rtype, 1);
                WEO_LE8(rp,(uint64_t)rl->data[ei].off);
                WEO_LE8(rp+8,rinfo);
                if(_is_rela_w) WEO_LE8S(rp+16,rl->data[ei].addend);
            } else {
                uint32_t rinfo=(uint32_t)weo_rinfo(sym, rl->data[ei].rtype, 0);
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

    const ElfMachineInfo *_mtbl_dbg = elf_machine_effective(st);
    if(st->gen_debug && st->line_map_len>0 && !_mtbl_dbg->dwarf_abs){
        axx_diagf(0, 0, " warning - DWARF debug info (-g) needs an absolute relocation "
                   "type for machine %d; declare it with .elfdwarf. Skipping debug "
                   "sections.\n", machine);
    }
    if(st->gen_debug && st->line_map_len>0 && _mtbl_dbg->dwarf_abs){


        int addr_sz = _is_elf64 ? 8 : 4;
        int is_rela_dbg = _is_rela_w;

        int abs64 = _mtbl_dbg->dwarf_abs;
        if(elf_machine_reloc_bytes(_mtbl_dbg, abs64) != addr_sz){
            int _alt = elf_machine_named(_mtbl_dbg, addr_sz == 8 ? "abs64" : "abs32");
            if(_alt > 0 && elf_machine_reloc_bytes(_mtbl_dbg, _alt) == addr_sz){
                abs64 = _alt;
            } else {
                axx_diagf(0, 0, " warning - DWARF debug info (-g) needs a %d-byte absolute "
                           "relocation, which %s does not have; skipping debug sections.\n",
                           addr_sz, _mtbl_dbg->name);
                goto dbg_done;
            }
        }

        RB abv; rb_init(&abv);
        int _dbg_nchild = 0;
        for(int i=0;i<nl;i++){
            if(larr[i].is_equ || larr[i].is_imported) continue;
            WSR _sr = weo_shndx(st,csecs,ncs,larr[i].val*(uint64_t)bpw,larr[i].section,bpw);
            if(_sr.shndx==0xfff1) continue;
            _dbg_nchild++;
        }

        rb_uleb(&abv,1); rb_uleb(&abv,0x11); rb_u8(&abv,_dbg_nchild?1:0);
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
        const char *producer = "axx general assembler (DWARF4)";

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
            WSR sr = weo_shndx(st,csecs,ncs,larr[i].val*(uint64_t)bpw,larr[i].section,bpw);
            if(sr.shndx==0xfff1) continue;
            rb_uleb(&die,2);
            rb_cstr(&die,larr[i].name);
            drv_add(&info_relas,die.len,(int)sr.shndx,abs64,(int64_t)sr.sv);
            rb_waddr(&die,is_rela_dbg?0:sr.sv,addr_sz,_is_le);
        }
        if(_dbg_nchild) rb_uleb(&die,0);
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
    dbg_done: ;
    }
    uint32_t dbg_prog_noff[3]={0,0,0};
    uint32_t dbg_rela_noff[2]={0,0};
    for(int i=0;i<n_dbg_prog;i++) dbg_prog_noff[i]=wbb_str(&shstr,dbg_prog[i].name);
    for(int i=0;i<n_dbg_rela;i++) dbg_rela_noff[i]=wbb_str(&shstr,dbg_rela[i].name);
    uint32_t *grp_noff = calloc((size_t)(G ? G : 1), sizeof(uint32_t));
    if(!grp_noff){ perror("calloc"); exit(1); }
    for(int g = 0; g < G; g++) grp_noff[g] = wbb_str(&shstr, st->elf_groups[grp_of[g]].name);
    /* `.eh_frame`（ソースの `.cfi_*` から）。 */
    if(st->cfi_open)
        axx_diagf(1, 0, " error - .cfi_startproc without .cfi_endproc.\n");
    int _has_eh = st->cfi_fdes_len > 0;
    uint32_t eh_noff = 0, ehr_noff = 0;
    if(_has_eh){
        eh_noff = wbb_str(&shstr, ".eh_frame");
        ehr_noff = wbb_str(&shstr, _is_rela_w ? ".rela.eh_frame" : ".rel.eh_frame");
    }
    uint32_t xidx_noff = _need_xidx ? wbb_str(&shstr, ".symtab_shndx") : 0;
    RB eh_data; rb_init(&eh_data);
    EhRelV eh_rel = {NULL, 0, 0};
    uint8_t *eh_rbuf = NULL; size_t eh_rlen = 0;
    if(_has_eh){
        build_eh_frame(st, _mtbl_w, _is_elf64, _is_rela_w, _is_le, bpw, csecs, ncs,
                       cfi_pts, n_cfi_pts, snimap, snimap_len, &eh_data, &eh_rel);
        eh_rlen = (size_t)eh_rel.n * (size_t)_reloc_entsz;
        eh_rbuf = calloc(1, eh_rlen ? eh_rlen : 1);
        if(!eh_rbuf){ perror("calloc"); exit(1); }
        for(int k = 0; k < eh_rel.n; k++){
            uint8_t *rp = eh_rbuf + (size_t)k * (size_t)_reloc_entsz;
            if(_is_elf64){
                weo_w8(rp, (uint64_t)eh_rel.d[k].off, _is_le);
                weo_w8(rp + 8, weo_rinfo(eh_rel.d[k].sym, eh_rel.d[k].rt, 1), _is_le);
                if(_is_rela_w) weo_w8s(rp + 16, eh_rel.d[k].addend, _is_le);
            } else {
                weo_w4(rp, (uint32_t)eh_rel.d[k].off, _is_le);
                weo_w4(rp + 4, (uint32_t)weo_rinfo(eh_rel.d[k].sym, eh_rel.d[k].rt, 0), _is_le);
                if(_is_rela_w) weo_w4(rp + 8, (uint32_t)eh_rel.d[k].addend, _is_le);
            }
        }
    }

    uint64_t foff=_is_elf64?64:52;
    uint64_t *sec_fo=calloc((size_t)ncs,sizeof(uint64_t));
    for(int i=0;i<ncs;i++){
        /* ファイル内の位置も sh_addralign に合わせる（16 を下限）。 */
        { uint64_t _al_f = csecs[i].al_set ? csecs[i].al
                                           : weo_default_align(csecs[i].sht,_is_elf64);
          if(_al_f < 16) _al_f = 16;
          foff=WEO_ALIGN(foff,_al_f); }
        sec_fo[i]=foff;
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

    int ndbg=n_dbg_prog+n_dbg_rela;
    int tot_sh=1+ncs+nrela+3+ndbg+G;
    int shstrndx=ncs+nrela+3+G;
    int dbg_base=ncs+nrela+3+G;
    int sym_shidx=ncs+nrela+1+G;
    int str_shidx=ncs+nrela+2+G;

    /* グループの中身: フラグの語、メンバーのセクション番号、メンバーの
       リロケーションセクションの番号。sh_info は署名のシンボル番号。 */
    uint8_t **grp_data = calloc((size_t)(G ? G : 1), sizeof(uint8_t*));
    size_t   *grp_len  = calloc((size_t)(G ? G : 1), sizeof(size_t));
    uint32_t *grp_info = calloc((size_t)(G ? G : 1), sizeof(uint32_t));
    uint64_t *grp_fo   = calloc((size_t)(G ? G : 1), sizeof(uint64_t));
    if(!grp_data || !grp_len || !grp_info || !grp_fo){ perror("calloc"); exit(1); }
    for(int g = 0; g < G; g++){
        int nw = 1 + grp_nnum[g];
        for(int k = 0; k < grp_nnum[g]; k++)
            for(int ri2 = 0; ri2 < nrela; ri2++) if(rs_idx[ri2] == grp_nums[g][k] - 1){ nw++; break; }
        uint8_t *gb = calloc((size_t)nw, 4);
        if(!gb){ perror("calloc"); exit(1); }
        int w = 0;
        weo_w4(gb + 4*w++, st->elf_groups[grp_of[g]].flags, _is_le);
        for(int k = 0; k < grp_nnum[g]; k++) weo_w4(gb + 4*w++, (uint32_t)(grp_nums[g][k] + G), _is_le);
        for(int k = 0; k < grp_nnum[g]; k++)
            for(int ri2 = 0; ri2 < nrela; ri2++)
                if(rs_idx[ri2] == grp_nums[g][k] - 1){
                    weo_w4(gb + 4*w++, (uint32_t)(ncs + 1 + ri2 + G), _is_le);
                    break;
                }
        grp_data[g] = gb; grp_len[g] = (size_t)nw * 4;
        const char *sig = st->elf_groups[grp_of[g]].sig;
        int si = weo_symof(snimap, snimap_len, sig);
        if(si == 0)
            for(int i = 0; i < ncs; i++) if(strcmp(csecs[i].name, sig) == 0){ si = i + 1; break; }
        if(si == 0)
            axx_diagf(0, 0, " warning - .elfgroup: signature symbol '%s' of group '%s' is not "
                       "in the symbol table.\n", sig, st->elf_groups[grp_of[g]].name);
        grp_info[g] = (uint32_t)si;
    }
    for(int g = 0; g < G; g++){ foff = WEO_ALIGN(foff, 4); grp_fo[g] = foff; foff += grp_len[g]; }
    uint64_t xidx_fo = 0;
    uint64_t eh_fo = 0, ehr_fo = 0; int eh_shidx = 0;
    uint64_t eh_fl; uint32_t eh_ty; int eh_as; uint32_t eh_al, eh_es;
    elf_section_attrs(st, ".eh_frame", &eh_fl, &eh_ty, &eh_as, &eh_al, &eh_es);
    if(!eh_as) eh_al = st->elf_cfi_set && st->elf_cfi_pad ? (uint32_t)st->elf_cfi_pad : (_is_elf64 ? 8u : 4u);
    if(_has_eh){
        foff = WEO_ALIGN(foff, eh_al ? eh_al : 1); eh_fo = foff; foff += eh_data.len;
        foff = WEO_ALIGN(foff, 8); ehr_fo = foff; foff += eh_rlen;
        eh_shidx = tot_sh; tot_sh += 2;
    }
    if(_need_xidx){ foff = WEO_ALIGN(foff, 4); xidx_fo = foff; foff += (uint64_t)n_xidx * 4; tot_sh++; }
    uint64_t shdr_fo=WEO_ALIGN(foff,8);

    /* SHN_LORESERVE 以上の数は 0 番目のセクションヘッダに置く（ELF の決まり）。 */
    uint16_t _e_shnum    = tot_sh >= 0xff00 ? 0 : (uint16_t)tot_sh;
    uint16_t _e_shstrndx = shstrndx >= 0xff00 ? 0xffff : (uint16_t)shstrndx;

    FILE *fp=fopen(path,"wb");
    if(!fp){
        char _eb[1200]; axx_oserr_str(path, errno, _eb, sizeof(_eb));
        axx_diagf(1, 0, " error - cannot write '%s': %s\n", path, _eb);
        goto weo_done;
    }

    uint16_t _e_type   = st->elf_hdr_set[EHF_TYPE]   ? (uint16_t)st->elf_hdr_val[EHF_TYPE] : 1;
    uint32_t _e_flags  = st->elf_hdr_set[EHF_FLAGS]  ? (uint32_t)st->elf_hdr_val[EHF_FLAGS] : 0;
    uint32_t _e_vers   = st->elf_hdr_set[EHF_VERSION]? (uint32_t)st->elf_hdr_val[EHF_VERSION] : 1;
    uint64_t _e_entry  = st->elf_hdr_set[EHF_ENTRY]  ? st->elf_hdr_val[EHF_ENTRY] : 0;
    uint8_t  _ei_osabi = st->elf_hdr_set[EHF_OSABI]  ? (uint8_t)st->elf_hdr_val[EHF_OSABI]
                                                     : (uint8_t)st->osabi;
    uint8_t  _ei_abiv  = st->elf_hdr_set[EHF_ABIVERSION] ? (uint8_t)st->elf_hdr_val[EHF_ABIVERSION] : 0;

    if(_is_elf64){
        uint8_t eh[64]={0};
        eh[0]=0x7f;eh[1]='E';eh[2]='L';eh[3]='F';
        eh[4]=2;eh[5]=(uint8_t)_ei_data;eh[6]=1;eh[7]=_ei_osabi;eh[8]=_ei_abiv;
        WEO_LE2(eh+16,_e_type); WEO_LE2(eh+18,(uint16_t)machine); WEO_LE4(eh+20,_e_vers);
        WEO_LE8(eh+24,_e_entry);
        WEO_LE8(eh+40,shdr_fo);
        WEO_LE4(eh+48,_e_flags);
        WEO_LE2(eh+52,64); WEO_LE2(eh+58,64);
        WEO_LE2(eh+60,_e_shnum); WEO_LE2(eh+62,_e_shstrndx);
        fwrite(eh,1,64,fp);
    } else {
        uint8_t eh[52]={0};
        eh[0]=0x7f;eh[1]='E';eh[2]='L';eh[3]='F';
        eh[4]=1;eh[5]=(uint8_t)_ei_data;eh[6]=1;eh[7]=_ei_osabi;eh[8]=_ei_abiv;
        WEO_LE2(eh+16,_e_type); WEO_LE2(eh+18,(uint16_t)machine); WEO_LE4(eh+20,_e_vers);
        WEO_LE4(eh+24,(uint32_t)_e_entry);
        WEO_LE4(eh+32,(uint32_t)shdr_fo);
        WEO_LE4(eh+36,_e_flags);
        WEO_LE2(eh+40,52); WEO_LE2(eh+46,40);
        WEO_LE2(eh+48,_e_shnum); WEO_LE2(eh+50,_e_shstrndx);
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
    for(int g=0;g<G;g++){ weo_pad(fp,grp_fo[g]); fwrite(grp_data[g],1,grp_len[g],fp); }
    if(_has_eh){
        weo_pad(fp,eh_fo); if(eh_data.len) fwrite(eh_data.b,1,eh_data.len,fp);
        weo_pad(fp,ehr_fo); if(eh_rlen) fwrite(eh_rbuf,1,eh_rlen,fp);
    }
    if(_need_xidx){
        weo_pad(fp,xidx_fo);
        for(int k=0;k<n_xidx;k++){ uint8_t b4[4]; weo_w4(b4,sym_xidx[k],_is_le); fwrite(b4,1,4,fp); }
    }
    weo_pad(fp,shdr_fo);

    weo_shdr(fp,_is_le,_is_elf64,0,0,0,0,0,
             tot_sh >= 0xff00 ? (uint64_t)tot_sh : 0,
             shstrndx >= 0xff00 ? (uint32_t)shstrndx : 0,0,0,0);
    for(int g=0;g<G;g++)
        weo_shdr(fp,_is_le,_is_elf64,grp_noff[g],17,0,0,grp_fo[g],grp_len[g],
                 (uint32_t)sym_shidx,grp_info[g],4,4);
    for(int i=0;i<ncs;i++){
        const char *_lk = "", *_inf = "";
        for(int k=0;k<st->elf_links_len;k++)
            if(strcasecmp(st->elf_links[k].sec, csecs[i].name)==0){
                _lk = st->elf_links[k].link; _inf = st->elf_links[k].info; break;
            }
        uint32_t _lkv = weo_shidx_of(st,_lk,csecs[i].name,"sh_link",csecs,ncs,rs_idx,nrela,G,
                                     _is_rela_w,sym_shidx,str_shidx,shstrndx,dbg_prog,n_dbg_prog,dbg_base);
        uint32_t _infv = weo_shidx_of(st,_inf,csecs[i].name,"sh_info",csecs,ncs,rs_idx,nrela,G,
                                      _is_rela_w,sym_shidx,str_shidx,shstrndx,dbg_prog,n_dbg_prog,dbg_base);
        weo_shdr(fp,_is_le,_is_elf64,sec_noff[i],csecs[i].sht,csecs[i].fl,0,sec_fo[i],csecs[i].bsz,
                 _lkv,_infv,
                 csecs[i].al_set ? csecs[i].al
                                 : weo_default_align(csecs[i].sht,_is_elf64),
                 (uint64_t)csecs[i].es);
    }
    {
    uint32_t _word_align = _is_elf64?8:4;
    uint32_t _rel_sh_type = _is_rela_w?4:9;
    for(int ri2=0;ri2<nrela;ri2++)
        weo_shdr(fp,_is_le,_is_elf64,rela_noff[ri2],_rel_sh_type,
                 0x40 | (grp_member[rs_idx[ri2]] ? 0x200 : 0),0,rela_fo[ri2],rela_szs[ri2],
                 (uint32_t)sym_shidx,(uint32_t)(rs_idx[ri2]+1+G),_word_align,(uint64_t)_reloc_entsz);
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
    if(_has_eh){
        weo_shdr(fp,_is_le,_is_elf64,eh_noff,eh_ty,eh_fl,0,eh_fo,eh_data.len,0,0,eh_al,(uint64_t)eh_es);
        weo_shdr(fp,_is_le,_is_elf64,ehr_noff,_is_rela_w?4:9,0x40,0,ehr_fo,eh_rlen,
                 (uint32_t)sym_shidx,(uint32_t)eh_shidx,_is_elf64?8:4,(uint64_t)_reloc_entsz);
    }
    if(_need_xidx)
        weo_shdr(fp,_is_le,_is_elf64,xidx_noff,18,0,0,xidx_fo,(uint64_t)n_xidx*4,
                 (uint32_t)sym_shidx,0,4,4);
    if(axx_close_out(fp, path)) goto weo_done;
    {
    char _dbg_msg[64];
    if(n_dbg_prog) snprintf(_dbg_msg,sizeof(_dbg_msg),", %d debug section(s)",n_dbg_prog);
    else           _dbg_msg[0]='\0';
    fprintf(stderr,"elf: wrote %s (%d section(s), %d %s section(s), %d symbol(s)%s)\n",
            path,ncs,nrela,_is_rela_w?"rela":"rel",nsyms,_dbg_msg);
    }

weo_done:
    free(sym_xidx);
    for(int k = 0; k < n_cfi_pts; k++) free(cfi_pts[k].name);
    free(cfi_pts);
    free(eh_data.b); free(eh_rel.d); free(eh_rbuf);
    #undef WEO_PSYM
    for(int g=0;g<G;g++){ free(grp_nums[g]); free(grp_data[g]); }
    free(grp_of); free(grp_nums); free(grp_nnum); free(grp_member);
    free(grp_noff); free(grp_data); free(grp_len); free(grp_info); free(grp_fo);
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
typedef struct { const char *s; int i; MacroPP *mp; const char *file; int line; } MEP;

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
    int        expr_depth;
    int        noeval;
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


/* ---- マクロ層 -----------------------------------------------------------
   アセンブラ本体の前に走る行指向のソース間変換。文はすべて行頭の `!` で始まり、
   補間は波括弧付きの `!{...}`。書式指定は Python のフォーマットミニ言語で、
   axx.py 側と同じ指定を受け、同じものを拒否し、文面もそろえてある。
   ソース側のマクロはラベル値と `$` / `$$` を読めるが、見えるのは前回の
   リラクゼーション反復の値。パターン側のマクロはソースのアセンブル前に
   走るので、ラベルもロケーションカウンタも存在しない。
   数は int64 で扱う。axx.py は多倍長なので、マクロ時の計算が 64bit を超える
   場合だけ結果が食い違いうる（マクロ層はテキストを出すので、本体の 256bit
   式評価には影響しない）。
   展開中の確保はアリーナにまとめ、1 パスの終わりに一度で捨てる。
   ------------------------------------------------------------------------ */
/* アリーナから確保する。個別に解放しない。 */
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
/* アリーナを巻き戻してまとめて捨てる。 */
static void marena_reset(MArena *a){
    MArenaBlk *b = a->head;
    while(b){ MArenaBlk *n = b->next; free(b->data); free(b); b = n; }
    a->head = NULL; a->total = 0;
}
/* アリーナ上に長さ付きで複製する。 */
static char *marena_strndup(MArena *a, const char *s, size_t n){
    char *p = marena_alloc(a, n + 1);
    memcpy(p, s, n); p[n] = '\0';
    return p;
}
/* アリーナ上に複製する。 */
static char *marena_strdup(MArena *a, const char *s){
    return marena_strndup(a, s, strlen(s));
}


/* ブロックに文を 1 つ積む。 */
static void mblock_push(MacroPP *mp, MBlock *b, MNode *n){
    if(b->len >= b->cap){
        int nc = b->cap ? b->cap * 2 : 8;
        MNode **nd = marena_alloc(&mp->arena, (size_t)nc * sizeof(MNode*));
        if(b->len) memcpy(nd, b->d, (size_t)b->len * sizeof(MNode*));
        b->d = nd; b->cap = nc;
    }
    b->d[b->len++] = n;
}
/* 展開結果の行を 1 つ積む（位置も覚える）。 */
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


/* マクロ層を初期化する。 */
static void macro_init(MacroPP *mp, Assembler *asmb){
    memset(mp, 0, sizeof(*mp));
    mp->asmb = asmb;
    mp->enabled = 1;
}
/* 1 パスぶんの状態を初期化する。 */
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
    mp->expr_depth = 0;
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
/* マクロ層を解放する。 */
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


/* 同じ文言を一度だけ報告するための判定。 */
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

/* `!warning` の出力。 */
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

/* マクロ展開を失敗として記録する。 */
static void m_fail(MacroPP *mp, const char *file, int line, const char *fmt, ...){
    char bodybuf[1024];
    char *body = bodybuf;
    va_list ap; va_start(ap, fmt);
    int bneed = vsnprintf(bodybuf, sizeof(bodybuf), fmt, ap);
    va_end(ap);
    if(bneed >= (int)sizeof(bodybuf)){
        char *bh = malloc((size_t)bneed + 1);
        if(bh){
            va_start(ap, fmt);
            vsnprintf(bh, (size_t)bneed + 1, fmt, ap);
            va_end(ap);
            body = bh;
        }
    }
    size_t msz = strlen(body) + (file ? strlen(file) : 1) + 32;
    char *msg = malloc(msz);
    if(!msg){ perror("malloc"); exit(1); }
    if(line < 0) snprintf(msg, msz, "%s: %s", file ? file : "?", body);
    else snprintf(msg, msz, "%s:%d: %s", file ? file : "?", line, body);
    if(body != bodybuf) free(body);
    if(m_first_report(mp, msg))
        axx_diagf(0, 1, " error - %s\n", msg);
    free(msg);
    mp->had_error = 1;
    if(mp->asmb) mp->asmb->st.had_error = 1;
    if(mp->pending_buf){ free(mp->pending_buf); mp->pending_buf = NULL; }
    if(mp->jb_active) longjmp(mp->jb, 1);
    exit(1);
}


/* 文字列を Python の repr() と同じ綴りにする。診断の文面を axx.py と
   一字一句そろえるために必要。 */
static void m_pyrepr_n(const char *s, size_t n, char *out, size_t outsz){
    if(outsz < 3){ if(outsz) out[0] = '\0'; return; }
    int has_sq = 0, has_dq = 0;
    for(size_t k = 0; k < n; k++){
        if(s[k] == '\'') has_sq = 1;
        else if(s[k] == '"') has_dq = 1;
    }
    char q = (has_sq && !has_dq) ? '"' : '\'';
    size_t o = 0;
    out[o++] = q;
    for(size_t k = 0; k < n; k++){
        unsigned char c = (unsigned char)s[k];
        if(o + 6 >= outsz) break;
        if(c == '\\' || c == (unsigned char)q){ out[o++] = '\\'; out[o++] = (char)c; }
        else if(c == '\n'){ out[o++] = '\\'; out[o++] = 'n'; }
        else if(c == '\t'){ out[o++] = '\\'; out[o++] = 't'; }
        else if(c == '\r'){ out[o++] = '\\'; out[o++] = 'r'; }
        else if(c < 0x20 || c == 0x7f){
            int nn = snprintf(out + o, outsz - o, "\\x%02x", c);
            o += (nn > 0) ? (size_t)nn : 0;
        } else if(c >= 0x80){
            /* UTF-8 の 1 文字はまとめて写す。読めないバイトは、Python が
               surrogateescape で読んだ文字を '\udcXX' と repr するのに合わせる。 */
            size_t L = utf8_prefix_bytes(s + k, n - k, 1);
            if(L == 1){
                if(o + 8 >= outsz) break;
                int nn = snprintf(out + o, outsz - o, "\\udc%02x", c);
                o += (nn > 0) ? (size_t)nn : 0;
            } else {
                if(o + L + 2 >= outsz) break;
                memcpy(out + o, s + k, L);
                o += L;
                k += L - 1;
            }
        } else out[o++] = (char)c;
    }
    out[o++] = q;
    out[o] = '\0';
}

/* 同じものを NUL 終端の文字列に対して行う。 */
static void m_pyrepr(const char *s, char *out, size_t outsz){
    m_pyrepr_n(s, strlen(s), out, outsz);
}

/* 診断に添える行の末尾を作る。 */
static char *m_trailer(MacroPP *mp, const char *s){
    const char *b = s;
    while(*b == ' ' || *b == '\t') b++;
    size_t n = strlen(b);
    while(n > 0 && isspace((unsigned char)b[n-1])) n--;
    if(n == 0 || b[0] == ';') return NULL;
    char *r = marena_alloc(&mp->arena, n + 1);
    memcpy(r, b, n); r[n] = '\0';
    return r;
}

/* repr() 形式の綴りをアリーナ上に作る。 */
static char *m_pyrepr_a(MacroPP *mp, const char *s){
    if(!s) s = "";
    size_t sz = strlen(s) * 4 + 8;
    char *out = marena_alloc(&mp->arena, sz);
    m_pyrepr(s, out, sz);
    return out;
}


static MVal mv_int(long long v){ MVal r; r.is_str = 0; r.i = v; r.s = NULL; return r; }
static MVal mv_str(char *s){ MVal r; r.is_str = 1; r.i = 0; r.s = s; return r; }
static int  mv_truth(MVal v){ return v.is_str ? (v.s && v.s[0]) : (v.i != 0); }

/* マクロ値をテキストにする。 */
static char *mv_to_text(MacroPP *mp, MVal v){
    if(v.is_str) return v.s ? v.s : (char*)"";
    char buf[32];
    snprintf(buf, sizeof(buf), "%lld", v.i);
    return marena_strdup(&mp->arena, buf);
}

/* その位置の `'` が符号拡張演算子か（文字定数の引用符ではないか）。 */
static int m_sext_tick_at(const char *s, int i){
    int j = i + 1;
    while(s[j] == ' ' || s[j] == '\t') j++;
    return (s[j] >= '0' && s[j] <= '9') || s[j] == '(';
}

/* `!echo` の出力を標準エラーへ書く。ミニ言語の `.echo` と体裁を共有する。 */
static void m_echo_write(char *const *items, int n){
    for(int i = 0; i < n; i++){
        if(i) fputc(' ', stderr);
        fputs(items[i] ? items[i] : "", stderr);
    }
    fputc('\n', stderr);
}
/* 整数を要求する。 */
static long long mv_need_int(MacroPP *mp, MVal v, const char *file, int line){
    if(v.is_str){
        if(mp->noeval) return 0;
        char *vr = m_pyrepr_a(mp, v.s ? v.s : "");
        char *er = mp->cur_expr ? m_pyrepr_a(mp, mp->cur_expr) : (char*)"?";
        m_fail(mp, file, line, "macro expression: expected an integer, got the string %s in %s", vr, er);
    }
    return v.i;
}
/* 符号反転（検査なし）。 */
static inline long long m_i64_neg(long long a){
    return (long long)(0ULL - (unsigned long long)a);
}
/* 絶対値（検査なし）。 */
static inline long long m_i64_abs(long long a){
    return a < 0 ? m_i64_neg(a) : a;
}
/* 符号反転。溢れたらエラーにする。 */
static inline long long m_i64_neg_ck(MEP *p, long long a){
    if(a == LLONG_MIN){
        if(p->mp->noeval) return 0;
        char *sr = m_pyrepr_a(p->mp, p->s);
        m_fail(p->mp, p->file, p->line, "macro expression: integer overflow (64-bit) in %s", sr);
    }
    return -a;
}
/* 絶対値。溢れたらエラーにする。 */
static inline long long m_i64_abs_ck(MEP *p, long long a){
    return a < 0 ? m_i64_neg_ck(p, a) : a;
}
/* 加算。溢れたらエラーにする。 */
static inline long long m_i64_add(MEP *p, long long a, long long b){
    long long r;
    if(__builtin_add_overflow(a, b, &r)){
        if(p->mp->noeval) return 0;
        char *sr = m_pyrepr_a(p->mp, p->s);
        m_fail(p->mp, p->file, p->line, "macro expression: integer overflow (64-bit) in %s", sr);
    }
    return r;
}
/* 減算。溢れたらエラーにする。 */
static inline long long m_i64_sub(MEP *p, long long a, long long b){
    long long r;
    if(__builtin_sub_overflow(a, b, &r)){
        if(p->mp->noeval) return 0;
        char *sr = m_pyrepr_a(p->mp, p->s);
        m_fail(p->mp, p->file, p->line, "macro expression: integer overflow (64-bit) in %s", sr);
    }
    return r;
}
/* 乗算。溢れたらエラーにする。 */
static inline long long m_i64_mul(MEP *p, long long a, long long b){
    long long r;
    if(__builtin_mul_overflow(a, b, &r)){
        if(p->mp->noeval) return 0;
        char *sr = m_pyrepr_a(p->mp, p->s);
        m_fail(p->mp, p->file, p->line, "macro expression: integer overflow (64-bit) in %s", sr);
    }
    return r;
}
/* 左シフト。 */
static inline long long m_i64_shl(long long a, int n){
    return (long long)((unsigned long long)a << n);
}
/* 加算（検査なし）。 */
static inline long long m_i64_add_raw(long long a, long long b){
    return (long long)((unsigned long long)a + (unsigned long long)b);
}
/* 乗算（検査なし）。 */
static inline long long m_i64_mul_raw(long long a, long long b){
    return (long long)((unsigned long long)a * (unsigned long long)b);
}

/* C と同じゼロ方向の切り捨て除算。 */
static long long m_cdiv(MEP *p, long long a, long long b){
    if(b == 0) return 0;
    if(a == LLONG_MIN && b == -1){
        if(p->mp->noeval) return 0;
        char *sr = m_pyrepr_a(p->mp, p->s);
        m_fail(p->mp, p->file, p->line, "macro expression: integer overflow (64-bit) in %s", sr);
    }
    unsigned long long ua = (a < 0) ? (0ULL - (unsigned long long)a) : (unsigned long long)a;
    unsigned long long ub = (b < 0) ? (0ULL - (unsigned long long)b) : (unsigned long long)b;
    unsigned long long q = ua / ub;
    return ((a >= 0) == (b >= 0)) ? (long long)q : (long long)(0ULL - q);
}
static long long m_cmod(MEP *p, long long a, long long b){ return m_i64_sub(p, a, m_i64_mul(p, m_cdiv(p, a, b), b)); }


static MScope *m_scope(MacroPP *mp){ return mp->scopes[mp->nscopes - 1]; }

/* スコープの中で名前を引く。 */
static MVal *m_scope_find(MScope *sc, const char *name){
    for(int i = 0; i < sc->len; i++)
        if(strcmp(sc->names[i], name) == 0) return &sc->vals[i];
    return NULL;
}
/* スコープに名前と値を置く。 */
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
/* スコープから名前を消す。 */
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

/* マクロ定義を名前で引く。 */
static MFunc *m_func_find(MacroPP *mp, const char *name){
    for(int i = 0; i < mp->nfuncs; i++)
        if(strcmp(mp->funcs[i].name, name) == 0) return &mp->funcs[i];
    return NULL;
}
/* マクロ定義を 1 つ作る。 */
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
/* その名前が宣言済みか。 */
static int m_declared(MacroPP *mp, const char *name){
    for(int i = 0; i < mp->ndecl; i++)
        if(strcmp(mp->declared[i], name) == 0) return 1;
    return 0;
}
/* その名前を宣言済みにする。 */
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

typedef enum { MLBL_NO = 0, MLBL_UNKNOWN, MLBL_VALUE } MLabelStatus;

/* ラベルの値を引く。「値がある」「名前は知っているが値はまだ無い」「無い」を
   区別する。パターン側のマクロでは常に「無い」で、読めるラベルが存在しない。 */
static MLabelStatus m_asm_label(MacroPP *mp, const char *name, long long *out){
    if(out) *out = 0;
    if(mp->pat_mode || !mp->asmb) return MLBL_NO;
    AsmState *st = &mp->asmb->st;
    if(!st->macro_labels_valid){
        return MLBL_UNKNOWN;
    }
    LabelEntry *e = lmap_find(&st->macro_labels, name);
    if(!e) return MLBL_NO;
    if(u256_is_undef_derived(e->value)) return MLBL_UNKNOWN;
    if(out) *out = (long long)u256_to_u64(e->value);
    return MLBL_VALUE;
}

/* `$` / `$$` の値。前回の反復で記録した行ごとの PC から引く。パターン側の
   マクロではエラーにする。 */
static long long m_loc_counter(MacroPP *mp, const char *file, int line){
    if(mp->pat_mode || !mp->asmb){
        m_fail(mp, file, line,
               "'$'/'$$' is not available in pattern-file macros "
               "(there is no location counter before the source is assembled)");
        return 0;
    }
    AsmState *st = &mp->asmb->st;
    int idx = mp->out ? mp->out->len : 0;
    return mlp_get(&st->macro_line_pcs, st->current_file, idx);
}

/* その名前が定義済みか。 */
static int m_is_defined(MacroPP *mp, const char *name){
    MFunc *_f = m_func_find(mp, name);
    if(_f && _f->defined) return 1;
    for(int i = mp->nscopes - 1; i >= 0; i--)
        if(m_scope_find(mp->scopes[i], name)) return 1;
    return m_asm_label(mp, name, NULL) == MLBL_VALUE;
}
/* 名前を解決する。内側のスコープから外側へたどる。 */
static MVal m_lookup(MacroPP *mp, const char *name, const char *file, int line){
    if(mp->noeval) return mv_int(0);
    for(int i = mp->nscopes - 1; i >= 0; i--){
        MVal *p = m_scope_find(mp->scopes[i], name);
        if(p) return *p;
    }
    {
        MFunc *_f = m_func_find(mp, name);
        if(_f && _f->defined)
            m_fail(mp, file, line, "macro '%s' used as a variable (call it as '%s(...)')", name, name);
    }
    {
        long long lv = 0;
        if(m_asm_label(mp, name, &lv) != MLBL_NO) return mv_int(lv);
    }
    m_fail(mp, file, line, "undefined macro variable '%s'", name);
    return mv_int(0);
}
/* `!set` の代入。内側から外側へ探し、無ければ現在のスコープに作る。 */
static void m_assign(MacroPP *mp, const char *name, MVal v){
    for(int i = mp->nscopes - 1; i >= 0; i--){
        MVal *p = m_scope_find(mp->scopes[i], name);
        if(p){ *p = v; return; }
    }
    m_scope_set(m_scope(mp), marena_strdup(&mp->arena, name), v);
}


static MVal mep_ternary(MEP *p);
static MVal m_call_value(MacroPP *mp, const char *name, MVal *args, int nargs,
                         const char *file, int line);

static void mep_skip(MEP *p){ while(p->s[p->i] == ' ' || p->s[p->i] == '\t') p->i++; }

/* マクロ式の再帰下降。値は整数と文字列の 2 種類で、演算子は C に倣う。
   本体の式評価器とは別物なので、`%` の符号と `'` の結合位置が違う。 */
/* 次がそのトークンなら消費して真。 */
static int mep_eat(MEP *p, const char *tok){
    mep_skip(p);
    size_t n = strlen(tok);
    if(strncmp(p->s + p->i, tok, n) != 0) return 0;
    p->i += (int)n;
    return 1;
}
/* そのトークンを必ず消費する。 */
static void mep_expect(MEP *p, const char *tok){
    if(!mep_eat(p, tok)){
        char tokr[16];
        m_pyrepr(tok, tokr, sizeof(tokr));
        char *sr = m_pyrepr_a(p->mp, p->s);
        m_fail(p->mp, p->file, p->line, "macro expression: expected %s in %s", tokr, sr);
    }
}
static char mep_peek(MEP *p){ mep_skip(p); return p->s[p->i]; }

/* 識別子を 1 個読む。 */
static char *mep_ident(MEP *p){
    mep_skip(p);
    int j = p->i;
    while(p->s[j] && (isalnum((unsigned char)p->s[j]) || p->s[j] == '_')) j++;
    if(j == p->i){
        char *sr = m_pyrepr_a(p->mp, p->s);
        m_fail(p->mp, p->file, p->line, "macro expression: expected a name in %s", sr);
    }
    char *r = marena_strndup(&p->mp->arena, p->s + p->i, (size_t)(j - p->i));
    p->i = j;
    return r;
}

/* 整数リテラルを読む。10 進・0x・0b・0o、アンダースコア可。 */
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
        v = m_i64_add_raw(m_i64_mul_raw(v, base), d);
        ndig++; j++;
    }
    if(ndig == 0 || j == start){
        char *sr = m_pyrepr_a(p->mp, p->s);
        m_fail(p->mp, p->file, p->line, "macro expression: malformed number in %s", sr);
    }
    p->i = j;
    return mv_int(v);
}

/* 文字列リテラルを読む。`'A'` は 1 文字なら文字コードになる。 */
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
        char *sr = m_pyrepr_a(p->mp, p->s);
        m_fail(p->mp, p->file, p->line, "macro expression: unterminated string literal in %s", sr);
    }
    return NULL;
}

/* 項そのもの。数値、文字列、名前、括弧、組み込み関数。 */
static MVal mep_primary(MEP *p){
    mep_skip(p);
    char c = p->s[p->i];
    if(!c){
        char *sr = m_pyrepr_a(p->mp, p->s);
        m_fail(p->mp, p->file, p->line, "macro expression: unexpected end of expression in %s", sr);
    }

    if(c == '('){
        if(p->mp->expr_depth >= EXPR_MAX_DEPTH){
            char *sr = m_pyrepr_a(p->mp, p->s);
            m_fail(p->mp, p->file, p->line, "macro expression: nesting too deep in %s", sr);
        }
        p->mp->expr_depth++;
        p->i++;
        MVal v = mep_ternary(p);
        mep_expect(p, ")");
        p->mp->expr_depth--;
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
    if(c == '$'){
        p->i++;
        if(p->s[p->i] == '$') p->i++;
        return mv_int(m_loc_counter(p->mp, p->file, p->line));
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
        char cbuf[2] = { c, 0 }, cr[16]; char *sr = m_pyrepr_a(p->mp, p->s);
        m_pyrepr(cbuf, cr, sizeof(cr));
        m_fail(p->mp, p->file, p->line, "macro expression: unexpected character %s in %s", cr, sr);
    }
    return mv_int(0);
}

/* 単項 `-` `+` `~` `!`。 */
static MVal mep_unary(MEP *p){
    mep_skip(p);
    if(p->s[p->i] == '!' && p->s[p->i+1] != '='){ p->i++; return mv_int(mv_truth(mep_unary(p)) ? 0 : 1); }
    if(p->s[p->i] == '~'){ p->i++; return mv_int(~mv_need_int(p->mp, mep_unary(p), p->file, p->line)); }
    if(p->s[p->i] == '-'){ p->i++; return mv_int(m_i64_neg_ck(p, mv_need_int(p->mp, mep_unary(p), p->file, p->line))); }
    if(p->s[p->i] == '+'){ p->i++; return mep_unary(p); }
    if(p->s[p->i] == '@'){
        p->i++;
        long long xv = mv_need_int(p->mp, mep_unary(p), p->file, p->line);
        return mv_int(op_msb(u256_from_i64(xv)));
    }
    if(p->s[p->i] == '*' && p->s[p->i+1] == '('){
        p->i += 2;
        MVal xa = mep_ternary(p);
        mep_expect(p, ",");
        MVal na = mep_ternary(p);
        mep_expect(p, ")");
        long long xv = mv_need_int(p->mp, xa, p->file, p->line);
        long long nv = mv_need_int(p->mp, na, p->file, p->line);
        int neg = 0;
        uint256_t r = op_byte(u256_from_i64(xv), u256_from_i64(nv), &neg);
        if(neg && !p->mp->noeval)
            m_fail(p->mp, p->file, p->line,
                   "negative byte-extract offset in *(expr, expr)");
        return mv_int(u256_to_i64(r));
    }
    return mep_primary(p);
}

static long long m_safe_repeat_len(MacroPP *mp, const char *file, int line,
                                    const char *srcline, long long n, size_t l){
    if(n < 0) n = 0;
    const long long MAXLEN = 16*1024*1024;
    if(n == 0 || l == 0) return 0;
    if((unsigned long long)n > (unsigned long long)(MAXLEN) / l){
        if(mp->noeval) return 0;
        char *sr = m_pyrepr_a(mp, srcline);
        m_fail(mp, file, line, "macro expression: string repetition too large in %s", sr);
    }
    return n * (long long)l;
}

/* `*` `/` `%`。文字列 `*` 整数は繰り返し。 */
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
                long long total = m_safe_repeat_len(p->mp, p->file, p->line, p->s, n, l);
                char *b = marena_alloc(&p->mp->arena, (size_t)total + 1);
                b[0] = '\0';
                for(long long k = 0; k < n; k++) memcpy(b + (size_t)k*l, v.s, l);
                b[(size_t)total] = '\0';
                v = mv_str(b);
            } else if(!v.is_str && r.is_str){
                MVal t = v; v = r; r = t;
                long long n = r.i < 0 ? 0 : r.i;
                size_t l = strlen(v.s);
                long long total = m_safe_repeat_len(p->mp, p->file, p->line, p->s, n, l);
                char *b = marena_alloc(&p->mp->arena, (size_t)total + 1);
                for(long long k = 0; k < n; k++) memcpy(b + (size_t)k*l, v.s, l);
                b[(size_t)total] = '\0';
                v = mv_str(b);
            } else {
                long long _lv = mv_need_int(p->mp, v, p->file, p->line);
                long long _rv = mv_need_int(p->mp, r, p->file, p->line);
                v = mv_int(m_i64_mul(p, _lv, _rv));
            }
        } else if(c == '/'){
            p->i++;
            long long r = mv_need_int(p->mp, mep_unary(p), p->file, p->line);
            if(r == 0 && !p->mp->noeval){
                char *sr = m_pyrepr_a(p->mp, p->s);
                m_fail(p->mp, p->file, p->line, "macro expression: division by zero in %s", sr);
            }
            v = mv_int(m_cdiv(p, mv_need_int(p->mp, v, p->file, p->line), r));
        } else if(c == '%'){
            p->i++;
            long long r = mv_need_int(p->mp, mep_unary(p), p->file, p->line);
            if(r == 0 && !p->mp->noeval){
                char *sr = m_pyrepr_a(p->mp, p->s);
                m_fail(p->mp, p->file, p->line, "macro expression: modulo by zero in %s", sr);
            }
            v = mv_int(m_cmod(p, mv_need_int(p->mp, v, p->file, p->line), r));
        } else return v;
    }
}

/* `+` `-`。どちらかが文字列なら `+` は連結。 */
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
            } else v = mv_int(m_i64_add(p, v.i, r.i));
        } else if(c == '-'){
            p->i++;
            { long long _lv = mv_need_int(p->mp, v, p->file, p->line);
              long long _rv = mv_need_int(p->mp, mep_mul(p), p->file, p->line);
              v = mv_int(m_i64_sub(p, _lv, _rv)); }
        } else return v;
    }
}

/* `<<` `>>`。 */
static MVal mep_shift(MEP *p){
    MVal v = mep_add(p);
    for(;;){
        mep_skip(p);
        if(p->s[p->i] == '<' && p->s[p->i+1] == '<'){
            p->i += 2;
            long long n = mv_need_int(p->mp, mep_add(p), p->file, p->line);
            if((n < 0 || n > 4096) && !p->mp->noeval){
                char *sr = m_pyrepr_a(p->mp, p->s);
                m_fail(p->mp, p->file, p->line, "macro expression: shift count out of range in %s", sr);
            }
            if(n < 0 || n > 4096) n = 0;
            long long base = mv_need_int(p->mp, v, p->file, p->line);
            if(n > 63){
                if(base != 0 && !p->mp->noeval){
                    char *sr = m_pyrepr_a(p->mp, p->s);
                    m_fail(p->mp, p->file, p->line, "macro expression: integer overflow (64-bit) in %s", sr);
                }
                v = mv_int(0);
                continue;
            }
            long long shifted = m_i64_shl(base, (int)n);
            if(n > 0 && (shifted >> n) != base && !p->mp->noeval){
                char *sr = m_pyrepr_a(p->mp, p->s);
                m_fail(p->mp, p->file, p->line, "macro expression: integer overflow (64-bit) in %s", sr);
            }
            v = mv_int(shifted);
        } else if(p->s[p->i] == '>' && p->s[p->i+1] == '>'){
            p->i += 2;
            long long n = mv_need_int(p->mp, mep_add(p), p->file, p->line);
            if((n < 0 || n > 4096) && !p->mp->noeval){
                char *sr = m_pyrepr_a(p->mp, p->s);
                m_fail(p->mp, p->file, p->line, "macro expression: shift count out of range in %s", sr);
            }
            if(n < 0 || n > 4096) n = 0;
            long long rbase = mv_need_int(p->mp, v, p->file, p->line);
            v = mv_int(n > 63 ? (rbase < 0 ? -1 : 0) : (rbase >> n));
        } else return v;
    }
}

/* 大小比較。整数と文字列が混ざる場合の規則をここに閉じる。 */
static int m_order(MEP *p, MVal a, MVal b, int or_equal){
    if(a.is_str != b.is_str){
        if(p->mp->noeval) return 0;
        char *sr = m_pyrepr_a(p->mp, p->s);
        m_fail(p->mp, p->file, p->line, "macro expression: cannot order a string against an integer in %s", sr);
    }
    if(a.is_str){
        int c = strcmp(a.s ? a.s : "", b.s ? b.s : "");
        return or_equal ? (c <= 0) : (c < 0);
    }
    return or_equal ? (a.i <= b.i) : (a.i < b.i);
}

/* `<` `<=` `>` `>=`。 */
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

/* 等値比較。 */
static int m_equal(MVal a, MVal b){
    if(a.is_str != b.is_str) return 0;
    if(a.is_str) return strcmp(a.s ? a.s : "", b.s ? b.s : "") == 0;
    return a.i == b.i;
}

/* `==` `!=`。 */
static MVal mep_eq(MEP *p){
    MVal v = mep_rel(p);
    for(;;){
        if(mep_eat(p, "=="))      v = mv_int(m_equal(v, mep_rel(p)) ? 1 : 0);
        else if(mep_eat(p, "!=")) v = mv_int(m_equal(v, mep_rel(p)) ? 0 : 1);
        else return v;
    }
}

/* `&`。 */
static MVal mep_band(MEP *p){
    MVal v = mep_eq(p);
    for(;;){
        mep_skip(p);
        if(p->s[p->i] == '&' && p->s[p->i+1] != '&'){
            p->i++;
            { long long _lv = mv_need_int(p->mp, v, p->file, p->line);
              long long _rv = mv_need_int(p->mp, mep_eq(p), p->file, p->line);
              v = mv_int(_lv & _rv); }
        } else return v;
    }
}
/* `^`。 */
static MVal mep_bxor(MEP *p){
    MVal v = mep_band(p);
    for(;;){
        mep_skip(p);
        if(p->s[p->i] == '^'){
            p->i++;
            { long long _lv = mv_need_int(p->mp, v, p->file, p->line);
              long long _rv = mv_need_int(p->mp, mep_band(p), p->file, p->line);
              v = mv_int(_lv ^ _rv); }
        } else return v;
    }
}
/* `|`。 */
static MVal mep_bor(MEP *p){
    MVal v = mep_bxor(p);
    for(;;){
        mep_skip(p);
        if(p->s[p->i] == '|' && p->s[p->i+1] != '|'){
            p->i++;
            { long long _lv = mv_need_int(p->mp, v, p->file, p->line);
              long long _rv = mv_need_int(p->mp, mep_bxor(p), p->file, p->line);
              v = mv_int(_lv | _rv); }
        } else return v;
    }
}
/* `'` — 符号拡張。マクロ層ではビット演算より緩く `&&` よりきつい。本体の
   評価器での位置とは違う。マクロ層の優先順位が C に倣っていて、そこでは
   比較がビット演算よりきつく結合するため。 */
static MVal mep_sext(MEP *p){
    MVal v = mep_bor(p);
    for(;;){
        mep_skip(p);
        if(p->s[p->i] != '\'' || !m_sext_tick_at(p->s, p->i)) break;
        p->i++;
        MVal t = mep_bor(p);
        long long xv = mv_need_int(p->mp, v, p->file, p->line);
        long long tv = mv_need_int(p->mp, t, p->file, p->line);
        int warn = 0;
        uint256_t r = op_sext(u256_from_i64(xv), u256_from_i64(tv), &warn);
        if(warn && !p->mp->noeval){
            char cb[96]; u256_to_pydec(u256_from_i64(tv), cb, sizeof(cb));
            m_warn(p->mp, p->file, p->line,
                    "sign-extension bit width %s exceeds maximum %d, result set to 0",
                    cb, SEXT_MAX_BITS);
        }
        v = mv_int(u256_to_i64(r));
    }
    return v;
}

/* `&&`。 */
static MVal mep_land(MEP *p){
    MVal v = mep_sext(p);
    while(mep_eat(p, "&&")){
        int skip = !p->mp->noeval && !mv_truth(v);
        if(skip) p->mp->noeval++;
        MVal r = mep_sext(p);
        if(skip) p->mp->noeval--;
        v = mv_int((!skip && mv_truth(v) && mv_truth(r)) ? 1 : 0);
    }
    return v;
}
/* `||`。 */
static MVal mep_lor(MEP *p){
    MVal v = mep_land(p);
    while(mep_eat(p, "||")){
        int skip = !p->mp->noeval && mv_truth(v);
        if(skip) p->mp->noeval++;
        MVal r = mep_land(p);
        if(skip) p->mp->noeval--;
        v = mv_int((skip || mv_truth(v) || mv_truth(r)) ? 1 : 0);
    }
    return v;
}
/* `?:`。 */
static MVal mep_ternary(MEP *p){
    MVal c = mep_lor(p);
    mep_skip(p);
    if(p->s[p->i] == '?'){
        p->i++;
        int taken = p->mp->noeval ? 0 : (mv_truth(c) ? 1 : 2);
        if(taken == 2) p->mp->noeval++;
        MVal a = mep_ternary(p);
        if(taken == 2) p->mp->noeval--;
        mep_expect(p, ":");
        if(taken == 1) p->mp->noeval++;
        MVal b = mep_ternary(p);
        if(taken == 1) p->mp->noeval--;
        return (taken == 2) ? b : a;
    }
    return c;
}

/* マクロ式を 1 個評価する。 */
static MVal m_eval(MacroPP *mp, const char *text, const char *file, int line){
    while(*text == ' ' || *text == '\t') text++;
    if(!*text) m_fail(mp, file, line, "empty macro expression");
    mp->expr_depth = 0;
    mp->noeval = 0;
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

/* Python の int(s, base) と同じ規則で文字列を整数にする（ASCII のみ）。
   前後の空白、符号、基数 0 のときの 0x/0o/0b 接頭辞（基数 16/8/2 でも可）、
   数字のあいだと接頭辞の直後の 1 個の `_` を認め、基数 0 の 10 進では
   `012` のような先頭の 0 を拒む。axx.py の _bi_int() が呼ぶ int() と同じ
   受理範囲である。返り値は 0 = 成功、1 = 数ではない、2 = 64 ビットを超える。 */
static int m_py_int(const char *s, long long base, long long *out){
    static const char ws[] = " \t\n\r\v\f\x1c\x1d\x1e\x1f";
    if(base != 0 && (base < 2 || base > 36)) return 1;
    for(const char *t = s; *t; t++) if((unsigned char)*t >= 0x80) return 1;
    while(*s && strchr(ws, *s)) s++;
    int neg = 0;
    if(*s == '+' || *s == '-'){ neg = (*s == '-'); s++; }
    int b = (int)base, prefixed = 0;
    if(s[0] == '0'){
        int c = tolower((unsigned char)s[1]);
        if((c == 'x' && (b == 0 || b == 16)) || (c == 'o' && (b == 0 || b == 8))
           || (c == 'b' && (b == 0 || b == 2))){
            b = (c == 'x') ? 16 : (c == 'o') ? 8 : 2;
            s += 2;
            prefixed = 1;
        }
    }
    int zero_only = 0;
    if(b == 0){ b = 10; zero_only = (s[0] == '0'); }
    unsigned long long acc = 0;
    unsigned long long lim = neg ? (1ULL << 63) : (1ULL << 63) - 1;
    int ndig = 0, last_us = 0, ov = 0;
    if(prefixed && *s == '_'){ s++; last_us = 1; }
    for(; *s; s++){
        int c = (unsigned char)*s, d;
        if(c == '_'){
            if(last_us || ndig == 0) return 1;
            last_us = 1;
            continue;
        }
        if(c >= '0' && c <= '9') d = c - '0';
        else if(isalpha(c)) d = tolower(c) - 'a' + 10;
        else break;
        if(d >= b) return 1;
        if(zero_only && d != 0) return 1;
        last_us = 0;
        ndig++;
        if(!ov){
            if(acc > (lim - (unsigned long long)d) / (unsigned long long)b) ov = 1;
            else acc = acc * (unsigned long long)b + (unsigned long long)d;
        }
    }
    if(ndig == 0 || last_us) return 1;
    while(*s && strchr(ws, *s)) s++;
    if(*s) return 1;
    if(ov) return 2;
    *out = neg ? (long long)(0ULL - acc) : (long long)acc;
    return 0;
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
        if(a[0].is_str) m_fail(mp, file, line, "hex() needs an integer");
        if(n > 1 && a[1].is_str) m_fail(mp, file, line, "hex() width must be an integer");
        long long v = a[0].i;
        long long w = (n > 1) ? a[1].i : 0;
        char digits[24];
        /* LLONG_MIN の符号反転は桁あふれするので、符号なしで反転する。 */
        unsigned long long uv = (v < 0) ? 0ULL - (unsigned long long)v : (unsigned long long)v;
        snprintf(digits, sizeof(digits), "%llx", uv);
        long long dl = (long long)strlen(digits);
        long long pad = (w > dl) ? w - dl : 0;   /* 幅に上限は無い（axx.py の _bi_hex() と同じ） */
        char *buf = marena_alloc(&mp->arena, (size_t)(pad + dl + 2));
        char *q = buf;
        if(v < 0) *q++ = '-';
        memset(q, '0', (size_t)pad); q += pad;
        memcpy(q, digits, (size_t)dl + 1);
        *out = mv_str(buf);
        return 1;
    }
    if(strcmp(name, "int") == 0){
        m_bi_argc(mp, "int", n, 1, 2, file, line);
        if(!a[0].is_str){ *out = a[0]; return 1; }
        if(n > 1 && a[1].is_str) m_fail(mp, file, line, "int() base must be an integer");
        long long base = (n > 1) ? a[1].i : 0;
        long long v = 0;
        int rc = m_py_int(a[0].s ? a[0].s : "", base, &v);
        if(rc == 1)
            m_fail(mp, file, line, "int(%s) is not a number",
                   m_pyrepr_a(mp, a[0].s ? a[0].s : ""));
        if(rc == 2)
            m_fail(mp, file, line, "macro expression: integer overflow (64-bit) in int()");
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
        if(a[1].is_str) m_fail(mp, file, line, "substr() index must be an integer");
        long long st = a[1].i;
        if(st < 0) st = 0;
        if(st > l) st = l;
        if(n > 2 && a[2].is_str) m_fail(mp, file, line, "substr() length must be an integer");
        long long cnt = (n > 2) ? a[2].i : l - st;
        if(cnt < 0) cnt = 0;
        if(st + cnt > l) cnt = l - st;
        *out = mv_str(marena_strndup(&mp->arena, t + st, (size_t)cnt));
        return 1;
    }
    if(strcmp(name, "abs") == 0){
        m_bi_argc(mp, "abs", n, 1, 1, file, line);
        if(a[0].is_str) m_fail(mp, file, line, "abs() needs an integer");
        long long v = a[0].i;
        if(v == LLONG_MIN)
            m_fail(mp, file, line, "macro expression: integer overflow (64-bit) in abs()");
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
    if(strcmp(name, "label") == 0){
        m_bi_argc(mp, "label", n, 1, 1, file, line);
        if(!a[0].is_str)
            m_fail(mp, file, line, "label() needs a string");
        long long lv = 0;
        if(m_asm_label(mp, a[0].s ? a[0].s : "", &lv) == MLBL_NO)
            m_fail(mp, file, line, "no such label or .equ: '%s'", a[0].s ? a[0].s : "");
        *out = mv_int(lv);
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

    mp->scopes[mp->nscopes++] = sc;
    for(int i = 0; i < f->nparams; i++){
        MVal v = (i < nargs) ? args[i] : m_eval(mp, f->defaults[i], file, line);
        m_scope_set(sc, f->params[i], v);
    }
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
    if(mp->noeval) return mv_int(0);
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
        size_t sl = (size_t)(e1-e0);
        char *stripped = marena_alloc(&mp->arena, sl + 1);
        memcpy(stripped, e0, sl); stripped[sl]='\0';
        char *er = m_pyrepr_a(mp, stripped);
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

/* 書式指定の整列文字か。 */
static int m_is_align(char c){
    return c == '<' || c == '>' || c == '=' || c == '^';
}

/* 書式指定を解析する。Python のフォーマットミニ言語の部分集合で、axx.py が
   受けるものを受け、拒否するものを拒否する。 */
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

/* 桁区切りを入れたあとの長さ。 */
static int m_group_len(int n, int iv){
    return n + (n - 1) / iv;
}

/* 桁区切りを入れて書く。 */
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

/* UTF-8 の文字数（バイト数ではない）。 */
static int m_utf8_len(const char *s){
    int n = 0;
    for(const unsigned char *p = (const unsigned char*)s; *p; p++)
        if((*p & 0xc0) != 0x80) n++;
    return n;
}

/* n 文字目のバイト位置。 */
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

/* コードポイントを UTF-8 に符号化する。 */
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

/* 整数に書式を適用する。`!{0:c}` はここで空文字列になる。C 文字列は内部に
   NUL を持てないためで、axx.py では NUL 文字が返る。これは既知の相違。 */
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
        if(nd < 0) nd = 0;
        if(nd >= (int)sizeof(digits)) nd = (int)sizeof(digits) - 1;
        if(type == '%'){
            if(nd > (int)sizeof(digits) - 2) nd = (int)sizeof(digits) - 2;
            digits[nd++] = '%';
            digits[nd] = '\0';
        }
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

/* 文字列に書式を適用する。 */
static char *m_fmt_str(MacroPP *mp, const char *s, MFmt *f, int *err){
    if(f->type && f->type != 's'){ *err = 1; return NULL; }
    if(f->sign || f->alt || f->group || f->zcoerce){ *err = 1; return NULL; }
    if(f->align == '='){ *err = 1; return NULL; }
    char *body = (char*)s;
    if(f->has_prec && f->prec < m_utf8_len(s))
        body = marena_strndup(&mp->arena, s, m_utf8_off(s, f->prec));
    return m_fmt_pad(mp, "", body, f, '<');
}

/* `!{式:書式}` の全体を処理する。 */
static char *m_format_value(MacroPP *mp, const char *body, const char *file, int line){
    int len = (int)strlen(body);
    int spec_at = -1;
    char quote = 0;
    int par = 0;
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
        else if(c == ':' && par == 0){
            int has_q = 0;
            for(int j = 0; j < k; j++) if(body[j] == '?'){ has_q = 1; break; }
            if(has_q) continue;
            spec_at = k; break;
        }
    }
    char *expr = (spec_at >= 0) ? marena_strndup(&mp->arena, body, (size_t)spec_at)
                                : (char*)body;
    const char *spec = (spec_at >= 0) ? body + spec_at + 1 : NULL;
    MVal v = m_eval(mp, expr, file, line);
    if(!spec) return mv_to_text(mp, v);
    /* 前後の空白を落とす（axx.py の format_value() の spec.strip() と同じ）。 */
    static const char ws[] = " \t\n\r\v\f\x1c\x1d\x1e\x1f";
    while(*spec && strchr(ws, *spec)) spec++;
    size_t sl = strlen(spec);
    while(sl > 0 && strchr(ws, spec[sl-1])) sl--;
    if(!sl) return mv_to_text(mp, v);
    spec = marena_strndup(&mp->arena, spec, sl);

    MFmt f;
    int err = 0;
    char *out = NULL;
    if(!m_fmt_parse(spec, &f)) err = 1;
    else if(v.is_str) out = m_fmt_str(mp, v.s ? v.s : "", &f, &err);
    else out = m_fmt_int(mp, v.i, &f, &err);
    if(err || !out){
        if(v.is_str)
            m_fail(mp, file, line, "bad format spec ':%s' for value %s",
                   spec, m_pyrepr_a(mp, v.s ? v.s : ""));
        m_fail(mp, file, line, "bad format spec ':%s' for value %lld", spec, v.i);
    }
    return out;
}

/* 行の中の補間を展開する。逃がされた開きはリテラルとして残す。 */
static char *m_interpolate(MacroPP *mp, const char *text, const char *file, int line){
    if(!strstr(text, "!{")) return (char*)text;
    size_t cap = strlen(text) + 256, n = 0;
    char *out = malloc(cap);
    if(!out){ perror("malloc"); exit(1); }
    int i = 0, len = (int)strlen(text);
    while(i < len){
        if(text[i] == '\\' && text[i+1] == '!' && text[i+2] == '{'){
            if(n + 3 >= cap){ cap *= 2; out = realloc(out, cap); if(!out){perror("realloc");exit(1);} }
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
            } else if(c == '\'' && m_sext_tick_at(text, j)) {
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


/* マクロ行のコメントを落とす。ソース側は `;`、パターン側はブロックコメント。
   文字列リテラルの中は触らない。 */
static char *m_strip_comment(MacroPP *mp, const char *text){
    int i = 0; char quote = 0;
    while(text[i]){
        char c = text[i];
        if(quote){
            if(c == '\\'){ i += 2; continue; }
            if(c == quote) quote = 0;
        } else if(c == '"') quote = c;
        else if(c == '\''){
            if(strchr(text + i + 1, '\'')) quote = c;
        }
        else if(mp->pat_mode){
            if(c == '/' && text[i+1] == '*') break;
        }
        else if(c == ';') break;
        i++;
    }
    while(i > 0 && (text[i-1] == ' ' || text[i-1] == '\t')) i--;
    return marena_strndup(&mp->arena, text, (size_t)i);
}

/* 先頭の空白を飛ばす。 */
static const char *m_lstrip(const char *s){
    while(*s == ' ' || *s == '\t') s++;
    return s;
}
/* 末尾の空白を落とす。 */
static char *m_rstrip(MacroPP *mp, const char *s){
    size_t n = strlen(s);
    while(n > 0 && (s[n-1] == ' ' || s[n-1] == '\t')) n--;
    return marena_strndup(&mp->arena, s, n);
}
static char *m_trim(MacroPP *mp, const char *s){ return m_rstrip(mp, m_lstrip(s)); }

/* 行頭の `!` 文のキーワードと残りを取り出す。 */
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

/* それがマクロのキーワードか。 */
static int m_is_keyword(const char *w){
    static const char *kw[] = { "if","then","else","elif","while","def","return",
                                "set","local","break","continue","error","warning",
                                "echo","include","undef", NULL };
    for(int i = 0; kw[i]; i++) if(strcasecmp(w, kw[i]) == 0) return 1;
    return 0;
}


typedef struct { MLine *d; int n; } MSrc;

static MBlock *m_parse_block(MacroPP *mp, MSrc *src, int *ip, int depth);

/* 文の節を 1 つ作る。 */
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
        int at = -1;
        for(int k = 0; body[k]; k++)
            if(body[k] == '!' && strncasecmp(body + k, "!then", 5) == 0) at = k;
        if(at < 0) m_fail(mp, file, line, "'!%s' needs '!then' before '{'", kw);
        body[at] = '\0';
    }
    return m_trim(mp, body);
}

/* `!if` / `!elif` / `!else` の連なりを解析する。 */
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
        if(!rest) m_fail(mp, cfile, cline, "unexpected text after '}': %s",
                         m_pyrepr_a(mp, tail));

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
            { char *_tr = m_trailer(mp, c2 + 1);
              if(_tr)
                m_fail(mp, src->d[*ip].file, src->d[*ip].line,
                       "unexpected text after '}': %s", m_pyrepr_a(mp, _tr)); }
            (*ip)++;
            return n;
        }
        m_fail(mp, cfile, cline, "unexpected '!%s' after '}'", w);
    }
}

/* `!while` を解析する。 */
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
    { char *_tr = m_trailer(mp, c2 + 1);
      if(_tr)
        m_fail(mp, src->d[*ip].file, src->d[*ip].line,
               "unexpected text after '}': %s", m_pyrepr_a(mp, _tr)); }
    (*ip)++;
    return n;
}

/* `!def` を解析する。既定値付きの引数を受ける。 */
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
                                   "substr","abs","min","max","uid","label","defined",NULL};
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
    { char *_tr = m_trailer(mp, c2 + 1);
      if(_tr)
        m_fail(mp, src->d[*ip].file, src->d[*ip].line,
               "unexpected text after '}': %s", m_pyrepr_a(mp, _tr)); }
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

/* 1 ブロックを構文木にする。開き波括弧はヘッダ行の最後、閉じは行頭に要る。
   入れ子の深さに上限がある。 */
static MBlock *m_parse_block(MacroPP *mp, MSrc *src, int *ip, int depth){
    if(depth > MACRO_MAX_DEPTH){
        const char *f = (*ip < src->n) ? src->d[*ip].file : (src->n ? src->d[src->n-1].file : "?");
        int l = (*ip < src->n) ? src->d[*ip].line : (src->n ? src->d[src->n-1].line : 0);
        m_fail(mp, f, l, "macro block nesting deeper than %d", MACRO_MAX_DEPTH);
    }
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
    mp->noeval = 0;
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
    {
        const char *rest = p.s + p.i;
        size_t rl = strlen(rest);
        while(rl > 0 && isspace((unsigned char)rest[rl-1])) rl--;
        if(rl > 0 && rest[0] != ';'){
            char *rb = marena_alloc(&mp->arena, rl + 1);
            memcpy(rb, rest, rl); rb[rl] = '\0';
            m_fail(mp, file, line, "unexpected text after macro call: %s",
                   m_pyrepr_a(mp, rb));
        }
    }
}

/* 展開結果の 1 行を出力に積む。 */
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

/* 文 1 個を実行する。 */
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
        if(!mp->asmb || mp->asmb->st.pas != 1){
            char *t = mv_to_text(mp, v);
            m_echo_write(&t, 1);
        }
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

/* 文の並びを順に実行する。 */
static void m_exec_block(MacroPP *mp, MBlock *b){
    for(int i = 0; i < b->len; i++){
        m_exec_node(mp, b->d[i]);
        if(mp->ctl != MCTL_NONE) return;
    }
}


/* 行を読み込む。行末のバックスラッシュで続く行はつなぎ、つないだぶんだけ
   空行を残すので行番号は入力とずれない。 */
static void m_read_lines(MacroPP *mp, FILE *f, const char *display, MSrc *out){
    int cap = 256, n = 0;
    MLine *d = marena_alloc(&mp->arena, (size_t)cap * sizeof(MLine));
    char *line = NULL; size_t lcap = 0;
    ssize_t r;
    char *name = marena_strdup(&mp->arena, display);
    char *pending = NULL; size_t pending_len = 0;
    while((r = getline(&line, &lcap, f)) != -1){
        while(r > 0 && (line[r-1] == '\n' || line[r-1] == '\r')) line[--r] = '\0';
        if(n >= cap){
            int nc = cap * 2;
            MLine *nd = marena_alloc(&mp->arena, (size_t)nc * sizeof(MLine));
            memcpy(nd, d, (size_t)n * sizeof(MLine));
            d = nd; cap = nc;
        }
        int continued = (r > 0 && line[r-1] == '\\');
        size_t body_len = continued ? (size_t)(r - 1) : (size_t)r;
        if(continued){
            char *np = realloc(pending, pending_len + body_len + 1);
            if(!np){ perror("realloc"); exit(1); }
            pending = np;
            memcpy(pending + pending_len, line, body_len);
            pending_len += body_len;
            pending[pending_len] = '\0';
            d[n].text = marena_strdup(&mp->arena, "");
        } else if(pending){
            char *np = realloc(pending, pending_len + body_len + 1);
            if(!np){ perror("realloc"); exit(1); }
            pending = np;
            memcpy(pending + pending_len, line, body_len);
            pending_len += body_len;
            pending[pending_len] = '\0';
            d[n].text = marena_strdup(&mp->arena, pending);
            free(pending); pending = NULL; pending_len = 0;
        } else {
            d[n].text = marena_strndup(&mp->arena, line, body_len);
        }
        d[n].file = name;
        d[n].line = n + 1;
        n++;
    }
    if(pending){
        /* ファイルの最後で続きが途切れたら、つないだ中身を塊の最後の物理行に
           置く。新しい行は足さないので、行数も行番号も入力のまま。axx.py の
           join_backslash_continuations() と同じ。 */
        d[n-1].text = marena_strdup(&mp->arena, pending);
        free(pending); pending = NULL;
    }
    free(line);
    out->d = d; out->n = n;
}

/* `!include` — 展開時にテキストを取り込む。 */
static void m_do_include(MacroPP *mp, const char *name, const char *file, int line){
    size_t psz = strlen(name) + (file ? strlen(file) : 0) + 4;
    char *path = marena_alloc(&mp->arena, psz);
    size_t dsz = (file ? strlen(file) : 0) + 4;
    char *dir  = marena_alloc(&mp->arena, dsz);
    if(name[0] == '/'){
        snprintf(path, psz, "%s", name);
    } else {
        axx_dir_of(file && file[0] ? file : ".", dir, dsz);
        if(dir[0] == '.' && dir[1] == '\0')
            snprintf(path, psz, "%s", name);
        else
            axx_resolve_path(dir, name, path, psz);
    }
    char real[PATH_MAX];
    if(!realpath(path, real)){ snprintf(real, sizeof(real), "%s", path); }
    for(int i = 0; i < mp->ninc; i++)
        if(strcmp(mp->inc_stack[i], real) == 0)
            m_fail(mp, file, line, "circular '!include' of %s", m_pyrepr_a(mp, name));
    if(mp->ninc >= MACRO_MAX_INCLUDE_DEPTH)
        m_fail(mp, file, line, "'!include' nested deeper than %d", MACRO_MAX_INCLUDE_DEPTH);

    /* ディレクトリは fopen() が通ってしまうことがあるので先に弾く
       （axx.py の open() は IsADirectoryError になる）。 */
    struct stat isb;
    FILE *f = (stat(path, &isb) == 0 && S_ISDIR(isb.st_mode)) ? (errno = EISDIR, NULL)
                                                              : fopen(path, "rt");
    if(!f){
        /* axx.py は OSError をそのまま文字列にするので、その体裁に合わせる。 */
        char eb[1400];
        axx_oserr_str(path, errno, eb, sizeof(eb));
        m_fail(mp, file, line, "cannot '!include' %s: %s", m_pyrepr_a(mp, name), eb);
    }

    MSrc src;
    m_read_lines(mp, f, path, &src);
    fclose(f);

    mp->inc_stack[mp->ninc++] = marena_strdup(&mp->arena, real);
    int ip = 0;
    MBlock *b = m_parse_block(mp, &src, &ip, 0);
    m_exec_block(mp, b);
    mp->ninc--;
}

/* ソース側に展開すべきものがあるか（軽い前判定）。 */
static int m_contains_macros(MSrc *src){
    for(int i = 0; i < src->n; i++){
        if(strchr(src->d[i].text, '!')) return 1;
        if(m_lstrip(src->d[i].text)[0] == '}') return 1;
    }
    return 0;
}

/* その行に補間があるか。 */
static int m_has_interpolation(const char *t){
    for(const char *p = strstr(t, "!{"); p; p = strstr(p + 2, "!{"))
        if(p == t || p[-1] != '\\') return 1;
    return 0;
}

/* パターン側に展開すべきものがあるか（軽い前判定）。 */
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

/* 行の並びをマクロ展開して返す。展開すべきものが 1 つも無ければ解析せずに
   そのまま返す。これがマクロを使わないパターンファイルの速さを保っている。 */
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

/* パターンファイル用のマクロ層を初期化する。 */
static void macro_init_pattern(Assembler *asmb){
    macro_init(&g_pat_macro, asmb);
    g_pat_macro.pat_mode = 1;
}

/* その 1 パスぶんの状態を初期化する。 */
static void macro_reset_pass_pattern(void){
    macro_reset_pass(&g_pat_macro);
}

/* パターンファイルをマクロ展開する。 */
/* パターンファイルをマクロ層に通す。lines_out が NULL でなければ、各行の展開前の
   行番号（axx.py の expand() が返す 3 つ組の行番号）を並べて返す。呼び出し側が
   free する。 */
static char **pat_macro_expand(FILE *f, const char *display, int *nlines, int **lines_out){
    MLineVec v = macro_expand(&g_pat_macro, f, display);
    char **out = malloc(sizeof(char*) * (size_t)(v.len + 1));
    if(!out){ perror("malloc"); exit(1); }
    if(lines_out){
        *lines_out = malloc(sizeof(int) * (size_t)(v.len + 1));
        if(!*lines_out){ perror("malloc"); exit(1); }
    }
    for(int i = 0; i < v.len; i++){
        out[i] = strdup(v.d[i].text ? v.d[i].text : "");
        if(!out[i]){ perror("strdup"); exit(1); }
        if(lines_out) (*lines_out)[i] = v.d[i].line;
    }
    out[v.len] = NULL;
    *nlines = v.len;
    return out;
}

/* 展開結果を解放する。 */
static void pat_macro_expand_free(char **v, int n){
    if(!v) return;
    for(int i = 0; i < n; i++) free(v[i]);
    free(v);
}

/* ソースファイル 1 つを 1 行ずつアセンブルする。 */
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

    char *_caller_file = strdup(st->current_file);
    if(!_caller_file){ perror("strdup"); exit(1); }
    sv_push(&st->fnstack, fn);
    is_push(&st->lnstack, st->ln);
    set_current_file(st, fn);
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
        char *_expkey = strdup(st->current_file);
        if(!_expkey){ perror("strdup"); exit(1); }
        MLineVec _mexp = macro_expand(&g_macro, f, st->current_file);
        fclose(f); f=NULL;
        int _lp = mlp_begin(&st->macro_line_pcs_cur, _expkey);
        for(int _mi=0; _mi<_mexp.len; _mi++){
            mlp_push(&st->macro_line_pcs_cur, _lp, (long long)u256_to_u64(st->pc));
            set_current_file(st, _mexp.d[_mi].file);
            st->ln = _mexp.d[_mi].line;
            lineassemble0(asmb, _mexp.d[_mi].text);
        }
        free(_expkey);
    }
    if(f) fclose(f);

done:
    free(stdin_buf);
    set_current_file(st, _caller_file);
    free(_caller_file);
    sv_pop(&st->fnstack);
    st->ln = is_pop(&st->lnstack);
}

/* ELF 記述の宣言が揃っているか、矛盾がないかを検査する。 */
static void check_elfdecls(Assembler *asmb){
    AsmState *st = &asmb->st;
    if(!st->elf_objfile[0]) return;
    const ElfMachineInfo *m = elf_machine_effective(st);
    for(int w=1; w<9; w++){
        if(!st->elf_decl_width[w]) continue;
        if(elf_decl_type_in(m->named, st->elf_decl_width[w]) < 0)
            axx_diagf(0, 0, " warning - .elfwidth: unknown relocation type '%s' for %s; "
                       "ignored.\n", st->elf_decl_width[w], m->name);
    }
    if(st->elf_decl_extern && elf_decl_type_in(m->named, st->elf_decl_extern) < 0)
        axx_diagf(0, 0, " warning - .elfextern: unknown relocation type '%s' for %s; "
                   "ignored.\n", st->elf_decl_extern, m->name);
    if(st->elf_decl_dwarf && elf_decl_type_in(m->named, st->elf_decl_dwarf) < 0)
        axx_diagf(0, 0, " warning - .elfdwarf: unknown relocation type '%s' for %s; "
                   "ignored.\n", st->elf_decl_dwarf, m->name);
    for(int i = 0; i < st->elf_fields_len; i++)
        if(elf_decl_type_in(m->named, st->elf_fields[i].type) < 0)
            axx_diagf(0, 0, " warning - .elffield: unknown relocation type '%s' for %s; "
                       "ignored.\n", st->elf_fields[i].type, m->name);
    for(int i = 0; i < st->elf_extras_len; i++){
        if(!elf_extra_first(st, i)) continue;
        if(elf_decl_type_in(m->named, st->elf_extras[i].type) < 0)
            axx_diagf(0, 0, " warning - .elfextra: unknown relocation type '%s' for %s; "
                       "ignored.\n", st->elf_extras[i].type, m->name);
        for(int k = i; k < st->elf_extras_len; k++){
            if(strcmp(st->elf_extras[k].type, st->elf_extras[i].type) != 0) continue;
            if(elf_decl_type_in(m->named, st->elf_extras[k].comp) < 0)
                axx_diagf(0, 0, " warning - .elfextra: unknown relocation type '%s' for %s; "
                           "ignored.\n", st->elf_extras[k].comp, m->name);
        }
    }
    for(int w = 1; w < 9; w++){
        if(!st->elf_diff_add[w]) continue;
        const char *tt[2] = { st->elf_diff_add[w], st->elf_diff_sub[w] };
        for(int k = 0; k < 2; k++)
            if(elf_decl_type_in(m->named, tt[k]) < 0)
                axx_diagf(0, 0, " warning - .elfdiff: unknown relocation type '%s' for %s; "
                           "ignored.\n", tt[k], m->name);
    }
    for(int i = 0; i < st->elf_diff_t_len; i++){
        const char *tt[3] = { st->elf_diff_t[i].type, st->elf_diff_t[i].add, st->elf_diff_t[i].sub };
        for(int k = 0; k < 3; k++)
            if(elf_decl_type_in(m->named, tt[k]) < 0)
                axx_diagf(0, 0, " warning - .elfdiff: unknown relocation type '%s' for %s; "
                           "ignored.\n", tt[k], m->name);
    }
    for(int i = 0; i < st->elf_encodes_len; i++)
        if(elf_decl_type_in(m->named, st->elf_encodes[i].type) < 0)
            axx_diagf(0, 0, " warning - .elfencode: unknown relocation type '%s' for %s; "
                       "ignored.\n", st->elf_encodes[i].type, m->name);
    for(int i = 0; i <= st->elf_encodes_len; i++){
        const char *dn, *fn;
        if(i < st->elf_encodes_len){ dn = ".elfencode"; fn = st->elf_encodes[i].fn; }
        else if(st->elf_decl_rinfo){ dn = ".elfrinfo"; fn = st->elf_decl_rinfo; }
        else break;
        MiniFunc *f = mfv_find(&st->funcs, fn);
        if(!f)
            axx_diagf(1, 0, " error - %s: no function named '%s'.\n", dn, fn);
        else if(f->nparams != 2)
            axx_diagf(1, 0, " error - %s: function '%s' must take 2 arguments.\n", dn, fn);
    }
}

static int elf_field_rt_cmp(const void *a, const void *b){
    int x = ((const ElfFieldInfo*)a)->rtype, y = ((const ElfFieldInfo*)b)->rtype;
    return x < y ? -1 : (x > y ? 1 : 0);
}
static int elf_sec_name_cmp(const void *a, const void *b){
    return strcmp(*(char *const *)a, *(char *const *)b);
}

/* 型番号を宣言に書く綴りにする（名前があれば名前、無ければ番号）。 */
static const char *elf_desc_tname(const ElfMachineInfo *m, int rt, char *buf, size_t bsz){
    const char *nm = elf_machine_reverse(m, rt);
    if(nm && elf_machine_named(m, nm) == rt) return nm;
    snprintf(buf, bsz, "%d", rt);
    return buf;
}

/* `--elfdesc` — いま有効な ELF マシン記述を、先頭に `.elfbuiltin::0` を
   置いたパターンファイルの宣言として書き出す。これを命令のパターンと
   一緒に読ませると、組み込みの表なしで同じ ELF が出る。axx.py の
   elf_desc_text() と同じ並びと書式である。 */
static void elf_desc_print(AsmState *st, FILE *fp){
    const ElfMachineInfo *m = elf_machine_effective(st);
    char b1[32];
    fprintf(fp, ".elfbuiltin::0\n");
    char dflt[48]; snprintf(dflt, sizeof(dflt), "machine %d", st->elf_machine);
    if(m->name && m->name[0] && strcmp(m->name, dflt) != 0)
        fprintf(fp, ".elfmachine::%d::%s\n", st->elf_machine, m->name);
    else
        fprintf(fp, ".elfmachine::%d\n", st->elf_machine);
    fprintf(fp, ".elfclass::%d\n", m->elfclass == 2 ? 64 : 32);
    fprintf(fp, ".elfrela::%d\n", m->is_rela ? 1 : 0);
    for(int i = 0; m->named[i].name; i++){
        int rt = m->named[i].rtype;
        int w = elf_machine_reloc_bytes(m, rt);
        int pc = elf_machine_is_pcrel(m, rt);
        fprintf(fp, ".elftype::%s::%d", m->named[i].name, rt);
        if(w || pc){
            if(w) fprintf(fp, "::%d", w); else fprintf(fp, "::");
        }
        if(pc) fprintf(fp, "::1");
        fprintf(fp, "\n");
    }
    for(int w = 1; w < 9; w++)
        if(m->wg[w])
            fprintf(fp, ".elfwidth::%d::%s\n", w, elf_desc_tname(m, m->wg[w], b1, sizeof(b1)));
    fprintf(fp, ".elfextern::%s\n", elf_desc_tname(m, m->extern_default, b1, sizeof(b1)));
    fprintf(fp, ".elfdwarf::%s\n", elf_desc_tname(m, m->dwarf_abs, b1, sizeof(b1)));
    fprintf(fp, ".elfpcguess::%d\n", m->pcrel_guess ? 1 : 0);
    fprintf(fp, ".elfunit::%s\n", st->elf_decl_unit == 1 ? "word" : "byte");
    for(int w = 1; w < 9; w++){
        int ra, rb;
        if(!elf_diff_of(st, w, &ra, &rb)) continue;
        char b2[32];
        fprintf(fp, ".elfdiff::%d::%s::%s\n", w, elf_desc_tname(m, ra, b1, sizeof(b1)),
                elf_desc_tname(m, rb, b2, sizeof(b2)));
    }
    {
        /* 型付きの差は型番号の小さい順（同じ型は最初の宣言）。 */
        int *rts = NULL; int nrt = 0, crt_ = 0;
        for(int i = 0; i < st->elf_diff_t_len; i++){
            int rt = elf_decl_type_in(m->named, st->elf_diff_t[i].type);
            int ra, rb;
            if(rt < 0 || !elf_diff_t_of(st, rt, &ra, &rb)) continue;
            int dup = 0;
            for(int k = 0; k < nrt; k++) if(rts[k] == rt){ dup = 1; break; }
            if(dup) continue;
            rts = elf_decl_grow(rts, &crt_, nrt, sizeof(int));
            rts[nrt++] = rt;
        }
        for(int a = 1; a < nrt; a++)
            for(int b = a; b > 0 && rts[b-1] > rts[b]; b--){ int t = rts[b]; rts[b] = rts[b-1]; rts[b-1] = t; }
        for(int k = 0; k < nrt; k++){
            int ra, rb; char b2[32], b3[32];
            elf_diff_t_of(st, rts[k], &ra, &rb);
            fprintf(fp, ".elfdiff::%s::%s::%s\n", elf_desc_tname(m, rts[k], b1, sizeof(b1)),
                    elf_desc_tname(m, ra, b2, sizeof(b2)), elf_desc_tname(m, rb, b3, sizeof(b3)));
        }
        free(rts);
    }
    {
        /* 添えるリロケーションと書き戻し関数は、型番号の小さい順。 */
        int *rts = NULL; int nrt = 0, crt_ = 0;
        for(int i = 0; i < st->elf_extras_len + st->elf_encodes_len; i++){
            const char *tx = i < st->elf_extras_len ? st->elf_extras[i].type
                                                    : st->elf_encodes[i - st->elf_extras_len].type;
            int rt = elf_decl_type_in(m->named, tx);
            if(rt < 0) continue;
            int dup = 0;
            for(int k = 0; k < nrt; k++) if(rts[k] == rt){ dup = 1; break; }
            if(dup) continue;
            rts = elf_decl_grow(rts, &crt_, nrt, sizeof(int));
            rts[nrt++] = rt;
        }
        for(int a = 1; a < nrt; a++)
            for(int b = a; b > 0 && rts[b-1] > rts[b]; b--){ int t = rts[b]; rts[b] = rts[b-1]; rts[b-1] = t; }
        for(int k = 0; k < nrt; k++){
            int crt[64], csym[64];
            int n = elf_extras_of(st, rts[k], crt, csym, 64);
            for(int j = 0; j < n; j++){
                char b2[32];
                fprintf(fp, ".elfextra::%s::%s::%d\n", elf_desc_tname(m, rts[k], b1, sizeof(b1)),
                        elf_desc_tname(m, crt[j], b2, sizeof(b2)), csym[j]);
            }
        }
        for(int k = 0; k < nrt; k++){
            const char *fn = elf_encode_of(st, rts[k]);
            if(fn) fprintf(fp, ".elfencode::%s::%s\n", elf_desc_tname(m, rts[k], b1, sizeof(b1)), fn);
        }
        free(rts);
    }
    if(st->elf_decl_rinfo) fprintf(fp, ".elfrinfo::%s\n", st->elf_decl_rinfo);
    if(st->elf_cfi_set){
        fprintf(fp, ".elfcfi::%d::%d::%d", st->elf_cfi_ra, st->elf_cfi_code, st->elf_cfi_data);
        if(st->elf_cfi_pad) fprintf(fp, "::%d", st->elf_cfi_pad);
        fprintf(fp, "\n");
    }
    for(int i = 0; i < st->elf_cfiinit_len; i++) fprintf(fp, ".elfcfiinit::%s\n", st->elf_cfiinit[i]);
    {
        int nr = st->elf_cfireg_len;
        int *ord = malloc(sizeof(int) * (size_t)(nr + 1));
        if(!ord){ perror("malloc"); exit(1); }
        for(int i = 0; i < nr; i++) ord[i] = i;
        for(int a = 1; a < nr; a++)
            for(int b = a; b > 0 && strcmp(st->elf_cfireg[ord[b-1]].name, st->elf_cfireg[ord[b]].name) > 0; b--){
                int t = ord[b]; ord[b] = ord[b-1]; ord[b-1] = t;
            }
        for(int i = 0; i < nr; i++)
            fprintf(fp, ".elfcfireg::%s::%d\n", st->elf_cfireg[ord[i]].name, st->elf_cfireg[ord[i]].num);
        free(ord);
    }
    elf_field_effective(st);
    int nf = g_elf_field_eff.n;
    ElfFieldInfo *fs = (ElfFieldInfo*)malloc(sizeof(ElfFieldInfo) * (size_t)(nf + 1));
    if(!fs){ perror("malloc"); exit(1); }
    if(nf) memcpy(fs, g_elf_field_eff.f, sizeof(ElfFieldInfo) * (size_t)nf);
    qsort(fs, (size_t)nf, sizeof(ElfFieldInfo), elf_field_rt_cmp);
    for(int i = 0; i < nf; i++)
        fprintf(fp, ".elffield::%s::0x%llx::%d::%d::%lld\n",
                elf_desc_tname(m, fs[i].rtype, b1, sizeof(b1)),
                (unsigned long long)fs[i].mask, fs[i].off, fs[i].shift, fs[i].bias);
    free(fs);
    for(int k = 0; _elf_hdr_fields[k].name; k++){
        int ix = _elf_hdr_fields[k].idx;
        if(st->elf_hdr_set[ix])
            fprintf(fp, ".elfheader::%s::0x%llx\n", _elf_hdr_fields[k].name,
                    (unsigned long long)st->elf_hdr_val[ix]);
    }
    int ns = st->elf_secs_len;
    char **names = (char**)malloc(sizeof(char*) * (size_t)(ns + 1));
    if(!names){ perror("malloc"); exit(1); }
    for(int i = 0; i < ns; i++){
        names[i] = strdup(st->elf_secs[i].name);
        if(!names[i]){ perror("strdup"); exit(1); }
        for(char *q = names[i]; *q; q++) *q = (char)tolower((unsigned char)*q);
    }
    qsort(names, (size_t)ns, sizeof(char*), elf_sec_name_cmp);
    for(int i = 0; i < ns; i++){
        int k = elf_sec_find(st, names[i]);
        fprintf(fp, ".elfsection::%s::0x%llx", names[i],
                (unsigned long long)st->elf_secs[k].flags);
        int last = st->elf_secs[k].es_set ? 3 : st->elf_secs[k].al_set ? 2
                 : st->elf_secs[k].type_set ? 1 : 0;
        if(last >= 1){
            if(st->elf_secs[k].type_set) fprintf(fp, "::%u", st->elf_secs[k].type);
            else fprintf(fp, "::");
        }
        if(last >= 2){
            if(st->elf_secs[k].al_set) fprintf(fp, "::%u", st->elf_secs[k].al);
            else fprintf(fp, "::");
        }
        if(last >= 3) fprintf(fp, "::%u", st->elf_secs[k].es);
        fprintf(fp, "\n");
        free(names[i]);
    }
    free(names);
    {
        int nl = st->elf_links_len;
        int *ord = (int*)malloc(sizeof(int) * (size_t)(nl + 1));
        if(!ord){ perror("malloc"); exit(1); }
        for(int i = 0; i < nl; i++) ord[i] = i;
        for(int a = 1; a < nl; a++)
            for(int b = a; b > 0 && strcmp(st->elf_links[ord[b-1]].sec, st->elf_links[ord[b]].sec) > 0; b--){
                int t = ord[b]; ord[b] = ord[b-1]; ord[b-1] = t;
            }
        for(int i = 0; i < nl; i++){
            int k = ord[i];
            fprintf(fp, ".elflink::%s::%s", st->elf_links[k].sec, st->elf_links[k].link);
            if(st->elf_links[k].info[0]) fprintf(fp, "::%s", st->elf_links[k].info);
            fprintf(fp, "\n");
        }
        free(ord);
    }
    for(int i = 0; i < st->elf_groups_len; i++){
        fprintf(fp, ".elfgroup::%s::%s::0x%x::", st->elf_groups[i].name, st->elf_groups[i].sig,
                (unsigned)st->elf_groups[i].flags);
        for(int k = 0; k < st->elf_groups[i].nmem; k++)
            fprintf(fp, "%s%s", k ? "," : "", st->elf_groups[i].mem[k]);
        fprintf(fp, "\n");
    }
}

/* パターンファイル中の ELF 記述ディレクティブを先に読んでおく。 */
static void register_elfdecls(Assembler *asmb){
    for(int pi=0; pi<asmb->st.pat.len; pi++){
        PatEntry *e = &asmb->st.pat.data[pi];
        if(!e->f[0] || !e->f[0][0]) continue;
        switch(e->dir_kind){
        case PD_ELFTYPE:    elftype_apply(asmb, e);   break;
        case PD_ELFMACHINE: dir_elfmachine(asmb, e);  break;
        case PD_ELFCLASS:   dir_elfclass(asmb, e);    break;
        case PD_ELFRELA:    dir_elfrela(asmb, e);     break;
        case PD_ELFWIDTH:   dir_elfwidth(asmb, e);    break;
        case PD_ELFEXTERN:  dir_elfextern(asmb, e);   break;
        case PD_ELFDWARF:   dir_elfdwarf(asmb, e);    break;
        case PD_ELFHEADER:  dir_elfheader(asmb, e);   break;
        case PD_ELFSECTION: dir_elfsection(asmb, e);  break;
        case PD_ELFFIELD:   dir_elffield(asmb, e);    break;
        case PD_ELFPCGUESS: dir_elfpcguess(asmb, e);  break;
        case PD_ELFBUILTIN: dir_elfbuiltin(asmb, e);  break;
        case PD_ELFEXTRA:   dir_elfextra(asmb, e);    break;
        case PD_ELFDIFF:    dir_elfdiff(asmb, e);     break;
        case PD_ELFENCODE:  dir_elfencode(asmb, e);   break;
        case PD_ELFRINFO:   dir_elfrinfo(asmb, e);    break;
        case PD_ELFUNIT:    dir_elfunit(asmb, e);     break;
        case PD_ELFLINK:    dir_elflink(asmb, e);     break;
        case PD_ELFGROUP:   dir_elfgroup(asmb, e);    break;
        case PD_ELFCFI:     dir_elfcfi(asmb, e);      break;
        case PD_ELFCFIINIT: dir_elfcfiinit(asmb, e);  break;
        case PD_ELFCFIREG:  dir_elfcfireg(asmb, e);   break;
        default: break;
        }
    }
    check_elfdecls(asmb);
}

/* パターンファイルが定義するシンボルを先に集める。ソースのラベルがこれらと
   衝突したらエラーにできるようにするため、アセンブルの前に名前を知っておく。 */
static void setpatsymbols(Assembler *asmb){
    SymMap fresh; smap_init(&fresh);
    sv_free(&asmb->st.strsym_names); sv_init(&asmb->st.strsym_names);
    sv_free(&asmb->st.strsym_vals);  sv_init(&asmb->st.strsym_vals);
    arrsym_clear_all(&asmb->st);

    int npat = g_unordered ? g_dirorder.n : asmb->st.pat.len;
    for(int pk=0; pk<npat; pk++){
        int pi = g_unordered ? g_dirorder.rows[pk] : pk;
        PatEntry *e=&asmb->st.pat.data[pi];
        if(!e) continue;

        if(strcmp(e->f[0],".setsym")==0){
            const char *name_field = e->f[1][0] ? e->f[1] : e->f[2];
            const char *value_field = e->f[1][0] ? e->f[2] : "";
            char key[512]; axx_strupr_to(key,name_field,sizeof(key));
            smap_clear(&asmb->st.symbols);
            for(int fi=0; fi<fresh.nb; fi++)
                for(SymEntry *fe=fresh.buckets[fi]; fe; fe=fe->next)
                    smap_set(&asmb->st.symbols, fe->key, fe->val);
            {
                const char *q = value_field;
                while(*q==' '||*q=='\t') q++;
                if(*q=='"'){
                    char *body = txt_template_inner(q);
                    strsym_set(&asmb->st, key, body);
                    free(body);
                    continue;
                }
                if(*q=='['){
                    arrsym_set_from_text(asmb, key, q);
                    continue;
                }
                if(symbol_copy_from_name(&asmb->st, key, value_field)) continue;
                if(symbol_set_from_text(&asmb->st, key, value_field)) continue;
            }
            int io;
            uint256_t v = value_field[0] ? expr_expression_pat(asmb,value_field,0,&io) : u256_zero();
            smap_set(&fresh, key, v);
            continue;
        }
        if(strcmp(e->f[0],".clearsym")==0){
            if(e->f[2][0]){
                char key[512]; axx_strupr_to(key,e->f[2],sizeof(key));
                smap_delete(&fresh, key);
                strsym_delete(&asmb->st, key);
                arrsym_delete(&asmb->st, key);
            } else {
                smap_clear(&fresh);
                sv_free(&asmb->st.strsym_names); sv_init(&asmb->st.strsym_names);
                sv_free(&asmb->st.strsym_vals);  sv_init(&asmb->st.strsym_vals);
                arrsym_clear_all(&asmb->st);
            }
            continue;
        }
        if(strcmp(e->f[0],".map")==0){
            if(g_unordered) continue;
            smap_clear(&asmb->st.symbols);
            for(int fi=0; fi<fresh.nb; fi++)
                for(SymEntry *fe=fresh.buckets[fi]; fe; fe=fe->next)
                    smap_set(&asmb->st.symbols, fe->key, fe->val);
            map_apply(asmb, e, &fresh, 0);
            continue;
        }
        if(strcmp(e->f[0],".free")==0){
            const char *names = e->f[2][0] ? e->f[2] : e->f[1];
            const char *p = names;
            while(*p){
                while(*p==' '||*p=='\t') p++;
                char nm[512]; int j=0;
                while(*p && *p!=',' && j<(int)sizeof(nm)-1) nm[j++]=*p++;
                while(j>0 && (nm[j-1]==' '||nm[j-1]=='\t')) j--;
                nm[j]='\0';
                if(nm[0]){
                    char key[512]; axx_strupr_to(key,nm,sizeof(key));
                    smap_delete(&fresh, key);
                    strsym_delete(&asmb->st, key);
                    arrsym_delete(&asmb->st, key);
                }
                if(*p==',') p++; else break;
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

/* インポートファイルの 16 進欄を最後まで読めたか。 */
static int hexfield_fully_consumed(const char *endp){
    while(*endp==' '||*endp=='\t') endp++;
    return *endp=='\0';
}

/* インポートファイルの 1 行からラベルを取り込む。 */
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
        if(endp == fields[1] || !hexfield_fully_consumed(endp)) return 0;
        uint64_t size  = strtoull(fields[2], &endp, 16);
        if(endp == fields[2] || !hexfield_fully_consumed(endp)) return 0;
        secrangevec_push(&asmb->imp_sections, sname,
                          u256_from_u64(start), u256_from_u64(size));
        return 1;
    }

    if(nfields == 2){
        char *labelbuf = strdup(fields[0]);
        if(!labelbuf){ perror("strdup"); exit(1); }
        const char *label = labelbuf;
        if(!label[0]){ free(labelbuf); return 0; }
        int reloc_type = -1;
        char *sep = strstr(labelbuf, "::");
        if(sep){
            *sep = '\0';
            const char *rt_str = sep + 2;
            reloc_type = elf_reloc_named(&asmb->st, elf_machine_effective(&asmb->st), rt_str);
            if(reloc_type < 0)
                axx_diagf(0, 0, " warning - unknown reloc type '%s' for imported label '%s'\n",
                           rt_str, label);
        }
        if(!label[0]){ free(labelbuf); return 0; }
        char *endp;
        uint64_t v = strtoull(fields[1], &endp, 16);
        if(endp == fields[1] || !hexfield_fully_consumed(endp)){ free(labelbuf); return 0; }

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
        free(labelbuf);
        return 1;
    }

    return 0;
}

/* 使い方を出す。引数なしで実行したときと、コマンド行の誤りのときに出る。 */
static void print_usage(const char *prog){
    printf("usage: %s patternfile [sourcefile] [--osabi OSNAME] [-b outfile] [-e export_tsv] [-E export_elf_tsv] [-i import_tsv] [-o elf_obj] [-f {32,64}] [-m machine] [-v] [-V] [-d] [-g] [--no-macro] [-P [file]] [-p [file]]\n",prog);
    printf("  -V           print the text built from string-template patterns (.textmode translation output) to stdout\n");
    printf("  --no-macro   disable the macro preprocessor layer (!if/!while/!def/!return/!set and !{...})\n");
    printf("  -P [file]    macro-expand the source and write it out (stdout if file is omitted), then stop\n");
    printf("  -p [file]    macro-expand the pattern file and write it out (stdout if file is omitted), then stop\n");
    printf("  --elfdesc    print the effective ELF machine description as pattern-file declarations, then stop\n");
    printf("axx general assembler programmed and designed by Taisuke Maekawa\n");
}

/* `-h` / `--help` の説明。axx.py（argparse）の -h と同じ項目を並べる。 */
static void print_help(const char *prog){
    printf("usage: %s patternfile [sourcefile] [options]\n\n", prog);
    printf("axx general assembler programmed and designed by Taisuke Maekawa\n\n");
    printf("positional arguments:\n");
    printf("  patternfile           Pattern definition file (.axx)\n");
    printf("  sourcefile            Assembly source file (.s). Omit for interactive mode.\n\n");
    printf("options:\n");
    printf("  -h, --help            show this help message and exit\n");
    printf("  --osabi ELF_OSABI     ELF OSABI value (default: Linux; FreeBSD/Linux,\n"
           "                        case-insensitive)\n");
    printf("  -b OUTFILE            Output binary file\n");
    printf("  -e EXPORT_TSV         Export labels to TSV file (plain format)\n");
    printf("  -E EXPORT_ELF_TSV     Export labels to TSV file (ELF section flags format)\n");
    printf("  -i IMPORT_TSV         Import labels from TSV file\n");
    printf("  -o OBJ_FILE           Write ELF relocatable object file (.o); class selected\n"
           "                        by -f (default: ELF64)\n");
    printf("  -f {32,64}            ELF class for -o output (default: the pattern file's\n"
           "                        .elfclass, or the conventional class of the -m machine)\n");
    printf("  -m MACHINE            ELF e_machine value (default: the pattern file's\n"
           "                        .elfmachine, else 62=EM_X86_64)\n");
    printf("  -v, --verbose         Verbose: print assembly listing to stdout\n");
    printf("  -V, --text-output     Print the text built from string-template patterns\n"
           "                        (.textmode translation output) to stdout\n");
    printf("  -d, --debug           Enable debug output (forward-ref fallback, relaxation\n"
           "                        log, etc.)\n");
    printf("  -g, --gen-debug       Generate DWARF debug information in the ELF object\n"
           "                        (effective only together with -o)\n");
    printf("  --no-macro            Disable the macro preprocessor layer\n"
           "                        (!if/!while/!def/!return/!set and !{...})\n");
    printf("  -P [FILE], --macro-expand [FILE]\n"
           "                        Macro-expand the source file and write it to FILE\n"
           "                        (stdout if omitted or \"-\") without assembling\n");
    printf("  --elfdesc             Print the effective ELF machine description as\n"
           "                        pattern-file declarations and exit\n");
    printf("  -p [FILE], --macro-expand-pattern [FILE]\n"
           "                        Macro-expand the pattern file and write it to FILE\n"
           "                        (stdout if omitted or \"-\") without assembling\n");
}

/* 2 つのラベル表が同じか。リラクゼーションの収束判定に使う。 */
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
/* ラベル表を写す。反復の頭で初期状態へ戻すのに使う。 */
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

/* `--osabi` の名前を ELF の OSABI 値にする。大文字小文字を区別しない。 */
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


/* 入口。引数を読み、パターンとソースを読み、出力を書く。
   パス1はリラクゼーションで、ラベル表が前回の反復と一致するまで繰り返す。
   上限まで回っても一致しない場合と、過去の状態に戻って振動している場合は、
   誤ったアドレスのコードを出すよりは何も出さないほうを選んで中断する。
   パス2は確定アドレスで 1 回だけ回し、バイト列とリロケーションを作る。 */
int main(int argc, char *argv[]){
    if(argc==1){ print_usage(argv[0]); return 0; }

    int exit_code = 0;
    Assembler *asmb=calloc(1,sizeof(Assembler));
    assembler_init(asmb);
    AsmState *st=&asmb->st;
    macro_init(&g_macro, asmb);
    macro_init_pattern(asmb);

    const char *patternfile=NULL, *sourcefile=NULL;
    char osabistr[16]="Linux";
    const char *macro_expand_dest=NULL;
    const char *pat_macro_expand_dest=NULL;
    int elf_desc_only=0;

    for(int i=1;i<argc;i++){
        if(strcmp(argv[i],"-h")==0||strcmp(argv[i],"--help")==0){
            print_help(argv[0]);
            return 0;
        }
        if(strcmp(argv[i],"--osabi")==0&&i+1<argc&&argv[i+1][0]!='-'){ strncpy(osabistr,argv[++i],sizeof(osabistr)-1); }
        else if(strcmp(argv[i],"-b")==0&&i+1<argc&&argv[i+1][0]!='-'){ st->outfile = argv[++i]; }
        else if(strcmp(argv[i],"-e")==0&&i+1<argc&&argv[i+1][0]!='-'){ st->expfile = argv[++i]; }
        else if(strcmp(argv[i],"-E")==0&&i+1<argc&&argv[i+1][0]!='-'){ st->expfile_elf = argv[++i]; }
        else if(strcmp(argv[i],"-i")==0&&i+1<argc&&argv[i+1][0]!='-'){ st->impfile = argv[++i]; }
        else if(strcmp(argv[i],"-o")==0&&i+1<argc&&argv[i+1][0]!='-'){ st->elf_objfile = argv[++i]; }
        else if(strcmp(argv[i],"-f")==0&&i+1<argc&&argv[i+1][0]!='-'){
            const char *_fs = argv[++i];
            if(strcmp(_fs,"64")==0){ st->elf_class = 2; }
            else if(strcmp(_fs,"32")==0){ st->elf_class = 1; }
            else {
                axx_diagf(0, 0, " error - -f: invalid choice: %s (choose from 32, 64)\n", _fs);
                return 1;
            }
        }
        else if(strcmp(argv[i],"-m")==0&&i+1<argc
                &&(argv[i+1][0]!='-'
                   || ((argv[i+1][1]>='0'&&argv[i+1][1]<='9')))){
            const char *_mstr = argv[++i];
            char *_mend = NULL;
            errno = 0;
            long _mlong = strtol(_mstr, &_mend, 10);
            if(_mend == _mstr || *_mend != '\0' || errno == ERANGE){
                char _mq[600]; m_pyrepr(_mstr, _mq, sizeof(_mq));
                axx_diagf(0, 0, " error - -m/--machine: invalid int value: %s\n", _mq);
                return 1;
            }
            int _mval = (int)_mlong;
            if(_mlong < 0 || _mlong > 65535){
                axx_diagf(0, 0, " error - -m/--machine value %lld is out of range "
                           "(an ELF e_machine number is 0..65535).\n", (long long)_mlong);
                return 1;
            }
            st->elf_machine = _mval;
            st->elf_machine_from_cli = 1;
        }
        else if(strcmp(argv[i],"-v")==0||strcmp(argv[i],"--verbose")==0){ st->verbose=1; }
        else if(strcmp(argv[i],"-V")==0||strcmp(argv[i],"--text-output")==0){ st->text_output=1; }
        else if(strcmp(argv[i],"-d")==0||strcmp(argv[i],"--debug")==0){ st->debug=1; }
        else if(strcmp(argv[i],"-g")==0||strcmp(argv[i],"--gen-debug")==0){ st->gen_debug=1; }
        else if(strcmp(argv[i],"--no-macro")==0){ g_macro.enabled=0; g_pat_macro.enabled=0; }
        else if(strcmp(argv[i],"--elfdesc")==0){ elf_desc_only=1; }
        else if(strncmp(argv[i],"--macro-expand-pattern=",23)==0){
            pat_macro_expand_dest=argv[i]+23;
            if(!*pat_macro_expand_dest) pat_macro_expand_dest="-";
        }
        else if(strcmp(argv[i],"-p")==0||strcmp(argv[i],"--macro-expand-pattern")==0){
            if(i+1<argc && strcmp(argv[i+1],"-")==0){
                pat_macro_expand_dest="-";
                i++;
            }
            else if(i+1<argc && argv[i+1][0]!='-' && patternfile)
                pat_macro_expand_dest=argv[++i];
            else if(i+1<argc && argv[i+1][0]!='-'){
                fprintf(stderr," error - '%s %s' is ambiguous here: '%s' could be "
                        "%s's output file or a positional argument. Write "
                        "'--macro-expand-pattern=%s', or put %s after the pattern file.\n",
                        argv[i], argv[i+1], argv[i+1], argv[i], argv[i+1], argv[i]);
                return 2;
            }
            else
                pat_macro_expand_dest="-";
        }
        else if(strncmp(argv[i],"--macro-expand=",15)==0){
            macro_expand_dest=argv[i]+15;
            if(!*macro_expand_dest) macro_expand_dest="-";
        }
        else if(strcmp(argv[i],"-P")==0||strcmp(argv[i],"--macro-expand")==0){
            if(i+1<argc && strcmp(argv[i+1],"-")==0){
                macro_expand_dest="-";
                i++;
            }
            else if(i+1<argc && argv[i+1][0]!='-' && patternfile && sourcefile)
                macro_expand_dest=argv[++i];
            else if(i+1<argc && argv[i+1][0]!='-'){
                fprintf(stderr," error - '%s %s' is ambiguous here: '%s' could be "
                        "%s's output file or a positional argument. Write "
                        "'--macro-expand=%s', or put %s after the pattern/source files.\n",
                        argv[i], argv[i+1], argv[i+1], argv[i], argv[i+1], argv[i]);
                return 2;
            }
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
        else if(strcmp(argv[i],"--osabi")==0||strcmp(argv[i],"-b")==0
                ||strcmp(argv[i],"-e")==0||strcmp(argv[i],"-E")==0
                ||strcmp(argv[i],"-i")==0||strcmp(argv[i],"-o")==0
                ||strcmp(argv[i],"-f")==0||strcmp(argv[i],"-m")==0){
            /* 値を取るオプションの後ろに値が無い（行末か、次が '-' で始まる）。
               axx.py（argparse）と同じく終了コード 2 で止める。 */
            fprintf(stderr,"error: option '%s' requires an argument.\n",argv[i]);
            print_usage(argv[0]);
            return 2;
        }
        else{
            fprintf(stderr,"error: unknown option '%s'.\n",argv[i]);
            print_usage(argv[0]);
            return 2;
        }
    }

    int osa = find_osabi(osabistr);
    if (osa==-1) {
        fprintf(stderr, "warning: unknown --osabi value '%s'; "
                "valid choices are Linux/linux/FreeBSD/freebsd. Using 'Linux'.\n",
                osabistr);
        osa = find_osabi("Linux");
    }
    st->osabi = osa;

    if(st->elf_machine_from_cli && st->elf_objfile[0]
       && !elf_machine_find(st->elf_machine)){
        char _known[512]; int _kn=0;
        for(int _mi=0; _mi<ELF_MACHINES_N && _kn < (int)sizeof(_known)-40; _mi++){
            _kn += snprintf(_known+_kn, sizeof(_known)-(size_t)_kn, "%s%d (%s)",
                             _mi?", ":"", ELF_MACHINES[_mi].machine, ELF_MACHINES[_mi].name);
        }
        axx_diagf(0, 0, " warning - -m/--machine value %d is not one of the machines axx "
                   "has built-in relocation numbering for (%s); relocation types must "
                   "come from the pattern file (.elftype / .elfwidth / .elfextern). "
                   "References whose type is not declared get no relocation entry, "
                   "rather than a guessed (and wrong) one.\n",
                   st->elf_machine, _known);
    }

    if(!patternfile){ print_usage(argv[0]); return 1; }

    if(pat_macro_expand_dest){
        if(!patternfile){
            axx_diagf(0, 0, " error - -p/--macro-expand-pattern needs a pattern file.\n");
            exit_code=1; goto cleanup;
        }
        FILE *pf=fopen(patternfile,"rt");
        if(!pf){
            { char eb[2*PATH_MAX + 256]; axx_oserr_str(patternfile, errno, eb, sizeof(eb));
              axx_diagf(0, 0, " error - cannot open pattern file '%s': %s\n",
                        patternfile, eb); }
            exit_code=1; goto cleanup;
        }
        macro_reset_pass_pattern();
        int _pn=0;
        char **_pv=pat_macro_expand(pf, patternfile, &_pn, NULL);
        fclose(pf);
        if(g_pat_macro.had_error || st->had_error){
            pat_macro_expand_free(_pv,_pn); exit_code=1; goto cleanup;
        }
        FILE *of = (strcmp(pat_macro_expand_dest,"-")==0) ? stdout
                                                          : fopen(pat_macro_expand_dest,"wt");
        if(!of){
            char _eb[1200]; axx_oserr_str(pat_macro_expand_dest, errno, _eb, sizeof(_eb));
            axx_diagf(0, 0, " error - cannot write '%s': %s\n",
                       pat_macro_expand_dest, _eb);
            pat_macro_expand_free(_pv,_pn); exit_code=1; goto cleanup;
        }
        for(int _pi=0;_pi<_pn;_pi++) fprintf(of,"%s\n",_pv[_pi]);
        if(of!=stdout ? axx_close_out(of, pat_macro_expand_dest)
                      : axx_flush_stdout(pat_macro_expand_dest)) exit_code=1;
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
            { char eb[2*PATH_MAX + 256]; axx_oserr_str(sourcefile, errno, eb, sizeof(eb));
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
            char _eb[1200]; axx_oserr_str(macro_expand_dest, errno, _eb, sizeof(_eb));
            axx_diagf(0, 0, " error - cannot write '%s': %s\n",
                       macro_expand_dest, _eb);
            exit_code=1; goto cleanup;
        }
        for(int _mi=0;_mi<mv.len;_mi++) fprintf(of,"%s\n",mv.d[_mi].text);
        if(of!=stdout ? axx_close_out(of, macro_expand_dest)
                      : axx_flush_stdout(macro_expand_dest)) exit_code=1;
        goto cleanup;
    }

    readpat(asmb,patternfile);
    pat_mark_static(&st->pat);
    pat_hoist_scan(&st->pat);
    pat_unordered_plan(&st->pat);
    patidx_build(&g_patidx, &st->pat);
    if(st->had_error){
        fprintf(stderr," error - one or more errors were reported during assembly; "
                       "output would be incomplete or wrong.\n");
        fprintf(stderr,"         Aborting: no output file written.\n");
        exit_code=1; goto cleanup;
    }
    setpatsymbols(asmb);
    register_elfdecls(asmb);
    if(st->had_error){
        fprintf(stderr," error - one or more errors were reported while reading the "
                       "pattern file; output would be incomplete or wrong.\n");
        fprintf(stderr,"         Aborting: no output file written.\n");
        exit_code=1; goto cleanup;
    }
    if(elf_desc_only){
        elf_desc_print(st, stdout);
        goto cleanup;
    }

    if(st->impfile[0]){
        FILE *lf=axx_open_input(st->impfile, "import file");
        if(!lf){ exit_code=1; goto cleanup; }
        StrVec _implines; sv_init(&_implines);
        { char *l=NULL; size_t lc=0;
          while(getline(&l,&lc,lf)!=-1) sv_push(&_implines, l);
          free(l); }
        fclose(lf);
        for(int _phase=0; _phase<2; _phase++){
            for(int _li=0; _li<_implines.len; _li++){
                const char *_l = _implines.data[_li];
                int _nf = 1;
                for(const char *_q=_l; *_q; _q++)
                    if(*_q=='\t') _nf++;
                    else if(*_q=='\n'||*_q=='\r') break;
                if(_phase==0 ? (_nf>=3) : (_nf==2))
                    imp_label(asmb, _l);
            }
        }
        sv_free(&_implines);
    }

    if(!sourcefile){
        st->pc=u256_zero(); st->pas=0; st->ln=1;
        set_current_file(st, "(stdin)");
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
        { int _n; LabelEntry **_v = lmap_in_order(&st->labels, &_n);
          for(int _i=0;_i<_n;_i++){ LabelEntry *e=_v[_i];
                lmap_set_full(&imported_labels, e->key, e->value, e->section,
                              e->is_equ, e->is_imported, e->reloc_type_override, e->is_undef); }
          free(_v); }

        PatVar    initial_vars[NVARS];
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
            { int _n; LabelEntry **_v = lmap_in_order(&imported_labels, &_n);
              for(int _i=0;_i<_n;_i++){ LabelEntry *e=_v[_i];
                    lmap_set_full(&st->labels, e->key, e->value, e->section,
                                  e->is_equ, e->is_imported, e->reloc_type_override, e->is_undef); }
              free(_v); }
            secmap_clear(&st->sections);
            secrangevec_clear(&st->section_ranges);
            st_set_current_section(st, ".text");
            lmap_free(&st->export_labels); lmap_init(&st->export_labels);
            sv_free(&st->export_order);
            smap_clear(&st->symbols);
            for(int pi=0; pi<st->patsymbols.nb; pi++)
                for(SymEntry *se2=st->patsymbols.buckets[pi]; se2; se2=se2->next)
                    smap_set(&st->symbols, se2->key, se2->val);
            memcpy(st->vars, initial_vars, sizeof(st->vars));
            vars_touch_all();
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
                for(LabelEntry *e=st->labels.buckets[bi]; e; e=e->next){
                    if(u256_is_undef_derived(e->value)) continue;
                    lmap_set_full(&prev_labels, e->key, e->value, e->section,
                                  e->is_equ, e->is_imported, e->reloc_type_override, e->is_undef);
                }

            lmap_free(&st->macro_labels); lmap_init(&st->macro_labels);
            for(int bi=0; bi<st->labels.nbuckets; bi++)
                for(LabelEntry *e=st->labels.buckets[bi]; e; e=e->next)
                    lmap_set_full(&st->macro_labels, e->key, e->value, e->section,
                                  e->is_equ, e->is_imported, e->reloc_type_override, e->is_undef);
            st->macro_labels_valid = 1;

            mlp_vec_free(&st->macro_line_pcs);
            st->macro_line_pcs = st->macro_line_pcs_cur;
            memset(&st->macro_line_pcs_cur, 0, sizeof(st->macro_line_pcs_cur));

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
            axx_diagf(0, 1, " error - Pass1 relaxation did not converge after %d iterations.\n",
                       MAX_RELAX);
            fprintf(stderr,"         Generated code would have incorrect addresses for\n");
            fprintf(stderr,"         variable-length instructions with forward references.\n");
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
        st_set_current_section(st, ".text");
        smap_clear(&st->symbols);
        for(int pi=0; pi<st->patsymbols.nb; pi++)
            for(SymEntry *se2=st->patsymbols.buckets[pi]; se2; se2=se2->next)
                smap_set(&st->symbols, se2->key, se2->val);
        memcpy(st->vars, initial_vars, sizeof(st->vars));
        vars_touch_all();
        fileassemble(asmb,sourcefile);

        secmap_finalize_current(st);

        {
            int _dn; LabelEntry **_dv = lmap_in_order(&st->labels, &_dn);
            int drift_count = 0;
            for(int _i=0;_i<_dn;_i++){
                    LabelEntry *e=_dv[_i];
                    if(e->is_equ) continue;
                    if(u256_is_undef_derived(e->value)) continue;
                    LabelEntry *p = lmap_find(&pass1_final, e->key);
                    if(p && !u256_eq(p->value, e->value)) drift_count++;
                }
            if(drift_count){
                axx_diagf(0, 0, " error - address mismatch between pass1 and pass2 "
                           "(%d label(s)); output addresses are UNRELIABLE.\n", drift_count);
                if(st->reported_label_errors.len > 0)
                    fprintf(stderr,"         This is a consequence of the label definition "
                        "error(s) reported above; fix those first.\n");
                else
                    fprintf(stderr,"         This usually means pass1 relaxation did "
                        "not fully converge for variable-length forward references.\n");
                int shown = 0;
                for(int _i=0;_i<_dn && shown<10;_i++){
                        LabelEntry *e=_dv[_i];
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
                free(_dv);
                lmap_free(&pass1_final);
                exit_code = 1;
                goto cleanup;
            }
            free(_dv);
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
        if(!lf){ \
            char _experrbuf[1200]; axx_oserr_str((path_), errno, _experrbuf, sizeof(_experrbuf)); \
            axx_diagf(0, 0, " error - cannot write '%s': %s\n", \
                       (path_), _experrbuf); \
            exit_code = 1; \
        } else { \
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
 \
                    uint256_t _lv = e->is_equ \
                                  ? e->value \
                                  : u256_mul_signed(e->value, u256_from_u64((uint64_t)_bpw_export)); \
                    char _lbl_addr[96]; u256_to_pyhex(_lv, _lbl_addr, sizeof(_lbl_addr)); \
 \
                    char _rtype_sfx[80]=""; \
                    if(elf_){ \
                        LabelEntry *_full=lmap_find(&st->labels,e->key); \
                        if(_full && _full->reloc_type_override>=0){ \
                            const char *_nm=elf_reloc_reverse(st, elf_machine_effective(st), \
                                                              _full->reloc_type_override); \
                            if(_nm) snprintf(_rtype_sfx,sizeof(_rtype_sfx),"::%s",_nm); \
                        } \
                    } \
                    fprintf(lf,"%s%s\t%s\n",e->key,_rtype_sfx,_lbl_addr); \
                } \
            } \
             \
            if(axx_close_out(lf, (path_))) exit_code = 1; \
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

    lmap_free(&st->macro_labels);
    mlp_vec_free(&st->macro_line_pcs);
    mlp_vec_free(&st->macro_line_pcs_cur);

    macro_free(&g_macro);
    macro_free(&g_pat_macro);

    if(fflush(stdout) != 0 || ferror(stdout)){
        int _e = errno ? errno : EIO;
        char _eb[1200]; axx_oserr_nopath(_e, _eb, sizeof(_eb));
        fprintf(stderr, " error - cannot write to standard output: %s\n", _eb);
        clearerr(stdout);
        if(exit_code == 0) exit_code = 1;
    }

    return exit_code;
}
