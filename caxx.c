
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
#include <setjmp.h>

static void axx_diagf(int set_error, int force, const char *fmt, ...);
static void m_pyrepr(const char *s, char *out, size_t outsz);
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
/* マクロ層とミニ言語で共通の `echo` 出力（定義はマクロ層側）。 */
static void m_echo_write(char *const *items, int n);

/* パターン変数（a〜z）1個ぶんの束縛。is_undef は「まだ束縛されていない」印。
 * is_float は、val が「C の double のビットパターン」（true）なのか
 * 「そのままの256bit整数値」（false）なのかを覚えておく印。浮動小数点モード
 * では同じ uint256_t をどちらの意味でも使うため、書き込み時にどちらの
 * 意味で書いたかを追跡しないと、読み出し側（浮動小数点モードの比較・算術）
 * が整数値をdoubleのビット列として誤って再解釈してしまう（破綻点修正、
 * var_get_for_mode 呼び出し側と var_put/var_put_tagged を参照）。
 * !F/!D/!Q での束縛は対象外: axx.py 自身がそれを struct.pack したビット列を
 * int.from_bytes() で普通の Python int として var_manager.put() に渡して
 * いる（put_tagged ではない）ため、そちら側は is_float=0（整数扱い）の
 * ままにして axx.py の実際の挙動に合わせる。 */
typedef struct { uint256_t val; int is_undef; int is_float; } PatVar;

/* パターン変数の置き場。名前は綴りだけで決まり、長さは問わない（`a` でも
 * `var_2` でも同じ扱い）。名前はパターンファイルを読むときに登録し、以後は
 * 添字（スロット番号）で扱う。g_nvars は登録した個数で、変数を走査する
 * ループの上限である。捕捉も代入もされていない名前にはスロットを作らず、
 * 式の中で読むと 0 になる。 */
#define NVARS 256
static int    g_nvars = 0;
static char  *g_varnames[NVARS];   /* スロット i の名前 */

/* パターン変数の名前は小文字で始まり、小文字・数字・`_` が続く。 */
static int var_name_len(const char *s){
    if(!(s[0] >= 'a' && s[0] <= 'z')) return 0;
    int n = 1;
    while((s[n]>='a'&&s[n]<='z')||(s[n]>='0'&&s[n]<='9')||s[n]=='_') n++;
    return n;
}

/* 先頭 len 文字がちょうど変数名ひとつか。 */
static int is_var_name_n(const char *s, int len){
    if(len <= 0) return 0;
    if(!(s[0] >= 'a' && s[0] <= 'z')) return 0;
    for(int i = 1; i < len; i++)
        if(!((s[i]>='a'&&s[i]<='z')||(s[i]>='0'&&s[i]<='9')||s[i]=='_')) return 0;
    return 1;
}

/* 名前をスロット番号にする。長さは問わない。create が真なら無ければ新しく
 * 割り当てる。見つからない（かつ create でない）ときは -1。 */
static int var_slot(const char *name, int len, int create){
    char lower[256];
    if(len <= 0 || len >= (int)sizeof(lower)) return -1;
    for(int i = 0; i < len; i++) lower[i] = (char)tolower((unsigned char)name[i]);
    lower[len] = '\0';
    if(!is_var_name_n(lower, len)) return -1;
    for(int i = 0; i < g_nvars; i++)
        if((int)strlen(g_varnames[i]) == len && memcmp(g_varnames[i], lower, (size_t)len) == 0)
            return i;
    if(!create) return -1;
    if(g_nvars >= NVARS){
        fprintf(stderr, " error - too many pattern variable names (maximum %d).\n", NVARS);
        return -1;
    }
    char *dup = malloc((size_t)len + 1);
    if(!dup){ perror("malloc"); exit(1); }
    memcpy(dup, lower, (size_t)len); dup[len] = '\0';
    g_varnames[g_nvars] = dup;
    return g_nvars++;
}

/* 診断に出すための名前。 */
static const char *var_slot_name(int slot){
    if(slot < 0 || slot >= g_nvars) return "?";
    return g_varnames[slot];
}

/* 配列シンボルの1項目。数値か文字列のどちらかを持つ。 */
typedef struct { int is_str; char *s; uint256_t v; } SymItem;
struct ArrSym { char *name; SymItem *items; int len; };

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
/* u256_to_i64/u64 は下位64bitしか見ないため、シフト量や指数のように
 * 「安全な範囲に収まっているか」を判定する用途にそのまま使うと、上位ワードに
 * 値が乗っている(=64bitを大きく超える)ケースで切り詰められた小さい値として
 * 誤判定してしまう(境界チェックの回避を許してしまう)。符号と、小さな定数
 * 上限との大小関係を上位ワードも含めて正しく判定するヘルパー。 */
static int u256_is_neg256(uint256_t v){ return (int)(v.w[3]>>63); }
static int u256_nonneg_gt_i64(uint256_t v, int64_t max){
    /* v は非負であることが呼び出し側で確認済みという前提。max は 64bit に
     * 収まる小さな正の定数であることが前提(EXP_MAX/SHIFT_MAX 用途)。 */
    if(v.w[1] || v.w[2] || v.w[3]) return 1;
    return v.w[0] > (uint64_t)max;
}

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

/* 本体の式評価器が持つ単項/後置演算子の実装。マクロ層からも同じ意味で呼べる
 * ように評価器の外へ出してある。どれも診断は出さず「値と、あれば伝えるべき
 * 文言」を返すだけにして、報告はそれぞれの層に任せる。
 * axx.py の op_msb / op_sext / op_byte と同じ。 */

#define SEXT_MAX_BITS 128

/* `@v` … 最上位の立っているビットの位置を右から数えた値。 */
static int op_msb(uint256_t v){ return u256_nbit(v); }

/* `x'bits` … ビット bits-1 を符号ビットとみなした符号拡張。
 * warn_out には上限超えのときだけ 1 が入る（表示は呼び出し側）。 */
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

/* `*(x, index)` … 下位から数えて index バイト目より上を残した値。
 * index が負なら neg_out に 1 を入れて 0 を返す（表示は呼び出し側）。
 * 256 を超える分は符号で埋まるだけなので先に頭打ちにする。 */
static uint256_t op_byte(uint256_t x, uint256_t index, int *neg_out){
    *neg_out = 0;
    if(u256_is_neg256(index)){ *neg_out = 1; return u256_zero(); }
    int shift = u256_nonneg_gt_i64(index, 256/8) ? 256 : (int)(u256_to_i64(index)*8);
    return u256_sar(x, shift);
}

/* 未定義ラベルの値を表す番兵。
 *
 * 破綻点修正: 以前は ~0（全ビット1）だった。これは二の補数では -1 そのものなので、
 * 式が正当に -1 を返しただけで「未定義ラベル由来」と誤判定していた
 * （`MVI A,-1` がアセンブルできない、等）。axx.py の番兵 (1<<1024)-1 は
 * 巨大な「正」の値で -1 とは別物であり、C 側だけが衝突していた。
 *
 * uint256_t には 256bit を超える帯域外の余地が無いため、代わりに
 * 「符号付きで表せる最大値」= 0x7FFF...FFFF を番兵に使う。こうすると
 *   - -1 は符号付き絶対値が 1 なので未定義由来と判定されない
 *   - 番兵そのものと、そこから算術で派生した値（UNDEF+4 等）は
 *     符号付き絶対値が 2**192 以上のままなので従来どおり検出できる
 * という両立ができる。2**192 以上の正当な巨大定数を誤判定しうる点は
 * 従来と変わらない（下の警告を参照）。 */
static uint256_t UNDEF_VAL(void) {
    uint256_t r = u256_not(u256_zero());
    r.w[3] &= 0x7FFFFFFFFFFFFFFFULL;
    return r;
}
static int u256_is_undef(uint256_t a) { return u256_eq(a, UNDEF_VAL()); }
static int u256_is_undef_derived(uint256_t a) {
    /* 番兵そのものは確定なので、下のヒューリスティック警告を出さずに返す。 */
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

/* 破綻点修正: VLIW パケットのスロット添字列（vliwprocess の idxlst）が
 * 固定256要素で確保されていて、それを超えると axx.py には無いエラーで
 * 打ち切っていた（axx.py はただの list なので無制限）。他の可変長配列
 * (IntVec)と同じ倍々伸長で置き換える。 */
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
/* 添字 idx の要素を s に置き換える。len<=idx なら空文字列で埋めて伸ばす。
 * .error::n::"Message" のような「番号を指定して差し替える」用途向け。 */
static AXX_UNUSED void sv_set(StrVec *v, int idx, const char *s){
    while(v->len<=idx) sv_push(v, "");
    char *dup = strdup(s);
    if(!dup){perror("strdup"); exit(1);}
    free(v->data[idx]);
    v->data[idx] = dup;
}

/* .enum で登録された列挙。names は要素名（大文字化済み）を列挙順に、
 * expr は `!E<変数>` が拾ったリストから値を作る式を持つ。
 * expr が NULL なら、その変数に列挙は定義されていない。 */
typedef struct { StrVec names; char *expr; } EnumDef;

static void enumdef_init(EnumDef *e){ sv_init(&e->names); e->expr=NULL; }
static void enumdef_clear(EnumDef *e){
    sv_free(&e->names);
    free(e->expr); e->expr=NULL;
}
static void enumdef_copy(EnumDef *dst, const EnumDef *src){
    enumdef_clear(dst);
    for(int i=0;i<src->names.len;i++) sv_push(&dst->names, src->names.data[i]);
    dst->expr = src->expr ? strdup(src->expr) : NULL;
}

/* `.sub::名前 … .return` で登録されたサブ表。
 * pat は項目の照合パターン、val は値欄（カンマ区切りの式）。
 * `!S{{名前}}<変数>` は、この表のどれか1項目に一致したとき、その項目の値欄を
 * 評価した結果をその変数に束縛する。 */
typedef struct { char *pat; char *val; } SubEntry;
typedef struct { char *name; SubEntry *e; int n; int cap; int freed; } SubDef;
typedef struct { SubDef *data; int len; int cap; } SubVec;

static void subv_init(SubVec*v){ v->data=NULL; v->len=0; v->cap=0; }
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
static SubDef *subv_find(SubVec*v, const char *name){
    for(int i=0;i<v->len;i++) if(strcmp(v->data[i].name,name)==0) return &v->data[i];
    return NULL;
}
/* `.free` で「この行から先は使わない」と印を付ける。表そのものは消さない。
 * `.sub` はパターンを読むときに一度だけ組み立てられ、`.setsym` のように
 * ソース1行ごとに作り直されはしないので、消してしまうと `.free` より前に
 * 書かれたパターンまで2行目以降に使えなくなる。印は行の頭で落とす。 */
static int subv_mark_freed(SubVec*v, const char *name){
    for(int i=0;i<v->len;i++)
        if(strcasecmp(v->data[i].name, name)==0){ v->data[i].freed = 1; return 1; }
    return 0;
}
static void subv_unfreeze_all(SubVec*v){
    for(int i=0;i<v->len;i++) v->data[i].freed = 0;
}
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

/* ==================== ミニ言語 (`.func` / `.call`) の型 ====================
 * `binary_list` 欄の `.call 名前(引数,…)` から呼ばれる、チューリング完全な
 * 小さな手続き型言語。値は 256bit 2の補数の整数か、その配列。 */

typedef struct {
    int        is_arr;
    uint256_t  num;
    uint256_t *arr;
    int        n, cap;
} MiniVal;

typedef enum {
    MX_NUM, MX_VAR, MX_ARRLIT, MX_INDEX, MX_SLICE, MX_LEN, MX_BIN, MX_UN,
    MX_CALL, /* 式の途中の `.call 名前(引数, ...)`。name と items を使う */
    MX_STR,  /* `.echo` の文字列リテラル専用。式としては評価されない */
    MX_CORE  /* `$$` `$.` `#記号` … 本体の式評価器に委譲する項 */
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
    char          *name;       /* 代入先 / 呼ぶ関数名 / .for の変数 */
    char          *fname;      /* `var = .call f(...)` の呼ぶ関数名 */
    MExpr         *idx;        /* 代入先の添字。無ければ NULL */
    MExpr         *val;        /* 代入する式 / .if .while の条件 / .return の値 */
    MExpr        **args;       /* .emit .call の引数, .for の range 引数 */
    int            nargs;
    struct MStmt **body;       /* .if の then / .while .for の本体 */
    int            nbody;
    struct MStmt **body2;      /* .if の else */
    int            nbody2;
    char         **names;      /* .nonlocal の名前 */
    int            nnames;
    const char    *file;
    int            line;
} MStmt;

typedef struct MiniFunc {
    char             *name;
    char            **params;
    int               nparams;
    char            **lines;     /* 読み込み時に集めた本体の行 */
    char            **lfiles;
    int              *llines;
    int               nlines, clines;
    MStmt           **body;      /* 解析済みの文の並び */
    int               nbody;
    struct MiniFunc  *parent;
    struct MiniFunc **children;
    int               nchildren, cchildren;
    char             *file;
    int               line;
    int               depth;     /* 読み込み中のブロック深さ */
} MiniFunc;

typedef struct { MiniFunc **data; int len; int cap; } MiniFuncVec;

static void mfv_init(MiniFuncVec *v){ v->data = NULL; v->len = 0; v->cap = 0; }

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
/* 破綻点修正: バケット数が 64 固定でリハッシュしなかったため、ラベルが増えると
 * チェインが伸びて検索が O(n) になり、全体が O(n^2) になっていた（大きなソースで
 * 目に見えて遅くなる）。要素数がバケット数の4倍を超えたら4倍に広げる。 */
static void lmap_maybe_grow(LabelMap *m) {
    if(!m->buckets || m->nbuckets <= 0) return;
    if(m->count < m->nbuckets * 4) return;
    int nb = m->nbuckets * 4;
    LabelEntry **nbuf = calloc((size_t)nb, sizeof(LabelEntry*));
    if(!nbuf) return;                    /* 広げられなくても動作は正しいまま */
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
    lmap_maybe_grow(m);
}
static void lmap_set_reloc_type(LabelMap *m, const char *key, int reloc_type) {
    LabelEntry *e = lmap_find(m, key);
    if(e) e->reloc_type_override = reloc_type;
}
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
    e->next=m->buckets[h]; m->buckets[h]=e; m->count++;
    lmap_maybe_grow(m);
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

/* 式評価器の「この場では何が書けるか」を表す能力記述子。
 * 本体・マクロ層・ミニ言語の 3 つの層が同じ式評価器を呼ぶが、呼ぶ時点で意味を
 * 成す項目は層ごとに違う。たとえばパターン変数 `a` はパターン行を符号化して
 * いる最中にしか束縛されていないし、`!!!` は VLIW のパターン行でしか意味が
 * ない。どの項目が生きているかを 1 か所にまとめ、評価器は st->expcaps を見て
 * 判断する。呼ぶタイミングが変われば記述子が変わり、使える機能が変わる。
 * axx.py の ExprCaps と同じ構成。 */
typedef struct {
    const char *name;
    int patvars;   /* 小文字 1 文字のパターン変数 a〜z */
    int vliw;      /* `!!!` / `!!!!` */
    int labels;    /* ラベル名・.equ 名の参照 */
    int loc;       /* `$$` / `$.` */
    int syms;      /* `#name` と .setsym の記号 */
} ExprCaps;

/* パターンファイルの式。すべて使える。 */
static const ExprCaps CAPS_PAT  = { "pattern",       1, 1, 1, 1, 1 };
/* アセンブリソース行の式。パターン変数と VLIW 計数は無い。 */
static const ExprCaps CAPS_ASM  = { "assembly",      0, 0, 1, 1, 1 };
/* ミニ言語 (`.func` 本体) から呼ぶとき。ラベル・`$$`・`#記号` は読めるが、
 * パターン変数はその場で束縛されていないので落とす。 */
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

/* =========================================================
 * AsmState — アセンブル中の全状態
 *
 * 式評価・パターン照合・ディレクティブ処理・出力生成の各関数は自前の状態を
 * 持たず、全てこの構造体を共有して読み書きする（axx.py の AssemblerState に対応）。
 * ========================================================= */
/* マクロ層の $/$$ 用。「あるファイルの展開後 N 行目が、直前の反復でどの
 * アドレスに置かれたか」を覚えておくための表。ファイル1つぶんが
 * MacroLinePcs、それをファイル名で引くのが MacroLinePcsVec。 */
typedef struct { char *file; long long *pcs; int len, cap; } MacroLinePcs;
typedef struct { MacroLinePcs *d; int len, cap; } MacroLinePcsVec;

static void mlp_vec_free(MacroLinePcsVec *v){
    for(int i=0;i<v->len;i++){ free(v->d[i].file); free(v->d[i].pcs); }
    free(v->d);
    v->d=NULL; v->len=v->cap=0;
}

/* file 用の記録欄を新しく開く（同名が既にあれば作り直す）。戻り値は欄の
 * 添字。ポインタを返さないのは、.INCLUDE で fileassemble が再帰すると
 * この配列が realloc されて既存のポインタが無効になるため。欄は追加しか
 * しないので、添字なら再帰をまたいでも有効なまま。 */
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

/* 展開後 idx 行目のアドレス。記録が無ければ 0。 */
static long long mlp_get(const MacroLinePcsVec *v, const char *file, int idx){
    if(!file || idx < 0) return 0;
    for(int i=0;i<v->len;i++)
        if(strcmp(v->d[i].file, file)==0)
            return (idx < v->d[i].len) ? v->d[i].pcs[idx] : 0;
    return 0;
}

typedef struct {
    /* --- 出力先 --- */
    char outfile[512];       /* -b 生バイナリ */
    char expfile[512];       /* -e ラベル TSV */
    char expfile_elf[512];   /* -E ラベル TSV（ELF フラグ付き） */
    char impfile[512];       /* -i ラベル TSV の取り込み */
    uint256_t pc_overflow_max;  /* pc が 64bit を超えた場合の記録（警告用） */
    int       pc_overflow_set;
    int  osabi;              /* ELF ヘッダの OSABI（0=Linux, 9=FreeBSD） */

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
    /* `.setsym::名前::"文字列"` で登録された文字列シンボル。値が数値では
     * ないので式には出せず、文字列テンプレート（3.5.2）の中でだけ使える。
     * 名前は大文字化して names に、中身をそのまま vals に、同じ添字で持つ。 */
    StrVec     strsym_names;
    StrVec     strsym_vals;

    /* `.setsym::名前::[項目,項目,…]` で登録された配列シンボル。項目は数値でも
     * 文字列でもよく、`x[3]`（テンプレート）や `#x[3]`（式）で引く。 */
    struct ArrSym *arrsyms;
    int        arrsyms_len;
    int        arrsyms_cap;
    LabelMap   export_labels;  /* .global 等で外部公開するラベル */
    StrVec     export_order;   /* 公開順（出力の再現性のため） */
    PatVec     pat;            /* 読み込んだパターン表 */
    SubVec     subs;           /* `.sub … .return` のサブ表 */
    MiniFuncVec funcs;         /* `.func … .return` のミニ言語の関数 */

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
    const ExprCaps *expcaps;   /* いま評価中の式で使える項目 */
    int        exp_typ_float;  /* 浮動小数点モードか */

    /* 直近の式評価で未定義ラベルを踏んだか。「失敗時に立てる」だけで
     * 成功しても降ろさない（1つの式が複数ラベルを引くため、途中で降ろすと
     * 先に起きた失敗が消える）。降ろすのは .ORG/.RESB/.ZERO/.ALIGN/.EQU 等、
     * 新規に判定したい側が評価直前に自分で行う。 */
    int        error_undefined_label;

    /* 既に報告したラベル定義の誤り（"種別:名前" の一覧）。パス1はリラクゼーション
     * で何度も走るので、同じ誤りを反復回数だけ並べないための記録。
     * report_definition_error() が使う。 */
    StrVec     reported_label_errors;

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

    /* パターンのエンコーディング欄が文字列テンプレート "..." だったときに、
     * そこから組み立てたアセンブリ結果のテキスト。1行ごとに作り直す。
     * asmtext は素のまま流す用につないだもの、asmtext_disp は -v の診断行に
     * 見せる用で、`"A","B"` のように欄に書いたとおり分けて括ってある。 */
    char      *asmtext;
    char      *asmtext_disp;

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
    /* rtype>0 なら `.reloc` が宣言された変数が運んだ参照。命令語のビット欄に
     * 値が詰まっていて加数を逆算できないので、型と加数をここに持って回る。
     * 加数は「変数が持っていた値 − ラベル値」で、`bl func` なら 0。 */
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
    int        elf_capturing_var;   /* 捕捉中の変数スロット。-1 でなし */
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
    StrVec     check_constraints[NVARS];
    /* .reloc で登録された「この変数が捕らえたラベル参照はこの型で外に出す」
     * 宣言。変数スロット -> 型番号（0 でなし）。型はオペランドの位置ごとに
     * 決まる（AArch64 では同じシンボルを adrp と add が別の型で参照する）ため、
     * シンボル側ではなくパターン側の、この変数単位でしか表せない。 */
    int        reloc_constraints[NVARS];
    char      *reloc_badname[32];   /* 未知型名の報告済み一覧 */
    int        reloc_badname_len;

    /* .enum で登録された、変数 a〜z の列挙（`!E<変数>` が使う） */
    EnumDef    enum_defs[NVARS];

    /* .enum の式を評価している間だけ非 NULL。要素名を「出現していれば
     * .setsym の値、非出現なら 0」に束縛した表を指す。 */
    const StrVec    *enum_bind_names;
    const uint256_t *enum_bind_vals;

    /* error_patterns 欄が返すエラーコード → メッセージ文字列。
     * ERRORS_TABLE の実行時可変コピーとして state_init() で複製する。
     * .error::n::"Message" ディレクティブで上書き・拡張できる。 */
    StrVec     errors;

    /* 式の再帰深度。深すぎる入れ子でネイティブスタックを溢れさせない番人 */
    int        expr_depth;

    /* --- パス1のリラクゼーション（サイズ収束） ---
     * relax_prev は前回反復での「ラベル→アドレス」。今回と一致したら収束。
     * relax_optimistic は未確定の前方参照を「近い」と仮定して収束を早めるモード。 */
    LabelMap  *relax_prev;

    int        relax_optimistic;

    /* --- マクロ層からラベル値・.equ・$/$$ を参照するためのスナップショット ---
     * マクロ展開はアドレス確定より前に走るので「今の値」は原理的に無い。
     * 前回リラクゼーション反復の値を使い、収束はリラクゼーションループ
     * （反復上限・振動検出・未収束なら出力しない）に委ねる。
     * macro_labels_valid==0 は「まだ一度も反復していない＝何も分からない」で、
     * このとき未知の名前は 0・defined() は偽になる。
     * relax_prev と別に持つのは、relax_prev がパス2の前に解放されるのに対し、
     * こちらは収束後の展開をパス2でも再現するため生かしておく必要があるため。 */
    LabelMap   macro_labels;
    int        macro_labels_valid;

    /* $/$$ 用。ラベルと違って位置で決まる値なので、展開後の行番号でしか
     * 対応が取れない。macro_line_pcs が前回反復の記録、_cur が今回ぶん。 */
    MacroLinePcsVec macro_line_pcs;
    MacroLinePcsVec macro_line_pcs_cur;

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
        /* 破綻点修正: nt と ns を別々に realloc していたため、nt は成功したが
         * ns は失敗した場合、両方を free して抜けていた。しかし realloc が
         * 成功した時点で古いブロックは既に解放/移動済みなので、そこで
         * st->diag_pending を更新しないまま抜けるとダングリングポインタが
         * 残る。成功した側だけでも必ず反映してから抜ける。 */
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

/* 内側の評価器が出す診断を一時的に飲み込むための退避/復元。
 *
 * qad{}/dbl{}/flt{} の「予備の評価器」を呼ぶときに使う。予備側で起きた
 * ゼロ除算等の内部エラーをそのまま表示すると、axx.py が出す
 * "dbl{}: cannot convert ..." とは別の文言（"Division by 0 error."）が
 * 混ざって両実装の出力が食い違うため、内側の分は捨てて呼び出し側が
 * 正しい文言を1本だけ出す。
 *
 * axx_diagf() は in_match_attempt かつ diag_capturing のときだけ溜め込む
 * ので、両方立てる。既に外側で捕捉中の場合を壊さないよう、現在の捕捉
 * バッファごと退避してから始め、終了時に元へ戻す。 */
typedef struct {
    char **texts; int *seterr; int n; int cap; int capturing; int in_match;
} DiagSuppress;

static void diag_suppress_begin(AsmState *st, DiagSuppress *sv){
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

static void diag_suppress_end(AsmState *st, DiagSuppress *sv){
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
    /* 命令フィールド型。値は命令語のビット欄に詰まるため、素の整数が並ぶ
     * データ型とは扱いが異なる（insn_reloc_field_mask を参照）。 */
    {"movw_uabs_g0", 263, 4}, {"movw_uabs_g0_nc", 264, 4},
    {"movw_uabs_g1", 265, 4}, {"movw_uabs_g1_nc", 266, 4},
    {"movw_uabs_g2", 267, 4}, {"movw_uabs_g2_nc", 268, 4},
    {"movw_uabs_g3", 269, 4},
    {"movw_prel_g0", 287, 4}, {"movw_prel_g0_nc", 288, 4},
    {"movw_prel_g1", 289, 4}, {"movw_prel_g1_nc", 290, 4},
    {"movw_prel_g2", 291, 4}, {"movw_prel_g2_nc", 292, 4},
    {"movw_prel_g3", 293, 4},
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
    /* GOT 経由。リンカが GOT エントリを作るので、値はアセンブル時には決まらない。
     * 欄は 0 で出し、リンカが埋める。 */
    {"got_ld_prel19", 309, 4},
    {"got_page", 311, 4}, {"adr_got_page", 311, 4},
    {"got_lo12", 312, 4}, {"ld64_got_lo12_nc", 312, 4},
    {"ld64_gotpage_lo15", 313, 4},
    {NULL, 0, 0},
};

/* AArch64 の「命令フィールド型」リロケーションが占める、32bit 命令語中の
 * ビットマスクを返す。データ型や未知の型では 0。
 *
 * データ型（ABS64 など）は値がそのまま連続バイトに並ぶが、こちらは命令語の
 * 飛び飛びのビット欄に、語単位・ページ単位に縮めた形で詰まる。そのため加数を
 * 「出力バイト列 − ラベル値」で逆算する通常の経路が使えない。該当する型では
 * 代わりに、パターンが捕らえたオペランド値とラベル値の差を加数とし、命令語側の
 * ビット欄は 0 にして出す（GNU as と同じ形。RELA なのでリンカが欄を埋める）。 */
static uint32_t insn_reloc_field_mask(int rtype){
    switch(rtype){
    case 263: case 264: case 265: case 266:
    case 267: case 268: case 269:
    case 287: case 288: case 289: case 290:
    case 291: case 292: case 293:
        return 0xffffu << 5;                    /* MOVW_UABS/PREL_G0..G3  imm16 */
    case 274: case 275: case 276:
        return (3u << 29) | (0x7ffffu << 5);    /* ADR/ADRP  immlo+immhi */
    case 277: case 278: case 284: case 285:
    case 286: case 299:
        return 0xfffu << 10;                    /* ADD/LDST lo12  imm12 */
    case 279: return 0x3fffu << 5;              /* TSTBR14  */
    case 280: case 309: return 0x7ffffu << 5;   /* CONDBR19 / GOT_LD_PREL19 */
    case 311: return (3u << 29) | (0x7ffffu << 5);  /* ADR_GOT_PAGE */
    case 312: case 313: return 0xfffu << 10;    /* LD64_GOT_LO12_NC / GOTPAGE_LO15 */
    case 282: case 283: return 0x3ffffffu;      /* JUMP26 / CALL26 */
    default: return 0;
    }
}
static const ElfNamedReloc _named_riscv[] = {
    {"abs64", 2, 8}, {"abs32", 1, 4}, {"abs16", 34, 2}, {"abs8", 33, 1},
    {NULL, 0, 0},
};

/* アーキテクチャ別 ELF 情報表（axx.py の ELF_MACHINES に対応）。
 * 列の意味は左から（ElfMachineInfo の宣言順そのまま）:
 *   e_machine, 名前, elfclass(1=32/2=64), is_rela(1=RELA/0=REL),
 *   外部シンボルの既定型, DWARF絶対参照の型,
 *   幅8の既定型, 幅4の既定型, 幅2の既定型, 幅1の既定型,
 *   PC相対型の一覧, その個数, 記号名テーブル
 * REL（加数を命令バイト列に埋め込む形式）を使うのは i386 と ARM(32) だけで、
 * 他は全て RELA（加数を専用フィールドに持つ）。
 * 幅N の既定型は、必ずその名前表(named)に現れて幅も一致していること
 * （ARM の幅2 はかつて 4 = R_ARM_LDR_PC_G0 という 16bit データ参照ではない
 *   値になっていた。正しくは R_ARM_ABS16 の 5）。 */
static const ElfMachineInfo ELF_MACHINES[] = {
    {3,   "i386",      1, 0, 2,   1,   0,  2, 20, 22, _pcrel_i386,    4, _named_i386},
    {4,   "m68k",       1, 1, 4,   1,   0,  4,  2,  3, _pcrel_m68k,    3, _named_m68k},
    {20,  "PowerPC",    1, 1, 26,  1,   0, 26,  4,  0, _pcrel_ppc32,   2, _named_ppc32},
    {21,  "PowerPC64",  2, 1, 26,  38,  38,26,  4,  0, _pcrel_ppc64,   3, _named_ppc64},
    {22,  "s390x",      2, 1, 5,   22,  22, 5,  3,  1, _pcrel_s390x,   3, _named_s390x},
    {40,  "ARM",        1, 0, 3,   2,   0,  3,  5,  8, _pcrel_arm,     2, _named_arm},
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

/* axx.py の Assembler._addr_to_word_offset() 相当。
 *
 * 破綻点修正: 以前は section_ranges しか見ていなかったため、そのセクションの
 * 断片が1つも記録されていない場合（.section/.endsection を跨がずに終わった等）
 * にオフセットが求まらず、シンボルのセクション所属や DWARF のアドレスが
 * axx.py と食い違っていた。axx.py の _section_word_ranges() と同じく、
 * 断片が無いときだけ sections 表の (start, size) を1つの断片とみなす。 */
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

static uint64_t dwarf_word_offset(AsmState *st, const char *sec_name, uint64_t word_pc, int bpw){
    if(st->sections.count == 0) return word_pc * (uint64_t)bpw;
    int64_t o = sec_word_offset(st, sec_name, word_pc);
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
    sv_init(&st->reported_label_errors);
    strcpy(st->lwordchars, "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz_.");
    strcpy(st->swordchars, "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz_%$-~&|");
    strcpy(st->current_section, ".text");
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
    sv_init(&st->strsym_names);
    sv_init(&st->strsym_vals);
    st->arrsyms = NULL; st->arrsyms_len = 0; st->arrsyms_cap = 0;
    st->osabi = 0;
    st->ln = 0;
    sv_init(&st->fnstack);
    is_init(&st->lnstack);
    for(int i=0;i<NVARS;i++){ st->vars[i].val=u256_zero(); st->vars[i].is_undef=0; }
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
    for(int _ci=0; _ci<NVARS; _ci++) sv_init(&st->check_constraints[_ci]);
    for(int _ci=0; _ci<NVARS; _ci++) st->reloc_constraints[_ci] = 0;
    st->reloc_badname_len = 0;
    for(int _ci=0; _ci<NVARS; _ci++) enumdef_init(&st->enum_defs[_ci]);
    st->enum_bind_names = NULL;
    st->enum_bind_vals  = NULL;
    sv_init(&st->errors);
    for(int _ei=0; _ei<ERRORS_COUNT; _ei++) sv_push(&st->errors, ERRORS_TABLE[_ei]);
}

static char axx_upper_char(char c) {
    if(c>='a'&&c<='z') return c-32;
    return c;
}
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

/* s の idx 位置に一致する列挙要素名のうち最長のものの番号を返す（無ければ -1）。
 * 直後が英数字・下線なら語の途中なので一致とみなさない。記号文字（.symbolc の
 * 既定に含まれる `-` 等）まで語の一部と見なすと `A0-A1` の範囲指定も減算も
 * 書けなくなるので、英数字と下線だけを見る。 */
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

/* Portable ISO C replacement for the GCC-only `({ ... })` statement-expression
 * that used to be inlined at each qad{}/dbl{}/flt{}/enflt{}/endbl{} lookahead
 * site: returns 1 if, after skipping spaces from idx, the next character is
 * '{' and still within bounds. */
static int axx_next_nonspace_is_brace(const char *s, int slen, int idx) {
    int j = axx_skipspc(s, idx);
    return j < slen && s[j] == '{';
}

/* アセンブリソース1行の空白を整える（引用符の中は手を付けない）。
 *
 * 引用符の外では タブ・CR・LF を空白に直し、連続する空白を1個に潰す。
 * 照合は空白の個数を見ないので、こうしておくと `MOV  A , B` のような書き方の
 * 揺れを吸収できる。
 *
 * 破綻点修正: 以前は行全体に一律で適用していた（\t を空白に置換するループ＋
 * axx_reduce_spaces()）ため、文字列リテラルの中身まで潰していた。
 * `.ascii "a    b"` が 3 バイトの `a b` になり、生のタブは空白へ化けていた
 * （診断は一切出ない）。文字列は「そのままのバイト列を置く」のがアセンブラの
 * 仕事なので、引用符の中は素通しする。
 *
 * `"..."` と `'x'` の扱いは axx_remove_comment_asm() と同じ規約に従う。
 * 常に w <= i なので同じバッファを上書きしても安全。 */
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

/* パターンファイルのコメント(スラッシュ+アスタリスクで始まりアスタリスク+
 * スラッシュで終わるブロックコメント)を落とす。
 *
 * 破綻点修正: 以前は「行単位で扱うので閉じ記号は不要」という設計で、
 * その行に現れた開始記号から行末までを問答無用で切り捨てるだけだった。
 * 実際のパターンファイル（got.axx 等）は何十行にもまたがる本物の
 * C 形式ブロックコメントを書いており、開始行以降・終了行までの中身
 * (説明文や区切り線など) が「'::' の無い迷子の行」として毎行
 * warning を出しながらパターン表に無害だが無駄なエントリとして
 * 積まれていた。呼び出し元がファイル全体で共有する *in_comment 経由で
 * 状態を引き継ぎ、複数行にまたがるブロックコメントとして正しく扱う。
 * 同じ行内に閉じ記号があれば、その後ろの内容は通常どおり生かす
 * (閉じ記号の直後に続く内容が消えていた副作用も合わせて直る)。 */
static void axx_remove_comment(char *l, int *in_comment) {
    int i=0, w=0;
    while(l[i]){
        if(*in_comment){
            if(l[i]=='*'&&l[i+1]=='/'){ *in_comment=0; i+=2; continue; }
            i++; continue;
        }
        if(l[i]=='/'&&l[i+1]=='*'){ *in_comment=1; i+=2; continue; }
        l[w++]=l[i++];
    }
    l[w]=0;
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
                if(l2[idx]&&is_xdigit_upper(axx_upper_char(l2[idx]))){
                    char r[600]; m_pyrepr(l2, r, sizeof(r));
                    axx_diagf(0, 0, " warning - '\\x' escape takes at most 2 hex digits; "
                                    "extra digit(s) treated as literal characters in: %s\n", r);
                }
                if(hn>0){
                    out[n++]=(char)(int)strtol(hex,NULL,16);
                } else {
                    if(n<osz-1) out[n++]='x';
                }
            }
            /* 破綻点修正: \u / \U を解釈していなかったため（axx.py は解釈する）、
             * `.INCLUDE "é..."` のようなファイル名で両実装が別のパスを開いていた。
             * axx.py は chr(コードポイント) を文字列に入れ、開くときに UTF-8 へ
             * 符号化されるので、ここでも UTF-8 バイト列を書き込む。 */
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
    if(!l2[idx])
        axx_diagf(0, 0, " warning - unterminated string literal: %s\n", l2);
}

static int char_in(char c, const char *set){
    return strchr(set,c)!=NULL;
}

static int axx_get_intstr(const char *s, int idx, char *fs, size_t fsz){
    /* 破綻点修正: 旧実装は桁数がバッファ上限に達すると idx を進めるのを
     * やめてしまい、残った数字がそのまま次のトークンとして解析され
     * "Syntax error" に化けていた（axx.py は無制限精度なので桁数の上限が
     * 無く、この desync が起きない）。桁数が上限を超えても数字である間は
     * idx を進め続け、バッファに書き込む桁だけを先頭 fsz-1 桁に絞る。 */
    size_t n=0;
    while(s[idx]&&is_digit(s[idx])){
        if(n<fsz-1) fs[n++]=s[idx];
        idx++;
    }
    fs[n]=0;
    return idx;
}

static int axx_get_floatstr(const char *s, int idx, char *fs, size_t fsz){
    /* 破綻点修正: axx_get_intstr と同じ desync バグがここにもあった。
     * バッファ上限に達すると idx を進めるのをやめてしまい、残った桁が
     * 次のトークンとして誤読されていた（axx.py は無制限）。さらに、
     * 仮数部だけでバッファが埋まっていると、指数部の数字が実在しても
     * `n<fsz-1` が false になって while が一度も回らず、"e/E の直後に
     * 数字が無い" と誤認して指数部ごと巻き戻す不具合もあった。数字/'.'/
     * 'e'/符号である間は常に idx を進め、バッファに書き込む文字数だけを
     * 先頭 fsz-1 文字に絞る。 */
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

/* 破綻点修正: 以前は本文を呼び出し側の固定長 char[512] に写していたため、
 * 512 文字を超える式で本文が途中で切れ、しかも切れた位置は "}" ではない
 * ので、その次の走査は "}" を読み飛ばすつもりで無関係な1文字を読み飛ばし、
 * 以降の構文解析全体がずれる（axx.py には長さ制限が無い）。まず区切り位置
 * だけを走査してから実際の長さぶんだけ動的に確保し、呼び出し側に
 * 所有権を渡す（使い終わったら free() すること）。 */
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

/* ラベル名を1語切り出す。
 *
 * eat_colon が真のときは、名前の直後の `:` も一緒に読み飛ばす。
 * `foo: NOP` の行頭ラベルや `.EXTERN foo::pc32` を切り出すための約束で、
 * 呼び出し側は l[idx-1]==':' を見て「ラベル定義だったか」を判定する。
 *
 * 破綻点修正: 式の評価（expr_factor1）からも同じ関数を呼んでいたため、
 * 三項演算子の `:` がラベル名の一部として食われていた。`1?foo:bar` は
 * `foo` の直後で `:` を失い、残った `bar` が解析されない余りとして残って
 * Syntax error になっていた（`foo :bar` と空白を入れたときだけ通るという
 * 再現条件の分かりにくい誤り）。式の文脈からは eat_colon=0 で呼ぶ。 */
/* ラベル名／シンボル名を切り出すための作業バッファを用意する。
 *
 * 破綻点修正: 呼び出し側はどこも char[512] の自動変数を渡していたため、
 * 511 文字を超える名前が（警告は出るものの）切り詰められ、axx.py には長さの
 * 制限が無いのでシンボル表が食い違っていた。語の長さは「入力の残り長」で
 * 上限が決まるので、そこに収まらないときだけヒープへ逃がす
 * （ふだんは自動変数のままなので、ラベル参照ごとの確保は起きない）。
 * 戻り値が stackbuf と違うときは、使い終わりに free() すること。 */
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

static int axx_get_label_word(const char *s, int idx, const char *lwordchars, char *t_out, size_t tsz){
    return axx_get_label_word_ex(s, idx, lwordchars, t_out, tsz, 1);
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

/* 破綻点修正: 10^n を `scale *= base` の逐次乗算で求めると、n が大きいとき
 * （小数部の桁数や指数部）に最大 n 回ぶんの丸め誤差が積み重なり、axx.py
 * （Decimal による正確な計算）と異なるビットパターンになっていた
 * （例: 1e300 の最下位ニブルがずれる）。二分累乗法なら乗算回数が
 * O(log n) で済み、丸め回数を大幅に減らせる。 */
static __float128 f128_ipow10(int n)
{
    __float128 base = (__float128)10;
    __float128 result = (__float128)1;
    while(n > 0){
        if(n & 1) result *= base;
        base *= base;
        n >>= 1;
    }
    return result;
}

static __float128 f128_from_decimal(const char *s)
{
    const __float128 ten  = (__float128)10;

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

    __float128 denom = f128_ipow10(frac_digits);
    __float128 result = int_val / denom;

    if(*s == 'e' || *s == 'E'){
        s++;
        int esign = 1;
        if(*s == '-'){ esign = -1; s++; }
        else if(*s == '+'){ s++; }
        int eabs = 0;
        /* 破綻点修正: 指数の桁数に上限が無く、極端に長い指数文字列で
         * eabs(int) が符号付きオーバーフロー(未定義動作)を起こしうる。
         * float128 の指数範囲(最大でも5桁程度)よりずっと大きい値で頭打ちにする。 */
        while(*s >= '0' && *s <= '9'){
            if(eabs < 1000000) eabs = eabs*10 + (*s-'0');
            s++;
        }
        /* 負の指数は「10^eabs の逆数を掛ける」のではなく「10^eabs で割る」。
         * 逆数自体が持つ丸め誤差を掛け算で複利させず、割り算1回ぶんに抑える。 */
        __float128 scale = f128_ipow10(eabs);
        result = (esign > 0) ? (result * scale) : (result / scale);
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

/* 破綻点修正: ここは元々 `(double)r.val` を isfinite() で見ていたため、
 * __float128 としては有限な正当な値（1e400 や 1e4900 のように quad の
 * 指数範囲 [~1e-4932, ~1e4932] には収まるが double の範囲 [~1e-308, 1e308]
 * には収まらない値）まで「非有限」と誤判定し、精度の落ちる strtold 経路
 * （x86 拡張倍精度なら 64bit 仮数、long double == double な環境なら 53bit
 * 仮数）へ不必要にフォールバックさせ、112bit 仮数で計算できるはずの値を
 * 誤ったビットパターンにしていた。__float128 の生のビット列から指数
 * フィールドを直接見れば、quad 自身の範囲内かどうかを正しく判定できる。 */
static int f128_is_finite(__float128 v)
{
    uint256_t u = f128_to_u256(v);
    uint64_t exp = (u.w[1] >> 48) & 0x7FFFu;
    return exp != 0x7FFFu;
}

static uint256_t f128_eval_text(const char *text, int *ok_out)
{
    F128R r = f128_expr_fn(text);
    if(r.ok && !f128_is_finite(r.val)) r.ok = 0;
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
        /* 破綻点修正: -0.0 と +0.0 は == で等しいため、符号を見ずに常に
         * u256_zero() を返すと "-0.0" の符号ビットが消えていた。 */
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
    /* 破綻点修正: 非正規化数(biased_exp==0)には暗黙の先頭1ビットが無い。
     * 正規化された sig (1.xxx 形式) からそのまま sig-1.0 で仮数部を作ると
     * 非正規化数のビットパターンを誤って符号化する。sig を 2^-subnorm_shift
     * だけ右シフトしてから仮数部を抽出する（十分小さければ自然に0へ丸まる）。 */
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
/* 定義は後方(expr_bitwise_result 付近)にある u256_int_to_double を
 * ここより前で使うための前方宣言。u256_to_double(memcpyでビット列を
 * そのまま取り出す)とは違い、こちらは「符号付き256bit整数としての値」を
 * 実際に数値変換して最も近いdoubleにする。PatVar が整数のまま
 * 浮動小数点モードの式に読み込まれたときに使う（var_get_for_mode 参照）。 */
static double u256_int_to_double(uint256_t v);
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

/* ワード幅ぶんのマスク。
 * 破綻点修正: 以前は `(uint64_t)1 << st->bts` を直に書いていたため、
 * `.bits` に 0 以下や 64 以上が入ると未定義動作（負シフト／幅以上のシフト）に
 * なっていた。.bits 側でも 1..64 を検証するようにしたが、ここでも守る。 */
static uint64_t axx_word_mask(int bts){
    if(bts <= 0)  return 0;
    if(bts >= 64) return (uint64_t)-1;
    return ((uint64_t)1 << bts) - 1;
}

static void outbin_store(AsmState *st, uint64_t position, uint256_t word_val){
    if(st->bts <= 0) return;   /* axx.py の _store と同じく何も書かない */
    uint64_t v = u256_to_u64(word_val) & axx_word_mask(st->bts);
    bufmap_set(&st->buf, position, v);
}

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
    /* 破綻点修正: max_pos が2^64に近い場合、(max_pos+1)*bytes_per_word が
     * 64bit算術でラップアラウンドし、小さな total_size を通してしまっていた
     * （巨大な .ORG + 複数バイト幅のワードで再現）。pc_overflow_set /
     * max_pos==-1 の特別扱いと同じく、256bit演算でオーバーフローさせずに
     * MAX_OUTPUT_BYTES と比較してから初めて64bitへ落とす。 */
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
    if(!fp){perror(st->outfile);free(data);return;}
    fwrite(data,1,(size_t)total_size,fp);
    fclose(fp);
    fprintf(stderr,"wrote raw binary %s (%llu bytes)\n",st->outfile,(unsigned long long)total_size);
    free(data);

    /* 命令フィールド型のリロケーションを出した箇所は、RELA の作法どおり命令語の
     * ビット欄を 0 にしてある（リンカが埋める）。同じ実行で -b も書いていると、
     * その 0 がそのまま生バイナリに残り、リンカを通さない側だけが壊れる。
     * 黙って壊れた方が困るので、どの箇所かを添えて知らせる。 */
    if(st->elf_objfile[0]){
        int _nz = 0;
        char _where[256]; size_t _wl = 0; _where[0] = '\0';
        for(int i = 0; i < st->reloc_count; i++){
            if(insn_reloc_field_mask(st->relocations[i].rtype) == 0) continue;
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

static int var_slot_is_undef(AsmState *st, int slot){
    if(slot>=0 && slot<NVARS) return st->vars[slot].is_undef;
    return 0;
}
/* 浮動小数点モード評価の直前に呼ぶ。整数のまま束縛された変数
 * (is_float==0) だけ数値変換し、既にdoubleのビット列として束縛済みの
 * 変数(is_float==1、例: !D で束縛、または flt モード下での `:=` 代入)は
 * そのまま通す（二重変換でビット列を壊さないため）。 */
static uint256_t var_slot_for_mode(AsmState *st, int slot, int want_float){
    if(slot<0||slot>=NVARS) return u256_zero();
    PatVar *pv = &st->vars[slot];
    if(want_float && !pv->is_float) return double_to_u256(u256_int_to_double(pv->val));
    return pv->val;
}
static void var_slot_put_tagged(AsmState *st, int slot, uint256_t v, int is_undef){
    if(slot<0||slot>=NVARS) return;
    st->vars[slot].val=v; st->vars[slot].is_undef=is_undef; st->vars[slot].is_float=st->exp_typ_float;
}
static void var_slot_put(AsmState *st, int slot, uint256_t v){
    var_slot_put_tagged(st, slot, v, 0);
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
            if(st->elf_capturing_var >= 0){
                int vi = st->elf_capturing_var;
                if(vi >= 0 && vi < g_nvars){
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
                st->elf_refs[st->elf_refs_len].rtype    = 0;
                st->elf_refs[st->elf_refs_len].addend   = 0;
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
        /* 破綻点修正: set_error=0 で出していたため had_error が立たず、
         * この診断だけが出る経路（パターンファイル側ディレクティブの式など）では
         * エラー表示ありで終了コード 0 になっていた。 */
        axx_diagf(1, 0, " error - Label undefined: '%s'  [%s:%d]\n",
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
/* ラベル定義の誤りを、1つにつき1回だけ必ず表示する。
 *
 * 破綻点修正: これらは had_error を立てながら通常の axx_diagf() で出していた。
 * しかし定義の衝突が見つかるのはパス1で、パス1の診断は抑制される。パス2では
 * 「既に在るラベル」に見えるので二度と検出されず、結果としてユーザには具体的な
 * 原因が一度も表示されないまま、
 * " error - one or more errors were reported during assembly" だけ、あるいは
 * （値がずれた場合）「パス1/パス2のアドレス不一致＝リラクゼーション未収束」という
 * 全く無関係なメッセージが出ていた。パス1の抑制を迂回して出す代わりに、
 * リラクゼーションの反復回数だけ重複しないよう、同じ誤りは1回に抑える。 */
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
    /* 破綻点修正: 固定長 char uk[512] へ無言で切り詰めていたため、511バイトを
     * 超える長さのラベル名同士が先頭511文字の一致だけで誤って衝突扱いになったり、
     * 逆に本来の衝突が511バイト以降の差異のせいで見逃されたりし得た。他の箇所
     * と同じく axx_word_buf() で必要なら収まらない分をヒープへ逃がす。 */
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
static void u256_to_pyhex(uint256_t a, char *out, size_t outsz){
    /* a is a 256-bit value, so buf can never hold more than 64 hex digits
     * (4 words x 16 hex digits via %llx/%016llx, both bounded by the 64-bit
     * width of unsigned long long); with the sign and "0x" prefix that is at
     * most 67 characters plus the terminator, well inside buf's 96 bytes.
     * GCC's -Wformat-truncation cannot prove that loop bound, hence the
     * diagnostic suppression above rather than an unbounded buffer. */
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
        char val[96];
        if(v[i]->is_undef) snprintf(val,sizeof(val),"UNDEF");
        else u256_to_pyhex(v[i]->value,val,sizeof(val));
        fprintf(stderr,"  %-40s  %s  (%s)\n",v[i]->key,val,v[i]->section);
    }
    free(v);
}

/* 配列シンボル（`.setsym::名前::[…]`）。定義は後方にある。 */
static struct ArrSym *arrsym_get(AsmState *st, const char *upper_name);

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

/* 破綻点修正(性能): 符号化欄は `@@[n,...]` の展開で要素数に比例して長くなる
 * 一方、要素ごとの評価は「文字列全体」に対して expr_terminate() の複製と
 * 各優先順位関数の strlen() を掛け直していたため、出力バイト数に対して
 * 二乗の時間が掛かっていた（axx.py は len() が O(1) なので線形）。
 * 評価の間だけ「この文字列の長さは既知で、二重 NUL 終端済み」と覚えておき、
 * 複製と再計測を省く。覚えている間その領域は解放されないので、別の割り当てが
 * 同じ番地を取ることはなく、値が古くなることはない。 */
static const char *g_expr_slen_ptr = NULL;
static int         g_expr_slen_len = 0;
static inline int expr_slen(const char *s){
    if(s == g_expr_slen_ptr) return g_expr_slen_len;
    return (int)strlen(s);
}

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
    asmb->st.expcaps=&CAPS_PAT;
    if(s == g_expr_slen_ptr) return expr_expression(asmb,s,idx,idx_out);
    char *ts=expr_terminate(s);
    uint256_t r=expr_expression(asmb,ts,idx,idx_out);
    free(ts);
    return r;
}
/* 能力記述子を指定して評価する。マクロ層・ミニ言語からの委譲用。 */
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
static uint256_t expr_expression_asm(Assembler *asmb, const char *s, int idx, int *idx_out){
    asmb->st.expmode=EXP_ASM;
    asmb->st.expcaps=&CAPS_ASM;
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
            /* 種類が不一致でも（例: "(...]"）深さは1段閉じたものとして扱う。
             * 型を厳密に照合してポップを拒否すると、不正な入力に対して
             * stkp が0に戻らなくなり、以降 stopchar を永久に見つけられなく
             * なってしまう（axx.py の expression_esc と同じ修正）。 */
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
    int slen=expr_slen(s);

    if(idx+4<=slen && strncmp(s+idx,"!!!!",4)==0 && st->expcaps->vliw){
        x=u256_from_i64(st->vliwstop); idx+=4;
        if(asmb->st.exp_typ_float) x=double_to_u256((double)st->vliwstop);
    } else if(idx+3<=slen && strncmp(s+idx,"!!!",3)==0 && st->expcaps->vliw){
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
        /* 破綻点修正: float 型式では x が IEEE754 の生ビットを保持しているため、
         * その生ビットに直接 u256_not() を掛けると axx.py の `~int(x)`（数値へ
         * 変換してから NOT する）と全く違う結果になっていた。<< / >> と同じ
         * expr_safe_bitwise_operand/expr_bitwise_result で整数域へ変換して
         * 演算する。 */
        x=expr_bitwise_result(asmb,u256_not(expr_safe_bitwise_operand(asmb,x,"~")));
    } else if(s[idx]=='@'){
        x=expr_factor(asmb,s,idx+1,&idx);
        /* 同上: nbit() は数値としてのビット長を求めるものなので、float 型式では
         * 生ビットではなく数値へ変換してから渡す(axx.py の nbit(x) と同じ)。 */
        int nb = op_msb(expr_safe_bitwise_operand(asmb,x,"@"));
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
                    /* 実装は共有関数 op_byte() 側。マクロ層も同じものを呼ぶ。 */
                    int neg = 0;
                    x = op_byte(x, x2, &neg);
                    if(neg && should_report_errors(st)){
                        axx_diagf(1, 0, " error - negative byte-extract offset in *(expr, expr).\n");
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
            /* 破綻点修正: ここで idx を '*' の次へ進めないと、呼び出し元の
             * 乗算ループ(term0)が同じ未消費の '*' を通常の乗算演算子として
             * 再度読み、"5+*x" のような壊れた式が 0 * <次の因子> という
             * 誤った値へ静かに縮退していた。エラー後は '*' を読み飛ばす。 */
            idx++;
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
    int slen=expr_slen(s);
    int _hexlit_val=0, _hexlit_end=idx;
    int _hexlit_ok = parse_hex_char_literal(s, idx, slen, &_hexlit_val, &_hexlit_end);
    /* .enum の式を評価している間だけ使う、列挙要素名の束縛。 */
    int _en_k=-1, _en_end=idx;
    int _vnl=0;   /* ここで読んだパターン変数名の長さ */

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
        /* `#x[3]` は配列シンボルの項目。添字は式で、0 から数える。 */
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
        while(s[idx]=='0'||s[idx]=='1'){
            x=u256_add(u256_mul(x,u256_from_u64(2)), u256_from_u64(s[idx]-'0'));
            idx++;
        }
        if(asmb->st.exp_typ_float)
            x=double_to_u256(u256_int_to_double(x));
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
            x=double_to_u256(u256_int_to_double(x));
    }
    else if(idx+3<=slen && strncmp(s+idx,"qad",3)==0 &&
            axx_next_nonspace_is_brace(s, slen, idx+3)){
        idx+=3;
        idx=axx_skipspc(s,idx);
        if(s[idx]=='{'){
            idx++;
            /* 破綻点修正: 以前は式本体を固定長 char[1024] に写していたため、
             * 1024 文字を超える式が診断もなく途中で切れ、axx.py（長さ制限なし）
             * と違う値になっていた。まず区切り位置だけを走査してから、
             * 実際の長さぶんだけ動的に確保する。 */
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
                /* 破綻点修正: 閉じ '}' が無いまま行末（や文字列末尾）に達した
                 * 場合、以前はそれを無視してそのまま式を評価し、黙って値を
                 * 出力していた（axx.py は "missing closing '}'" エラーで
                 * 中断する）。ここで揃える。 */
                if(should_report_errors(&asmb->st)){
                    axx_diagf(1, 0, " error - missing closing '}' in expression: '{%s'\n", expr_buf);
                }
                x=u256_zero();
                free(expr_buf);
            }
            else {
            idx++;
            if(en==0){
                /* 破綻点修正: 空の `qad{}` を、以前は評価器に一切通さず
                 * そのまま 0 として黙って成功させていた（axx.py は
                 * "cannot evaluate expression ''" エラーで中断する）。 */
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
                if(xeval_eval(asmb, expr_buf, &xv)){
                    char fstr[64]; snprintf(fstr,sizeof(fstr),"%.17g",xv);
                    x=ieee754_128_from_str(fstr);
                } else {
                    int io2;
                    int prev_flt=asmb->st.exp_typ_float;
                    int _prior_had_error=asmb->st.had_error;
                    DiagSuppress _sv;
                    asmb->st.exp_typ_float=1;
                    diag_suppress_begin(&asmb->st, &_sv);
                    uint256_t fv=expr_expression_pat(asmb,expr_buf,0,&io2);
                    int _inner_errs = asmb->st.diag_pending_len;
                    diag_suppress_end(&asmb->st, &_sv);
                    asmb->st.exp_typ_float=prev_flt;
                    int _fallback_errored = _inner_errs > 0
                                            || (asmb->st.had_error && !_prior_had_error);
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
            int io2; uint256_t iv=expr_expression_pat(asmb,t,0,&io2);
            asmb->st.exp_typ_float=prev_flt;
            double fval=enfloat_bits(u256_to_u64(iv));
            /* 破綻点修正: 常に double_to_u256()（ビットキャスト）を格納していたため、
             * 整数モードの文脈では IEEE754 のビット列そのものが整数として読まれ、
             * 例えば enflt{0x3f800000}（=1.0）が 0x3FF0000000000000 の下位バイト、
             * すなわち 0 になっていた（axx.py は 1 を返す）。
             * dbl{}/flt{} で既に使っている規約に合わせ、浮動小数点モードのときだけ
             * ビットキャストし、整数モードでは数値そのものを切り捨てて格納する。
             * 非有限値は (int64_t) キャストが未定義動作なので 0 に倒す。 */
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
            int io2; uint256_t iv=expr_expression_pat(asmb,t,0,&io2);
            asmb->st.exp_typ_float=prev_flt;
            double fval=endouble_bits(u256_to_u64(iv));
            /* 破綻点修正: enflt{} と同じ問題。上のコメントを参照。 */
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
            /* 破綻点修正: 空の `dbl{}` を xeval_eval("") が「空式=0.0」として
             * 黙って成功させていた（axx.py の ast.parse は空式を構文エラーと
             * するので "cannot convert expression" エラーで中断する）。 */
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
                if(xeval_eval(asmb, t, &xv)){
                    memcpy(&bits,&xv,8);
                } else {
                    int prev_flt = asmb->st.exp_typ_float;
                    int _prior_had_error = asmb->st.had_error;
                    DiagSuppress _sv;
                    asmb->st.exp_typ_float = 1;
                    diag_suppress_begin(&asmb->st, &_sv);
                    int io2; uint256_t fv = expr_expression_pat(asmb,t,0,&io2);
                    int _inner_errs = asmb->st.diag_pending_len;
                    diag_suppress_end(&asmb->st, &_sv);
                    asmb->st.exp_typ_float = prev_flt;
                    int _fallback_errored = _inner_errs > 0
                                            || (asmb->st.had_error && !_prior_had_error);
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
            /* 破綻点修正: dbl{} と同じ問題。上のコメントを参照。 */
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
                if(xeval_eval(asmb, t, &xv)){
                    float v = (float)xv;
                    memcpy(&bits,&v,4);
                } else {
                    int prev_flt = asmb->st.exp_typ_float;
                    int _prior_had_error = asmb->st.had_error;
                    DiagSuppress _sv;
                    asmb->st.exp_typ_float = 1;
                    diag_suppress_begin(&asmb->st, &_sv);
                    int io2; uint256_t fv = expr_expression_pat(asmb,t,0,&io2);
                    int _inner_errs = asmb->st.diag_pending_len;
                    diag_suppress_end(&asmb->st, &_sv);
                    asmb->st.exp_typ_float = prev_flt;
                    int _fallback_errored = _inner_errs > 0
                                            || (asmb->st.had_error && !_prior_had_error);
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
        /* 128bit(四倍精度)を正しく往復させるには仮数部だけで最大36桁前後
         * 要る。旧来の64バイトだと、仮数部だけでバッファが埋まった場合に
         * 指数部を書き込む余地が無くなり、idx はその先まで正しく進んでも
         * strtod に渡る文字列からは指数だけ丸ごと消えてしまっていた
         * （桁落ちではなく桁ごと消える誤り）。余裕を持って96バイト。 */
        char fs[96];
        idx=axx_get_floatstr(s,idx,fs,sizeof(fs));
        if(fs[0]) x=double_to_u256(strtod(fs,NULL));
    }
    else if(is_digit(s[idx])){
        /* 2**256 は10進78桁なので、正当な256bit値を丸ごと収めるには
         * 64バイトでは足りない（axx.py は無制限精度）。余裕を持って128バイト。 */
        char fs[128];
        idx=axx_get_intstr(s,idx,fs,sizeof(fs));
        x=u256_zero();
        uint256_t ten=u256_from_u64(10);
        for(int di=0;fs[di];di++) x=u256_add(u256_mul(x,ten),u256_from_u64((uint64_t)(fs[di]-'0')));
    }
    /* .enum の式の中では、列挙要素名はその束縛値として読む。`#name` は
     * これより前の枝で処理されるので、そちらは素の .setsym 値になる。 */
    else if(st->enum_bind_names
            && (_en_k=enum_name_at(s, idx, st->enum_bind_names, &_en_end)) >= 0){
        x = st->enum_bind_vals[_en_k];
        idx = _en_end;
    }
    /* パターン変数は「小文字で始まる名前で、直後がラベル構成文字でない」とき。
     * 長さは問わず、`a` も `var_2` も同じ規則でラベルより先にここで読む。
     * 直後の文字を見るのは、`aB` や `a.b` のようにラベル構成文字（大文字や
     * `.`）が続く綴りをラベルとして残すためである。
     * 捕捉も代入もされていない名前にはスロットが無いので、値は 0 になる。 */
    else if(st->expcaps->patvars
            && (_vnl = var_name_len(s+idx)) > 0
            && (s[idx+_vnl]=='\0' || !char_in(s[idx+_vnl], st->lwordchars))){
        /* 場所を作るのは代入のときだけ。読むだけの名前は増やさない。 */
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
            /* 破綻点修正: 通常(整数)モードで束縛されたパターン変数を
             * 浮動小数点モードの式（.error の error_patterns 等）で
             * そのまま読むと、後続の演算子が u256_to_double() で
             * 「整数のビット列」を無変換で「doubleのビット列」として
             * 再解釈してしまい、桁の大きい値の比較・算術が意味不明な
             * 結果になっていた（axx.py はPythonのint/float混在比較・
             * 算術がそもそも精度を失わないため、この問題が起きない）。
             * is_float タグを見て、整数のまま束縛された値だけ、ここで
             * 数値としてdoubleへ変換する。 */
            x=var_slot_for_mode(st,vslot,asmb->st.exp_typ_float);
            idx+=_vnl;
            if(!st->in_match_attempt
               && !st->pass1_size_mode
               && should_report_errors(st)){
                /* 破綻点修正: 束縛時に付けたタグ(var_get_is_undef)だけを見ていたため、
                 * 「ラベル自体は定義されているが、その値が未定義由来」という場合を
                 * 取りこぼしていた。例: `L: .equ NOSUCH` は L を定義するが値は
                 * UNDEF 由来になる。`!x` が L に束縛されてもラベル検索自体は成功して
                 * いるのでタグは付かず、結果として 0xff 等のゴミを黙って生成していた
                 * （axx.py は値そのものを _is_undef_derived() で見るので検出できる）。
                 * axx.py と同じく値も検査する。 */
                if(var_slot_is_undef(st, vslot) || u256_is_undef_derived(x)){
                    st->error_undefined_label = 1;
                    axx_diagf(0, 0, " error - Label undefined: variable '%s' contains undefined value"
                               "  [%s:%d]\n",
                               var_slot_name(vslot), st->current_file, (int)st->ln);
                }
            }
            if(st->elf_tracking && st->elf_current_word_idx >= 0){
                int _vi = vslot;
                if(_vi >= 0 && _vi < g_nvars && st->elf_var_to_label[_vi].set == 1){
                    if(st->elf_refs_len >= st->elf_refs_cap){
                        st->elf_refs_cap = st->elf_refs_cap ? st->elf_refs_cap*2 : 8;
                        st->elf_refs = realloc(st->elf_refs,
                            st->elf_refs_cap * sizeof(st->elf_refs[0]));
                        if(!st->elf_refs){ perror("realloc"); exit(1); }
                    }
                    st->elf_refs[st->elf_refs_len].name     = strdup(st->elf_var_to_label[_vi].label_name);
                    st->elf_refs[st->elf_refs_len].val      = st->elf_var_to_label[_vi].label_val;
                    st->elf_refs[st->elf_refs_len].word_idx = st->elf_current_word_idx;
                    st->elf_refs[st->elf_refs_len].rtype    = st->reloc_constraints[_vi];
                    /* 加数は「変数が持っていた値 − ラベル値」。`bl func` なら 0、
                     * `bl func+8` なら 8。命令語のビット欄を逆算しなくて済むので、
                     * 欄の分割や語単位の縮尺に左右されない。 */
                    st->elf_refs[st->elf_refs_len].addend   =
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
            if(asmb->st.exp_typ_float && !st->error_undefined_label)
                x=double_to_u256(u256_int_to_double(x));
        }
        if(w!=wbuf) free(w);
    }

    idx=axx_skipspc(s,idx);
    *idx_out=idx;
    return x;
}

static uint256_t expr_term0_0(Assembler *asmb, const char *s, int idx, int *idx_out){
    uint256_t x=expr_factor(asmb,s,idx,&idx);
    int slen=expr_slen(s);
    while(idx<slen && axx_q(s,slen,"**",idx)){
        uint256_t t=expr_factor(asmb,s,idx+2,&idx);
        if(asmb->st.exp_typ_float){
            double a=u256_to_double(x), b=u256_to_double(t);
            x=double_to_u256(pow(a,b));
        } else {
            const int64_t EXP_MAX = 1024;
            /* axx.py の _EXP_RESULT_MAX_BITS ( _UNDEF_SANE_CEILING(1<<256).bit_length()-1 )
             * に合わせる。1<<20 のままだと base_bits(<=256)*exp_factor(<=1024) が
             * 構造的にこの上限を超えられず、桁溢れ検出が常に不発になっていた。 */
            const int64_t EXP_RESULT_MAX_BITS = 256;
            if(u256_is_neg256(t)){
                if(should_report_errors(&asmb->st)){
                    axx_diagf(1, 0, " error - Negative exponent in ** expression; result set to 0.\n");
                }
                x = u256_zero();
                break;
            }
            if(u256_nonneg_gt_i64(t, EXP_MAX)){
                if(should_report_errors(&asmb->st)){
                    char _ec[96]; u256_to_pydec(t, _ec, sizeof(_ec));
                    axx_diagf(1, 0, " error - Exponent %s exceeds maximum %lld in ** expression; result set to 0.\n", _ec, (long long)EXP_MAX);
                }
                x = u256_zero();
                break;
            }
            int64_t t_int = u256_to_i64(t);
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
    int slen=expr_slen(s);
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
    int slen=expr_slen(s);
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
    int slen=expr_slen(s);
    const int64_t SHIFT_MAX = 65536;
    while(idx<slen){
        if(axx_q(s,slen,"<<",idx)){
            uint256_t t=expr_term1(asmb,s,idx+2,&idx);
            uint256_t sop=expr_safe_bitwise_operand(asmb,t,"<<");
            if(u256_is_neg256(sop)){
                /* 破綻点修正: シフト量を %lld へ切り詰めて表示していたため、
                 * 64bit に収まらない値が別の数（や 0）として報告されていた。
                 * axx.py と同じく元の値をそのまま出す。 */
                char _sc[96]; u256_to_pydec(sop, _sc, sizeof(_sc));
                if(should_report_errors(&asmb->st)){
                    axx_diagf(1, 0, " error - negative shift count (%s) in << expression.\n", _sc);
                }
                /* 破綻点修正: エラー後もループを続けていたため、axx.py（ここで
                 * 打ち切る）には出ない後続の診断まで余計に出ていた。 */
                x=u256_zero(); break;
            } else if(u256_nonneg_gt_i64(sop,SHIFT_MAX)){
                char _sc[96]; u256_to_pydec(sop, _sc, sizeof(_sc));
                if(should_report_errors(&asmb->st)){
                    axx_diagf(1, 0, " error - shift count %s exceeds maximum %lld in << expression.\n", _sc, (long long)SHIFT_MAX);
                }
                x=u256_zero(); break;
            } else x=expr_bitwise_result(asmb,u256_shl(expr_safe_bitwise_operand(asmb,x,"<<"),(int)u256_to_i64(sop)));
        } else if(axx_q(s,slen,">>",idx)){
            uint256_t t=expr_term1(asmb,s,idx+2,&idx);
            uint256_t sop=expr_safe_bitwise_operand(asmb,t,">>");
            if(u256_is_neg256(sop)){
                /* 破綻点修正: シフト量を %lld へ切り詰めて表示していたため、
                 * 64bit に収まらない値が別の数（や 0）として報告されていた。
                 * axx.py と同じく元の値をそのまま出す。 */
                char _sc[96]; u256_to_pydec(sop, _sc, sizeof(_sc));
                if(should_report_errors(&asmb->st)){
                    axx_diagf(1, 0, " error - negative shift count (%s) in >> expression.\n", _sc);
                }
                /* 破綻点修正: エラー後もループを続けていたため、axx.py（ここで
                 * 打ち切る）には出ない後続の診断まで余計に出ていた。 */
                x=u256_zero(); break;
            } else if(u256_nonneg_gt_i64(sop,SHIFT_MAX)){
                char _sc[96]; u256_to_pydec(sop, _sc, sizeof(_sc));
                if(should_report_errors(&asmb->st)){
                    axx_diagf(1, 0, " error - shift count %s exceeds maximum %lld in >> expression.\n", _sc, (long long)SHIFT_MAX);
                }
                x=u256_zero(); break;
            } else x=expr_bitwise_result(asmb,u256_sar(expr_safe_bitwise_operand(asmb,x,">>"),(int)u256_to_i64(sop)));
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
    int slen=expr_slen(s);
    while(idx<slen && s[idx]=='&' && s[idx+1]!='&'){
        uint256_t t=expr_term2(asmb,s,idx+1,&idx);
        x=expr_bitwise_result(asmb,u256_and(expr_safe_bitwise_operand(asmb,x,"&"),expr_safe_bitwise_operand(asmb,t,"&")));
    }
    *idx_out=idx; return x;
}

static uint256_t expr_term4(Assembler *asmb, const char *s, int idx, int *idx_out){
    uint256_t x=expr_term3(asmb,s,idx,&idx);
    int slen=expr_slen(s);
    while(idx<slen && s[idx]=='|' && s[idx+1]!='|'){
        uint256_t t=expr_term3(asmb,s,idx+1,&idx);
        x=expr_bitwise_result(asmb,u256_or(expr_safe_bitwise_operand(asmb,x,"|"),expr_safe_bitwise_operand(asmb,t,"|")));
    }
    *idx_out=idx; return x;
}

static uint256_t expr_term5(Assembler *asmb, const char *s, int idx, int *idx_out){
    uint256_t x=expr_term4(asmb,s,idx,&idx);
    int slen=expr_slen(s);
    while(idx<slen && s[idx]=='^'){
        uint256_t t=expr_term4(asmb,s,idx+1,&idx);
        x=expr_bitwise_result(asmb,u256_xor(expr_safe_bitwise_operand(asmb,x,"^"),expr_safe_bitwise_operand(asmb,t,"^")));
    }
    *idx_out=idx; return x;
}

static uint256_t expr_term6(Assembler *asmb, const char *s, int idx, int *idx_out){
    uint256_t x=expr_term5(asmb,s,idx,&idx);
    int slen=expr_slen(s);
    while(idx<slen && s[idx]=='\''){
        int ni=idx+1; ni=axx_skipspc(s,ni);
        if(ni>=slen||((s[ni]<'0'||s[ni]>'9')&&s[ni]!='(')) break;
        uint256_t t=expr_term5(asmb,s,idx+1,&idx);
        /* 実装は共有関数 op_sext() 側。マクロ層も同じものを呼ぶ。 */
        int warn = 0;
        x = op_sext(x, t, &warn);
        if(warn && should_report_errors(&asmb->st)){
            char cb[96]; u256_to_pydec(t, cb, sizeof(cb));
            axx_diagf(0, 0, " warning - sign-extension bit width %s exceeds maximum %d, result set to 0.\n",
                       cb, SEXT_MAX_BITS);
        }
    }
    *idx_out=idx; return x;
}

static uint256_t expr_term7(Assembler *asmb, const char *s, int idx, int *idx_out){
    uint256_t x=expr_term6(asmb,s,idx,&idx);
    int slen=expr_slen(s);
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

/* 破綻点修正: `&&` / `||` を短絡評価していたが、axx.py は必ず両辺を評価する
 * （`x = 1 if x and t else 0`）。式には `a:=...` の代入や、パス2の ELF
 * リロケーション収集（ラベル参照の記録）といった副作用があるため、右辺を
 * 読み飛ばすと生成コードが変わってしまう。両辺を評価する形に揃える。 */
static uint256_t expr_term9(Assembler *asmb, const char *s, int idx, int *idx_out){
    uint256_t x=expr_term8(asmb,s,idx,&idx);
    int slen=expr_slen(s);
    while(idx<slen && axx_q(s,slen,"&&",idx)){
        uint256_t t=expr_term8(asmb,s,idx+2,&idx);
        x=u256_from_i64((!u256_is_zero(x) && !u256_is_zero(t))?1:0);
    }
    *idx_out=idx; return x;
}

static uint256_t expr_term10(Assembler *asmb, const char *s, int idx, int *idx_out){
    uint256_t x=expr_term9(asmb,s,idx,&idx);
    int slen=expr_slen(s);
    while(idx<slen && axx_q(s,slen,"||",idx)){
        uint256_t t=expr_term9(asmb,s,idx+2,&idx);
        x=u256_from_i64((!u256_is_zero(x) || !u256_is_zero(t))?1:0);
    }
    *idx_out=idx; return x;
}


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

static int skip_ternary_expr_d(const char *s, int idx, int depth) {
    /* 破綻点修正: 深くネストした三項式の偽側を読み飛ばす再帰に上限が無く、
     * expr_factor の EXPR_MAX_DEPTH ガードも経由しないため、巨大な連鎖
     * `?:` でCスタックオーバーフローしうる。expr_factor と同じ上限で止める。 */
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
static int skip_ternary_expr(const char *s, int idx) {
    return skip_ternary_expr_d(s, idx, 0);
}

static uint256_t expr_term11(Assembler *asmb, const char *s, int idx, int *idx_out){
    AsmState *st = &asmb->st;
    uint256_t x = expr_term10(asmb, s, idx, &idx);
    int slen = expr_slen(s);
    if(idx < slen && axx_q(s, slen, "?", idx)){
        /* 破綻点修正: 連鎖した `?:` の再帰は expr_factor を経由しないため
         * EXPR_MAX_DEPTH の深さガードが効かず、巨大な連鎖式でCスタック
         * オーバーフローしうる。expr_factor と同じカウンタを共有して防ぐ。 */
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
            /* 破綻点修正: 真側を expr_term10 で解析していたため、
             * `c1 ? c2 ? a : b : d` のような括弧なしの入れ子三項が
             * axx.py（真側も term11 で解析する）と違う結び付きになっていた。 */
            x = expr_term11(asmb, s, idx, &idx);
            idx = axx_skipspc(s, idx);
            if(axx_q(s, slen, ":", idx) && s[idx+1] != '='){
                /* 偽側は評価しない。skip_ternary_expr() は字面を追うだけで
                 * 副作用が無いので、変数や旗の退避・復元は要らない。 */
                idx = skip_ternary_expr(s, axx_skipspc(s, idx + 1));
            }
        }
        st->expr_depth--;
    }
    *idx_out = idx;
    return x;
}

static uint256_t expr_expression(Assembler *asmb, const char *s, int idx, int *idx_out){
    idx=axx_skipspc(s,idx);
    return expr_term11(asmb,s,idx,idx_out);
}

/* 文字列シンボル（`.setsym::名前::"文字列"`）。定義は後方にある。 */
static void        strsym_set(AsmState *st, const char *upper_name, const char *val);
static void        strsym_delete(AsmState *st, const char *upper_name);
static const char *strsym_get(AsmState *st, const char *upper_name);
static char       *txt_template_inner(const char *q);
/* 配列シンボル（`.setsym::名前::[…]`）。定義は後方にある。 */
static void        arrsym_set_from_text(Assembler *asmb, const char *upper_name, const char *q);
static void        arrsym_delete(AsmState *st, const char *upper_name);
static void        arrsym_clear_all(AsmState *st);
static int         symbol_copy_from_name(AsmState *st, const char *dst_upper, const char *value_field);
/* 集合（`.setsym::a::a1,a2,a3` / `.setsym::x::a&b`）。定義は後方にある。 */
static int         symbol_set_from_text(AsmState *st, const char *dst_upper, const char *value_field);

static int dir_set_symbol(Assembler *asmb, PatEntry *e){
    if(!e||strcmp(e->f[0],".setsym")!=0) return 0;
    const char *name_field = e->f[1][0] ? e->f[1] : e->f[2];
    const char *value_field = e->f[1][0] ? e->f[2] : "";
    char key[512]; axx_strupr_to(key,name_field,sizeof(key));
    /* 値が `"..."` なら文字列シンボル、`[...]` なら配列シンボル。 */
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
        /* `.setsym::y::x` — x が文字列／配列シンボルなら、その写しを作る。 */
        if(symbol_copy_from_name(&asmb->st, key, value_field)) return 1;
        /* `名前,名前,…` は名前の集合、`a&b` などは集合どうしの演算。 */
        if(symbol_set_from_text(&asmb->st, key, value_field)) return 1;
    }
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

/* `.bits[::<big|little>][::<幅>]`
 *
 * 破綻点修正1: 以前は endian_big を無条件に
 *   `strcasecmp(f[1],"big")==0`
 * で上書きしていたため、エンディアン欄を書かない2欄形式（`.bits::16`、
 * このとき f[1] は空）が来るたびにビッグエンディアン指定が黙って
 * リトルに戻っていた（axx.py はエンディアン欄が big/little のときしか
 * 変更しないので、同じパターンファイルで両者のバイト順が食い違う）。
 * 欄が big/little のときだけ設定する。
 *
 * 破綻点修正2: 幅の検証が無く、`.bits::big`（幅を書き忘れた形。この形では
 * "big" が f[2] に入る）だと "big" をラベルとして評価しようとして未定義
 * ラベルになり、そのゴミ値がワード幅になっていた。1〜64 の範囲を検証し、
 * 外れていたらエラーにして従来の幅を保つ。 */
static int dir_bits(Assembler *asmb, PatEntry *e){
    if(!e||strcmp(e->f[0],".bits")!=0) return 0;

    /* 破綻点修正: 欄の意味を位置（第1欄=エンディアン,第2欄=幅）で固定していた
     * ため、`.bits::<幅>::<big|little>`（順序が逆）を書くと幅の値が捨てられた
     * 上で診断なしにエンディアンだけが適用されていた（axx.py の bits() と
     * 同じ問題を移植時に作り込んでいた）。位置ではなく内容('big'/'little'か
     * どうか)でフィールドの役割を判定し、順序に依らず両方正しく解釈する。 */
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
            axx_diagf(1, 0, " error - .bits: word width must be an integer in 1..64, got '%s'.\n", wf);
        } else {
            asmb->st.bts = (int)nb;
        }
        asmb->st.error_undefined_label = 0;
    }
    return 1;
}

static int dir_padding(Assembler *asmb, PatEntry *e){
    if(!e||strcmp(e->f[0],".padding")!=0) return 0;
    /* axx.py と同じく f[2] を優先し、空なら f[1] を見る。 */
    const char *pf = e->f[2][0] ? e->f[2] : (e->f[1][0] ? e->f[1] : "");
    int io;
    uint256_t v = pf[0] ? expr_expression_pat(asmb,pf,0,&io) : u256_zero();
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

    /* 破綻点修正: vliwbits/vliwinstbits/vliwtemplatebits を範囲検証なしに
     * int へ切り詰めていた。2^32 の倍数だけずれた値は int へのキャストで
     * 別の（たまたま範囲内に見える）値に化けて検証をすり抜けてしまい、
     * さらに vliwbits/vliwtemplatebits が INT_MIN だと vliwprocess() 側の
     * 符号反転(-vliwbits)が未定義動作になり得た。dir_bits と同じ
     * 「256bit値への往復チェック」で切り詰め前の値を検証してから代入する。 */
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

static int dir_epic(Assembler *asmb, PatEntry *e){
    if(!e) return 0;
    char uf[16]; axx_strupr_to(uf,e->f[0],sizeof(uf));
    if(strcmp(uf,"EPIC")!=0) return 0;
    if(!e->f[1][0]) return 0;
    const char *s=e->f[1];
    int idx=0;
    /* 破綻点修正: int idxs[64] の固定長で、65 個目以降を診断もなく捨てていた。
     * axx.py には個数の制限が無いので、スロットの組み合わせが一致せず
     * 「No vliw instruction-set defined.」になったり別のテンプレートが選ばれたり
     * していた。要素数はカンマの数で上限が決まるので、そのぶん確保する。 */
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

/* ディレクティブの変数欄を読む。1文字でも `var_2` のように長くてもよい。
 * 名前全体を使い切っていなければ -1（綴りの誤り）。 */
static int dir_var_slot(const char *field){
    const char *p = field;
    while(*p==' '||*p=='\t') p++;
    char lower[64]; int n = 0;
    while(*p && n < (int)sizeof(lower)-1 && !(*p==' '||*p=='\t'))
        lower[n++] = (char)tolower((unsigned char)*p++);
    lower[n] = '\0';
    while(*p==' '||*p=='\t') p++;
    if(*p || n == 0) return -1;
    if(var_name_len(lower) != n) return -1;
    return var_slot(lower, n, 1);
}

/* 要素の列挙欄（`.check` `.enum` `.map` の「名前の並び」）を項目に切る。
 * 項目が配列シンボルの名前なら、その内容をその場に展開する。つまり
 *   .setsym::regs::["R0","R1","R2"]
 *   .check::x::regs
 * は `.check::x::R0,R1,R2` と同じ意味になる。配列と素の名前は混ぜて書ける。
 * 名前は大文字化して積み、`""` `''`（省略可の印）と空欄は長さ0の項目にする。 */
static void elem_list_expand(AsmState *st, const char *text, StrVec *out){
    const char *p = text;
    while(*p){
        while(*p == ' ' || *p == '\t') p++;
        char buf[512]; int j = 0;
        while(*p && *p != ',' && j < (int)sizeof(buf)-1) buf[j++] = axx_upper_char(*p++);
        while(*p && *p != ',') p++;
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
                        char up[512]; axx_strupr_to(up, ar->items[k].s, sizeof(up));
                        sv_push(out, up);
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
}

static int dir_check(Assembler *asmb, PatEntry *e){
    if(!e || strcmp(e->f[0], ".check") != 0) return 0;
    const char *var_str  = e->f[1][0] ? e->f[1] : e->f[2];
    const char *syms_str = e->f[1][0] ? e->f[2] : "";
    if(!var_str[0]){
        axx_diagf(1, 0, " error - .check: variable name is not specified.\n");
        return 1;
    }
    int idx = dir_var_slot(var_str);
    if(idx < 0){
        axx_diagf(1, 0, " error - .check: variable should be a lower case name ('%s').\n",
                   var_str);
        return 1;
    }
    sv_free(&asmb->st.check_constraints[idx]);
    sv_init(&asmb->st.check_constraints[idx]);
    StrVec elems; sv_init(&elems);
    elem_list_expand(&asmb->st, syms_str, &elems);
    for(int ei = 0; ei < elems.len; ei++){
        const char *nm = elems.data[ei];
        if(!nm[0]){
            /* 空文字リテラルは「このオペランドは省略可」の印。
               省略時、変数には 0 が入る。長さ0の要素として積む。 */
            int dup = 0;
            for(int si = 0; si < asmb->st.check_constraints[idx].len; si++)
                if(asmb->st.check_constraints[idx].data[si][0] == '\0'){ dup = 1; break; }
            if(!dup) sv_push(&asmb->st.check_constraints[idx], "");
        } else {
            sv_push(&asmb->st.check_constraints[idx], nm);
        }
    }
    sv_free(&elems);
    return 1;
}

/* 未知の型名を報告済みか。報告済みなら 1。パターン行は1ソース行ごとに
 * 読み直されるため、これが無いと同じ診断が何度も出る。 */
static int reloc_badname_seen(AsmState *st, const char *name){
    for(int i = 0; i < st->reloc_badname_len; i++)
        if(strcmp(st->reloc_badname[i], name) == 0) return 1;
    if(st->reloc_badname_len < (int)(sizeof(st->reloc_badname)/sizeof(st->reloc_badname[0])))
        st->reloc_badname[st->reloc_badname_len++] = strdup(name);
    return 0;
}

/* `.reloc::<変数>::<型名>`
 *
 * その変数が捕らえたラベル参照を、指定の ELF リロケーション型で書き出す。
 * `.check` と同じく位置依存で、後の `.reloc` が前のものを置き換える。
 *
 * 型名は `-m` で選んだマシンの名前表（`::pc32` などに使うものと同じ）から引く。
 * AArch64 の `call26` のような命令フィールド型は、値が命令語のビット欄に詰まって
 * いて出力バイト列から加数を逆算できないため、この宣言が要る。 */
static int dir_reloc(Assembler *asmb, PatEntry *e){
    if(!e || strcmp(e->f[0], ".reloc") != 0) return 0;
    const char *var_str  = e->f[1][0] ? e->f[1] : e->f[2];
    const char *type_str = e->f[1][0] ? e->f[2] : "";
    if(!var_str[0]){
        axx_diagf(1, 0, " error - .reloc: variable name is not specified.\n");
        return 1;
    }
    int idx = dir_var_slot(var_str);
    if(idx < 0){
        axx_diagf(1, 0, " error - .reloc: variable should be a lower case name ('%s').\n",
                   var_str);
        return 1;
    }
    char tname[64]; size_t tn = 0;
    for(const char *q = type_str; *q && tn + 1 < sizeof(tname); q++){
        if(*q == ' ' || *q == '\t') continue;
        tname[tn++] = (char)tolower((unsigned char)*q);
    }
    tname[tn] = '\0';
    if(!tname[0]){
        axx_diagf(1, 0, " error - .reloc: relocation type is not specified.\n");
        return 1;
    }
    /* リロケーションは `-o` の ELF 出力にしか現れない。`-b` などでは宣言は
     * 無意味なので、型名を照合せずに受け流す。パターンファイルは複数の `-m`
     * で使い回せるべきで、対象外のときに落ちてはいけない。 */
    if(!asmb->st.elf_objfile[0]) return 1;
    const ElfMachineInfo *m = elf_machine_find(asmb->st.elf_machine);
    int rtype = elf_machine_named(m, tname);
    if(rtype < 0){
        /* パターン行は1ソース行ごとに読み直されるので、同じ名前で何度も
         * 出さないよう一度だけ報告する。 */
        if(!reloc_badname_seen(&asmb->st, tname))
            axx_diagf(1, 0, " error - .reloc: unknown relocation type '%s' for %s.\n",
                       tname, m ? m->name : "?");
        return 1;
    }
    asmb->st.reloc_constraints[idx] = rtype;
    return 1;
}

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
        sv_free(&asmb->st.check_constraints[idx]);
        sv_init(&asmb->st.check_constraints[idx]);
    } else {
        for(int i = 0; i < g_nvars; i++){
            sv_free(&asmb->st.check_constraints[i]);
            sv_init(&asmb->st.check_constraints[i]);
        }
    }
    return 1;
}

/* `.free::名前,名前,…`
 * その名前を、パターン層のあらゆる表から外す。置き場所ごとに
 * `.clearsym` `.clrcheck` `.clrenum` と書き分けなくても、名前ひとつで
 * 「もうこの名前は使わない」と宣言できるようにするためのもの。外すのは
 *   - `.setsym` の数値シンボル・文字列シンボル・配列シンボル
 *   - `.sub` の表
 *   - `.check` の候補（どの変数の一覧に入っていても取り除く）
 *   - 名前が小文字1文字なら、その変数の `.check` と `.enum` ごと
 * で、`.clearsym` などと同じく書かれた位置から先に効く。 */
static void free_one_name(Assembler *asmb, const char *name){
    AsmState *st = &asmb->st;
    if(!name[0]) return;
    char key[512]; axx_strupr_to(key,name,sizeof(key));

    smap_delete(&st->symbols, key);
    strsym_delete(st, key);
    arrsym_delete(st, key);
    subv_mark_freed(&st->subs, name);

    /* `.check` の候補からも外す。候補は大文字で積まれている。 */
    for(int vi=0; vi<g_nvars; vi++){
        StrVec *cv = &st->check_constraints[vi];
        int w = 0;
        for(int k=0; k<cv->len; k++){
            if(strcmp(cv->data[k], key)==0){ free(cv->data[k]); continue; }
            cv->data[w++] = cv->data[k];
        }
        cv->len = w;
    }

    /* 名前が変数そのものなら、その変数の制約と列挙ごと外す。 */
    {
        char lower[64]; int n = 0;
        for(const char *q = name; *q && n < (int)sizeof(lower)-1; q++)
            lower[n++] = (char)tolower((unsigned char)*q);
        lower[n] = '\0';
        if(var_name_len(lower) == n){
            int vi = var_slot(lower, n, 0);
            if(vi >= 0){
                sv_free(&st->check_constraints[vi]); sv_init(&st->check_constraints[vi]);
                st->reloc_constraints[vi] = 0;
                enumdef_clear(&st->enum_defs[vi]);
            }
        }
    }
}

/* 定義は後方にある。 */
static char *pat_trim(char *s);
static char *map_subst_index(const char *expr, const char *var, int i);

/* `.map::<変数>::<名前の並び>::<式>`
 * 並びの各名前に値を与える `.setsym` と、その変数の `.check` をまとめて書く
 * ための省略形。式の中の変数は「その名前が並びの何番目か」(0 から数える)。
 *
 *   .map::x::R0,R1,R2::1<<x
 * は
 *   .setsym::R0::1<<(0)
 *   .setsym::R1::1<<(1)
 *   .setsym::R2::1<<(2)
 *   .check::x::R0,R1,R2
 * と等価である。式を省くと変数そのもの、すなわち 0 からの連番になる。
 * 並びには配列シンボルの名前を書ける（elem_list_expand() が展開する）。
 *
 * into が非NULLならシンボルはそこへ、NULLなら st->symbols へ入れる。
 * set_check が真なら `.check` も設定する。 */
/* 文字列を最上位のカンマで切る。括弧の中のカンマは区切りにしない
 * （`*(x,1)` のような式がそのまま1項目になるようにするため）。深さの数え方は
 * expr_expression_esc() と同じで、閉じ括弧の種類は厳密に照合しない。
 * axx.py の split_top_commas() と同じ規則である。 */
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
    /* 値欄が最上位のカンマで区切られていれば、並びと1対1の値のリスト。
     * 1項目しか無ければ従来どおり「変数を含む式」1本として扱う。 */
    StrVec vals; sv_init(&vals);
    split_top_commas(expr_str, &vals);
    if(vals.len > 1 && vals.len != elems.len){
        axx_diagf(1, 0, " error - .map: the value list has %d items "
                        "but the name list has %d.\n", vals.len, elems.len);
        sv_free(&vals); sv_free(&elems);
        return;
    }
    for(int i = 0; i < elems.len; i++){
        /* 空の要素（`""` の省略可印など）は番号だけ消費して何も定義しない。 */
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
        sv_free(&st->check_constraints[idx]);
        sv_init(&st->check_constraints[idx]);
        for(int i = 0; i < elems.len; i++){
            if(!elems.data[i][0]){
                int dup = 0;
                for(int si = 0; si < st->check_constraints[idx].len; si++)
                    if(st->check_constraints[idx].data[si][0] == '\0'){ dup = 1; break; }
                if(!dup) sv_push(&st->check_constraints[idx], "");
            } else {
                sv_push(&st->check_constraints[idx], elems.data[i]);
            }
        }
    }
    sv_free(&elems);
}

static int dir_map(Assembler *asmb, PatEntry *e){
    if(!e || strcmp(e->f[0], ".map") != 0) return 0;
    map_apply(asmb, e, NULL, 1);
    return 1;
}

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

/* `.enum::<変数>::<要素名の並び>::<式>`
 * `!E<変数>` が拾う「要素名のリスト」の語彙と、そこから値を作る式を決める。
 * 式の中では各要素名が「そのリストに現れていれば .setsym の値、
 * 現れていなければ 0」に束縛される。 */
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
    asmb->st.enum_defs[idx].names = names;   /* 所有権を移す */
    asmb->st.enum_defs[idx].expr  = strdup(expr_str);
    if(!asmb->st.enum_defs[idx].expr){ perror("strdup"); exit(1); }
    return 1;
}

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

/* `.error::n::"Message"` — error_patterns 欄（`n>7;5` の `5` のような
 * エラーコード）に対応するメッセージ文字列を errors テーブルに登録する。
 * 組み込みの ERRORS_TABLE が文言を持たないコード（4 や 7 以上）にも
 * 新しくメッセージを追加できるし、既存コード（1・2・3・5・6）の文言を
 * 上書きすることもできる。n がテーブルの現在の大きさを超える場合は
 * 空文字列で埋めて拡張する（axx.py の errmsg_processing と対応）。 */
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
    /* エラーコードは errors StrVec の添字として (int) にキャストされ、
     * 添字ぶんだけ空文字列で埋めて伸長する。上限を設けないと、
     * INT_MAX を超える値がキャストで負値に化けて配列外アクセスになったり、
     * 巨大な正値が数十億要素の伸長でハング/OOM したりする。 */
    #define AXX_ERROR_CODE_MAX 1000000
    if(st->error_undefined_label || u256_is_undef_derived(n)
       || n_int < 0 || n_int > AXX_ERROR_CODE_MAX || !u256_eq(n, u256_from_i64(n_int))){
        axx_diagf(1, 0, " error - .error: error code must be a non-negative integer (0-%d), got '%s'.\n", AXX_ERROR_CODE_MAX, n_field);
        st->error_undefined_label = 0;
        return 1;
    }
    st->error_undefined_label = 0;

    int idx0 = axx_skipspc(msg_field, 0);
    if(msg_field[idx0] != '"'){
        axx_diagf(1, 0, " error - .error: message must be a double-quoted string, got '%s'.\n", msg_field);
        return 1;
    }

    /* 復号後の文字列はエスケープの分だけ短くなりこそすれ伸びないので、
     * 元欄の長さ+1 を出力バッファに取れば絶対に切り詰まらない。 */
    size_t mlen = strlen(msg_field);
    char stackbuf[512];
    char *msg = (mlen < sizeof(stackbuf)) ? stackbuf : malloc(mlen + 1);
    if(!msg){ perror("malloc"); exit(1); }
    axx_get_string(msg_field, msg, mlen + 1);

    sv_set(&st->errors, (int)n_int, msg);

    if(msg != stackbuf) free(msg);
    return 1;
}

/* この条件式は、リンカが値を決める変数を見ているか。
 *
 * `-o` で命令フィールド型のリロケーションを出す箇所では、命令語のビット欄は 0 で
 * 出してリンカが埋める。つまりその変数の値はアセンブル時には確定しておらず、axx が
 * 持っているのは自分の仮レイアウト上の値にすぎない。その値に対する整列・範囲
 * チェックは判定できないものを判定していることになり、正しいソースまで弾く。範囲や
 * 整列が本当に外れていればリンカが報告する（例: `improper alignment for relocation
 * R_AARCH64_LDST64_ABS_LO12_NC`）ので、ここでは黙って通す。
 *
 * 対象は「その変数を読んでいる条件」だけ。同じ行の他のオペランドを見る条件
 * （PRFM の `p<0` 等）はそのまま働く。axx.py の
 * DirectiveProcessor._cond_tests_relocated_var() と同じ判定。 */
static int cond_tests_relocated_var(AsmState *st, const char *cond, size_t len){
    if(!st->elf_objfile[0]) return 0;
    for(int vi = 0; vi < g_nvars; vi++){
        int rtype = st->reloc_constraints[vi];
        if(rtype == 0 || insn_reloc_field_mask(rtype) == 0) continue;
        const char *nm = g_varnames[vi];
        if(!nm || !*nm) continue;
        size_t nl = strlen(nm);
        if(nl > len) continue;
        for(size_t b = 0; b + nl <= len; b++){
            if(memcmp(cond + b, nm, nl) != 0) continue;
            /* 変数名は単独の語として現れたときだけ。`t` が `tmp` や `xt` の
             * 一部であるものを拾わない。 */
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

static int dir_error(Assembler *asmb, const char *s){
    AsmState *st=&asmb->st;
    int has_content=0;
    for(const char*p=s;*p;p++) if(*p!=' '){has_content=1;break;}
    if(!has_content) return 0;

    /* 破綻点修正: 固定長 char buf[4096] へ無言で切り詰めていたため、
     * condition;errorcode の対応リストが4096バイトを超えるパターンファイルでは
     * 条件とエラーコードの対応がずれ得た。他の箇所と同じく、収まらないときだけ
     * ヒープへ逃がす。 */
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
        /* 破綻点修正: axx.py の error() は idx が全く進まなかった場合に
         * ループを打ち切る（axx.py:3235-3236）。ここにその歯止めが無かった
         * ため、式評価器が1文字も消費できないトークン（例: 単独の ')'）で
         * 無限ループに陥っていた（axx.py はこの歯止めで即座に打ち切る）。 */
        int idx_before = idx;
        int io;
        int prev_flt = st->exp_typ_float;
        st->exp_typ_float = 1;
        uint256_t u=expr_expression_pat(asmb,buf,idx,&io);
        st->exp_typ_float = prev_flt;
        idx=io;
        int io_cond = io;          /* 条件式の終端。判定に条件の本文だけを渡す */
        if(buf[idx]==';') idx++;
        uint256_t t=expr_expression_pat(asmb,buf,idx,&io);
        idx=io;
        if(idx <= idx_before) break;
        if((should_report_errors(st))&&!u256_is_zero(u)
           && !cond_tests_relocated_var(st, buf + idx_before,
                                        (size_t)(io_cond - idx_before))){
            int64_t tc=u256_to_i64(t);
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
/* .enum の式を、出現した要素だけ .setsym の値に束縛して評価する。
 * 現れた要素に .setsym が無ければ *ok_out=0（不一致）にする。 */
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
            /* 現れた要素に .setsym が無い ＝ パターンファイル側の書き損じ。
             * 0 を黙って混ぜて誤ったバイトを出すより、不一致にして知らせる。 */
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
    /* expr_expression_pat() は expmode を戻さないので、照合中の EXP_ASM を
     * 壊さないようここで自分で戻す。 */
    st->expmode = prev_expmode;
    st->expcaps = prev_expcaps;
    st->enum_bind_names = prev_names;
    st->enum_bind_vals  = prev_vals;
    free(vals);
    *ok_out = 1;
    return r;
}

/* `!E<変数>` の位置から列挙要素のリストを読む。
 * 受け付けるのは `A0`、`A0-A2`（列挙順での範囲）、およびそれらを `,` か `/` で
 * 並べたもの。区切り記号は「その先に要素名が続くとき」だけ消費するので、
 * `MOVEM !Ex,-(SP)` のようにパターン側が後ろで `,` を使っていても
 * リストの一部と取り違えない。
 * 成功時は 1 を返し、*val_out に値、*idx_out に読み終えた位置を入れる。 */
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
                /* 範囲として読めない `-` は、減算などパターン側の続きに残す。 */
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

/* ソース行 s_orig をパターン t_orig と照合する（字句解析なしの1文字ずつ突き合わせ）。
 * パターン側の文字の意味:
 *   大文字      大小無視でリテラル一致（ニーモニック）
 *   小文字1文字 .setsym のシンボル（レジスタ名等）を取る
 *   !x          任意の式を読んで変数 x に束縛
 *   !!x         式ではなく factor 1個だけを束縛
 *   !Fx/!Dx/!Qx 浮動小数点式を IEEE754 の 32/64/128bit として束縛
 *   !Ex         .enum で決めた列挙要素のリストを読み、その式の値を束縛
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
            /* 破綻点修正: パターンが `!` で終わっている等、変数名が無い／小文字で
             * ない場合の不一致判定が無かった。axx.py は False を返して次の
             * パターンを試すが、C は '\0' を変数名として扱い、代入も行われない
             * まま照合を続けてしまっていた。 */
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
                idx_t += _nl;
                idx_t = axx_skipspc(t, idx_t);
                char stopchar = '\0';
                if(idx_t < tlen && t[idx_t] == '\\'){
                    idx_t++;
                    /* axx.py は `\` の直後の1文字をそのまま停止文字にする
                     * （空白読み飛ばしを挟まない）ので、ここでも挟まない。 */
                    stopchar = (idx_t < tlen) ? t[idx_t] : '\0';
                    idx_t++;
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
                    /* 破綻点修正: axx.py の !F/!D/!Q 捕捉は struct.pack した
                     * ビット列を int.from_bytes() でただの Python int として
                     * var_manager.put() に渡している（put_tagged ではない）。
                     * つまり axx.py 自身、!D 等で束縛した変数をその後
                     * error_patterns 等で比較・算術に使うときは「doubleの値」
                     * ではなく「ビット列を整数値とみなした値」として扱われる
                     * （これが axx.py の実際の挙動である以上、caxx.c 側も
                     * "既にdoubleとして正しい" と特別扱いしてはいけない。
                     * var_put_float ではなく var_put で is_float=0 のまま
                     * 束縛する）。 */
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
                    var_slot_put(st, vslot, qbits);
                }
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
                idx_s = eend;
                var_slot_put(st, vslot, ev);
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
                uint256_t v=expr_factor(asmb,s,idx_s,&idx_s);
                int _cap_this_undef = st->error_undefined_label;
                st->error_undefined_label = _cap_prior_eul || _cap_this_undef;
                st->elf_capturing_var = -1;
                var_slot_put_tagged(st,vslot,v,_cap_this_undef);
                continue;
            } else {
                /* `!name` の名前は小文字で始まり、小文字・数字・`_` が続く。
                 * 直前で1文字だけ読み進めてあるので、そこから測り直す。 */
                int _nl = var_name_len(t+idx_t-1);
                if(_nl == 0){ result=0; break; }
                int vslot = var_slot(t+idx_t-1, _nl, 1);
                if(vslot < 0){ result=0; break; }
                idx_t += _nl - 1;
                idx_t=axx_skipspc(t,idx_t);
                char stopchar='\0';
                if(idx_t<tlen && t[idx_t]=='\\'){
                    idx_t++;
                    /* axx.py と同じく `\` の直後の1文字をそのまま停止文字にする。 */
                    stopchar=(idx_t<tlen) ? t[idx_t] : '\0';
                    idx_t++;
                }
                st->elf_capturing_var = vslot;
                int _cap_prior_eul2 = st->error_undefined_label;
                st->error_undefined_label = 0;
                uint256_t v=expr_expression_esc(asmb,s,idx_s,stopchar,&idx_s);
                int _cap_this_undef2 = st->error_undefined_label;
                st->error_undefined_label = _cap_prior_eul2 || _cap_this_undef2;
                st->elf_capturing_var = -1;
                var_slot_put_tagged(st,vslot,v,_cap_this_undef2);
                if(stopchar && s[idx_s]==stopchar) idx_s++;
                continue;
            }
        } else if(a>='a'&&a<='z'){
            prev_alnum=0;
            /* シンボルを取る位置。名前は1文字でも `var_2` のように長くてもよい。 */
            int _nl = var_name_len(t+idx_t);
            int vi = var_slot(t+idx_t, _nl, 1);
            if(vi < 0){ result=0; break; }
            idx_t += _nl;
            int prev_idx_s = idx_s;
            StrVec *cv = &st->check_constraints[vi];
            int allow_omit = 0, n_named = 0;
            for(int si = 0; si < cv->len; si++){
                if(cv->data[si][0] == '\0') allow_omit = 1;
                else                        n_named++;
            }

            char wbuf[512]; size_t wsz;
            char *w = axx_word_buf(s, idx_s, wbuf, sizeof(wbuf), &wsz);
            idx_s=axx_get_symbol_word(s,idx_s,st->swordchars,w,wsz);
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
                if(best_si >= 0 && strlen(cv->data[best_si]) < wsz
                   && symbol_get(st, cv->data[best_si], &sv)){
                    snprintf(w, wsz, "%s", cv->data[best_si]);
                    idx_s = prev_idx_s + best_len;
                    ok = 1;
                }
            }

            if(w!=wbuf) free(w);

            if(!ok){
                if(!allow_omit){ result=0; break; }
                /* 省略とみなす。ソースは1文字も消費せず、変数は未代入(0)。 */
                idx_s = prev_idx_s;
                var_slot_put(st, vi, u256_zero());
                n_sym++;
                continue;
            }

            var_slot_put(st,vi,sv);
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

static int pat_match0_brackets(Assembler *asmb, const char *s, const char *t_orig){
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

    /* `[[...]]` の省略可グループの組み合わせを、削除する個数の少ない順・
     * 同じ個数なら添字の辞書順で試す（axx.py の
     * `for i in range(len(sl)+1): for j in itertools.combinations(sl, i)` と同じ順）。
     *
     * 破綻点修正: 以前はビットマスクの昇順（0,1,2,3,...）で回していた。これは
     * 削除個数の順ではないため、グループが3個以上あって複数の組み合わせが
     * 一致する場合に採用される組み合わせが axx.py と食い違っていた
     * （例: 3個なら Python は {3} を先に試すのに対し C は {1,2} を先に試す）。 */
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
            goto combo_done;
        }
        int ri[MAX_OPT_GROUPS + 1]; int nr=0;
        for(int k=0;k<size;k++) ri[nr++]=sl[comb[k]];
        char *lt=remove_brackets_str(t,ri,nr);

        PatVar    saved_vars[NVARS];
        memcpy(saved_vars, asmb->st.vars, sizeof(saved_vars));

        int saved_elf_refs_len = asmb->st.elf_refs_len;
        struct {int set; char *label_name; uint64_t label_val;} saved_vtl[NVARS];
        /* 退避した個数を控える。評価の途中で変数名が増えても、復元は
         * 退避した分だけを回す。 */
        int saved_nvars = g_nvars;
        for(int vi=0;vi<saved_nvars;vi++){
            saved_vtl[vi].set       = asmb->st.elf_var_to_label[vi].set;
            saved_vtl[vi].label_val = asmb->st.elf_var_to_label[vi].label_val;
            saved_vtl[vi].label_name = asmb->st.elf_var_to_label[vi].label_name
                                       ? strdup(asmb->st.elf_var_to_label[vi].label_name)
                                       : NULL;
        }

        if(pat_match(asmb,s,lt)){
            found=1;
            for(int vi=0;vi<saved_nvars;vi++) free(saved_vtl[vi].label_name);
        } else {
            memcpy(asmb->st.vars, saved_vars, sizeof(saved_vars));
            for(int ri2=saved_elf_refs_len; ri2<asmb->st.elf_refs_len; ri2++)
                free(asmb->st.elf_refs[ri2].name);
            asmb->st.elf_refs_len = saved_elf_refs_len;
            for(int vi=0;vi<saved_nvars;vi++){
                free(asmb->st.elf_var_to_label[vi].label_name);
                asmb->st.elf_var_to_label[vi].set       = saved_vtl[vi].set;
                asmb->st.elf_var_to_label[vi].label_val = saved_vtl[vi].label_val;
                asmb->st.elf_var_to_label[vi].label_name = saved_vtl[vi].label_name;
                saved_vtl[vi].label_name = NULL;
            }
        }
        free(lt);

        /* 次の組み合わせ（同じ個数のまま辞書順で1つ進める）。
           進められなければこの個数は打ち止め。 */
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

/* `!S{{名前}}<変数>` を探す。見つかれば開始位置を返し、*end に変数の次の位置、
 * name に表名、*var に変数名を書く。無ければ -1。 */
/* `!S{{表名}}変数` を探す。変数名は1文字でも `var_2` のように長くてもよく、
 * 見つけた名前はスロット番号にして返す。 */
static int pat_find_sub_ref(const char *t, int start, int *end, char *name, size_t nsz, int *var){
    for(int i=start; t[i]; i++){
        if(!(t[i]=='!' && t[i+1]=='S' && t[i+2]=='{' && t[i+3]=='{')) continue;
        /* `\!` とエスケープされていれば式ではなくリテラルの `!`。 */
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

/* サブ表の値欄を評価する。カンマ区切りで複数書かれていれば、先頭を上位として
 * `.bits` 幅ずつ詰めた1つの値にする（`0x01,0x02` は 8bit 幅なら 0x0102）。 */
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

enum { SUB_MAX_DEPTH = 8 };

static int pat_match0_subs(Assembler *asmb, const char *s, const char *t,
                           SubBind *binds, int nbinds, int depth){
    char name[64]; int var; int end;
    int start = pat_find_sub_ref(t, 0, &end, name, sizeof(name), &var);
    if(start < 0){
        PatVar saved_vars[NVARS];
        memcpy(saved_vars, asmb->st.vars, sizeof(saved_vars));
        int saved_elf_refs_len = asmb->st.elf_refs_len;
        struct {int set; char *label_name; uint64_t label_val;} saved_vtl[NVARS];
        int saved_nvars = g_nvars;   /* 復元は退避した個数だけ回す。 */
        for(int vi=0;vi<saved_nvars;vi++){
            saved_vtl[vi].set        = asmb->st.elf_var_to_label[vi].set;
            saved_vtl[vi].label_val  = asmb->st.elf_var_to_label[vi].label_val;
            saved_vtl[vi].label_name = asmb->st.elf_var_to_label[vi].label_name
                                       ? strdup(asmb->st.elf_var_to_label[vi].label_name)
                                       : NULL;
        }
        if(pat_match0_brackets(asmb, s, t)){
            /* 値欄は照合成功後に評価する。項目のパターンが束縛した変数を
             * 値欄から使えるようにするため。入れ子のときは内側から評価する
             * ので、外側の値欄が内側の変数を使える。 */
            for(int k=nbinds-1;k>=0;k--)
                var_slot_put(&asmb->st, binds[k].var, pat_sub_value(asmb, binds[k].val));
            for(int vi=0;vi<saved_nvars;vi++) free(saved_vtl[vi].label_name);
            return 1;
        }
        memcpy(asmb->st.vars, saved_vars, sizeof(saved_vars));
        for(int ri=saved_elf_refs_len; ri<asmb->st.elf_refs_len; ri++)
            free(asmb->st.elf_refs[ri].name);
        asmb->st.elf_refs_len = saved_elf_refs_len;
        for(int vi=0;vi<saved_nvars;vi++){
            free(asmb->st.elf_var_to_label[vi].label_name);
            asmb->st.elf_var_to_label[vi].set        = saved_vtl[vi].set;
            asmb->st.elf_var_to_label[vi].label_val  = saved_vtl[vi].label_val;
            asmb->st.elf_var_to_label[vi].label_name = saved_vtl[vi].label_name;
        }
        return 0;
    }

    if(depth >= SUB_MAX_DEPTH){
        axx_diagf(1, 0, " error - !S{{%s}}: sub table expansion exceeds maximum "
                   "depth %d.\n", name, SUB_MAX_DEPTH);
        return 0;
    }
    SubDef *d = subv_find(&asmb->st.subs, name);
    if(d && d->freed) d = NULL;   /* `.free` で解放済み */
    if(!d){
        axx_diagf(1, 0, " error - !S{{%s}}: no sub table named '%s' (define it with "
                   "'.sub::%s ... .return').\n", name, name, name);
        return 0;
    }
    if(nbinds >= SUB_MAX_DEPTH) return 0;

    int tlen = (int)strlen(t);
    for(int k=0; k<d->n; k++){
        size_t nl = (size_t)start + strlen(d->e[k].pat) + (size_t)(tlen-end) + 1;
        char *nt = malloc(nl);
        if(!nt){ perror("malloc"); exit(1); }
        memcpy(nt, t, (size_t)start);
        strcpy(nt + start, d->e[k].pat);
        strcat(nt + start, t + end);
        binds[nbinds].var = var;
        binds[nbinds].val = d->e[k].val;
        int ok = pat_match0_subs(asmb, s, nt, binds, nbinds+1, depth+1);
        free(nt);
        if(ok) return 1;
    }
    return 0;
}

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

static void axx_dir_of(const char *path, char *out, size_t osz)
{
    snprintf(out, osz, "%s", path ? path : "");
    char *d = dirname(out);
    if(d != out) memmove(out, d, strlen(d) + 1);
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
            axx_diagf(1, 0, " error - .INCLUDE directive has no filename: %s\n", l);
            return;
        }
    }
    char resolved[1024];
    axx_resolve_path(base_dir, raw, resolved, sizeof(resolved));
    readpat(asmb, resolved);
}

/* `!S{{名前}}` の参照を読み込み時に検算する。
 * 照合中に出した診断は「採用されなかった候補のもの」として捨てられるので、
 * 名前の綴り違いや循環参照はそのままだと全行が素の Syntax error になる。
 * パターンファイル側の誤りはここで一度だけ報告する。 */
static void sub_check_unknown(Assembler *asmb, const char *where, const char *t){
    char name[64]; int var; int end, i = 0;
    while((i = pat_find_sub_ref(t, i, &end, name, sizeof(name), &var)) >= 0){
        if(!subv_find(&asmb->st.subs, name))
            axx_diagf(1, 0, " error - !S{{%s}} in %s: no sub table named '%s' "
                       "(define it with '.sub::%s ... .return').\n",
                       name, where, name, name);
        i = end;
    }
}

static void sub_walk_cycle(Assembler *asmb, int idx, char *mark, int *stack, int nstack){
    SubVec *sv = &asmb->st.subs;
    if(mark[idx] == 2) return;
    if(mark[idx] == 1){
        char path[512]; size_t n = 0;
        for(int k = 0; k < nstack; k++)
            n += (size_t)snprintf(path+n, n<sizeof(path)?sizeof(path)-n:0,
                                  "%s -> ", sv->data[stack[k]].name);
        snprintf(path+n, n<sizeof(path)?sizeof(path)-n:0, "%s", sv->data[idx].name);
        axx_diagf(1, 0, " error - sub table '%s' is circular (%s); expansion would "
                   "not terminate.\n", sv->data[idx].name, path);
        return;
    }
    mark[idx] = 1;
    SubDef *d = &sv->data[idx];
    for(int k = 0; k < d->n; k++){
        char name[64]; int var; int end, i = 0;
        while((i = pat_find_sub_ref(d->e[k].pat, i, &end, name, sizeof(name), &var)) >= 0){
            SubDef *tgt = subv_find(sv, name);
            if(tgt && nstack < sv->len){
                stack[nstack] = idx;
                sub_walk_cycle(asmb, (int)(tgt - sv->data), mark, stack, nstack+1);
            }
            i = end;
        }
    }
    mark[idx] = 2;
}

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

/* ==================== ミニ言語: 実装 ====================
 * `.func::名前::引数 … .endfunc` で定義し、`binary_list` 欄の
 * `.call 名前(引数,…)` から呼ぶ。`.emit` した値がその位置のワードになる。
 * `.return` / `.return 式` は本体中どこでも(トップレベルでも `.if`/`.while`/
 * `.for` の中でも、何回でも)書ける早期リターン文で、関数の終わりを示す
 * ものではない。本体そのものを閉じるのは `.endfunc` だけ。
 * axx.py の MiniParser / MiniInterp の移植で、同じ入力に同じ値を出す。 */

enum {
    MINI_MAX_STEPS = 4000000,
    MINI_MAX_DEPTH = 128,
    MINI_MAX_EMIT  = 1 << 20,
    MINI_MAX_ARRAY = 1 << 20,
    MINI_MAX_TOK   = 1024
};

typedef enum { MT_END, MT_NUM, MT_NAME, MT_DOT, MT_OP, MT_STR, MT_CORE } MTKind;
/* 字句1個ぶん。s は名前／ディレクティブ名を丸ごと収める。axx.py 側に名前の
 * 長さ制限は無いので、実用上ぶつからない幅を取っておく（作業領域はヒープ）。 */
typedef struct { MTKind k; uint256_t num; char s[512]; } MTok;

typedef struct {
    jmp_buf     jb;
    int         jb_active;
    char        err[512];
    const char *file;
    int         line;
} MiniCtx;

static void mini_fail(MiniCtx *c, const char *fmt, ...){
    va_list ap;
    char body[400];
    va_start(ap, fmt);
    vsnprintf(body, sizeof(body), fmt, ap);
    va_end(ap);
    snprintf(c->err, sizeof(c->err), "%s:%d: %s",
             c->file ? c->file : "?", c->line, body);
    if(c->jb_active) longjmp(c->jb, 1);
    fprintf(stderr, " error - %s\n", c->err);
    exit(1);
}

static void *mini_alloc(size_t n){
    void *p = calloc(1, n);
    if(!p){ perror("calloc"); exit(1); }
    return p;
}

static char *mini_strdup(const char *s){
    char *p = strdup(s ? s : "");
    if(!p){ perror("strdup"); exit(1); }
    return p;
}

/* --------------------------- 値 --------------------------- */

/* ミニ言語の値を、マクロ層の `!echo` と同じ体裁の文字列にする。整数は符号つき
 * 10 進、配列は `[1, 2, 3]`。返り値は free() すること。 */
static char *mini_echo_text(MiniVal *v);

static void mini_val_free(MiniVal *v){
    if(v->arr) free(v->arr);
    v->arr = NULL; v->n = v->cap = 0; v->is_arr = 0;
}

static MiniVal mini_num(uint256_t x){
    MiniVal v; memset(&v, 0, sizeof(v));
    v.num = x;
    return v;
}

static MiniVal mini_val_copy(const MiniVal *src){
    MiniVal v; memset(&v, 0, sizeof(v));
    v.is_arr = src->is_arr;
    v.num = src->num;
    if(src->is_arr && src->n > 0){
        v.arr = mini_alloc((size_t)src->n * sizeof(uint256_t));
        memcpy(v.arr, src->arr, (size_t)src->n * sizeof(uint256_t));
        v.n = v.cap = src->n;
    }
    return v;
}

static void mini_arr_reserve(MiniVal *v, int want){
    if(want <= v->cap) return;
    int cap = v->cap ? v->cap : 8;
    while(cap < want) cap *= 2;
    uint256_t *na = realloc(v->arr, (size_t)cap * sizeof(uint256_t));
    if(!na){ perror("realloc"); exit(1); }
    v->arr = na; v->cap = cap;
}

static char *mini_echo_text(MiniVal *v){
    if(!v->is_arr){
        char cb[96]; u256_to_pydec(v->num, cb, sizeof(cb));
        return mini_strdup(cb);
    }
    /* 1 要素あたり 256bit 符号つき 10 進は最長 78 桁 + 符号。区切りの ", " を
     * 足して 98 文字を見ておけば足りる。 */
    size_t cap = (size_t)v->n * 98 + 4;
    char *b = mini_alloc(cap);
    size_t len = 0;
    b[len++] = '[';
    for(int i = 0; i < v->n; i++){
        if(i){ b[len++] = ','; b[len++] = ' '; }
        char cb[96]; u256_to_pydec(v->arr[i], cb, sizeof(cb));
        size_t l = strlen(cb);
        memcpy(b + len, cb, l); len += l;
    }
    b[len++] = ']';
    b[len] = 0;
    return b;
}

/* --------------------------- 字句 --------------------------- */

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

static int mini_lex(MiniCtx *c, const char *t, MTok *out){
    static const char *ops2[] = { "**","<<",">>","<=",">=","==","!=","&&","||", NULL };
    int n = 0, i = 0;
    int len = (int)strlen(t);
    while(i < len){
        if(n >= MINI_MAX_TOK - 1) mini_fail(c, "statement is too long");
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
            out[n].s[0] = 0; n++; i = j; continue;
        }
        if(isalpha((unsigned char)ch) || ch == '_'){
            int j = i;
            while(j < len && (isalnum((unsigned char)t[j]) || t[j] == '_')) j++;
            if(j - i >= (int)sizeof(out[n].s)) mini_fail(c, "name is too long");
            out[n].k = MT_NAME;
            memcpy(out[n].s, t + i, (size_t)(j - i)); out[n].s[j - i] = 0;
            n++; i = j; continue;
        }
        if(ch == '$'){
            /* `$$` / `$.` は本体の式評価器が持つ項。ここでは字面を覚えるだけで、
             * 実際の値は評価時に本体へ渡して求める。 */
            if(t[i+1] == '$' || t[i+1] == '.'){
                out[n].k = MT_CORE;
                out[n].s[0] = t[i]; out[n].s[1] = t[i+1]; out[n].s[2] = 0;
                n++; i += 2; continue;
            }
            mini_fail(c, "'$' must be written '$$' (location counter) or '$.' "
                         "(start of the next instruction)");
        }
        if(ch == '#'){
            /* `#name` も本体の式評価器が持つ項（`.setsym` の記号）。 */
            int j = i + 1;
            while(j < len && (isalnum((unsigned char)t[j]) || t[j] == '_'
                              || t[j] == '.' || t[j] == '$')) j++;
            if(j == i + 1) mini_fail(c, "'#' needs a symbol name");
            if(j - i >= (int)sizeof(out[n].s)) mini_fail(c, "symbol name is too long");
            out[n].k = MT_CORE;
            memcpy(out[n].s, t + i, (size_t)(j - i)); out[n].s[j - i] = 0;
            n++; i = j; continue;
        }
        if(ch == '"'){
            /* 文字列リテラル。値は整数と配列だけなので、書けるのは `.echo` の
             * 引数欄だけである（式の中に現れたら mxp_primary が弾く）。 */
            int j = i + 1, m = 0;
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
                    if(m >= (int)sizeof(out[n].s) - 1) mini_fail(c, "string is too long");
                    out[n].s[m++] = r;
                    j += 2;
                    continue;
                }
                if(m >= (int)sizeof(out[n].s) - 1) mini_fail(c, "string is too long");
                out[n].s[m++] = cc;
                j++;
            }
            out[n].s[m] = 0;
            out[n].k = MT_STR;
            n++; i = j; continue;
        }
        if(ch == '.'){
            int j = i + 1;
            while(j < len && (isalnum((unsigned char)t[j]) || t[j] == '_')) j++;
            if(j == i + 1) mini_fail(c, "stray '.'");
            if(j - i >= (int)sizeof(out[n].s)) mini_fail(c, "directive name is too long");
            out[n].k = MT_DOT;
            for(int q = i; q < j; q++) out[n].s[q - i] = axx_upper_char(t[q]);
            out[n].s[j - i] = 0;
            n++; i = j; continue;
        }
        {
            int hit = 0;
            for(int q = 0; ops2[q]; q++){
                if(t[i] == ops2[q][0] && i + 1 < len && t[i+1] == ops2[q][1]){
                    out[n].k = MT_OP;
                    out[n].s[0] = ops2[q][0]; out[n].s[1] = ops2[q][1]; out[n].s[2] = 0;
                    n++; i += 2; hit = 1; break;
                }
            }
            if(hit) continue;
        }
        if(strchr("+-*/%&|^~<>!()[]:,=", ch)){
            out[n].k = MT_OP; out[n].s[0] = ch; out[n].s[1] = 0;
            n++; i++; continue;
        }
        mini_fail(c, "unexpected character '%c'", ch);
    }
    out[n].k = MT_END; out[n].s[0] = 0;
    return n;
}

/* --------------------------- 式の構文解析 --------------------------- */

typedef struct { MTok *t; int n; int i; MiniCtx *c; } MXP;

static MExpr *mxp_or(MXP *p);

static MExpr *mx_new(MXKind k){
    MExpr *e = mini_alloc(sizeof(MExpr));
    e->k = k;
    return e;
}

static int mxp_is_op(MXP *p, const char *op){
    return p->i < p->n && p->t[p->i].k == MT_OP && strcmp(p->t[p->i].s, op) == 0;
}

static int mxp_eat(MXP *p, const char *op){
    if(mxp_is_op(p, op)){ p->i++; return 1; }
    return 0;
}

static void mxp_expect(MXP *p, const char *op){
    if(!mxp_eat(p, op)){
        if(p->i < p->n) mini_fail(p->c, "expected '%s', found '%s'", op, p->t[p->i].s);
        else mini_fail(p->c, "expected '%s', found end of line", op);
    }
}

static int mxp_end(MXP *p){ return p->i >= p->n; }

static MExpr *mxp_primary(MXP *p){
    if(mxp_end(p)) mini_fail(p->c, "expected a value, found end of line");
    MTok *tk = &p->t[p->i];
    if(tk->k == MT_STR) mini_fail(p->c, "a string can only be used in '.echo'");
    if(tk->k == MT_CORE){ p->i++; MExpr *e = mx_new(MX_CORE); e->name = mini_strdup(tk->s); return e; }
    if(tk->k == MT_NUM){ p->i++; MExpr *e = mx_new(MX_NUM); e->num = tk->num; return e; }
    if(tk->k == MT_NAME){ p->i++; MExpr *e = mx_new(MX_VAR); e->name = mini_strdup(tk->s); return e; }
    if(tk->k == MT_DOT){
        if(strcmp(tk->s, ".LEN") == 0){
            p->i++;
            mxp_expect(p, "(");
            MExpr *e = mx_new(MX_LEN);
            e->a = mxp_or(p);
            mxp_expect(p, ")");
            return e;
        }
        if(strcmp(tk->s, ".CALL") == 0){
            /* 式の途中の `.call 名前(引数, ...)`。呼んだ関数の返り値になる。 */
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
        mini_fail(p->c, "'%s' cannot be used in an expression", tk->s);
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
    mini_fail(p->c, "expected a value, found '%s'", tk->s);
    return NULL;
}

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

static MExpr *mxp_unary(MXP *p){
    if(mxp_is_op(p, "-") || mxp_is_op(p, "+") || mxp_is_op(p, "~")){
        char op[3]; strcpy(op, p->t[p->i].s);
        p->i++;
        MExpr *e = mx_new(MX_UN);
        strcpy(e->op, op);
        e->a = mxp_unary(p);
        return e;
    }
    return mxp_power(p);
}

static MExpr *mxp_binlevel(MXP *p, int level){
    /* level: 0=| 1=^ 2=& 3=shift 4=add 5=mul */
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

static MExpr *mxp_not(MXP *p){
    if(mxp_is_op(p, "!")){
        p->i++;
        MExpr *e = mx_new(MX_UN);
        strcpy(e->op, "!");
        e->a = mxp_not(p);
        return e;
    }
    return mxp_cmp(p);
}

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

static MExpr *mxp_or(MXP *p){
    MExpr *e = mxp_and(p);
    while(mxp_is_op(p, "||")){
        p->i++;
        MExpr *b = mx_new(MX_BIN);
        strcpy(b->op, "||"); b->a = e; b->b = mxp_and(p);
        e = b;
    }
    return e;
}

static MExpr *mxp_full(MXP *p){
    MExpr *e = mxp_or(p);
    if(!mxp_end(p)) mini_fail(p->c, "unexpected '%s' in expression", p->t[p->i].s);
    return e;
}

/* `(` の直後から `)` までのカンマ区切りの式を読む。 */
/* `.echo` の引数欄。項目は文字列リテラルか式。文字列は MX_STR のまま持ち回り、
 * 表示のときだけ取り出す（式としては評価しない）。 */
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
            if(p->i < p->n && p->t[p->i].k == MT_STR){
                MExpr *e = mx_new(MX_STR);
                e->name = mini_strdup(p->t[p->i].s);
                p->i++;
                (*outv)[(*outn)++] = e;
            } else {
                (*outv)[(*outn)++] = mxp_or(p);
            }
        } while(mxp_eat(p, ","));
    }
    mxp_expect(p, ")");
}

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

/* --------------------------- 文の構文解析 --------------------------- */

typedef struct {
    MiniFunc *f;
    int       i;
    MiniCtx  *c;
    /* 字句の作業領域。MTok[MINI_MAX_TOK] は 170KB 近くあり、msp_block は
     * ブロックの深さぶん再帰するので、各段で自動変数に取るとスタックが尽きる
     * （40段ほどで落ちていた）。解析は 1 行ぶんずつ完結し、式は木に写してから
     * 次の段へ進むので、1本を使い回して構わない。 */
    MTok     *tok;
    int       loopdepth;   /* `.break` / `.continue` が書ける深さ */
} MSP;

static void ms_push(MStmt ***v, int *n, int *cap, MStmt *s){
    if(*n >= *cap){
        *cap = *cap ? *cap * 2 : 8;
        *v = realloc(*v, (size_t)*cap * sizeof(MStmt*));
        if(!*v){ perror("realloc"); exit(1); }
    }
    (*v)[(*n)++] = s;
}

static MStmt *ms_new(MSKind k, MSP *p, int li){
    MStmt *s = mini_alloc(sizeof(MStmt));
    s->k = k;
    s->file = p->f->lfiles[li];
    s->line = p->f->llines[li];
    return s;
}

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

static int mini_is_ender(const char *kw){
    return strcmp(kw, ".ELIF") == 0 || strcmp(kw, ".ELSE") == 0
        || strcmp(kw, ".ENDIF") == 0
        || strcmp(kw, ".NEXT") == 0 || strcmp(kw, ".ENDWHILE") == 0;
}

static void msp_block(MSP *p, const char *e1, const char *e2, const char *e3,
                      MStmt ***outv, int *outn);
static MStmt *msp_if_chain(MSP *p, int li);

/* `.call 名前(引数, ...)` の後半を読む。toks[0] は '.CALL'。 */
static void ms_call_tail(MiniCtx *c, MTok *toks, int n, char **namep,
                         MExpr ***argv, int *argn){
    if(n < 2 || toks[1].k != MT_NAME) mini_fail(c, "'.call' needs a function name");
    *namep = mini_strdup(toks[1].s);
    MXP ep; ep.t = toks + 2; ep.n = n - 2; ep.i = 0; ep.c = c;
    mxp_arglist(&ep, argv, argn);
    if(!mxp_end(&ep)) mini_fail(c, "unexpected text after '.call'");
}

static MStmt *msp_simple(MSP *p, int li){
    MiniCtx *c = p->c;
    const char *text = p->f->lines[li];
    c->file = p->f->lfiles[li];
    c->line = p->f->llines[li];
    MTok *toks = p->tok;
    int n = mini_lex(c, text, toks);
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
            /* `.raise n` … error_patterns 欄の `条件;n` と同じ形でエラーコード n を
             * 報告する。`.error::n::"文言"` で登録した文言もそのまま使われる。 */
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
        mini_fail(c, "unknown statement '%s'", kw);
    }
    if(toks[0].k != MT_NAME)
        mini_fail(c, "statement must be a directive or an assignment");
    {
        MStmt *s = ms_new(MS_ASSIGN, p, li);
        s->name = mini_strdup(toks[0].s);
        MXP ep; ep.t = toks + 1; ep.n = n - 1; ep.i = 0; ep.c = c;
        if(mxp_is_op(&ep, "[")){
            ep.i++;
            s->idx = mxp_or(&ep);
            mxp_expect(&ep, "]");
        }
        mxp_expect(&ep, "=");
        MTok *rt = ep.t + ep.i;
        int rn = ep.n - ep.i;
        /* `var = .call f(...)` は呼んだ関数の返り値を代入する。 */
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

/* `.if` / `.elif` の 1 段を読む。戻り値の文を返した時点で p->i は対応する
 * `.endif` の行を指している。`.elif` は「`.else` の中に `.if` が 1 つだけある」
 * 形へ展開するので、連鎖の途中では `.endif` を読み飛ばさない。1 行進めるのは
 * いちばん外側の呼び出し元（msp_block）だけでよい。 */
static MStmt *msp_if_chain(MSP *p, int li){
    MiniCtx *c = p->c;
    char kw[32];
    mini_dotkw(p->f->lines[li], kw, sizeof(kw));
    char low[32];
    snprintf(low, sizeof(low), "%s", kw);
    for(char *q = low; *q; q++) *q = (char)tolower((unsigned char)*q);
    c->file = p->f->lfiles[li];
    c->line = p->f->llines[li];
    MTok *toks = p->tok;
    int n = mini_lex(c, p->f->lines[li], toks);
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
        MTok *t2 = p->tok;
        c->file = p->f->lfiles[p->i]; c->line = p->f->llines[p->i];
        if(mini_lex(c, p->f->lines[p->i], t2) != 1)
            mini_fail(c, "unexpected text after '.else'");
        p->i++;
        msp_block(p, ".ENDIF", NULL, NULL, &s->body2, &s->nbody2);
        if(p->i >= p->f->nlines){
            c->file = s->file; c->line = s->line;
            mini_fail(c, "'.if' is never closed with '.endif'");
        }
    }
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
            MTok *toks = p->tok;
            int n = mini_lex(c, p->f->lines[li], toks);
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
            p->i++;
            ms_push(outv, outn, &cap, s);
            continue;
        }
        if(strcmp(kw, ".FOR") == 0){
            MTok *toks = p->tok;
            int n = mini_lex(c, p->f->lines[li], toks);
            if(n < 4 || toks[1].k != MT_NAME)
                mini_fail(c, "'.for' needs 'variable in range(...)'");
            MStmt *s = ms_new(MS_FOR, p, li);
            s->name = mini_strdup(toks[1].s);
            if(!(toks[2].k == MT_NAME && strcmp(toks[2].s, "in") == 0) ||
               !(toks[3].k == MT_NAME && strcmp(toks[3].s, "range") == 0))
                mini_fail(c, "'.for %s' must be followed by 'in range(...)'", s->name);
            MXP ep; ep.t = toks + 4; ep.n = n - 4; ep.i = 0; ep.c = c;
            mxp_arglist(&ep, &s->args, &s->nargs);
            if(!mxp_end(&ep)) mini_fail(c, "unexpected text after 'range(...)'");
            if(s->nargs < 1 || s->nargs > 3)
                mini_fail(c, "range() takes 1 to 3 arguments, got %d", s->nargs);
            p->i = li + 1;
            p->loopdepth++;
            msp_block(p, ".NEXT", NULL, NULL, &s->body, &s->nbody);
            p->loopdepth--;
            if(p->i >= p->f->nlines){
                c->file = s->file; c->line = s->line;
                mini_fail(c, "'.for' is never closed with '.next'");
            }
            p->i++;
            ms_push(outv, outn, &cap, s);
            continue;
        }
        ms_push(outv, outn, &cap, msp_simple(p, li));
        p->i = li + 1;
    }
}

/* 本体の行を文の木にする。エラーは *errout に書いて 0 を返す。 */
/* 字句の作業領域。解析は 1 関数ずつ順に走るので 1 本で足りる。
 * msp_block の再帰段ごとに自動変数で持つとスタックが尽きるため外に出す。 */
static MTok *mini_tokbuf(void){
    static MTok *buf;
    if(!buf){
        buf = malloc((size_t)MINI_MAX_TOK * sizeof(MTok));
        if(!buf){ perror("malloc"); exit(1); }
    }
    return buf;
}

static int mini_compile_func(MiniFunc *f, char *errout, size_t esz){
    MiniCtx c;
    MTok *tokbuf = mini_tokbuf();
    memset(&c, 0, sizeof(c));
    c.file = f->file; c.line = f->line;
    c.jb_active = 1;
    if(setjmp(c.jb)){
        snprintf(errout, esz, "%s", c.err);
        f->body = NULL; f->nbody = 0;
        return 0;
    }
    MSP p; p.f = f; p.i = 0; p.c = &c; p.tok = tokbuf; p.loopdepth = 0;
    msp_block(&p, NULL, NULL, NULL, &f->body, &f->nbody);
    if(p.i < f->nlines){
        c.file = f->lfiles[p.i]; c.line = f->llines[p.i];
        mini_fail(&c, "'%s' has no matching opener", f->lines[p.i]);
    }
    return 1;
}

/* --------------------------- 実行 --------------------------- */

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
    int        loopctl;  /* 1 = `.break` 実行中, 2 = `.continue` 実行中 */
    MiniVal    retval;   /* 直前の `.return 式` の値。整数でも配列でもよい */
    int        has_ret;  /* retval が有効か。値なしの `.return` なら 0 */
} MiniRun;

static MiniVal mini_eval(MiniRun *r, MExpr *e);
static void mini_exec_block(MiniRun *r, MStmt **body, int n);
static MiniFunc *mini_lookup(MiniRun *r, const char *name);
static void mini_call_func(MiniRun *r, MiniFunc *f, MiniVal *args, int nargs);

static void mini_at(MiniRun *r, MStmt *s){ r->c.file = s->file; r->c.line = s->line; }

/* 添字やスライス境界のように「範囲外なら丸める」場所で使う飽和変換。
 * axx.py は多倍長のまま比較するので、long long に収まらない値でエラーに
 * せず、符号の向きに振り切った値として扱えば同じ結果になる。 */
static long long mini_to_ll_sat(uint256_t v){
    if(u256_is_neg256(v)){
        uint256_t p = u256_neg(v);
        if(u256_nonneg_gt_i64(p, 0x7fffffffffffffffLL)) return -0x7fffffffffffffffLL - 1;
        return -(long long)u256_to_u64(p);
    }
    if(u256_nonneg_gt_i64(v, 0x7fffffffffffffffLL)) return 0x7fffffffffffffffLL;
    return (long long)u256_to_u64(v);
}

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

static uint256_t mini_need_num(MiniRun *r, MiniVal v, const char *what){
    if(v.is_arr){
        mini_val_free(&v);
        mini_fail(&r->c, "%s must be a number, not an array", what);
    }
    return v.num;
}

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

static MiniBind *mini_find(MiniFrame *fr, const char *name){
    for(int i = 0; i < fr->nvars; i++)
        if(strcmp(fr->vars[i].name, name) == 0) return &fr->vars[i];
    return NULL;
}

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

/* `$$` `$.` `#記号` ラベル名を本体の式評価器に評価してもらう。
 * ミニ言語は本体と同じ 256bit の値を扱うので、結果はそのまま使える。
 * 能力記述子は CAPS_MINI。パターン変数 a〜z と `!!!` は `.func` の本体が
 * 走っている時点では束縛されていないか意味を持たないので、そこで落とす。
 * 未定義ラベル由来の値は 0 にする。`.call` の引数を評価するときと同じ扱いで、
 * 番兵の巨大な値で反復回数が爆発するのを防ぐ。
 * axx.py の MiniInterp._core_eval と同じ。 */
static uint256_t mini_core_eval(MiniRun *r, const char *text){
    if(!r->asmb) mini_fail(&r->c, "'%s' is not available here", text);
    int io = 0;
    uint256_t v = expr_expression_caps(r->asmb, text, 0, &CAPS_MINI, &io);
    if(u256_is_undef_derived(v)) return u256_zero();
    return v;
}

/* その名前をアセンブラ本体が知っているか（ラベル / `.setsym` 記号）。 */
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

static MiniVal mini_get(MiniRun *r, const char *name){
    int found;
    MiniFrame *fr = mini_frame_for(r, name, &found);
    if(!found)
        mini_fail(&r->c, "'.nonlocal %s' found no enclosing definition of '%s'", name, name);
    MiniBind *b = mini_find(fr, name);
    if(!b){
        /* ローカルに無い名前は、アセンブラ本体のラベル / `.setsym` 記号として
         * 読み直す。パス2では本体の表が揃っているので「そんな名前は無い」と
         * 断定でき、綴り間違いは従来どおりミニ言語のエラーになる。パス1では
         * まだ前方参照が埋まっていないので、判断を本体側に預ける。 */
        if(r->asmb && (mini_core_name(r, name) || r->asmb->st.pas != 2))
            return mini_num(mini_core_eval(r, name));
        mini_fail(&r->c, "'%s' is used before it is set", name);
    }
    return mini_val_copy(&b->v);
}

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

/* 代入で伸ばすため、変数そのものへの参照を得る。 */
static MiniBind *mini_ref(MiniRun *r, const char *name){
    int found;
    MiniFrame *fr = mini_frame_for(r, name, &found);
    if(!found)
        mini_fail(&r->c, "'.nonlocal %s' found no enclosing definition of '%s'", name, name);
    MiniBind *b = mini_find(fr, name);
    if(!b) mini_fail(&r->c, "'%s' is used before it is set", name);
    return b;
}

static uint256_t mini_bool(int b){ return b ? u256_one() : u256_zero(); }

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
        /* 0 方向への切り捨て除算と対になる剰余（符号は被除数に従う）。
         * u256_mod は floor 除算が前提で符号の扱いが違うので使わない。 */
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

static MiniVal mini_eval(MiniRun *r, MExpr *e){
    switch(e->k){
    /* MX_STR は `.echo` の表示側でしか取り出さない。式として来たら構文解析の
     * 取りこぼしなので、黙って 0 にせず止める。 */
    case MX_STR:
        mini_fail(&r->c, "a string can only be used in '.echo'");
        return mini_num(u256_zero());   /* mini_fail は longjmp で戻らない */
    case MX_CORE: return mini_num(mini_core_eval(r, e->name));
    case MX_NUM: return mini_num(e->num);
    case MX_VAR: return mini_get(r, e->name);
    case MX_ARRLIT: {
        MiniVal v; memset(&v, 0, sizeof(v));
        v.is_arr = 1;
        mini_arr_reserve(&v, e->nitems > 0 ? e->nitems : 1);
        for(int i = 0; i < e->nitems; i++)
            v.arr[v.n++] = mini_need_num(r, mini_eval(r, e->items[i]), "an array element");
        return v;
    }
    case MX_CALL: {
        MiniFunc *f = mini_lookup(r, e->name);
        MiniVal *vals = e->nitems ? mini_alloc((size_t)e->nitems * sizeof(MiniVal)) : NULL;
        for(int i = 0; i < e->nitems; i++) vals[i] = mini_eval(r, e->items[i]);
        /* 呼んだ先で進む診断位置を、戻ったあとに元の行へ戻す。 */
        const char *sfile = r->c.file;
        int sline = r->c.line;
        mini_call_func(r, f, vals, e->nitems);
        for(int i = 0; i < e->nitems; i++) mini_val_free(&vals[i]);
        free(vals);
        r->c.file = sfile; r->c.line = sline;
        if(!r->has_ret)
            mini_fail(&r->c, "'%s' returned no value; give it a "
                      "'.return <expression>'", e->name);
        MiniVal ret = r->retval;          /* 所有権をここで引き取る */
        memset(&r->retval, 0, sizeof(r->retval));
        r->has_ret = 0;
        return ret;
    }
    case MX_LEN: {
        MiniVal b = mini_eval(r, e->a);
        if(!b.is_arr){ mini_val_free(&b); mini_fail(&r->c, "'.len' needs an array"); }
        int n = b.n;
        mini_val_free(&b);
        return mini_num(u256_from_u64((uint64_t)n));
    }
    case MX_INDEX: {
        MiniVal b = mini_eval(r, e->a);
        if(!b.is_arr){ mini_val_free(&b); mini_fail(&r->c, "only an array can be indexed"); }
        uint256_t iv = mini_need_num(r, mini_eval(r, e->b), "an index");
        long long i = mini_to_ll_sat(iv);
        /* 範囲外の読み出しは 0。配列は書き込みで伸びるので読みでは伸ばさない。 */
        uint256_t out = (i < 0 || i >= b.n) ? u256_zero() : b.arr[i];
        mini_val_free(&b);
        return mini_num(out);
    }
    case MX_SLICE: {
        MiniVal b = mini_eval(r, e->a);
        if(!b.is_arr){ mini_val_free(&b); mini_fail(&r->c, "only an array can be sliced"); }
        long long n = b.n;
        long long lo = 0, hi = n;
        if(e->b) lo = mini_to_ll_sat(mini_need_num(r, mini_eval(r, e->b), "a slice bound"));
        if(e->c) hi = mini_to_ll_sat(mini_need_num(r, mini_eval(r, e->c), "a slice bound"));
        if(lo < 0) lo = 0;
        if(lo > n) lo = n;
        if(hi < lo) hi = lo;
        if(hi > n) hi = n;
        MiniVal v; memset(&v, 0, sizeof(v));
        v.is_arr = 1;
        if(hi > lo){
            mini_arr_reserve(&v, (int)(hi - lo));
            for(long long i = lo; i < hi; i++) v.arr[v.n++] = b.arr[i];
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
        uint256_t a = mini_need_num(r, mini_eval(r, e->a), "an operand");
        uint256_t b = mini_need_num(r, mini_eval(r, e->b), "an operand");
        return mini_num(mini_binop(r, e->op, a, b));
    }
    }
    mini_fail(&r->c, "bad expression");
    return mini_num(u256_zero());
}

static void mini_tick(MiniRun *r){
    if(++r->steps > MINI_MAX_STEPS)
        mini_fail(&r->c, "mini language ran more than %d statements; "
                  "assuming a runaway loop", MINI_MAX_STEPS);
}

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

/* `name = v` / `name[idx] = v`。v の所有権はこの関数が引き取る。 */
static void mini_store(MiniRun *r, MStmt *s, MiniVal v){
    if(!s->idx){ mini_set(r, s->name, v); return; }
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
    uint256_t elem = mini_need_num(r, v, "an array element");
    MiniBind *b = mini_ref(r, s->name);
    if(!b->v.is_arr) mini_fail(&r->c, "'%s' is not an array", s->name);
    if(i >= b->v.n){
        mini_arr_reserve(&b->v, (int)i + 1);
        for(int q = b->v.n; q <= (int)i; q++) b->v.arr[q] = u256_zero();
        b->v.n = (int)i + 1;
    }
    b->v.arr[i] = elem;
}

/* 直前の呼び出しが置いていった返り値を捨てる。 */
static void mini_drop_ret(MiniRun *r){
    if(r->has_ret){ mini_val_free(&r->retval); r->has_ret = 0; }
}

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
                mini_val_free(&ev);
                mini_fail(&r->c, "'.emit' needs numbers, not an array");
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
        /* 命令長を測るだけの試し打ちと、収束途中のパス1では黙る（`.echo` と同じ）。
         * 同じ行が反復回数だけ重複して報告されるのを防ぐため。
         * 報告の体裁は error_patterns 欄（dir_error）と揃えてある。 */
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
        /* 命令長を測るだけの試し打ちと、収束途中のパス1では黙る。
         * 同じ行が反復回数だけ重複して出るのを防ぐため。 */
        int show = r->asmb && should_report_errors(&r->asmb->st)
                   && !r->asmb->st.pass1_size_mode;
        char **items = s->nargs ? mini_alloc((size_t)s->nargs * sizeof(char*)) : NULL;
        for(int i = 0; i < s->nargs; i++){
            if(s->args[i]->k == MX_STR){
                if(show) items[i] = mini_strdup(s->args[i]->name);
                continue;
            }
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
        mini_drop_ret(r);   /* 文としての `.call` は返り値を使わない */
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
        MiniVal ret = r->retval;          /* 所有権をここで引き取る */
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
        /* 反復変数は 256bit のまま回す。long long に落とすと、範囲の端が
         * 64bit を超えるだけで axx.py（多倍長）と挙動が食い違うため。 */
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
            /* axx.py の反復変数は桁あふれしない整数なので、256bit の符号付き
             * 範囲を越えた時点で必ず停止条件を満たす。同じ所で打ち切る。 */
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

static void mini_exec_block(MiniRun *r, MStmt **body, int n){
    for(int i = 0; i < n; i++){
        mini_exec(r, body[i]);
        if(r->returning || r->loopctl) return;
    }
}

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

/* --------------------------- 関数表 --------------------------- */

static void mini_expr_free(MExpr *e){
    if(!e) return;
    mini_expr_free(e->a); mini_expr_free(e->b); mini_expr_free(e->c);
    for(int i = 0; i < e->nitems; i++) mini_expr_free(e->items[i]);
    free(e->items);
    free(e->name);
    free(e);
}

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

static void mfv_free(MiniFuncVec *v){
    for(int i = 0; i < v->len; i++) mini_func_free(v->data[i]);
    free(v->data);
    mfv_init(v);
}

static MiniFunc *mfv_find(MiniFuncVec *v, const char *name){
    for(int i = 0; i < v->len; i++)
        if(strcmp(v->data[i]->name, name) == 0) return v->data[i];
    return NULL;
}

/* 親が NULL ならトップレベル、そうでなければ親の children に入れる。
 * 同名が既にあればそれを捨てて置き換える（後の定義が勝つ）。 */
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

static void mini_func_addparam(MiniFunc *f, const char *p){
    f->params = realloc(f->params, (size_t)(f->nparams + 1) * sizeof(char*));
    if(!f->params){ perror("realloc"); exit(1); }
    f->params[f->nparams++] = mini_strdup(p);
}

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

/* 読み込みの最後に、集めた本体をまとめて文の木にする。 */
static void mini_compile_all(MiniFunc **v, int n){
    for(int i = 0; i < n; i++){
        char err[512];
        if(!mini_compile_func(v[i], err, sizeof(err)))
            axx_diagf(1, 0, " error - %s\n", err);
        mini_compile_all(v[i]->children, v[i]->nchildren);
    }
}

/* --------------------------- binary_list からの呼び出し --------------------------- */

/* `.call 名前(引数, …)` を実行して objl に積む。戻り値は次に読む位置。 */
/* `.call` の引数欄の `[式, 式, ...]` を読んで配列の値にする。
 * t は書き換えてよい作業用バッファ。ok に 0 を返したら読めなかったということ。 */
static MiniVal mini_arg_array(Assembler *asmb, char *t, int a, int *out_i, int *ok){
    MiniVal v; memset(&v, 0, sizeof(v));
    v.is_arr = 1;
    *ok = 0;
    int len = (int)strlen(t);
    int depth = 0, k = a;
    while(k < len){
        if(t[k] == '(' || t[k] == '[') depth++;
        else if(t[k] == ')' || t[k] == ']'){ depth--; if(depth == 0) break; }
        k++;
    }
    if(depth != 0 || k >= len || t[k] != ']'){ *out_i = len; return v; }
    /* 中身だけを見せるため、いったん `]` を終端にする。 */
    t[k] = 0;
    int i = a + 1;
    while(1){
        i = axx_skipspc(t, i);
        if(!t[i]) break;
        if(t[i] == ','){ i++; continue; }
        int io;
        uint256_t x = expr_expression_pat(asmb, t, i, &io);
        if(io <= i) break;
        i = io;
        /* 未定義ラベル由来の巨大な番兵で反復回数が爆発しないよう 0 を渡す。 */
        if(u256_is_undef_derived(x)) x = u256_zero();
        mini_arr_reserve(&v, v.n + 1);
        v.arr[v.n++] = x;
        i = axx_skipspc(t, i);
        if(t[i] == ','){ i++; continue; }
        break;
    }
    t[k] = ']';
    *out_i = k + 1;
    *ok = 1;
    return v;
}

static int mini_call_binary(Assembler *asmb, const char *s, int idx, IntVec *objl){
    AsmState *st = &asmb->st;
    int slen = expr_slen(s);
    /* 命令長を測るだけの試し打ちでも makeobj は走るので、そのときは黙る。 */
    int quiet = st->pass1_size_mode;

    idx += 5;
    idx = axx_skipspc(s, idx);
    int j = idx;
    while(j < slen && (isalnum((unsigned char)s[j]) || s[j] == '_')) j++;
    int namelen = j - idx;
    char name[512];
    if(namelen <= 0 || namelen >= (int)sizeof(name)){
        if(!quiet) axx_diagf(1, 0, " error - '.call' needs 'name(argument, ...)'.\n");
        return slen;
    }
    memcpy(name, s + idx, (size_t)namelen); name[namelen] = 0;
    idx = axx_skipspc(s, j);
    if(idx >= slen || s[idx] != '('){
        if(!quiet) axx_diagf(1, 0, " error - '.call' needs 'name(argument, ...)'.\n");
        return slen;
    }
    int depth = 0, k = idx;
    while(k < slen){
        if(s[k] == '(' || s[k] == '[') depth++;
        else if(s[k] == ')' || s[k] == ']'){ depth--; if(depth == 0) break; }
        k++;
    }
    if(depth != 0 || k >= slen){
        if(!quiet) axx_diagf(1, 0, " error - '.call %s': unbalanced parentheses.\n", name);
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
        return idx;
    }

    MiniVal *args = NULL;
    int nargs = 0, cargs = 0;
    int a = 0, alen = (int)strlen(argtext);
    while(1){
        a = axx_skipspc(argtext, a);
        if(a >= alen || !argtext[a]) break;
        if(argtext[a] == ','){ a++; continue; }
        MiniVal av;
        /* `[式, 式, ...]` は配列の引数。要素もパターン層の式。 */
        if(argtext[a] == '['){
            int ok, io;
            av = mini_arg_array(asmb, argtext, a, &io, &ok);
            if(!ok){
                mini_val_free(&av);
                if(!quiet)
                    axx_diagf(1, 0, " error - '.call %s': unbalanced '[' in the "
                               "argument list.\n", name);
                for(int i = 0; i < nargs; i++) mini_val_free(&args[i]);
                free(args);
                free(argtext);
                return idx;
            }
            a = io;
        } else {
            int io;
            uint256_t v = expr_expression_pat(asmb, argtext, a, &io);
            if(io <= a) break;
            a = io;
            /* 未定義ラベル由来の巨大な番兵で反復回数が爆発しないよう 0 を渡す。 */
            if(u256_is_undef_derived(v)) v = u256_zero();
            av = mini_num(v);
        }
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
        /* 返り値もワードになる。配列なら添字 0 から順に、スカラーなら 1 ワード。 */
        if(r.has_ret){
            if(r.retval.is_arr)
                for(int i = 0; i < r.retval.n; i++) iv_push(objl, r.retval.arr[i]);
            else
                iv_push(objl, r.retval.num);
        }
    } else {
        if(!quiet) axx_diagf(1, 0, " error - %s\n", r.c.err);
    }
    for(int i = 0; i < r.nframes; i++) mini_frame_clear(&r.frames[i]);
    free(r.frames);
    mini_drop_ret(&r);
    free(r.out.data);
    for(int i = 0; i < nargs; i++) mini_val_free(&args[i]);
    free(args);
    return idx;
}

/* 前後の空白を落とす（s は書き換え可能であること）。 */
static char *pat_trim(char *s){
    char *p = s + axx_skipspc(s, 0);
    size_t n = strlen(p);
    while(n > 0 && isspace((unsigned char)p[n-1])) p[--n] = '\0';
    return p;
}

/* `.func 名前(引数, 引数)` の見出しを名前と引数名の配列に分解する。
 * 引数欄は丸ごと省略できる（`.func name`）。空の括弧 `.func name()` も同じ。
 * `.call 名前(引数)` の呼び出し側と同じ書き方にそろえるための形。
 *
 * 旧来の `.func::名前::引数,引数` も読める。`.func` の直後が `::` のときだけ
 * そちらに切り替えるので、新しい形と取り違えることはない。
 *
 * 戻り値: 0=成功。0以外ならエラーで、errbuf に理由が入る。
 * name / params は呼び出し側が用意した領域に書く（params は最大 npmax 個）。 */
static int parse_func_header(const char *l, char *name, size_t nsz,
                             char *params, size_t psz, int npmax, int *np,
                             char *errbuf, size_t esz){
    name[0] = '\0';
    *np = 0;
    errbuf[0] = '\0';

    /* 行頭の空白を落とし、末尾の空白も見ないよう長さを詰める。 */
    int b = axx_skipspc(l, 0);
    const char *t = l + b;
    int tlen = (int)strlen(t);
    while(tlen > 0 && isspace((unsigned char)t[tlen-1])) tlen--;

    int i = 1;   /* t[0] は '.' */
    while(i < tlen && (isalnum((unsigned char)t[i]) || t[i]=='_')) i++;
    i = axx_skipspc(t, i);

    if(t[i]==':' && t[i+1]==':'){
        /* 旧形式。`::` で最大3欄に割る。 */
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
    if(k >= tlen) return 0;                 /* `.func name` — 引数なし */
    if(t[k] != '('){
        snprintf(errbuf, esz, " error - '.func': expected '(' or end of line after "
                 "the name, got '%.*s'\n", tlen - k, t + k);
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
            /* 前後の空白は落として報告する（axx.py の strip() と揃える）。 */
            int ts = e + 1, te = tlen;
            while(ts < te && isspace((unsigned char)t[ts])) ts++;
            while(te > ts && isspace((unsigned char)t[te-1])) te--;
            snprintf(errbuf, esz, " error - '.func': trailing text after ')': "
                     "'%.*s'\n", te - ts, t + ts);
            return 1;
        }
    }

    /* 括弧の中をカンマで割る。strtok は使わず自前で刻む（呼び出し側の
     * バッファを壊さないため）。 */
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
        if(q < e) q++;  /* ',' を飛ばす */
    }
    return 0;
}

/* `.map` の式の中の変数を、並びの番号に置き換えた新しい式を作る。
 * 置き換えるのは語として独立している出現だけで、`0xff` の `x` のように
 * 英数字に挟まれたものは触らない。番号は `(3)` と括って埋めるので、
 * `1<<x` は `1<<(3)` となり、前後の演算子の優先順位は変わらない。 */
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
        int is_var = (strncasecmp(expr+k, var, vl) == 0);
        int lsep = (k == 0) || !(isalnum((unsigned char)expr[k-1]) || expr[k-1]=='_');
        int rsep = !(isalnum((unsigned char)expr[k+vl]) || expr[k+vl]=='_');
        if(is_var && lsep && rsep){ memcpy(out+w, num, nl); w += nl; k += vl; }
        else out[w++] = expr[k++];
    }
    out[w] = '\0';
    return out;
}

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

    char this_dir[1024];
    axx_dir_of(fn, this_dir, sizeof(this_dir));

    if(asmb->st.pat_include_depth == 1){
        macro_reset_pass_pattern();
        subv_free(&asmb->st.subs);
        mfv_free(&asmb->st.funcs);
    }

    int nexp = 0;
    char **exp = pat_macro_expand(f, fn, &nexp);
    fclose(f);
    f = NULL;

    /* 破綻点修正: 「本物の複数行ブロックコメント(閉じ記号が後の行にあり、
     * 中身の行は開始記号で始まらない)」と「開始記号を単なる行末コメントの
     * 目印として毎行書くだけの古い流儀(コメントの各行が開始記号で始まり、
     * 閉じ記号は無いか、あっても離れた場所にある別の無関係なコメントの
     * ものでしかない)」の2つの書き方が実在のパターンファイルに混在している。
     * 「次の1行だけ」を見て判定すると、旧来スタイルの連続コメントの最後の
     * 1行(次の行はもう普通のコード)を誤って「本物のブロックコメント開始」
     * と誤認し、たまたま遠く離れた場所にある無関係な閉じ記号まで実際の
     * パターン行を丸ごと呑み込んでしまう(8080.axx で発生)。そこで、
     * 「直前の行も開始記号で始まる行で、かつ単発扱い(旧来スタイル)と
     * 判定されていたか」を legacy_chain として引き継ぎ、旧来スタイルの
     * 連続コメントは何行続いても・最後の1行であっても単発行として扱う。
     * legacy_chain が途切れた(=直前が普通のコードだった)場合のみ、次の
     * 行が開始記号で始まらずかつこの位置より後ろに閉じ記号が本当に存在する
     * ときに限り、新規のブロックコメントとして正しく閉じるまで追跡する。 */
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
            /* このコメントはこの行の中で完結した(あるいは元々コメントで
             * なかった)ので、旧来スタイルの連鎖はここで途切れる。 */
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

        /* ミニ言語の `.func` 本体は `::` で分解せず、行のまま集める。 */
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
                    enum { FUNC_PARAM_MAX = 64, FUNC_NAME_MAX = 256 };
                    char nmbuf[FUNC_NAME_MAX];
                    char *pbuf = malloc((size_t)FUNC_PARAM_MAX * FUNC_NAME_MAX);
                    if(!pbuf){ perror("malloc"); exit(1); }
                    char errbuf[512];
                    int nparam = 0;
                    int hdr_err = parse_func_header(line, nmbuf, sizeof(nmbuf),
                                                    pbuf, FUNC_NAME_MAX,
                                                    FUNC_PARAM_MAX, &nparam,
                                                    errbuf, sizeof(errbuf));
                    int ok = 1;
                    if(hdr_err){
                        axx_diagf(1, 0, "%s", errbuf);
                        ok = 0;
                    } else if(!is_sub_name(nmbuf)){
                        axx_diagf(1, 0, " error - '.func' needs a name made of letters, "
                                   "digits and '_': '%s'\n", nmbuf);
                        ok = 0;
                    }
                    MiniFunc *parent = nfunc_stack ? func_stack[nfunc_stack-1] : NULL;
                    MiniFunc *nf = mini_func_new(asmb, parent, ok ? nmbuf : "?", fn, li + 1);
                    if(ok){
                        for(int q=0;q<nparam;q++){
                            char *pn = pbuf + (size_t)q*FUNC_NAME_MAX;
                            if(!is_sub_name(pn)){
                                axx_diagf(1, 0, " error - '.func %s': bad parameter "
                                           "name '%s'\n", nmbuf, pn);
                            } else {
                                mini_func_addparam(nf, pn);
                            }
                        }
                    }
                    free(pbuf);
                    func_stack[nfunc_stack++] = nf;
                    continue;
                }
                MiniFunc *cur = func_stack[nfunc_stack-1];
                if(strcmp(dk, ".ENDFUNC") == 0){
                    /* 本体を閉じるのは `.endfunc` のみ。`.if`/`.while`/`.for` が
                     * 閉じきらないまま来たら壊れたパターンなので報告するが、
                     * 後続行を巻き込まないよう関数はここで閉じてしまう。 */
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
                        axx_diagf(1, 0, " error - '.func::%s': %s without a matching "
                                   "block opener.\n", cur->name, dk);
                        cur->depth = 0;
                    }
                }
                {
                    int nb = axx_skipspc(line, 0);
                    if(line[nb]) mini_func_addline(cur, line, fn, li + 1);
                }
                continue;
            }
        }

        char uline[16]={0};
        int si=axx_skipspc(line,0);
        for(int i=0;i<8&&line[si+i];i++) uline[i]=axx_upper_char(line[si+i]);
        if(strcmp(uline,".INCLUDE")==0){ include_pat(asmb,line+si,this_dir); continue; }

        /* 破綻点修正: フィールドを char[8][1024] の固定長に写していたため、
         * 1023 文字を超える欄（長い三項式や @@[] を並べた符号化欄など）が
         * 診断もなく途中で切れていた。axx.py には長さの制限が無いので、
         * 同じパターンファイルから違うバイト列が出る。行長から必要量が
         * 決まるので、行ごとに確保する。 */
        size_t fsz = strlen(line) + 1;
        char *fbuf = malloc(8 * fsz);
        if(!fbuf){ perror("malloc"); exit(1); }
        char *fields[8];
        for(int i=0;i<8;i++){ fields[i] = fbuf + (size_t)i*fsz; fields[i][0]=0; }
        int nf=0;
        int idx=0;
        while(1){
            idx=axx_get_params1(line,idx,fields[nf],fsz);
            nf++;
            if(idx>=(int)strlen(line)||nf>=8) break;
        }

        /* `.sub::名前 … .return` はパターン層のサブ表。中の項目は本体の
         * パターン表には積まず、サブ表として別に覚えておく。 */
        {
            char kw[16]={0};
            {
                /* fields[0] は書き換えずに、前後の空白を除いた大文字の写しを作る。 */
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
                free(fbuf); continue;
            }
            if(strcmp(kw,".RETURN")==0){
                if(!cur_sub)
                    axx_diagf(1, 0, " error - '.return' without a matching '.sub'.\n");
                cur_sub = NULL;
                free(fbuf); continue;
            }
            if(cur_sub){
                if(nf<2){
                    if(pat_trim(fields[0])[0])
                        axx_diagf(1, 0, " error - sub table '%s': entry has no '::' "
                                   "field separator: '%s'\n", cur_sub->name, fields[0]);
                } else {
                    subdef_push(cur_sub, fields[0], fields[nf-1]);
                }
                free(fbuf); continue;
            }
        }

        /* `.map::<変数>::<名前の並び>::<式>` の書式検査。展開は
         * setpatsymbols() と dir_map() で行う（並びに配列シンボルを書けるよう
         * にするため。配列はパターンを読み終えてから登録される）。 */
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
            if(nonblank){
                axx_diagf(0, 0, " warning - pattern line has no '::' field separator "
                           "and can never match (a pattern file has no line-"
                           "continuation mechanism, so this is likely a stray "
                           "line left over from a multi-line comment, or a "
                           "binary_list/error_patterns that was continued onto "
                           "the next physical line): '%s'\n", fields[0]);
            }
        }
        PatEntry *pe=pv_push_blank(&asmb->st.pat);
        if(nf==1){ pat_set(pe,0,fields[0]); }
        else if(nf==2){ pat_set(pe,0,fields[0]); pat_set(pe,2,fields[1]); }
        else if(nf==3){ pat_set(pe,0,fields[0]); pat_set(pe,1,fields[1]); pat_set(pe,2,fields[2]); }
        else if(nf==4){ pat_set(pe,0,fields[0]); pat_set(pe,1,fields[1]); pat_set(pe,2,fields[2]); pat_set(pe,3,fields[3]); }
        else if(nf==5){ for(int i=0;i<5;i++) pat_set(pe,i,fields[i]); }
        else if(nf>=6){ for(int i=0;i<6;i++) pat_set(pe,i,fields[i]); }
        free(fbuf);
    }
    if(in_block_comment){
        axx_diagf(0, 0, " warning - pattern file '%s' ends while a /* ... */ comment "
                   "is still open (missing closing '*/').\n", fn);
    }
    if(cur_sub){
        axx_diagf(1, 0, " error - pattern file '%s' ends while sub table '%s' is "
                   "still open (missing '.return').\n", fn, cur_sub->name);
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
        /* `"..."` の中身は文字列テンプレート（3.5.2）の材料なので、
         * 連番置換の対象にせずそのまま写す。 */
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

/* エンコーディング欄の `@@[個数, 式]` を個数分だけ展開する。
 * 例: `0xe8,@@[4,*(e-$.,%%)]` は 4 バイトのリトルエンディアン展開になる。
 * is_empty には「展開の結果ワードが1つも無い」ことを返す（`;` 条件付き出力で
 * 何も出さない命令を、長さ0として扱うため）。 */
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
                /* `"..."` の中の `[` `]` `,` は区切りとして数えない。 */
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
                /* 破綻点修正: 1024 バイトの自動変数に写していたため、長い
                 * `@@[n, ...]` の反復パターン（や回数の式）が診断もなく途中で
                 * 切れていた。axx.py には制限が無いので同じパターンファイルから
                 * 違うバイト列が出る。実際の長さぶんだけ確保する。 */
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
                /* 破綻点修正: 繰り返し回数の未定義判定のために旗を降ろしたまま
                 * 復元していなかったため、オペランド捕捉の段階で立った
                 * 「未定義ラベルを踏んだ」という情報が、`@@[]` を含むパターンでは
                 * 必ず消えていた。makeobj() は e_p() の呼び出し「後」に旗を退避
                 * するので、呼び出し元の状態ごと失われていた。 */
                int _rep_prior = asmb->st.error_undefined_label;
                asmb->st.error_undefined_label = 0;
                uint256_t nv=expr_expression_pat(asmb,expr_part,0,&io);
                int _rep_undef = asmb->st.error_undefined_label;
                asmb->st.error_undefined_label = _rep_prior || _rep_undef;
                int64_t nrep=u256_to_i64(nv);
                /* 破綻点修正: 繰り返し回数について、未定義ラベルの判定も上限の
                 * チェックも無かった（axx.py はどちらも行う）。未定義なら 0 回、
                 * 上限 (1<<24) 超はエラーにして 0 回に倒す。 */
                const int64_t N_MAX = (int64_t)1 << 24;
                if(_rep_undef || u256_is_undef_derived(nv)) nrep = 0;
                /* 破綻点修正: nrep は u256_to_i64() で下位64bitに切り詰めた値
                 * なので、2**64+3 のような回数が 3 に化けて上限チェックを
                 * すり抜けていた（axx.py はエラーにする）。元の 256bit 値でも
                 * 判定し、表示も切り詰めない値で行う。 */
                else if(u256_gt_signed(nv, u256_from_i64(N_MAX))){
                    char cb[96]; u256_to_pydec(nv, cb, sizeof(cb));
                    axx_diagf(0, 0, " error - @@[n,...]: repeat count %s exceeds maximum %lld.\n",
                              cb, (long long)N_MAX);
                    asmb->st.had_error = 1;
                    nrep = 0;
                }
                if(nrep>0){
                    has_content=1;
                    /* 破綻点修正: rep_pat をそのまま複製していたため、その中に
                     * ネストした @@[...] があっても再帰展開されず、
                     * axx.py（e_p を再帰呼び出しして展開する）と食い違って
                     * いた。展開してから複製する。 */
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
            /* `"..."` の中は `@@[` の展開対象にせず、そのまま写す。 */
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

/* ==================== 配列シンボル ====================
 * `.setsym::名前::[項目,項目,…]` で登録する。項目は数値の式でも
 * `"文字列"` でもよく、混ざっていてもよい。添字は 0 から数える。
 *   x[3]      … 文字列テンプレート（3.5.2）の中から
 *   #x[3]     … 式の中から（数値の項目のみ）
 * 数は多くないので、文字列シンボルと同じく素直な線形探索で引く。 */
static int arrsym_find(AsmState *st, const char *upper_name){
    for(int i=0;i<st->arrsyms_len;i++)
        if(strcmp(st->arrsyms[i].name, upper_name)==0) return i;
    return -1;
}
static struct ArrSym *arrsym_get(AsmState *st, const char *upper_name){
    int i = arrsym_find(st, upper_name);
    return (i < 0) ? NULL : &st->arrsyms[i];
}
static void arrsym_free_one(struct ArrSym *a){
    for(int i=0;i<a->len;i++) free(a->items[i].s);
    free(a->items); free(a->name);
    a->items = NULL; a->name = NULL; a->len = 0;
}
static void arrsym_delete(AsmState *st, const char *upper_name){
    int i = arrsym_find(st, upper_name);
    if(i < 0) return;
    arrsym_free_one(&st->arrsyms[i]);
    for(int k=i+1;k<st->arrsyms_len;k++) st->arrsyms[k-1] = st->arrsyms[k];
    st->arrsyms_len--;
}
static void arrsym_clear_all(AsmState *st){
    for(int i=0;i<st->arrsyms_len;i++) arrsym_free_one(&st->arrsyms[i]);
    free(st->arrsyms);
    st->arrsyms = NULL; st->arrsyms_len = 0; st->arrsyms_cap = 0;
}

/* 組み立て済みの項目列をそのまま配列シンボルとして据える（所有権を渡す）。 */
static void arrsym_install(AsmState *st, const char *dst_upper, SymItem *items, int n){
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

/* 既にある配列シンボルをそのまま複製する。`.setsym::y::x` 用。 */
static void arrsym_copy(AsmState *st, const char *dst_upper, const char *src_upper){
    struct ArrSym *src = arrsym_get(st, src_upper);
    if(!src) return;
    /* 自分自身への代入は何もしない（複製元を消してしまわないように）。 */
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

/* 値欄が「名前ひとつ」で、それが文字列／配列シンボルなら複製する。
 * `.setsym::y::x` が `x` の写しを作るための枝で、複製したら真を返す。
 * 素の名前は本来ラベル参照なので（シンボルは `#x` と書く）、ここで拾っても
 * これまで書けていた式の意味は変わらない。 */
static int symbol_copy_from_name(AsmState *st, const char *dst_upper, const char *value_field){
    const char *q = value_field;
    while(*q==' '||*q=='\t') q++;
    const char *b = q;
    if(!(isalpha((unsigned char)*q) || *q=='_')) return 0;
    while(isalnum((unsigned char)*q) || *q=='_') q++;
    int n = (int)(q - b);
    while(*q==' '||*q=='\t') q++;
    if(*q) return 0;                 /* 名前だけの欄ではない */
    char src[512];
    if(n >= (int)sizeof(src)) return 0;
    for(int i=0;i<n;i++) src[i] = (char)axx_upper_char(b[i]);
    src[n] = '\0';

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
    return 0;
}

/* ==================== 集合（名前の並び）====================
 * `.setsym::a::a1,a2,a3` は名前の集合を作り、`.setsym::x::a&b` のように
 * 既にある集合どうしを演算できる。集合は配列シンボルとして持つので、
 * `.check` `.enum` `.map` の並び欄や `{{a}}` からそのまま使える。 */

typedef struct { SymItem *data; int len, cap; } ItemVec;

static void itv_init(ItemVec *v){ v->data = NULL; v->len = 0; v->cap = 0; }
static void itv_free(ItemVec *v){
    for(int i=0;i<v->len;i++) free(v->data[i].s);
    free(v->data);
    itv_init(v);
}
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
static int symitem_eq(const SymItem *a, const SymItem *b){
    if(a->is_str != b->is_str) return 0;
    if(a->is_str) return strcmp(a->s ? a->s : "", b->s ? b->s : "") == 0;
    return u256_eq(a->v, b->v);
}
static int itv_has(const ItemVec *v, const SymItem *it){
    for(int i=0;i<v->len;i++) if(symitem_eq(&v->data[i], it)) return 1;
    return 0;
}
/* 集合なので同じ要素は1つだけ持つ。並び順は最初に現れた順。 */
static void itv_push_unique(ItemVec *v, const SymItem *it){
    if(!itv_has(v, it)) itv_push(v, it);
}

/* acc に rhs を演算子 op で作用させる。演算子は左から順に適用する。 */
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
    } else {   /* '-' */
        for(int i=0;i<acc->len;i++)
            if(!itv_has(rhs, &acc->data[i])) itv_push_unique(&out, &acc->data[i]);
    }
    itv_free(acc);
    *acc = out;
}

/* 集合の要素として書ける名前なら大文字化して out へ。でなければ 0。
 * 数字で始まるものと空白を含むものは名前とみなさない（`.setsym::X::1,2` の
 * ような数式が集合に化けないようにするため）。 */
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

/* 集合式の被演算子。素の識別子で、既にある集合ならその項目を out へ。 */
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

/* `a&b` `a|b` `a^b` `a+b` `a-b` の集合式を評価する。
 * 被演算子はすべて既にある集合であること。集合式として読めなければ 0。
 * axx.py の set_expr_from_text() と同じ規則である。 */
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
    if(nops == 0){ itv_free(&acc); return 0; }   /* 演算子が無ければ集合式ではない */
    *out = acc;
    return 1;
}

/* `名前,名前,…` を集合の項目にする。集合として読めなければ 0。
 * 項目に既存の集合の名前を書くと、その中身をその場に展開する。
 * axx.py の set_literal_from_text() と同じ規則である。 */
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

/* 値欄が集合の書き方なら、その集合を作って真を返す。
 *   .setsym::a::a1,a2,a3   名前の集合
 *   .setsym::x::a&b        既にある集合どうしの演算
 * 結果は写しなので、あとで元の集合を書き換えても影響しない。
 * axx.py の symbol_set_from_text() と同じ規則である。 */
static int symbol_set_from_text(AsmState *st, const char *dst_upper, const char *value_field){
    ItemVec items;
    if(!set_expr_from_text(st, value_field, &items)
       && !set_literal_from_text(st, value_field, &items)) return 0;
    arrsym_install(st, dst_upper, items.data, items.len);   /* 所有権を移す */
    return 1;
}

/* `[...]` の中身を項目に切って登録する。q は `[` を指していること。
 * 区切りは最上位のカンマだけで、`"..."` の中や入れ子の括弧の中のカンマは
 * 区切りにしない（`[1,(2,3)]` のような書き方で崩れないようにするため）。 */
static void arrsym_set_from_text(Assembler *asmb, const char *upper_name, const char *q){
    AsmState *st = &asmb->st;
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

    const char *p = q + 1;         /* `[` の次から */
    while(*p){
        while(*p==' '||*p=='\t') p++;
        if(*p==']' || !*p) break;
        /* 1項目ぶんの範囲を測る。 */
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
        if(item[0]=='"'){
            it->is_str = 1;
            it->s = txt_template_inner(item);
        } else if(item[0]){
            int io;
            it->v = expr_expression_pat(asmb, item, 0, &io);
        }
        free(item);
        if(*p==',') p++;
        else break;
    }
}

/* 文字列シンボルの表。数は多くないので素直な線形探索で引く。
 * 名前は大文字化した形で覚える（`.setsym` の数値シンボルと同じ規約）。 */
static int strsym_find(AsmState *st, const char *upper_name){
    for(int i=0;i<st->strsym_names.len;i++)
        if(strcmp(st->strsym_names.data[i], upper_name)==0) return i;
    return -1;
}
static const char *strsym_get(AsmState *st, const char *upper_name){
    int i = strsym_find(st, upper_name);
    return (i < 0) ? NULL : st->strsym_vals.data[i];
}
static void strsym_set(AsmState *st, const char *upper_name, const char *val){
    int i = strsym_find(st, upper_name);
    if(i >= 0){ free(st->strsym_vals.data[i]); st->strsym_vals.data[i] = strdup(val); return; }
    sv_push(&st->strsym_names, upper_name);
    sv_push(&st->strsym_vals,  val);
}
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

/* ==================== 文字列テンプレートのエンコーディング欄 ====================
 * パターンの3欄目が `"..."` で始まるとき、その行は式の並びではなく
 * 「アセンブリ結果のテキスト」を作る。別の書式のニーモニックへ書き換える
 * ための欄で、たとえば
 *
 *     MOV R!r,!e:: "LD R{{r}},0x{{.hex(e)}}"
 *
 * に `MOV R1,0x10` を与えると `LD R1,0x10` を出す。
 *
 * 置き換わるのは `{{ }}` で囲んだところだけで、それ以外は書いたままの字が
 * 出る。`{{ }}` の中には
 *   - `式`                          … 評価して10進で埋める
 *   - `.hex(式)` `.dec(式)` `.bin(式)` `.float(式)`
 *                                   … 16進/10進/2進/浮動小数の文字列にする
 *                                     （桁だけで、`0x` などの接頭辞は付かない
 *                                      ので、要るなら外に書く）
 *   - `名前` `名前[添字]`           … 文字列シンボル／配列シンボル、
 *                                     どちらでもなければパターン変数の値
 * が書ける。文字列の外と同じく `\n` `\t` `\r` `\\` `\"` は解く。
 *
 * 組み上がったテキストはそのままバイナリとしても出る。`.ascii` と同じく
 * UTF-8 の 1 バイトが 1 ワードになり、ロケーションカウンタもその分進んで
 * バイナリ／ELF 出力に載る。標準出力へのテキスト出力（トランスレータとしての
 * 使い方）はそのまま残るので、同じパターンで両方が得られる。 */

typedef struct { char *b; size_t len, cap; } TxtBuf;

static void txt_init(TxtBuf *t){ t->b=NULL; t->len=0; t->cap=0; }
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

/* -v の診断行に見せる写し。行が折れないよう、テキストの中の改行やタブは
 * `\n` `\t` と書いたまま見せる。素のまま流す方（トランスレータとしての
 * 標準出力）は解いた文字のままで、こちらは表示用の写しだけを変える。 */
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

/* 値を radix 進の桁だけの文字列にする（`0x` のような接頭辞は付けない）。
 * 負の値は 2 の補数のままではなく `-` を付けた絶対値で出す。 */
static void txt_radix(TxtBuf *t, uint256_t v, int radix){
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

/* `.float(式)` は値を10進128ビット浮動小数点数（有効数字34桁）として書く。
 * 表記は「digits を d1.d2d3… ×10^exp10 と読む」形に正規化してから組み立てる。
 * 指数が小さいうちは普通の小数表記にし、小数部が無ければ `.0` を付ける
 * （16 なら `16.0`）。axx.py の _txt_float_parts() と同じ規則である。 */
#define TXT_FLOAT_PREC 34

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

/* 整数として束縛された値。10進の桁をそのまま取り出し、34桁を超える分は
 * 四捨五入して落とす。 */
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
            /* 全桁が繰り上がったら桁が1つ増える。 */
            if(i < 0){ memmove(all+1, all, (size_t)n+1); all[0] = '1'; exp10++; }
        }
    }
    txt_float_emit(t, neg, all, n, exp10);
}

/* 浮動小数として束縛された値。34桁に正しく丸めた10進を取り出す。 */
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

/* テンプレート中の丸括弧の対応を取り、閉じ括弧の位置を返す。 */
static int txt_close_paren(const char *s, int i){
    int depth = 0;
    for(; s[i]; i++){
        if(s[i]=='(') depth++;
        else if(s[i]==')'){ if(--depth == 0) return i; }
    }
    return -1;
}

/* `.hex` `.dec` `.bin` `.float` のどれかなら、名前の長さを返す。違えば 0。 */
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

/* 式を評価し、kind（-1/1:10進 0:16進 2:2進 3:浮動小数）に従って積む。 */
static void txt_emit_expr(Assembler *asmb, TxtBuf *t, const char *expr, int kind){
    AsmState *st = &asmb->st;
    int io;
    int saved_undef = st->error_undefined_label;
    st->error_undefined_label = 0;
    uint256_t v = expr_expression_pat(asmb, expr, 0, &io);
    if(st->error_undefined_label) saved_undef = 1;
    st->error_undefined_label = saved_undef;

    switch(kind){
    case 0: txt_radix(t, v, 16); break;
    case 2: txt_radix(t, v, 2);  break;
    case 3:
        /* 浮動小数として評価された式はビット列を、そうでなければ整数値を読む。 */
        if(st->exp_typ_float) txt_float_double(t, u256_to_double(v));
        else                  txt_float_int(t, v);
        break;
    default: txt_radix(t, v, 10); break;
    }
}

/* テンプレートの中の名前を解決して積む。
 * 優先順位は
 *   1. `.setsym::名前::"文字列"` の文字列シンボル … その文字列
 *   2. 変数として使われている名前                 … パターン変数の値（10進）
 *   3. どれでもない                               … 書かれたままの文字
 * で、`{{x}}` の `x` は 1 に、`{{r}}` の `r` は 2 に当たる。
 * 数値シンボルをここで引かないのは、`num=` のような普通の文（たまたま
 * `.setsym::NUM` がある）が黙って数字に化けるのを避けるため。数値が要る
 * ときは `{{#NUM}}` と書けば本体の式評価器が引く。 */
static void txt_emit_name(Assembler *asmb, TxtBuf *t, const char *name, int len){
    AsmState *st = &asmb->st;
    char key[512];
    if(len >= (int)sizeof(key)) len = (int)sizeof(key)-1;
    for(int k=0;k<len;k++) key[k] = (char)axx_upper_char(name[k]);
    key[len] = '\0';

    const char *sv = strsym_get(st, key);
    if(sv){ txt_adds(t, sv); return; }

    /* 添字なしの配列は、全項目を `,` でつないで出す。 */
    struct ArrSym *ar = arrsym_get(st, key);
    if(ar){
        for(int k=0;k<ar->len;k++){
            if(k) txt_addc(t, ',');
            if(ar->items[k].is_str) txt_adds(t, ar->items[k].s);
            else                    txt_radix(t, ar->items[k].v, 10);
        }
        return;
    }

    /* パターン変数（`a` でも `var_2` でも同じ規則）。パターンファイルが
     * その名前を変数として使っていれば値を、そうでなければ書かれたままの
     * 文字を出す。ふつうの単語が黙って数字に化けないようにするためで、
     * 変数と決まっている名前が未束縛なら 0 になる。 */
    if(is_var_name_n(name, len)){
        int vs = var_slot(name, len, 0);
        if(vs >= 0){ txt_radix(t, st->vars[vs].val, 10); return; }
    }
    txt_addn(t, name, (size_t)len);
}

/* `x[3]` のような添字つきの参照を積む。添字は式で、0 から数える。
 * 配列でない名前や範囲外の添字は診断して何も出さない。 */
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
    int io;
    int saved_undef = st->error_undefined_label;
    st->error_undefined_label = 0;
    uint256_t iv = expr_expression_pat(asmb, idxtext, 0, &io);
    if(st->error_undefined_label) saved_undef = 1;
    st->error_undefined_label = saved_undef;
    int64_t n = u256_to_i64(iv);
    if(n < 0 || n >= ar->len){
        if(should_report_errors(st))
            axx_diagf(1, 0, " error - index %lld is out of range for array symbol "
                       "'%s' (0..%d).\n", (long long)n, key, ar->len-1);
        return;
    }
    if(ar->items[n].is_str) txt_adds(t, ar->items[n].s);
    else                    txt_radix(t, ar->items[n].v, 10);
}

/* 名前の直後の `[...]` の閉じ位置を返す。無ければ -1。 */
static int txt_close_bracket(const char *s, int i){
    int depth = 0;
    for(; s[i]; i++){
        if(s[i]=='[') depth++;
        else if(s[i]==']'){ if(--depth == 0) return i; }
    }
    return -1;
}

/* `{{...}}` の中身が名前ひとつだけかどうか。そうなら長さを返す。 */
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

/* テンプレート本文（引用符の中身）を展開して t に積む。 */
static void txt_render(Assembler *asmb, TxtBuf *t, const char *s){
    AsmState *st = &asmb->st;
    for(int i = 0; s[i]; ){
        if(s[i]=='\\' && s[i+1]){
            /* `.ascii` と同じ逃げ方をする制御文字だけを解き、それ以外の
             * `\x` は x をそのままの字として出す（小文字の逃げ道）。 */
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
            /* `{{.hex(e)}}` のように中身が変換関数ならそれを使う。 */
            int j = 0; while(inner[j]==' ') j++;
            int kind = -1, nl = 0;
            if(inner[j]=='.') nl = txt_conv_name(inner+j+1, &kind);
            int done = 0;
            if(nl){
                int cp = txt_close_paren(inner, j+1+nl);
                if(cp > 0){
                    inner[cp] = '\0';
                    txt_emit_expr(asmb, t, inner + j + 1 + nl + 1, kind);
                    done = 1;
                }
            }
            if(!done){
                /* `{{x[3]}}` のように名前と添字なら、配列シンボルを引く。 */
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
                /* `{{x}}` のように名前ひとつなら、文字列／配列シンボルを先に見る。 */
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

/* `"..."` から中身を取り出す。`\` はそのまま残して txt_render() に任せる。 */
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

/* パターンのエンコーディング欄を評価して、出力ワード列 objl を作る。
 * s_in はカンマ区切りの式の並び。`%%`(連番) と `@@[]`(反復) は呼び出し前に
 * 展開済み。要素が `;` で始まるものは条件付き出力で、値が 0 なら何も出さない
 * （x86 の REX プレフィックスの有無のような分岐に使う）。
 * 要素が `"..."` のときは文字列テンプレート（3.5.2）で、展開したテキストの
 * バイト列がそのままワードになる。式と混ぜて並べてよい。 */
static void makeobj(Assembler *asmb, const char *s_in, IntVec *objl){
    AsmState *st=&asmb->st;
    iv_clear(objl);

    /* 行に現れた `"..."` の展開結果をつないでおく。標準出力へのテキスト出力
     * （トランスレータとしての使い方）に使う。 */
    TxtBuf txtacc;  txt_init(&txtacc);
    TxtBuf dispacc; txt_init(&dispacc);
    int have_text = 0;

    size_t ep_cap = 8192;
    char *ep_buf = NULL;
    int is_empty = 0;

    /* 破綻点修正: バッファが小さすぎて再試行するとき、e_p() はキャプチャ
     * スロット(vars / elf_var_to_label / elf_refs)を書き換える副作用を
     * 持つ。捨てられる1回目の評価の副作用が2回目の評価に持ち越されると、
     * 「同じキャプチャ参照の2回目の出現」と誤判定されて曖昧扱いになり、
     * 有効なラベル→変数キャプチャが静かに失われることがあった。
     * combo_done 側の既存パターンと同じく、再試行のたびに退避した状態へ
     * 復元してから e_p() を呼び直す。 */
    PatVar saved_vars[NVARS];
    memcpy(saved_vars, st->vars, sizeof(saved_vars));
    int saved_elf_refs_len = st->elf_refs_len;
    struct {int set; char *label_name; uint64_t label_val;} saved_vtl[NVARS];
    /* 退避した個数を控える。e_p() の評価中に `名前:=式` で変数名が増えても、
     * 復元は退避した分だけを回す。 */
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
    /* 破綻点修正(性能): 要素ごとの評価に「長さは既知・二重NUL終端済み」を
     * 教えて、文字列全体の複製と strlen() の掛け直しを省く。s はこのループが
     * 終わるまで解放されないので、番地が使い回されて古くなることはない。 */
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
            /* `;;要素` は評価だけして何も出さない。 */
            if(s[idx]==';'){ drop=1; idx++; }
        }
        /* `"..."` はテキストとして展開し、そのバイト列をワードとして出す。 */
        {
            int qs = idx;
            while(s[qs]==' '||s[qs]=='\t') qs++;
            if(s[qs]=='"'){
                char *inner = txt_template_inner(s+qs);
                TxtBuf t; txt_init(&t);
                txt_render(asmb, &t, inner);
                free(inner);
                const char *txt = t.b ? t.b : "";
                /* `;;` は何も出さず、`;` は中身が空なら出さない。 */
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
                    /* 診断行では欄に書いたとおり `"A","B"` と分けて見せる。 */
                    if(have_text) txt_addc(&dispacc, ',');
                    txt_addc(&dispacc, '"');
                    txt_add_escaped(&dispacc, txt);
                    txt_addc(&dispacc, '"');
                    have_text = 1;
                }
                free(t.b);
                /* 閉じ `"` の次まで読み飛ばす。 */
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
            /* 引数はふつうのパターン式なので、ここでも何ワード目かを立てておく。
             * そうしないと `.call` に渡したラベル参照が追跡されず、`.reloc` を
             * 宣言してもリロケーションが出ない。 */
            int _call_widx = objl->len;
            st->elf_current_word_idx = _call_widx;
            idx = mini_call_binary(asmb, s, idx, &callw);
            /* `;` 付きは、出したワードが 1 個で 0 のときだけ何も出さない。 */
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
        /* ワード番号は「いま objl に積まれている数」。`;` 付きで出力されなかった
         * 要素は番号を消費しない（axx.py の `_elf_current_word_idx = len(objl)`）。 */
        int cur_widx = objl->len;
        st->elf_current_word_idx = cur_widx;
        if(st->pas==1) st->pass1_size_mode=1;
        int io;
        uint256_t x=expr_expression_pat(asmb,s,idx,&io);
        if(st->pas==1){ st->pass1_size_mode=0; st->error_undefined_label=0; }
        idx=io;
        /* 破綻点修正: 以前は未定義ラベルを含むワードを objl に積まずに読み飛ばして
         * いたため、命令長と `$.` が axx.py（値がゴミでも必ず積む）とずれていた。
         * 未定義は error_undefined_label の伝播だけで表現し、長さは変えない。 */
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

AXX_UNUSED static int int_cmp(const void*a,const void*b){
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
        /* 破綻点修正: 以前は両方の並びをソートしてから比較していたため、
         * スロットの「順序」が違うだけの EPIC テンプレートまで一致扱いになり、
         * axx.py（`list(k[0]) == list(idxlst)` で順序込みの比較）と
         * 違うテンプレート値を選ぶことがあった。順序込みで比較する。 */
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
            /* 破綻点修正: 以前は「不足数 × NOP のバイト数」個を積んでいた
             * （必要なのは不足数ぶんだけ）。使われるのは先頭 target_len 個なので
             * 出力は変わらないが、NOP 1個ぶんのバイト数倍の無駄な確保をしていた。
             * NOP パターンを周期的に繰り返して、不足数ちょうどを積む
             * （axx.py の「NOP を full 個＋余り」と同じ並びになる）。 */
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
            const char *expr_tail = l + idx;
            int reloc_type = -1;
            const char *dcolon = strstr(expr_tail, "::");
            /* 破綻点修正: `.EQU 式::型名` の式を 1024 バイトの自動変数に写して
             * いたため、長い式が診断もなく途中で切れて axx.py と違う値になって
             * いた。実際の長さぶんだけ確保する。 */
            char *expr_buf = NULL;
            if(dcolon){
                size_t elen = (size_t)(dcolon - expr_tail);
                expr_buf = malloc(elen + 1);
                if(!expr_buf){ perror("malloc"); exit(1); }
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
            free(expr_buf);
            if(label!=lblbuf) free(label);
            out[0]=0; return out;
        } else {
            label_put_value(st,label,st->pc,st->current_section,0,-1,0);
            if(label!=lblbuf) free(label);
            strncpy(out,l+lidx,osz-1); out[osz-1]=0; return out;
        }
    }
    if(label!=lblbuf) free(label);
    strncpy(out,l,osz-1); out[osz-1]=0; return out;
}

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
    if(u256_lt_signed(delta, u256_zero())){
        /* 破綻点修正: delta が負（.org でセクション内の pc を巻き戻した後に
         * .ENDSECTION した場合）でも entry_pc・confirmed を無条件に更新して
         * いたため、次にこのセクションを測る基準点が「既に (旧entry_pc,pc)
         * として section_ranges へ記録済みの範囲」の内側まで後退し、
         * アセンブリ終了時の最終クローズ処理がその範囲と重複するバイト域を
         * 二重に積んでいた（axx.py はこの分岐で entry_pc を変更せずに抜ける
         * ので重複しない。また axx.py はここで警告も出す）。 */
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
    /* 64bit へ切り詰めた値だけで判定すると、2**64 の倍数のような値が 0 に
     * 見えて検査をすり抜けるので、元の 256bit 値でも比較する。 */
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
    if(u256_lt_signed(x, u256_zero())){
        if(should_report_errors(&asmb->st)){
            char cb[96]; u256_to_pydec(x, cb, sizeof(cb));
            axx_diagf(1, 0, " error - .ZERO requires a non-negative count, got %s.\n", cb);
        }
        return 1;
    }
    /* 破綻点修正: 上限チェックが無く、巨大な .ZERO で事実上ハングしていた
     * （axx.py は 1<<28 で打ち切る）。同じ上限を入れる。
     * 64bit に収まらない値は u256_to_i64() の切り捨てで小さく見えうるので、
     * 元の 256bit 値でも判定する。 */
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
    char up[16]; axx_strupr_to(up,l,sizeof(up));
    if(strcmp(up,".EXPORT")!=0 && strcmp(up,".GLOBAL")!=0) return 0;
    /* 破綻点修正: パス1では 0 を返して「未処理」扱いにしていたため、
     * `.global foo` の行がパス1だけパターン照合へ流れ、たまたま一致する
     * パターンがあるとパス1でだけバイトが出てパス1/パス2のアドレスがずれた。
     * ディレクティブとして必ず消費し、記録だけをパス2/対話時に限る。 */
    if(st->pas!=2&&st->pas!=0) return 1;
    /* 破綻点修正: 4096 バイトの自動変数に写してから走査していたため、
     * ラベルを多数並べた `.global a,b,c,...` が診断もなく途中で切れていた
     * （実測: 600 個並べると caxx だけ 513 個しか登録されない）。
     * このバッファは書き換えないので、写さず l2 をそのまま読めばよい。 */
    const char *buf = l2;
    int idx=0; int blen=(int)strlen(buf);
    while(idx<blen&&buf[idx]){
        idx=axx_skipspc(buf,idx);
        char sbuf[512]; size_t ssz;
        char *s = axx_word_buf(buf, idx, sbuf, sizeof(sbuf), &ssz);
        idx=axx_get_label_word(buf,idx,st->lwordchars,s,ssz);
        if(!s[0]){ if(s!=sbuf) free(s); break; }
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
        if(buf[idx]==',') idx++;
    }
    return 1;
}

static int adir_extern(Assembler *asmb, const char *l, const char *l2){
    AsmState *st=&asmb->st;
    char up[16]; axx_strupr_to(up,l,sizeof(up));
    if(strcmp(up,".EXTERN")!=0) return 0;
    /* 破綻点修正: 4096 バイトの自動変数に写してから走査していたため、
     * ラベルを多数並べた `.global a,b,c,...` が診断もなく途中で切れていた
     * （実測: 600 個並べると caxx だけ 513 個しか登録されない）。
     * このバッファは書き換えないので、写さず l2 をそのまま読めばよい。 */
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
        const ElfMachineInfo *_mtbl_ext = elf_machine_find(st->elf_machine);
        int reloc_type = _mtbl_ext ? _mtbl_ext->extern_default : 2;
        /* このEXTERN文自身が `::型名` を明示したかどうか。reloc_type は
         * 明示指定が無ければデフォルト型で埋まってしまうため、reloc_type
         * 自体では「明示されたか」を区別できない。既存ラベルの
         * reloc_type_override は明示指定があったときだけ上書きしたいので、
         * 別のフラグで覚えておく。 */
        int explicit_reloc_type = 0;
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
                else {
                    reloc_type = rtype;
                    explicit_reloc_type = 1;
                }
            }
        }
        if(idx < blen && buf[idx]==':') idx++;
        LabelEntry *existing=lmap_find(&st->labels,s);
        if(!existing){
            lmap_set_imported(&st->labels, s, u256_zero(), ".text", reloc_type);
        } else if(existing->is_imported){
            if(explicit_reloc_type && existing->reloc_type_override >= 0)
                existing->reloc_type_override = reloc_type;
        }
        if(s!=sbuf) free(s);
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

    /* 写さずに読む（理由は adir_export のコメント参照）。 */
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
    PatVar    vars[NVARS];
    struct { char *name; uint64_t val; int word_idx;
             int rtype; int64_t addend; } *refs;
    int       refs_len;
    struct { int set; char *label_name; uint64_t label_val; } vtl[NVARS];
    SymMap    symbols;
    StrVec    check_constraints[NVARS];
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
    for(int i=0;i<g_nvars;i++) free(b->vtl[i].label_name);
    smap_free(&b->symbols);
    for(int i=0;i<g_nvars;i++) sv_free(&b->check_constraints[i]);
    for(int i=0;i<g_nvars;i++) enumdef_clear(&b->enum_defs[i]);
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
        sv_init(&b->check_constraints[i]);
        for(int j=0;j<st->check_constraints[i].len;j++)
            sv_push(&b->check_constraints[i], st->check_constraints[i].data[j]);
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

static void best_restore_dirstate(AsmState *st, const BestMatch *b){
    smap_clear(&st->symbols);
    for(int bi=0; bi<b->symbols.nb; bi++)
        for(SymEntry *e=b->symbols.buckets[bi]; e; e=e->next)
            smap_set(&st->symbols, e->key, e->val);
    for(int i=0;i<g_nvars;i++){
        sv_free(&st->check_constraints[i]);
        for(int j=0;j<b->check_constraints[i].len;j++)
            sv_push(&st->check_constraints[i], b->check_constraints[i].data[j]);
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

    /* ニーモニック直後のパターン文字が英数字を食える種類かどうか。
       小文字（シンボル）, '!'（式）, '\\'（エスケープ）, '['（[[ ]] の開き）,
       数字（リテラル）は食いうる。それ以外（'.' ',' '(' '#' 等のリテラル、
       またはパターン終端）は食えないので、ソース側がそこで語を続けていれば
       不一致が確定する。`MOVE` のパターンを `MOVEM` の行に試さないための足切り。 */
    int closed = 1;
    if(np >= (int)sizeof(pfx)-1){
        closed = 0;               /* 打ち切ったので直後の文字が分からない */
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

/* 作業用バッファは呼び出し元（lineassemble2）がソース行の長さに合わせて確保する。
 *
 * 破綻点修正: ここは l[1024] / l2[4096] / lin[8192] という固定長の自動変数で、
 * それを超える行は診断もなく黙って切り捨てていた。`.ascii "…"` に 4096 文字を
 * 超える文字列を書くと axx.py は全部出すのに caxx は途中で打ち切る、という形で
 * 生成物が食い違っていた（実測: 5000 文字 → axx.py 5000 バイト / caxx 4086 バイト）。
 * バッファ長は行長から決まるので、上限そのものを無くす。
 *   lbuf, l2buf, nsbuf : 各 bufsz バイト（行長+2）
 *   linbuf             : linsz バイト（"l l2" が入る長さ）*/
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
              /* 破綻点修正: axx_get_string() は引用符で始まらない文字列に
               * 常に空を返す。axx.py の include_asm はこの場合、①引用符
               * なしのファイル名らしき語があれば警告した上でそれを使う、
               * ②本当に何もなければエラーにする、のどちらかを必ず行うのに、
               * caxx はここで何もせずに行を読み飛ばしていた（インクルード
               * されるはずの内容が無言でオブジェクトファイルに反映されない、
               * このプロジェクトが最も嫌う「黙って間違った結果を出す」
               * 失敗モードそのもの）。axx.py と同じ2分岐に揃える。 */
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
                  *idx_out=idx; return 1;
              }
          }
          if(raw[0]){
              char resolved[2048];
              const char *cur = st->current_file;
              if(strcmp(raw,"stdin")==0){
                  strncpy(resolved, raw, sizeof(resolved)-1);
                  resolved[sizeof(resolved)-1]='\0';
              } else if(cur && cur[0] && strcmp(cur,"(stdin)")!=0 && strcmp(cur,"stdin")!=0){
                  char abs_buf[2048], dir_buf[2048];
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
        for(int vi=0;vi<g_nvars;vi++){ st->vars[vi].val=u256_zero(); st->vars[vi].is_undef=0; }

        if(dir_set_symbol(asmb,i)) continue;
        if(dir_clear_symbol(asmb,i)) continue;
        if(dir_padding(asmb,i)) continue;
        if(dir_bits(asmb,i)) continue;
        if(dir_symbolc(asmb,i)) continue;
        if(dir_epic(asmb,i)) continue;
        if(dir_vliwp(asmb,i)) continue;
        if(dir_check(asmb,i)) continue;
        if(dir_clrcheck(asmb,i)) continue;
        if(dir_reloc(asmb,i)) continue;
        if(dir_clrreloc(asmb,i)) continue;
        if(dir_map(asmb,i)) continue;
        if(dir_free(asmb,i)) continue;
        if(dir_enum(asmb,i)) continue;
        if(dir_clrenum(asmb,i)) continue;
        if(dir_errmsg(asmb,i)) continue;

        int lw=0; for(int fi=0;fi<PAT_FIELDS;fi++) if(i->f[fi][0]) lw++;
        if(lw==0) continue;

        if(l2[0]) snprintf(lin,linsz,"%s %s",l,l2);
        else      snprintf(lin,linsz,"%s",l);
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
        st->expcaps=&CAPS_ASM;

        PatVar    saved_vars[NVARS];
        memcpy(saved_vars, st->vars, sizeof(saved_vars));
        int saved_refs_len = st->elf_refs_len;
        struct { int set; char *label_name; uint64_t label_val; } saved_vtl[NVARS];
        /* 退避した個数を控える。照合や値欄の評価で新しい変数名が登録されて
         * g_nvars が増えても、書き戻すのは退避した分だけにする。 */
        int saved_nvars = g_nvars;
        for(int vi=0;vi<saved_nvars;vi++){
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
            for(int vi=0;vi<saved_nvars;vi++){
                free(st->elf_var_to_label[vi].label_name);
                st->elf_var_to_label[vi].set        = saved_vtl[vi].set;
                st->elf_var_to_label[vi].label_val  = saved_vtl[vi].label_val;
                st->elf_var_to_label[vi].label_name = saved_vtl[vi].label_name;
                saved_vtl[vi].label_name = NULL;
            }
            st->error_undefined_label=0;

            /* 破綻点修正: 「式もシンボルも0個」なら即打ち切っていたが、スコアは
             * (式の数が少ない, リテラル数が多い, シンボル数が少ない) の順で勝つので、
             * あとからもっとリテラルの多い（より具体的な）パターンが現れうる。
             * 健全な打ち切り条件は `+`/`-` の読み替え（ソースを消費せずリテラル数
             * だけ増える）があるため作りにくく、全走査でも実測で十分速いので、
             * 打ち切り自体をやめて常に最良スコアを選ぶ。 */
        } else {
            /* 破綻点修正: マッチに失敗した候補でも pat_match0() 内の式評価が
             * elf_var_to_label[] を書き換え得る。ここで saved_vtl を書き戻さず
             * label_name を解放するだけだと、失敗した候補による汚染がそのまま
             * 次の候補の pat_match0() に持ち越されてしまう（st->vars は
             * ループ先頭で毎回ゼロクリアされるが elf_var_to_label には
             * 同様のリセットが無い）。成功時の巻き戻しと対称に、ここでも
             * 保存しておいた値を書き戻す。 */
            for(int vi=0;vi<saved_nvars;vi++){
                free(st->elf_var_to_label[vi].label_name);
                st->elf_var_to_label[vi].set        = saved_vtl[vi].set;
                st->elf_var_to_label[vi].label_val  = saved_vtl[vi].label_val;
                st->elf_var_to_label[vi].label_name = saved_vtl[vi].label_name;
                saved_vtl[vi].label_name = NULL;
            }
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
            /* 破綻点修正: パターン番号と生の6フィールド配列という内部表現を
             * 常にユーザ向けメッセージへ混ぜており、-d の有無に関わらず
             * 出力されていた。さらに " error - " より前に "; pat ..." が付くため、
             * 他の全診断が従う書式からも外れ、axx_diagf() を通さない生の
             * fprintf だったため表示制御からも外れていた。
             * 詳細は -d 指定時だけ、本文とは別行で出す。 */
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

/* 作業用バッファを行長に合わせて確保し、本体へ渡す薄い皮。
 * 本体には途中 return が多数あるので、確保と解放はここ1か所に集める。 */
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

/* ワード番号の昇順。同じワード番号なら元の出現順（ord）を保つ。
 * 破綻点修正: qsort は安定ソートではないので、ワード番号だけで比較すると
 * 同一ワードに複数の参照があるときの並びが不定になり、あとの重複排除
 * （直前の要素としか比較しない）の結果が実行ごとに変わりうる。axx.py は
 * 安定ソートなので、ここでも出現順をタイブレークに使って揃える。 */
static int elf_ref_cmp(const void *a, const void *b){
    const ElfRef *x = (const ElfRef *)a, *y = (const ElfRef *)b;
    if(x->word_idx != y->word_idx) return (x->word_idx > y->word_idx) - (x->word_idx < y->word_idx);
    return (x->ord > y->ord) - (x->ord < y->ord);
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

    axx_normalize_ws(line);
    axx_remove_comment_asm(line);
    if(!line[0]){ free(line); return 0; }
    axx_resolve_vliw_escapes(line);

    for(int _ci = 0; _ci < g_nvars; _ci++){
        sv_free(&asmb->st.check_constraints[_ci]);
        sv_init(&asmb->st.check_constraints[_ci]);
        asmb->st.reloc_constraints[_ci] = 0;
        enumdef_clear(&asmb->st.enum_defs[_ci]);
    }
    subv_unfreeze_all(&asmb->st.subs);

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

            /* 破綻点修正1: 重複排除が「直前に残した要素」としか比較していなかった
             * ため、同じ (ラベル, ワード番号) の組が離れて並ぶと重複が残っていた
             * （axx.py は集合で全体を見る）。同一ワード内を総当たりで見る。
             * 破綻点修正2: 「同じワード位置に別々のラベルの参照がある」曖昧な場合を
             * 落とす処理が無かった（axx.py の _ambiguous）。どちらのラベルに対する
             * リロケーションなのか決められないので、そのワードは丸ごと除外する。 */
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

                /* `.reloc` が宣言された変数が運んだ参照は、命令語のビット欄に値が
                 * 詰まっていて出力バイト列から加数を逆算できない。型と加数は宣言側
                 * で決まっているので、通常の推定経路を通さずに出す。 */
                int _forced_rtype = 0;
                if(_valid[_gi].rtype > 0){
                    uint32_t _fmask = insn_reloc_field_mask(_valid[_gi].rtype);
                    if(_fmask == 0){
                        /* データ型を宣言した場合。加数は通常どおり出力バイト列
                         * から求まるので、型だけを固定して下の経路へ渡す。 */
                        _forced_rtype = _valid[_gi].rtype;
                    } else {
                        int _ibytes = elf_machine_reloc_bytes(_mtbl_rm, _valid[_gi].rtype);
                        if(_ibytes <= 0) _ibytes = 4;
                        int _iwords = _ibytes / bpw;
                        if(_iwords < 1) _iwords = 1;
                        if(_widx + _iwords <= objl.len){
                            /* RELA ではリンカが欄を埋めるので、命令語側は 0 に
                             * しておく（GNU as と同じ形）。 */
                            uint64_t _wmask_i = axx_word_mask(st->bts);
                            for(int _k = 0; _k < _iwords; _k++){
                                int _sh = st->endian_big
                                        ? st->bts * (_iwords - 1 - _k)
                                        : st->bts * _k;
                                uint64_t _clear = (_sh < 32)
                                                ? (((uint64_t)_fmask >> _sh) & _wmask_i) : 0;
                                uint64_t _wv = u256_to_u64(objl.data[_widx + _k]);
                                objl.data[_widx + _k] =
                                    u256_from_u64((_wv & ~_clear) & _wmask_i);
                            }
                        }
                        int64_t _sec_rel_h =
                            (int64_t)((sec_completed_words +
                                       (cur_pc + (uint64_t)_widx - sec_entry_pc_cur))
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
                        st->relocations[st->reloc_count].rtype      = _valid[_gi].rtype;
                        st->relocations[st->reloc_count].addend     = _valid[_gi].addend;
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
                /* リロケーション型が決まらないとき、axx.py は「型が無いので省いた」
                 * と警告してから捨てる。ただしこの幅の型を持たない ISA では、
                 * アセンブラが自分で解決し終えた参照（分岐や adrp/:lo12: 等）が
                 * 必ずここに落ちる。出力は正しいのに毎回警告が出て本物の診断を
                 * 埋めてしまうため、両者そろえて詳細は -d 指定時だけ出す。 */
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
                                /* 破綻点修正: bts*_k が64以上になりうる(例: 32bit幅
                                 * ワードが3つ以上連なるリロケーション)場合、uint64_t
                                 * を64以上シフトするのは未定義動作になるため避ける。
                                 * 64bitの蓄積先に収まらない上位語は元々表現できない
                                 * ので寄与を0とする。 */
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
                    int64_t _abs_w_bytes = (int64_t)_valid[_gi].val * (int64_t)bpw;

                    if(_rtype_is_default_guess && st->elf_machine == 62
                       && elf_machine_is_pcrel(_mtbl_rm, _rtype)
                       && (int64_t)_raw_val == _abs_w_bytes){
                        /* 破綻点修正: 4バイト幅（PC32→abs32=10）しか判定して
                         * いなかったため、.RELOCTYPE でデフォルト型を
                         * pc64/pc16/pc8 相当に変えた上でこの自動判定に
                         * 掛かった場合、8/2/1バイト幅では絶対値型への
                         * 差し替えが起きず axx.py と食い違っていた。 */
                        switch(_nbytes){
                            case 8: _rtype = 1;  break;
                            case 4: _rtype = 10; break;
                            case 2: _rtype = 12; break;
                            case 1: _rtype = 14; break;
                        }
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

    /* 破綻点修正: 改行を落とした行を st->cl（表示用の cl[4096]）に strncpy して
     * から、その「切り詰められた写し」を lineassemble() に渡していた。
     * 4095 文字を超える行は診断もなく途中で切れ、例えば 5000 文字の
     * `.ascii "…"` が 4086 バイトしか出ないという形で axx.py と食い違っていた。
     * 組み立てには元の行をそのまま渡し、st->cl はあくまで表示用の写しに留める。 */
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
    /* パターンが文字列テンプレートだった行は、バイナリ出力とは別に、
     * アセンブリ結果をテキストでも出す。
     * -v の診断行の中では `` ではなく "" で括って見せ、診断を出さないときは
     * その行だけを素のまま標準出力へ流す（トランスレータとしての出力）。 */
    if(st->asmtext && (st->pas==0 || st->pas==2)){
        if(show) printf(" %s", st->asmtext_disp ? st->asmtext_disp : "");
        else     printf("%s\n", st->asmtext);
    }
    free(st->asmtext); st->asmtext=NULL;
    free(st->asmtext_disp); st->asmtext_disp=NULL;
    if(show) printf("\n");
    free(cleaned);
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

static uint8_t *weo_extract_ranges(AsmState*st, int bpw, const char*name, uint64_t *out_nb){
    uint64_t total_words = 0;
    int have_range = 0;
    for(int i=0;i<st->section_ranges.len;i++)
        if(strcmp(st->section_ranges.data[i].name,name)==0){
            have_range = 1;
            total_words += u256_to_u64(st->section_ranges.data[i].len);
        }
    /* 破綻点修正: 断片が1つも記録されていないセクションで中身が空になっていた。
     * axx.py の _section_word_ranges() と同じく sections 表を代わりに使う。 */
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
                if(woff >= 0) return (WSR){(uint16_t)(i+1), (uint64_t)woff*(uint64_t)bpw};
            }
        }
    }
    for(int i=0;i<ncs;i++){
        int64_t woff = sec_word_offset(st, csecs[i].name, word_pc);
        if(woff >= 0) return (WSR){(uint16_t)(i+1), (uint64_t)woff*(uint64_t)bpw};
    }
    if(ncs>0){
        int best_i=0; uint64_t best_start=0; int found=0;
        for(int i=0;i<ncs;i++){
            if(csecs[i].bs<=ba && (!found || csecs[i].bs>=best_start)){ best_i=i; best_start=csecs[i].bs; found=1; }
        }
        uint64_t sv = ba - csecs[best_i].bs;
        if(!found || ba < csecs[best_i].bs) sv = 0;
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
        if(sidx<0){
            /* 破綻点修正: セクション名が一致しないリロケーションを無警告で
             * 捨てていたため、修正が抜け落ちた「見た目は正常な」.oファイルが
             * 静かに生成されていた。診断を出す。 */
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
                 : weo_shndx(st,csecs,ncs,larr[i].val*(uint64_t)bpw,larr[i].section,bpw);
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
                 : weo_shndx(st,csecs,ncs,earr[i].val*(uint64_t)bpw,earr[i].section,bpw);
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

        /* DWARF が書く絶対アドレス参照の欄幅は addr_sz（= -f で決まる ELF クラス）
         * だが、dwarf_abs はマシンごとの固定値。`-f` がそのマシンの慣習クラスと
         * 違うときは両者がずれ、4バイトの欄に 8バイト型（あるいはその逆）の
         * リロケーションを張ることになる。欄と同じ幅の型に取り替える。 */
        int abs64 = _mtbl_dbg->dwarf_abs;
        if(elf_machine_reloc_bytes(_mtbl_dbg, abs64) != addr_sz){
            int _alt = elf_machine_named(_mtbl_dbg, addr_sz == 8 ? "abs64" : "abs32");
            if(_alt > 0 && elf_machine_reloc_bytes(_mtbl_dbg, _alt) == addr_sz){
                abs64 = _alt;
            } else {
                /* 幅の合う絶対型を持たないマシン（32bit 機を -f 64 で出した場合）。
                 * 幅の違う型を張れば黙って壊れたデバッグ情報になるので出さない。 */
                axx_diagf(0, 0, " warning - DWARF debug info (-g) needs a %d-byte absolute "
                           "relocation, which %s does not have; skipping debug sections.\n",
                           addr_sz, _mtbl_dbg->name);
                goto dbg_done;
            }
        }

        RB abv; rb_init(&abv);
        /* 子 DIE になるラベルを先に数える。CU の DW_CHILDREN は「子があるか」を
         * 宣言するもので、ラベルを1つも持たないソース（命令だけのファイル）では
         * 子なしになる。宣言と中身が食い違うと DWARF の検証器が指摘するため、
         * 表を組む前に確定させる。axx.py の _dbg_labels と同じ判定。 */
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
        /* 破綻点修正: axx.py は "(DWARF4)" なので、-g を付けると DW_AT_producer
          * の長さが違い、.debug_info（と先頭の unit_length）がずれて、両実装の
          * .o が同一バイト列にならなかった。DW_AT_producer は「どのツールが
          * 作ったか」を書く欄で、実装言語を区別する場所ではない。文言を揃える。 */
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
        /* 子の連鎖を閉じる null DIE。DW_CHILDREN_no のときは連鎖自体が無いので
         * 置いてはいけない（読み手が余分な abbrev コード 0 を拾ってしまう）。 */
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

    /* 破綻点修正: tot_sh/shstrndx は ELF ヘッダの e_shnum/e_shstrndx
     * (uint16_t) へ無言でキャストされていたため、セクションヘッダ総数が
     * 65535 を超えるソースでは値が 65536 でラップし、readelf/objdump が
     * セクション数を誤解釈する壊れた .o が黙って生成されていた。
     * (axx.py 側は struct.pack('H', ...) がこの場合に例外で落ちるので、
     * 少なくとも壊れた出力は書かれない。) SHN_XINDEX 拡張には対応せず、
     * 明示的にエラーで打ち切る。 */
    if(tot_sh > 0xFFFF || shstrndx > 0xFFFF){
        if(should_report_errors(st)){
            axx_diagf(1, 0, " error - too many ELF section headers (%d) to represent in e_shnum; "
                       "cannot write ELF object.\n", tot_sh);
        }
        goto weo_done;
    }

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
    {
    /* 破綻点修正: axx.py は ", N debug section(s)" と出すのに対し、ここだけ
     * ", +DWARF debug" という別の文言だった。-g のときだけ両実装の stderr が
     * 食い違い、出力比較による回帰検査をすり抜けていた。 */
    char _dbg_msg[64];
    if(n_dbg_prog) snprintf(_dbg_msg,sizeof(_dbg_msg),", %d debug section(s)",n_dbg_prog);
    else           _dbg_msg[0]='\0';
    fprintf(stderr,"elf: wrote %s (%d section(s), %d %s section(s), %d symbol(s)%s)\n",
            path,ncs,nrela,_is_rela_w?"rela":"rel",nsyms,_dbg_msg);
    }

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
    /* 破綻点修正: `&&` `||` `?:` の「取らない側」を評価しないための印。
     * この評価器は式のテキストを直接たどるので、取らない側も構文としては
     * 最後まで読まないと位置が合わない。読みはするが、実行時のエラー
     * （0除算・桁溢れ・未定義の名前）と副作用（uid() の採番、マクロ呼び出し）
     * だけを止める。axx.py は木を組んでから評価するので初めから短絡している。 */
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

/* マクロ層の `!echo` とミニ言語の `.echo` に共通の出力ルーチン。
 * 項目を空白区切りで 1 行にまとめて標準エラーへ出す。体裁を 1 か所に
 * 集めておくため、どちらの層もここを通す（axx.py の _echo_write と同じ）。 */
/* `s[i]` の `'` が符号拡張の演算子か（右に幅が続くか）を見分ける。
 * 文字定数 `'A'` と区別するため、本体の評価器と同じく「続く文字が数字か `(`」
 * を条件にする。`!{...}` の走査とマクロ式パーサの両方から使う。
 * axx.py の _sext_tick_at と同じ。 */
static int m_sext_tick_at(const char *s, int i){
    int j = i + 1;
    while(s[j] == ' ' || s[j] == '\t') j++;
    return (s[j] >= '0' && s[j] <= '9') || s[j] == '(';
}

static void m_echo_write(char *const *items, int n){
    for(int i = 0; i < n; i++){
        if(i) fputc(' ', stderr);
        fputs(items[i] ? items[i] : "", stderr);
    }
    fputc('\n', stderr);
}
static long long mv_need_int(MacroPP *mp, MVal v, const char *file, int line){
    if(v.is_str){
        if(mp->noeval) return 0;
        char vr[600], er[600];
        m_pyrepr(v.s ? v.s : "", vr, sizeof(vr));
        if(mp->cur_expr) m_pyrepr(mp->cur_expr, er, sizeof(er));
        else { er[0] = '?'; er[1] = '\0'; }
        m_fail(mp, file, line, "macro expression: expected an integer, got the string %s in %s", vr, er);
    }
    return v.i;
}
/* 破綻点修正: マクロ時の int64 演算は、MACRO.md が明言するとおり axx.py の
 * 多倍長整数と違って 64bit で切り捨てる仕様である。しかし従来の実装は
 * その切り捨てを素の `+`/`-`/`*`/単項 `-`/`<<` で行っており、これらは
 * オペランドが INT64_MIN や桁あふれを起こす値のとき C の符号付き整数
 * オーバーフロー（未定義動作）を踏む。UBSan はこれを多数検出する
 * （`9223372036854775807+1`、`INT64_MIN` の単項 `-` や abs()、
 * 負値の `<<` など）。未定義動作である以上、最適化次第で「64bit 切り捨て」
 * にすらならない壊れ方をしうるので、意図した2の補数の折り返しを
 * 符号なし演算で明示的に行い、結果だけ符号付きへ戻す。
 * （符号なし→符号付きの変換は実装依存だが、実用上の全処理系で
 * 2の補数として素通しされ、これは C 標準でも許容された実装依存動作であって
 * 未定義動作ではない。） */
static inline long long m_i64_neg(long long a){
    return (long long)(0ULL - (unsigned long long)a);
}
static inline long long m_i64_abs(long long a){
    return a < 0 ? m_i64_neg(a) : a;
}
/* 破綻点修正: 単項 '-' と abs() だけが桁溢れ検査を通っておらず、
 * INT64_MIN に対して黙ってラップアラウンド（符号付きオーバーフロー）していた。
 * 他の演算子と同じく、表現できない結果は明示的なエラーにする。 */
static inline long long m_i64_neg_ck(MEP *p, long long a){
    if(a == LLONG_MIN){
        if(p->mp->noeval) return 0;
        char sr[600]; m_pyrepr(p->s, sr, sizeof(sr));
        m_fail(p->mp, p->file, p->line, "macro expression: integer overflow (64-bit) in %s", sr);
    }
    return -a;
}
static inline long long m_i64_abs_ck(MEP *p, long long a){
    return a < 0 ? m_i64_neg_ck(p, a) : a;
}
/* 破綻点修正: 以前は +,-,* を unsigned キャスト経由で無言のままラップアラウンド
 * させていた。axx.py 側は任意精度整数なので、64bit を超えるマクロ計算では
 * 両実装が黙って別々の(誤った)値を返す食い違いが起きていた。完全な任意精度化
 * はここでは行わないが、64bit をオーバーフローする場合は黙って間違った値を
 * 返す代わりに、呼び出し元(MEP*)経由で明示的にエラーにする。 */
static inline long long m_i64_add(MEP *p, long long a, long long b){
    long long r;
    if(__builtin_add_overflow(a, b, &r)){
        if(p->mp->noeval) return 0;
        char sr[600]; m_pyrepr(p->s, sr, sizeof(sr));
        m_fail(p->mp, p->file, p->line, "macro expression: integer overflow (64-bit) in %s", sr);
    }
    return r;
}
static inline long long m_i64_sub(MEP *p, long long a, long long b){
    long long r;
    if(__builtin_sub_overflow(a, b, &r)){
        if(p->mp->noeval) return 0;
        char sr[600]; m_pyrepr(p->s, sr, sizeof(sr));
        m_fail(p->mp, p->file, p->line, "macro expression: integer overflow (64-bit) in %s", sr);
    }
    return r;
}
static inline long long m_i64_mul(MEP *p, long long a, long long b){
    long long r;
    if(__builtin_mul_overflow(a, b, &r)){
        if(p->mp->noeval) return 0;
        char sr[600]; m_pyrepr(p->s, sr, sizeof(sr));
        m_fail(p->mp, p->file, p->line, "macro expression: integer overflow (64-bit) in %s", sr);
    }
    return r;
}
static inline long long m_i64_shl(long long a, int n){
    return (long long)((unsigned long long)a << n);
}
/* 数値リテラルの桁読み取り専用: 例えば 0xFFFFFFFFFFFFFFFF のような
 * 64bit いっぱいのビットパターンは、signed long long としては
 * 「ラップアラウンドして -1 になる」のがビットパターンとして正しい表現であり、
 * 演算子の桁溢れとは性質が違う。ここでは意図的に無言のラップアラウンドを保つ。 */
static inline long long m_i64_add_raw(long long a, long long b){
    return (long long)((unsigned long long)a + (unsigned long long)b);
}
static inline long long m_i64_mul_raw(long long a, long long b){
    return (long long)((unsigned long long)a * (unsigned long long)b);
}

static long long m_cdiv(MEP *p, long long a, long long b){
    if(b == 0) return 0;                 /* 取らない側を読み飛ばしている最中 */
    if(a == LLONG_MIN && b == -1){
        if(p->mp->noeval) return 0;
        char sr[600]; m_pyrepr(p->s, sr, sizeof(sr));
        m_fail(p->mp, p->file, p->line, "macro expression: integer overflow (64-bit) in %s", sr);
    }
    /* 破綻点修正: m_i64_abs(INT64_MIN) は INT64_MIN のままなので（絶対値が
     * 表現できない）、商が既に負のところへさらに符号反転がかかり、
     * INT64_MIN/2 が +4611686018427387904 という符号の逆な値になっていた。
     * 絶対値は符号なしで取れば必ず正しく表せるので、そちらで割る。 */
    unsigned long long ua = (a < 0) ? (0ULL - (unsigned long long)a) : (unsigned long long)a;
    unsigned long long ub = (b < 0) ? (0ULL - (unsigned long long)b) : (unsigned long long)b;
    unsigned long long q = ua / ub;
    /* 符号が違えば商は 2**63 以下なので -q は必ず表現できる。符号が同じ
     * 場合、a==INT64_MIN && b==-1 は上で弾いてあるので q は INT64_MAX 以下。 */
    return ((a >= 0) == (b >= 0)) ? (long long)q : (long long)(0ULL - q);
}
static long long m_cmod(MEP *p, long long a, long long b){ return m_i64_sub(p, a, m_i64_mul(p, m_cdiv(p, a, b), b)); }


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

/* アセンブラ側のラベル / .equ を引いた結果。 */
typedef enum { MLBL_NO = 0, MLBL_UNKNOWN, MLBL_VALUE } MLabelStatus;

/* アセンブラ側のラベル / .equ を引く。
 *
 * マクロ展開はアドレス確定より前に走るので「今の値」は存在しない。前回
 * リラクゼーション反復のスナップショット(st->macro_labels)を見て、
 *   MLBL_VALUE   … 前回反復で値が確定していた（*out に値）
 *   MLBL_UNKNOWN … ラベルとしては在るが値が未確定（初回反復では全ての名前）
 *   MLBL_NO      … そんなラベルは無い（＝綴り間違い）
 * を返す。パターンファイル側のマクロ層はソースのアセンブル前に走るので、
 * そこでは常に MLBL_NO。
 *
 * 値が確定しているかの判定に LabelEntry::is_undef を使わず値だけを見るのは、
 * axx.py 側にこのフラグが無く、値で判定しているため。両実装でマクロ層から
 * 見える世界を一致させる。 */
static MLabelStatus m_asm_label(MacroPP *mp, const char *name, long long *out){
    if(out) *out = 0;
    if(mp->pat_mode || !mp->asmb) return MLBL_NO;
    AsmState *st = &mp->asmb->st;
    if(!st->macro_labels_valid){
        /* まだ一度も反復していない。前方参照なのか綴り間違いなのかを区別
         * できないので、エラーにせず未確定として扱う。綴り間違いは次の
         * 反復で MLBL_NO として捕まる。 */
        return MLBL_UNKNOWN;
    }
    LabelEntry *e = lmap_find(&st->macro_labels, name);
    if(!e) return MLBL_NO;
    if(u256_is_undef_derived(e->value)) return MLBL_UNKNOWN;
    if(out) *out = (long long)u256_to_u64(e->value);
    return MLBL_VALUE;
}

/* マクロ展開時の位置カウンタ（$ / $$）。ラベルと違って名前ではなく位置で
 * 決まる値なので、前回反復で記録した「展開後 N 行目のアドレス」を返す。
 * 初回反復や、展開行数が変わって対応する行がまだ無い場合は 0。 */
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

static int m_is_defined(MacroPP *mp, const char *name){
    /* 破綻点修正: `!undef` はマクロを表から消さず defined=0 にするだけなのに、
     * ここは存在するかどうかしか見ていなかった。そのため `!undef foo` のあとも
     * `defined(foo)` が真を返し、axx.py（funcs から削除する）と食い違っていた。 */
    MFunc *_f = m_func_find(mp, name);
    if(_f && _f->defined) return 1;
    for(int i = mp->nscopes - 1; i >= 0; i--)
        if(m_scope_find(mp->scopes[i], name)) return 1;
    return m_asm_label(mp, name, NULL) == MLBL_VALUE;
}
static MVal m_lookup(MacroPP *mp, const char *name, const char *file, int line){
    /* 取らない側を読み飛ばしている最中は、名前を引かない。 */
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
        v = m_i64_add_raw(m_i64_mul_raw(v, base), d);
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
        /* 破綻点修正: mep_primary〜mep_ternary の相互再帰に上限が無く、
         * `(` の深いネスト（!set/!if/!while の式に現れうる）でCスタックを
         * 使い果たしてクラッシュしうた（expr_factor 側の EXPR_MAX_DEPTH と
         * 同種の問題）。axx.py は RecursionError で安全に止まるのに対し、
         * こちらは無防備だったので、同じ上限で止める。 */
        if(p->mp->expr_depth >= EXPR_MAX_DEPTH){
            char sr[600]; m_pyrepr(p->s, sr, sizeof(sr));
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
        /* 位置カウンタ。`$` と `$$` は同義（アセンブラ本体では `$$` が位置
         * カウンタなので、そちらの綴りも受ける）。空白を挟んだ `$ $` を
         * `$$` と読まないよう、次の文字は素で見る。 */
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
    if(p->s[p->i] == '-'){ p->i++; return mv_int(m_i64_neg_ck(p, mv_need_int(p->mp, mep_unary(p), p->file, p->line))); }
    if(p->s[p->i] == '+'){ p->i++; return mep_unary(p); }
    /* 本体の `@`（最上位ビット位置）。実装は共有関数 op_msb()。 */
    if(p->s[p->i] == '@'){
        p->i++;
        long long xv = mv_need_int(p->mp, mep_unary(p), p->file, p->line);
        return mv_int(op_msb(u256_from_i64(xv)));
    }
    /* 本体の `*(値, 位置)`（バイト抽出）。値が来る位置の `*` だけがこれで、
     * 中置の `*` は従来どおり掛け算（本体の評価器と同じ見分け方）。 */
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

/* 破綻点修正: `n * (long long)l` は n が大きいと符号付きオーバーフロー（UB）を
 * 起こし、上限チェック自体をすり抜けてから marena_alloc() に渡っていた
 * （ヒープバッファオーバーフロー。ASan で確認済み）。しかも文字列側が右辺に
 * 来る形（!v.is_str && r.is_str）には上限チェックが一切無かった。
 * 掛け算をせずに割り算で判定すれば、n・l がどちらも非負である前提のもとで
 * オーバーフローなしに「n*l が上限を超えるか」を判定できる。 */
static long long m_safe_repeat_len(MacroPP *mp, const char *file, int line,
                                    const char *srcline, long long n, size_t l){
    if(n < 0) n = 0;
    const long long MAXLEN = 16*1024*1024;
    if(n == 0 || l == 0) return 0;
    if((unsigned long long)n > (unsigned long long)(MAXLEN) / l){
        if(mp->noeval) return 0;
        char sr[600]; m_pyrepr(srcline, sr, sizeof(sr));
        m_fail(mp, file, line, "macro expression: string repetition too large in %s", sr);
    }
    return n * (long long)l;
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
                v = mv_int(m_i64_mul(p, mv_need_int(p->mp, v, p->file, p->line),
                                      mv_need_int(p->mp, r, p->file, p->line)));
            }
        } else if(c == '/'){
            p->i++;
            long long r = mv_need_int(p->mp, mep_unary(p), p->file, p->line);
            if(r == 0 && !p->mp->noeval){
                char sr[600]; m_pyrepr(p->s, sr, sizeof(sr));
                m_fail(p->mp, p->file, p->line, "macro expression: division by zero in %s", sr);
            }
            v = mv_int(m_cdiv(p, mv_need_int(p->mp, v, p->file, p->line), r));
        } else if(c == '%'){
            p->i++;
            long long r = mv_need_int(p->mp, mep_unary(p), p->file, p->line);
            if(r == 0 && !p->mp->noeval){
                char sr[600]; m_pyrepr(p->s, sr, sizeof(sr));
                m_fail(p->mp, p->file, p->line, "macro expression: modulo by zero in %s", sr);
            }
            v = mv_int(m_cmod(p, mv_need_int(p->mp, v, p->file, p->line), r));
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
            } else v = mv_int(m_i64_add(p, v.i, r.i));
        } else if(c == '-'){
            p->i++;
            v = mv_int(m_i64_sub(p, mv_need_int(p->mp, v, p->file, p->line),
                       mv_need_int(p->mp, mep_mul(p), p->file, p->line)));
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
            /* 破綻点修正: 上限を 63 にしていたため、axx.py が受け付ける
             * 0〜4096 のシフト量のうち 64 以上が、値の大小に関わらず
             * 「shift count out of range」で落ちていた。上限を axx.py に
             * 合わせ、64bit から溢れるかどうかは下の桁溢れ検査で見る。 */
            if((n < 0 || n > 4096) && !p->mp->noeval){
                char sr[600]; m_pyrepr(p->s, sr, sizeof(sr));
                m_fail(p->mp, p->file, p->line, "macro expression: shift count out of range in %s", sr);
            }
            if(n < 0 || n > 4096) n = 0;   /* 取らない側を読み飛ばしている最中 */
            long long base = mv_need_int(p->mp, v, p->file, p->line);
            if(n > 63){
                /* 64bit では表せない。0 を何ビット左にずらしても 0 なので、
                 * その場合だけは axx.py と同じ値を返せる。 */
                if(base != 0 && !p->mp->noeval){
                    char sr[600]; m_pyrepr(p->s, sr, sizeof(sr));
                    m_fail(p->mp, p->file, p->line, "macro expression: integer overflow (64-bit) in %s", sr);
                }
                v = mv_int(0);
                continue;
            }
            long long shifted = m_i64_shl(base, (int)n);
            /* 破綻点修正: 64bit を超えて追い出されたビットを黙って捨てていたため、
             * axx.py(任意精度)と異なる値を無言で返していた。追い出されたビットが
             * あれば(逆シフトで元に戻らなければ)明示的にエラーにする。 */
            if(n > 0 && (shifted >> n) != base && !p->mp->noeval){
                char sr[600]; m_pyrepr(p->s, sr, sizeof(sr));
                m_fail(p->mp, p->file, p->line, "macro expression: integer overflow (64-bit) in %s", sr);
            }
            v = mv_int(shifted);
        } else if(p->s[p->i] == '>' && p->s[p->i+1] == '>'){
            p->i += 2;
            long long n = mv_need_int(p->mp, mep_add(p), p->file, p->line);
            /* 破綻点修正: 同上。右シフトは 64 以上でも結果が 64bit に収まる
             * （符号に応じて 0 か -1 に落ち着く）ので、そこまで含めて
             * axx.py と同じ値を返す。 */
            if((n < 0 || n > 4096) && !p->mp->noeval){
                char sr[600]; m_pyrepr(p->s, sr, sizeof(sr));
                m_fail(p->mp, p->file, p->line, "macro expression: shift count out of range in %s", sr);
            }
            if(n < 0 || n > 4096) n = 0;   /* 取らない側を読み飛ばしている最中 */
            long long rbase = mv_need_int(p->mp, v, p->file, p->line);
            v = mv_int(n > 63 ? (rbase < 0 ? -1 : 0) : (rbase >> n));
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
/* 本体の `'`（任意ビット位置からの符号拡張）をマクロ式でも使えるようにする。
 * 実装は本体と同じ共有関数 op_sext()。位置はビット演算子より緩く `&&` より
 * きつい段。本体では `^` と比較のあいだだが、マクロ層の優先順位は C に
 * 合わせてあり比較のほうがビット演算子よりきついので、同じ相対位置は取れない。
 * axx.py の _ExprParser.sext と同じ。 */
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

static MVal mep_land(MEP *p){
    MVal v = mep_sext(p);
    while(mep_eat(p, "&&")){
        /* 左が偽なら右は評価しない（C と同じ短絡）。 */
        int skip = !p->mp->noeval && !mv_truth(v);
        if(skip) p->mp->noeval++;
        MVal r = mep_sext(p);
        if(skip) p->mp->noeval--;
        v = mv_int((!skip && mv_truth(v) && mv_truth(r)) ? 1 : 0);
    }
    return v;
}
static MVal mep_lor(MEP *p){
    MVal v = mep_land(p);
    while(mep_eat(p, "||")){
        /* 左が真なら右は評価しない（C と同じ短絡）。テキストをたどる評価器
         * なので読み飛ばしはせず、noeval を立てたまま最後まで読む。 */
        int skip = !p->mp->noeval && mv_truth(v);
        if(skip) p->mp->noeval++;
        MVal r = mep_land(p);
        if(skip) p->mp->noeval--;
        v = mv_int((skip || mv_truth(v) || mv_truth(r)) ? 1 : 0);
    }
    return v;
}
static MVal mep_ternary(MEP *p){
    MVal c = mep_lor(p);
    mep_skip(p);
    if(p->s[p->i] == '?'){
        p->i++;
        int taken = p->mp->noeval ? 0 : (mv_truth(c) ? 1 : 2);
        /* 取る側だけを評価する。取らない側は noeval のまま読む。 */
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

static MVal m_eval(MacroPP *mp, const char *text, const char *file, int line){
    while(*text == ' ' || *text == '\t') text++;
    if(!*text) m_fail(mp, file, line, "empty macro expression");
    /* 破綻点修正: m_fail は longjmp で抜けるため、エラーで打ち切られた前回の
     * 評価が mep_primary の '(' で加算した expr_depth を減算し損ねたまま
     * 残ることがある。各トップレベル評価の開始時に必ず 0 へ戻す。 */
    mp->expr_depth = 0;
    /* 同上: 取らない側を読んでいる途中で m_fail に飛ばれると noeval が
     * 立ったまま残り、以後の実行時エラーが黙って握り潰される。 */
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
        /* 破綻点修正: abs(INT64_MIN) は 64bit で表現できない。黙って
         * INT64_MIN のまま返さず、他の演算子と同じくエラーにする。 */
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
        /* label("名前") — アセンブラ側のラベル / .equ の値。裸の識別子でも
         * 同じ値を引けるが、`.L1` のようにマクロの識別子として書けない名前は
         * こちらでしか参照できない。解決規則は裸の識別子と同一。 */
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

    /* 破綻点修正: 引数のデフォルト式を新しいスコープを push する前に評価
     * していたため、`!def f(a, b=a+1)` の b のデフォルトが呼び出し元の
     * スコープの 'a' を参照してしまっていた(axx.py 側にも同じ破綻点があり
     * 併せて修正済み)。先にスコープを push し、仮引数を確定させるたびに
     * そのスコープへ書き込みながら進めることで、後続のデフォルト式から
     * 前方の仮引数を正しく参照できるようにする。 */
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
    /* 取らない側を読み飛ばしている最中は呼ばない。uid() の採番や
     * マクロ本体の副作用が起きてしまうため。 */
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
                /* 符号拡張の `'` は文字定数の開始ではないので数えない。 */
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
        } else if(c == '"') quote = c;
        else if(c == '\''){
            /* 破綻点修正: `'` を無条件に引用符の開きとして扱っていた。しかし
             * パターンファイルでは `'` は符号拡張演算子（`!x'8` 等）でもあり、
             * 行に1個しか無いとそこから行末までが「引用符の中」になって
             * 以降のブロックコメント開始記号が除去されず、マクロ層の行判定が狂っていた。
             * 対になる `'` が同じ行にあるときだけ文字リテラルとみなす。 */
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
    /* 破綻点修正: !if/!while/!def のブロック入れ子に上限が無く、深すぎる
     * ネストでパース時のC再帰がスタックオーバーフローしうる。
     * MACRO_MAX_DEPTH は呼び出し(実行)時の深さガードなので、
     * パース時のブロック入れ子はここで別途止める。 */
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
    mp->noeval = 0;     /* m_eval と同じく、前回の打ち切りの取りこぼしを消す */
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

static void m_exec_block(MacroPP *mp, MBlock *b){
    for(int i = 0; i < b->len; i++){
        m_exec_node(mp, b->d[i]);
        if(mp->ctl != MCTL_NONE) return;
    }
}


static void m_read_lines(MacroPP *mp, FILE *f, const char *display, MSrc *out){
    /* 行末が '\' の行は次の行と連結する(行継続)。パターンファイル・ソース
     * ファイルのどちらも1物理行=1パターン/1命令が前提の実装なので、複雑な
     * 式を複数行に分けて書くとそこで暗黙に切れてしまう(README Appendix A.3
     * の AND immediate 例がまさにこれで、警告も出さずに後半のフィールドを
     * 取りこぼしていた)。要素数(=行番号の基準)は変えず、継続元の行は空文字
     * 列にして、連結された内容は継続が終わった行の位置にまとめる。 */
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
        if(n >= cap){
            int nc = cap + 1;
            MLine *nd = marena_alloc(&mp->arena, (size_t)nc * sizeof(MLine));
            memcpy(nd, d, (size_t)n * sizeof(MLine));
            d = nd; cap = nc;
        }
        d[n].text = marena_strdup(&mp->arena, pending);
        d[n].file = name;
        d[n].line = n + 1;
        n++;
        free(pending); pending = NULL;
    }
    free(line);
    out->d = d; out->n = n;
}

static void m_do_include(MacroPP *mp, const char *name, const char *file, int line){
    /* 破綻点修正: path は char[1024] の固定長だった。長いパスが黙って切り詰め
     * られ、意図しないファイルを読むか「開けない」で止まっていた。必要量は
     * name と file の長さで決まる。m_fail() は longjmp で抜けるので、解放を
     * 気にしなくてよいマクロ用アリーナから取る（reset_pass でまとめて戻る）。 */
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
    st->current_file[sizeof(st->current_file)-1]='\0';
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
        /* マクロ層の $/$$ は「展開後の何行目か」で決まる値なので、この反復で
         * 各行がどのアドレスに置かれたかを記録しておき、次の反復の展開時に
         * 参照する。読む先(macro_line_pcs)と書く先(_cur)は別の表なので、
         * 展開中に自分が読んでいる記録を壊すことはない。 */
        char _expkey[sizeof(st->current_file)];
        strncpy(_expkey, st->current_file, sizeof(_expkey)-1);
        _expkey[sizeof(_expkey)-1]='\0';
        MLineVec _mexp = macro_expand(&g_macro, f, st->current_file);
        fclose(f); f=NULL;
        int _lp = mlp_begin(&st->macro_line_pcs_cur, _expkey);
        for(int _mi=0; _mi<_mexp.len; _mi++){
            mlp_push(&st->macro_line_pcs_cur, _lp, (long long)u256_to_u64(st->pc));
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
    sv_free(&asmb->st.strsym_names); sv_init(&asmb->st.strsym_names);
    sv_free(&asmb->st.strsym_vals);  sv_init(&asmb->st.strsym_vals);
    arrsym_clear_all(&asmb->st);

    for(int pi=0; pi<asmb->st.pat.len; pi++){
        PatEntry *e=&asmb->st.pat.data[pi];
        if(!e) continue;

        if(strcmp(e->f[0],".setsym")==0){
            const char *name_field = e->f[1][0] ? e->f[1] : e->f[2];
            const char *value_field = e->f[1][0] ? e->f[2] : "";
            char key[512]; axx_strupr_to(key,name_field,sizeof(key));
            /* 破綻点修正: axx.py は各 .setsym の値を評価する直前に、それまで
             * 積み上げた fresh を毎回 st->symbols へ再公開している
             * (axx.py:6732)。これにより `#symbol1` のようなここまでの
             * .setsym 参照が値の式の中で解決できる（README 3.6）。caxx.c は
             * ループが終わってから一括でしか smap_set していなかったため、
             * `.setsym::symbol2::#symbol1` が常に「未定義シンボル」で失敗
             * していた（機能が丸ごと壊れていた）。 */
            smap_clear(&asmb->st.symbols);
            for(int fi=0; fi<fresh.nb; fi++)
                for(SymEntry *fe=fresh.buckets[fi]; fe; fe=fe->next)
                    smap_set(&asmb->st.symbols, fe->key, fe->val);
            /* 値が `"..."` なら文字列シンボル、`[...]` なら配列シンボル。
             * どちらも数値ではないので式には直接出せず、文字列テンプレート
             * （3.5.2）や `#名前[添字]` から引く。 */
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
                /* `.setsym::y::x` — x が文字列／配列シンボルなら写しを作る。 */
                if(symbol_copy_from_name(&asmb->st, key, value_field)) continue;
                /* `名前,名前,…` は名前の集合、`a&b` などは集合どうしの演算。 */
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
            /* `.map` のシンボルもこの前処理の表に積む。ここまでに積んだ
             * ものを公開してから展開するので、並びに書いた配列シンボルも、
             * 値の式に書いた `#記号` も解決できる。 */
            smap_clear(&asmb->st.symbols);
            for(int fi=0; fi<fresh.nb; fi++)
                for(SymEntry *fe=fresh.buckets[fi]; fe; fe=fe->next)
                    smap_set(&asmb->st.symbols, fe->key, fe->val);
            map_apply(asmb, e, &fresh, 0);
            continue;
        }
        /* `.free` はシンボルもこの前処理の表から外す（本体の走査でも同じ
         * ことをするが、ここで外しておかないと後続の `.setsym` の値の式から
         * 見えたままになる）。 */
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

/* imp_label の16進フィールド検査で使う。axx.py の int(s,16) は前後の空白を
 * 許容しつつも、それ以外の余分な文字が混じっていれば ValueError にする。
 * strtoull は末尾を切り詰めるだけなので、endp から先が空白だけであることを
 * 別途確認する。 */
static int hexfield_fully_consumed(const char *endp){
    while(*endp==' '||*endp=='\t') endp++;
    return *endp=='\0';
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
        /* 破綻点修正: strtoull は末尾に余分な非16進文字があっても、先頭が
         * 数字であれば途中までを黙って解釈して成功扱いにする。axx.py の
         * int(s,16) はフィールド全体が正当な16進数でなければ ValueError に
         * なりインポート行ごと捨てる。endp が文字列末尾まで届いているかも
         * 確認しないと、壊れた値をそのまま採用して「成功」してしまう。 */
        uint64_t start = strtoull(fields[1], &endp, 16);
        if(endp == fields[1] || !hexfield_fully_consumed(endp)) return 0;
        uint64_t size  = strtoull(fields[2], &endp, 16);
        if(endp == fields[2] || !hexfield_fully_consumed(endp)) return 0;
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
        if(endp == fields[1] || !hexfield_fully_consumed(endp)) return 0;

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
    /* 破綻点修正: 既定値が FreeBSD(9) 固定だったため、--osabi を指定しない
     * 通常の使い方では、標準的な Linux 環境の ld が OSABI ミスマッチで
     * 生成された .o を拒否し得た（axxelfbug 参照）。axx.py と同じく既定値を
     * Linux(0) に変更する。 */
    char osabistr[16]="Linux";
    const char *macro_expand_dest=NULL;
    const char *pat_macro_expand_dest=NULL;

    /* 破綻点修正: 値を取るオプションが `i+1<argc` だけを見て次の argv を
     * 無条件に値として飲み込んでいたため、値を書き忘れて後ろに別のフラグが
     * 続く場合（例: `-b -o`）、そのフラグ文字列がそのままファイル名として
     * 採用されてしまっていた（axx.py の argparse は "expected one argument"
     * で即座に拒否する）。同じファイル内で -p/-P に既にある「次の argv が
     * '-' で始まっていたら値として食わない」規約を、値を取る単純なフラグ
     * 全部に揃える。値を食わずに条件が外れれば、末尾の catch-all が
     * "unknown option" として拒否する。 */
    for(int i=1;i<argc;i++){
        if(strcmp(argv[i],"--osabi")==0&&i+1<argc&&argv[i+1][0]!='-'){ strncpy(osabistr,argv[++i],sizeof(osabistr)-1); }
        else if(strcmp(argv[i],"-b")==0&&i+1<argc&&argv[i+1][0]!='-'){ strncpy(st->outfile,argv[++i],sizeof(st->outfile)-1); }
        else if(strcmp(argv[i],"-e")==0&&i+1<argc&&argv[i+1][0]!='-'){ strncpy(st->expfile,argv[++i],sizeof(st->expfile)-1); }
        else if(strcmp(argv[i],"-E")==0&&i+1<argc&&argv[i+1][0]!='-'){ strncpy(st->expfile_elf,argv[++i],sizeof(st->expfile_elf)-1); }
        else if(strcmp(argv[i],"-i")==0&&i+1<argc&&argv[i+1][0]!='-'){ strncpy(st->impfile,argv[++i],sizeof(st->impfile)-1); }
        else if(strcmp(argv[i],"-o")==0&&i+1<argc&&argv[i+1][0]!='-'){ strncpy(st->elf_objfile,argv[++i],sizeof(st->elf_objfile)-1); }
        else if(strcmp(argv[i],"-f")==0&&i+1<argc&&argv[i+1][0]!='-'){
            const char *_fs = argv[++i];
            if(strcmp(_fs,"64")==0){ st->elf_class = 2; }
            else if(strcmp(_fs,"32")==0){ st->elf_class = 1; }
            else {
                axx_diagf(0, 0, " error - -f: invalid choice: %s (choose from 32, 64)\n", _fs);
                return 1;
            }
        }
        else if(strcmp(argv[i],"-m")==0&&i+1<argc&&argv[i+1][0]!='-'){
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
            /* An explicit "-" always names stdout; consume it so that it is
               not left behind to be reported as an unknown option. */
            if(i+1<argc && strcmp(argv[i+1],"-")==0){
                pat_macro_expand_dest="-";
                i++;
            }
            else if(i+1<argc && argv[i+1][0]!='-' && patternfile)
                pat_macro_expand_dest=argv[++i];
            else if(i+1<argc && argv[i+1][0]!='-'){
                /* 破綻点修正: 位置引数が揃う前に `-p out.txt pat.axx` と
                 * 書かれた場合、ここは -p を引数なしと解釈し、out.txt を
                 * 位置引数（＝パターンファイル）へ流していた。どちらの意味かは
                 * 原理的に決められないので、黙って一方に倒さず断る。 */
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
            /* An explicit "-" always names stdout; consume it so that it is
               not left behind to be reported as an unknown option. */
            if(i+1<argc && strcmp(argv[i+1],"-")==0){
                macro_expand_dest="-";
                i++;
            }
            else if(i+1<argc && argv[i+1][0]!='-' && patternfile && sourcefile)
                macro_expand_dest=argv[++i];
            else if(i+1<argc && argv[i+1][0]!='-'){
                /* 曖昧な指定を黙って取り違えない。理由は -p 側のコメント参照。 */
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
        else{
            fprintf(stderr,"error: unknown option '%s'.\n",argv[i]);
            print_usage(argv[0]);
            return 1;
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

    if(!patternfile){ print_usage(argv[0]); return 1; }

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
        fclose(pf);
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

    readpat(asmb,patternfile);
    /* 破綻点修正: パターンファイルが読めなかった場合、readpat() はエラーを
     * 報告して空のパターン表のまま戻るが、そのまま組み立てに進んでいたため、
     * 全ソース行が「どのパターンにも一致しない」となり偽の "Syntax error" が
     * 行数ぶん並んで真の原因が埋もれていた。
     * （終了コードが 1 になっていたのはその偽エラーの副作用にすぎない。） */
    if(st->had_error){
        fprintf(stderr," error - one or more errors were reported during assembly; "
                       "output would be incomplete or wrong.\n");
        fprintf(stderr,"         Aborting: no output file written.\n");
        exit_code=1; goto cleanup;
    }
    setpatsymbols(asmb);
    /* 破綻点修正: パターンファイル側のディレクティブ評価（.setsym / .bits 等）で
     * 出たエラーを誰も拾っていなかったため、" error - ..." を表示しながら
     * 終了コード 0 で「出力ファイルだけ作られない」無言の失敗になっていた。 */
    if(st->had_error){
        fprintf(stderr," error - one or more errors were reported while reading the "
                       "pattern file; output would be incomplete or wrong.\n");
        fprintf(stderr,"         Aborting: no output file written.\n");
        exit_code=1; goto cleanup;
    }

    if(st->impfile[0]){
        FILE *lf=axx_open_input(st->impfile, "import file");
        if(!lf){ exit_code=1; goto cleanup; }
        /* 破綻点修正: 1回の走査で処理していたため、ラベル行がセクション行より
         * 前に置かれた TSV では、そのラベルの所属セクションを決めるための
         * 範囲情報がまだ登録されておらず、常に .text 扱いになっていた。
         * axx.py と同じく「3欄以上（セクション範囲）を先に全部」→
         * 「2欄（ラベル）をあとで全部」の2パスで読む。 */
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

    /* 破綻点修正: ここで既存の -b 出力を先に消すと、この後リラクゼーションが
     * 振動/非収束で失敗して "no output file written" と表示した場合でも、
     * 実際には直前の正常なビルド成果物が既に失われてしまう。binary_flush()
     * の fopen(..,"wb") が成功時に上書き・切り詰めを行うので、ここでの
     * 事前削除は不要かつ有害。 */
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

            /* マクロ層に見せるスナップショット。prev_labels と別に持つのは、
             * prev_labels がパス2の前に解放されるのに対し、こちらは収束後の
             * 展開をパス2でも同じに再現するため生かしておく必要があるため。 */
            lmap_free(&st->macro_labels); lmap_init(&st->macro_labels);
            for(int bi=0; bi<st->labels.nbuckets; bi++)
                for(LabelEntry *e=st->labels.buckets[bi]; e; e=e->next)
                    lmap_set_full(&st->macro_labels, e->key, e->value, e->section,
                                  e->is_equ, e->is_imported, e->reloc_type_override, e->is_undef);
            st->macro_labels_valid = 1;

            /* 行番号→アドレスの記録は「複製」ではなく「移動」する。同じ表を
             * 共有すると、次に fileassemble() が今回ぶんを積み直すときに、
             * まさに展開中の式が読んでいる記録を壊してしまう。 */
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
        /* 破綻点修正: pass1 の各リラクゼーション反復は毎回 vars/symbols を
         * initial_vars/patsymbols から作り直してから fileassemble() を
         * 呼んでいたが、pass2 は最後の pass1 反復が実行し終えた後の
         * vars/symbols をそのまま引き継いでいた。.setsym 等でシンボル・
         * 変数を書き換えるソースでは pass2 の開始状態が pass1 のどの反復
         * とも食い違い、アドレスに影響しなければ後段のドリフト検査（ラベル
         * アドレスのみ比較）もすり抜けて出力の値が静かに誤り得た。 */
        smap_clear(&st->symbols);
        for(int pi=0; pi<st->patsymbols.nb; pi++)
            for(SymEntry *se2=st->patsymbols.buckets[pi]; se2; se2=se2->next)
                smap_set(&st->symbols, se2->key, se2->val);
        memcpy(st->vars, initial_vars, sizeof(st->vars));
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
                /* ラベル定義の誤りを既に報告している場合、ずれはその結果に
                 * すぎない（パス1では定義を拒否し、パス2では通ってしまう）。
                 * リラクゼーションの話を持ち出すと原因を見誤らせる。 */
                if(st->reported_label_errors.len > 0)
                    fprintf(stderr,"         This is a consequence of the label definition "
                        "error(s) reported above; fix those first.\n");
                else
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
        if(!lf){ \
            char _experrbuf[1200]; axx_oserr_str((path_), errno, _experrbuf, sizeof(_experrbuf)); \
            axx_diagf(0, 0, " error - cannot open export file '%s': %s\n", \
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
                    /* 破綻点修正: 64bit 符号なしに丸めて出していたため、負の .EQU が \
                     * 0xffffffffffffffff になっていた（axx.py は -0x1）。 \
                     * 256bit のまま計算し、符号付きの Python 表記で出す。 */ \
                    uint256_t _lv = e->is_equ \
                                  ? e->value \
                                  : u256_mul_signed(e->value, u256_from_u64((uint64_t)_bpw_export)); \
                    char _lbl_addr[96]; u256_to_pyhex(_lv, _lbl_addr, sizeof(_lbl_addr)); \
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
                    fprintf(lf,"%s%s\t%s\n",e->key,_rtype_sfx,_lbl_addr); \
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

    lmap_free(&st->macro_labels);
    mlp_vec_free(&st->macro_line_pcs);
    mlp_vec_free(&st->macro_line_pcs_cur);

    macro_free(&g_macro);
    macro_free(&g_pat_macro);

    return exit_code;
}
