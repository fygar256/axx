#ifndef BIGINT_SIMPLE_H
#define BIGINT_SIMPLE_H
#include <stdint.h>
#include <string.h>

// 256-bit integer (4 x 64-bit words) for VLIW
typedef struct {
    uint64_t w[4];
} bigint_t;

static inline void bi_zero(bigint_t *a) {
    memset(a->w, 0, sizeof(a->w));
}

static inline void bi_set(bigint_t *a, int64_t val) {
    bi_zero(a);
    a->w[0] = val;
}

static inline void bi_lsh(bigint_t *r, const bigint_t *a, int bits) {
    *r = *a;
    if (bits >= 256) { bi_zero(r); return; }
    
    int ws = bits / 64;
    int bs = bits % 64;
    
    if (ws > 0) {
        for (int i = 3; i >= ws; i--) r->w[i] = r->w[i - ws];
        for (int i = 0; i < ws; i++) r->w[i] = 0;
    }
    
    if (bs > 0) {
        uint64_t c = 0;
        for (int i = 0; i < 4; i++) {
            uint64_t nc = r->w[i] >> (64 - bs);
            r->w[i] = (r->w[i] << bs) | c;
            c = nc;
        }
    }
}

static inline void bi_rsh(bigint_t *r, const bigint_t *a, int bits) {
    *r = *a;
    if (bits >= 256) { bi_zero(r); return; }
    
    int ws = bits / 64;
    int bs = bits % 64;
    
    if (ws > 0) {
        for (int i = 0; i < 4 - ws; i++) r->w[i] = r->w[i + ws];
        for (int i = 4 - ws; i < 4; i++) r->w[i] = 0;
    }
    
    if (bs > 0) {
        for (int i = 0; i < 4; i++) {
            uint64_t c = (i + 1 < 4) ? (r->w[i + 1] << (64 - bs)) : 0;
            r->w[i] = (r->w[i] >> bs) | c;
        }
    }
}

static inline void bi_or(bigint_t *r, const bigint_t *a, const bigint_t *b) {
    for (int i = 0; i < 4; i++) r->w[i] = a->w[i] | b->w[i];
}

static inline void bi_and(bigint_t *r, const bigint_t *a, const bigint_t *b) {
    for (int i = 0; i < 4; i++) r->w[i] = a->w[i] & b->w[i];
}

static inline void bi_sub(bigint_t *r, const bigint_t *a, const bigint_t *b) {
    uint64_t borrow = 0;
    for (int i = 0; i < 4; i++) {
        uint64_t old = a->w[i];
        r->w[i] = old - b->w[i] - borrow;
        borrow = (r->w[i] > old || (borrow && r->w[i] == old)) ? 1 : 0;
    }
}

static inline int64_t bi_get(const bigint_t *a) {
    return a->w[0];
}

#endif
