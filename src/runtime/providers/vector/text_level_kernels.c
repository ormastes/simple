/* Text kernels, one object per SIMD level: UTF-8 validate / find-invalid /
 * codepoint count, ASCII check and case fold, substring search (first/last).
 *
 * Moved from the static runtime (runtime_simd_utf8.c / _case.c / _search.c,
 * which now keep only portable scalar code): the per-ISA block primitives are
 * the old SSE2 / AVX2 / NEON kernels' bodies, written once against a block
 * width W, and the algorithms are the old ones (the AVX2 ASCII-block skip with
 * a scalar walk that finishes the crossing sequence, now for every op and
 * level; Keiser-Lemire lead-byte count; Mula first+last byte filter). Two
 * deliberate changes: the walk checks Unicode Table 3-7 byte ranges instead
 * of decoding (same verdicts), and FIND_LAST walks blocks from the end
 * instead of scanning the whole haystack forward. AVX-512 (L4) is new: the
 * static runtime never had it. The ISA is chosen by the -march this TU is
 * compiled with, never by target attributes or CPUID here:
 *   __AVX512BW__ (x86-64-v4)  W=64   __AVX2__ (x86-64-v3) W=32
 *   __SSE2__ (x86-64, -v2)    W=16   aarch64 NEON W=16 (+SVE count/ascii)
 *   otherwise portable C that the compiler vectorizes (RVV).
 * Libc-free (the compile lane has no sysroot). No load leaves the span. */
#include "text_kernel_private.h"

typedef uint64_t mask_t;
static inline unsigned ctzm(mask_t m) { return (unsigned)__builtin_ctzll(m); }
static inline unsigned topm(mask_t m) { return 63u - (unsigned)__builtin_clzll(m); }

#if defined(__AVX512BW__)
#include <immintrin.h>
#define W 64u
static inline __m512i ld(const uint8_t *p) { return _mm512_loadu_si512((const void *)p); }
static inline mask_t eq_mask(const uint8_t *p, uint8_t c) {
    return (mask_t)_mm512_cmpeq_epi8_mask(ld(p), _mm512_set1_epi8((char)c));
}
static inline int block_ascii(const uint8_t *p) { return _mm512_movepi8_mask(ld(p)) == 0; }
static inline unsigned block_leads(const uint8_t *p) {
    const __mmask64 cont = _mm512_cmpeq_epi8_mask(
        _mm512_and_si512(ld(p), _mm512_set1_epi8((char)0xC0)), _mm512_set1_epi8((char)0x80));
    return 64u - (unsigned)__builtin_popcountll((uint64_t)cont);
}
static inline void block_case(const uint8_t *s, uint8_t *d, uint8_t first, int upper) {
    const __m512i x = ld(s);
    const __mmask64 in = _mm512_cmp_epu8_mask(_mm512_sub_epi8(x, _mm512_set1_epi8((char)first)),
        _mm512_set1_epi8(26), _MM_CMPINT_LT);
    const __m512i bit5 = _mm512_set1_epi8(0x20);
    const __m512i y = upper ? _mm512_andnot_si512(bit5, x) :_mm512_or_si512(x, bit5);
    _mm512_storeu_si512((void *)d, _mm512_mask_blend_epi8(in, x, y));
}
#elif defined(__AVX2__)
#include <immintrin.h>
#define W 32u
static inline __m256i ld(const uint8_t *p) { return _mm256_loadu_si256((const __m256i *)p); }
static inline mask_t eq_mask(const uint8_t *p, uint8_t c) {
    return (uint32_t)_mm256_movemask_epi8(_mm256_cmpeq_epi8(ld(p), _mm256_set1_epi8((char)c)));
}
static inline int block_ascii(const uint8_t *p) { return _mm256_movemask_epi8(ld(p)) == 0; }
static inline unsigned block_leads(const uint8_t *p) {
    const __m256i hi = _mm256_and_si256(ld(p), _mm256_set1_epi8((char)0xC0));
    const __m256i cont = _mm256_cmpeq_epi8(hi, _mm256_set1_epi8((char)0x80));
    return 32u - (unsigned)__builtin_popcount((unsigned)_mm256_movemask_epi8(cont));
}
static inline void block_case(const uint8_t *s, uint8_t *d, uint8_t first, int upper) {
    const __m256i x = ld(s);
    const __m256i ge = _mm256_cmpgt_epi8(x, _mm256_set1_epi8((char)(first - 1)));
    const __m256i le = _mm256_cmpgt_epi8(_mm256_set1_epi8((char)(first + 26)), x);
    const __m256i bit5 = _mm256_and_si256(_mm256_and_si256(ge, le), _mm256_set1_epi8(0x20));
    const __m256i y = upper ? _mm256_andnot_si256(bit5, x) : _mm256_or_si256(x, bit5);
    _mm256_storeu_si256((__m256i *)d, y);
}
#elif defined(__SSE2__)
#include <immintrin.h>
#define W 16u
static inline __m128i ld(const uint8_t *p) { return _mm_loadu_si128((const __m128i *)p); }
static inline mask_t eq_mask(const uint8_t *p, uint8_t c) {
    return (uint32_t)_mm_movemask_epi8(_mm_cmpeq_epi8(ld(p), _mm_set1_epi8((char)c)));
}
static inline int block_ascii(const uint8_t *p) { return _mm_movemask_epi8(ld(p)) == 0; }
static inline unsigned block_leads(const uint8_t *p) {
    const __m128i hi = _mm_and_si128(ld(p), _mm_set1_epi8((char)0xC0));
    const __m128i cont = _mm_cmpeq_epi8(hi, _mm_set1_epi8((char)0x80));
    return 16u - (unsigned)__builtin_popcount((unsigned)_mm_movemask_epi8(cont));
}
static inline void block_case(const uint8_t *s, uint8_t *d, uint8_t first, int upper) {
    const __m128i x = ld(s);
    const __m128i ge = _mm_cmpgt_epi8(x, _mm_set1_epi8((char)(first - 1)));
    const __m128i le = _mm_cmplt_epi8(x, _mm_set1_epi8((char)(first + 26)));
    const __m128i bit5 = _mm_and_si128(_mm_and_si128(ge, le), _mm_set1_epi8(0x20));
    const __m128i y = upper ? _mm_andnot_si128(bit5, x) : _mm_or_si128(x, bit5);
    _mm_storeu_si128((__m128i *)d, y);
}
#elif defined(__aarch64__) && defined(__ARM_NEON)
#include <arm_neon.h>
#define W 16u
static inline mask_t eq_mask(const uint8_t *p, uint8_t c) {
    /* Moved neon_movemask: bit k = lane k. */
    static const uint8_t bits[16] = {1, 2, 4, 8, 16, 32, 64, 128, 1, 2, 4, 8, 16, 32, 64, 128};
    const uint8x16_t m = vandq_u8(vceqq_u8(vld1q_u8(p), vdupq_n_u8(c)), vld1q_u8(bits));
    return (mask_t)vaddv_u8(vget_low_u8(m)) | ((mask_t)vaddv_u8(vget_high_u8(m)) << 8);
}
static inline int block_ascii(const uint8_t *p) { return vmaxvq_u8(vld1q_u8(p)) < 0x80; }
#if !defined(__ARM_FEATURE_SVE) /* SVE levels count with whole-vector predicates */
static inline unsigned block_leads(const uint8_t *p) {
    const uint8x16_t cont = vceqq_u8(vandq_u8(vld1q_u8(p), vdupq_n_u8(0xC0)), vdupq_n_u8(0x80));
    return vaddvq_u8(vandq_u8(vmvnq_u8(cont), vdupq_n_u8(1)));
}
#endif
static inline void block_case(const uint8_t *s, uint8_t *d, uint8_t first, int upper) {
    const uint8x16_t x = vld1q_u8(s);
    const uint8x16_t in = vandq_u8(vcgeq_u8(x, vdupq_n_u8(first)), vcleq_u8(x, vdupq_n_u8((uint8_t)(first + 25))));
    const uint8x16_t bit5 = vandq_u8(in, vdupq_n_u8(0x20));
    vst1q_u8(d, upper ? vbicq_u8(x, bit5) : vorrq_u8(x, bit5));
}
#if defined(__ARM_FEATURE_SVE)
#include <arm_sve.h>
#define TEXT_SVE_SPAN 1
#endif
#else
/* Portable: fixed-trip loops the vectorizer turns into the level's ISA. */
#define W 16u
static inline mask_t eq_mask(const uint8_t *p, uint8_t c) {
    mask_t m = 0;
    for (unsigned j = 0; j < W; ++j) m |= (mask_t)(p[j] == c) << j;
    return m;
}
static inline int block_ascii(const uint8_t *p) {
    uint8_t acc = 0;
    for (unsigned j = 0; j < W; ++j) acc |= p[j];
    return acc < 0x80;
}
static inline unsigned block_leads(const uint8_t *p) {
    unsigned c = 0;
    for (unsigned j = 0; j < W; ++j) c += (p[j] & 0xC0) != 0x80;
    return c;
}
static inline void block_case(const uint8_t *s, uint8_t *d, uint8_t first, int upper) {
    for (unsigned j = 0; j < W; ++j) {
        const uint8_t c = s[j];
        const uint8_t bit5 = (uint8_t)((uint8_t)(c - first) < 26 ? 0x20 : 0);
        d[j] = upper ? (uint8_t)(c & ~bit5) : (uint8_t)(c | bit5);
    }
}
#endif

/* Walk complete sequences from a proven boundary through `end`; the last one
 * may cross `end`. Returns the first invalid offset, or -1 with *next set. */
static int64_t walk_utf8(const uint8_t *d, size_t len, size_t pos, size_t end, size_t *next) {
    /* Unicode Table 3-7: the second byte's range encodes the overlong
     * (E0/F0), surrogate (ED) and > U+10FFFF (F4) rules; same verdicts as
     * decoding the codepoint, without the shifts. */
    while (pos < end && pos < len) {
        const uint8_t b = d[pos];
        if (b < 0x80) { pos++; continue; }
        size_t need;
        uint8_t lo = 0x80, hi = 0xBF;
        if (b < 0xC2) return (int64_t)pos;
        else if (b < 0xE0) need = 2;
        else if (b < 0xF0) { need = 3; if (b == 0xE0) lo = 0xA0; else if (b == 0xED) hi = 0x9F; }
        else if (b < 0xF5) { need = 4; if (b == 0xF0) lo = 0x90; else if (b == 0xF4) hi = 0x8F; }
        else return (int64_t)pos;
        if (len - pos < need || d[pos + 1] < lo || d[pos + 1] > hi) return (int64_t)pos;
        if (need > 2 && (d[pos + 2] & 0xC0) != 0x80) return (int64_t)pos;
        if (need > 3 && (d[pos + 3] & 0xC0) != 0x80) return (int64_t)pos;
        pos += need;
    }
    *next = pos;
    return -1;
}

static int64_t utf8_find_invalid(const uint8_t *d, size_t len) {
    size_t i = 0;
    while (len - i >= W) {
        if (block_ascii(d + i)) { i += W; continue; }
        const int64_t bad = walk_utf8(d, len, i, i + W, &i);
        if (bad >= 0) return bad;
    }
    return walk_utf8(d, len, i, len, &i);
}

static int64_t utf8_count(const uint8_t *d, size_t len) {
    int64_t count = 0;
    size_t i = 0;
#if defined(TEXT_SVE_SPAN)
    for (; i < len; i += svcntb()) {
        const svbool_t pg = svwhilelt_b8_u64(i, len);
        const svuint8_t hi = svand_n_u8_x(pg, svld1_u8(pg, d + i), 0xC0);
        count += (int64_t)(svcntp_b8(pg, pg) - svcntp_b8(pg, svcmpeq_n_u8(pg, hi, 0x80)));
    }
#else
    for (; len - i >= W; i += W) count += block_leads(d + i);
#endif
    for (; i < len; i++) count += (d[i] & 0xC0) != 0x80;
    return count;
}

static int ascii_check(const uint8_t *d, size_t len) {
    size_t i = 0;
#if defined(TEXT_SVE_SPAN)
    for (; i < len; i += svcntb()) {
        const svbool_t pg = svwhilelt_b8_u64(i, len);
        if (svptest_any(pg, svcmpge_n_u8(pg, svld1_u8(pg, d + i), 0x80))) return 0;
    }
#else
    for (; len - i >= W; i += W) if (!block_ascii(d + i)) return 0;
#endif
    for (; i < len; i++) if (d[i] >= 0x80) return 0;
    return 1;
}

static void ascii_case(const uint8_t *s, uint8_t *d, size_t len, int upper) {
    const uint8_t first = upper ? 'a' : 'A';
    size_t i = 0;
    for (; len - i >= W; i += W) block_case(s + i, d + i, first, upper);
    for (; i < len; i++) {
        const uint8_t c = s[i];
        const uint8_t bit5 = (uint8_t)((uint8_t)(c - first) < 26 ? 0x20 : 0);
        d[i] = upper ? (uint8_t)(c & ~bit5) : (uint8_t)(c | bit5);
    }
}

static int bytes_equal(const uint8_t *a, const uint8_t *b, size_t n) {
    for (size_t i = 0; i < n; i++) if (a[i] != b[i]) return 0;
    return 1;
}

/* Mula filter: a candidate start needs the first and the last needle byte to
 * match (for a 1-byte needle both masks are the same, AND is idempotent);
 * only candidates pay the middle compare. */
static int64_t find_first(const uint8_t *h, size_t hlen, const uint8_t *n, size_t nlen) {
    if (nlen == 0) return 0;
    if (nlen > hlen) return -1;
    const size_t span = nlen - 1;
    size_t i = 0;
    for (; hlen - i >= span + W; i += W) {
        mask_t m = eq_mask(h + i, n[0]) & eq_mask(h + i + span, n[span]);
        while (m) {
            const unsigned bit = ctzm(m);
            if (nlen <= 2 || bytes_equal(h + i + bit + 1, n + 1, nlen - 2)) return (int64_t)(i + bit);
            m &= m - 1;
        }
    }
    for (; hlen - i >= nlen; i++)
        if (h[i] == n[0] && h[i + span] == n[span] &&
                (nlen <= 2 || bytes_equal(h + i + 1, n + 1, nlen - 2)))
            return (int64_t)i;
    return -1;
}

/* Same filter walking candidate blocks from the end, so the last match is
 * found without scanning the whole haystack. */
static int64_t find_last(const uint8_t *h, size_t hlen, const uint8_t *n, size_t nlen) {
    if (nlen == 0) return (int64_t)hlen;
    if (nlen > hlen) return -1;
    const size_t span = nlen - 1;
    size_t e = hlen - span; /* candidate starts are [0, e) */
    while (e >= W) {
        const size_t b = e - W;
        mask_t m = eq_mask(h + b, n[0]) & eq_mask(h + b + span, n[span]);
        while (m) {
            const unsigned bit = topm(m);
            if (nlen <= 2 || bytes_equal(h + b + bit + 1, n + 1, nlen - 2)) return (int64_t)(b + bit);
            m &= ~((mask_t)1 << bit);
        }
        e = b;
    }
    while (e-- > 0)
        if (h[e] == n[0] && h[e + span] == n[span] &&
                (nlen <= 2 || bytes_equal(h + e + 1, n + 1, nlen - 2)))
            return (int64_t)e;
    return -1;
}

int simple_text_kernel(uint32_t op, const uint8_t *a, size_t n,
        const uint8_t *b, size_t bn, uint8_t *out, int64_t *result) {
    switch (op) {
    case SIMPLE_VECTOR_TEXT_UTF8_VALIDATE: *result = utf8_find_invalid(a, n) < 0; return 0;
    case SIMPLE_VECTOR_TEXT_UTF8_FIND_INVALID: *result = utf8_find_invalid(a, n); return 0;
    case SIMPLE_VECTOR_TEXT_UTF8_COUNT: *result = utf8_count(a, n); return 0;
    case SIMPLE_VECTOR_TEXT_ASCII_CHECK: *result = ascii_check(a, n); return 0;
    case SIMPLE_VECTOR_TEXT_ASCII_UPPER:
    case SIMPLE_VECTOR_TEXT_ASCII_LOWER:
        ascii_case(a, out, n, op == SIMPLE_VECTOR_TEXT_ASCII_UPPER);
        *result = 0; return 0;
    case SIMPLE_VECTOR_TEXT_FIND: *result = find_first(a, n, b, bn); return 0;
    case SIMPLE_VECTOR_TEXT_FIND_LAST: *result = find_last(a, n, b, bn); return 0;
    default: return -1;
    }
}
