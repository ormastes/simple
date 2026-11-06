/* Levelled vector provider TEXT opcodes: parity of one DSO (one admitted
 * level) against an independent scalar reference, through the real wire ABI
 * (query -> apply). Usage:
 *   vector_text_level_parity <provider.{so,dll}> <expect_level> [random_cases]
 * expect_level 0: every text opcode must answer FEATURE_UNAVAILABLE.
 * Covers: every tail length 0..2*64+3, misaligned starts, every ill-formed
 * UTF-8 class (overlong, surrogate, >U+10FFFF, bad lead, bad/truncated
 * continuation) at every position, valid 2/3/4-byte sequences straddling
 * every 16/32/64-byte boundary, bytes past the span, ASCII case of all 256
 * bytes incl. in place, search traps, random inputs, and wire refusals. */
#include "../simple_vector_kernel_abi_v1.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#ifdef _WIN32
#include <windows.h>
#define LOAD(p) ((void *)LoadLibraryA(p))
#define SYM(l, n) ((void *)GetProcAddress((HMODULE)(l), n))
#else
#include <dlfcn.h>
#define LOAD(p) dlopen(p, RTLD_NOW | RTLD_LOCAL)
#define SYM(l, n) dlsym(l, n)
#endif

#define FAIL(...) do { fprintf(stderr, "FAIL line=%d: ", __LINE__); fprintf(stderr, __VA_ARGS__); \
    fputc('\n', stderr); exit(1); } while (0)
#define MAXN 300u
#define PAD 80u

static simple_vector_apply_fn_v1 apply;
static int64_t handle;
static int level;
static unsigned long long checks;

/* ---- independent reference (Unicode 15 Table 3-7 well-formed sequences) ---- */
static size_t wf_len(const uint8_t *p, size_t avail) {
    const uint8_t b = p[0];
    if (b < 0x80) return 1;
    uint8_t lo = 0x80, hi = 0xBF;
    size_t need;
    if (b >= 0xC2 && b <= 0xDF) need = 2;
    else if (b == 0xE0) { need = 3; lo = 0xA0; }
    else if (b == 0xED) { need = 3; hi = 0x9F; }
    else if (b >= 0xE1 && b <= 0xEF) need = 3;
    else if (b == 0xF0) { need = 4; lo = 0x90; }
    else if (b == 0xF4) { need = 4; hi = 0x8F; }
    else if (b >= 0xF1 && b <= 0xF3) need = 4;
    else return 0;
    if (avail < need) return 0;
    if (p[1] < lo || p[1] > hi) return 0;
    for (size_t j = 2; j < need; j++) if (p[j] < 0x80 || p[j] > 0xBF) return 0;
    return need;
}
static int64_t ref_find_invalid(const uint8_t *p, size_t n) {
    for (size_t i = 0; i < n;) { size_t l = wf_len(p + i, n - i); if (!l) return (int64_t)i; i += l; }
    return -1;
}
static int64_t ref_count(const uint8_t *p, size_t n) {
    int64_t c = 0; for (size_t i = 0; i < n; i++) c += (p[i] & 0xC0) != 0x80; return c;
}
static int ref_ascii(const uint8_t *p, size_t n) { for (size_t i = 0; i < n; i++) if (p[i] & 0x80) return 0; return 1; }
static uint8_t ref_case(uint8_t c, int upper) {
    if (upper) return (c >= 'a' && c <= 'z') ? (uint8_t)(c - 32) : c;
    return (c >= 'A' && c <= 'Z') ? (uint8_t)(c + 32) : c;
}
static int64_t ref_find(const uint8_t *h, size_t hn, const uint8_t *nd, size_t nn, int last) {
    if (nn == 0) return last ? (int64_t)hn : 0;
    int64_t r = -1;
    for (size_t i = 0; i + nn <= hn; i++) if (!memcmp(h + i, nd, nn)) { if (!last) return (int64_t)i; r = (int64_t)i; }
    return r;
}

/* ---- wire ---- */
static uint32_t call_h(int64_t h, uint32_t op, const uint8_t *a, uint64_t n, const uint8_t *b, uint64_t bn,
        uint8_t *out, uint64_t cap, int64_t *found, uint64_t *written) {
    uint8_t q[64] = {0}, r[24];
    memset(r, 0xEE, sizeof(r));
    simple_vector_wr32(q, 64); simple_vector_wr32(q + 4, op);
    simple_vector_wr64(q + 8, n ? (uintptr_t)a : 0); simple_vector_wr64(q + 16, n);
    simple_vector_wr64(q + 24, bn ? (uintptr_t)b : 0); simple_vector_wr64(q + 32, bn);
    simple_vector_wr64(q + 40, (out && cap) ? (uintptr_t)out : 0); simple_vector_wr64(q + 48, cap);
    if (apply(h, (int64_t)(uintptr_t)q, (int64_t)(uintptr_t)r) != 0) FAIL("apply transport op=%u", op);
    if (simple_vector_rd32(r) != 24) FAIL("response size op=%u", op);
    if (found) *found = (int64_t)simple_vector_rd64(r + 16);
    if (written) *written = simple_vector_rd64(r + 8);
    return simple_vector_rd32(r + 4);
}
static int64_t run(uint32_t op, const uint8_t *a, size_t n, const uint8_t *b, size_t bn) {
    int64_t f = 0;
    uint32_t st = call_h(handle, op, a, n, b, bn, NULL, 0, &f, NULL);
    if (level == 0) { if (st != SIMPLE_VECTOR_FEATURE_UNAVAILABLE) FAIL("level0 op=%u status=%u", op, st); return -2; }
    if (st != SIMPLE_VECTOR_OK) FAIL("op=%u n=%zu status=%u", op, n, st);
    return f;
}

/* All four UTF-8 ops of one span vs the reference. */
static void check_utf8(const uint8_t *p, size_t n, const char *what) {
    const int64_t inv = ref_find_invalid(p, n);
    int64_t v = run(SIMPLE_VECTOR_TEXT_UTF8_VALIDATE, p, n, NULL, 0);
    if (level == 0) { checks++; return; }
    if (v != (inv < 0)) FAIL("%s validate n=%zu got=%lld want=%d", what, n, (long long)v, inv < 0);
    int64_t f = run(SIMPLE_VECTOR_TEXT_UTF8_FIND_INVALID, p, n, NULL, 0);
    if (f != inv) FAIL("%s find_invalid n=%zu got=%lld want=%lld", what, n, (long long)f, (long long)inv);
    int64_t c = run(SIMPLE_VECTOR_TEXT_UTF8_COUNT, p, n, NULL, 0);
    if (c != ref_count(p, n)) FAIL("%s count n=%zu got=%lld want=%lld", what, n, (long long)c, (long long)ref_count(p, n));
    int64_t s = run(SIMPLE_VECTOR_TEXT_ASCII_CHECK, p, n, NULL, 0);
    if (s != ref_ascii(p, n)) FAIL("%s ascii n=%zu", what, n);
    checks += 4;
}
static void check_case(const uint8_t *p, size_t n, uint8_t *out) {
    for (int upper = 0; upper <= 1; upper++) {
        const uint32_t op = upper ? SIMPLE_VECTOR_TEXT_ASCII_UPPER : SIMPLE_VECTOR_TEXT_ASCII_LOWER;
        memset(out, 0xCD, n + 2);
        uint64_t w = 0;
        uint32_t st = call_h(handle, op, p, n, NULL, 0, out + 1, n, NULL, &w);
        if (level == 0) { if (st != SIMPLE_VECTOR_FEATURE_UNAVAILABLE) FAIL("level0 case st=%u", st); continue; }
        if (st != SIMPLE_VECTOR_OK || w != n) FAIL("case n=%zu st=%u w=%llu", n, st, (unsigned long long)w);
        if (out[0] != 0xCD || out[n + 1] != 0xCD) FAIL("case wrote outside span n=%zu", n);
        for (size_t i = 0; i < n; i++) if (out[1 + i] != ref_case(p[i], upper)) FAIL("case n=%zu i=%zu", n, i);
        checks++;
    }
}
static void check_find(const uint8_t *h, size_t hn, const uint8_t *nd, size_t nn) {
    for (int last = 0; last <= 1; last++) {
        int64_t f = run(last ? SIMPLE_VECTOR_TEXT_FIND_LAST : SIMPLE_VECTOR_TEXT_FIND, h, hn, nd, nn);
        if (level == 0) continue;
        int64_t want = ref_find(h, hn, nd, nn, last);
        if (f != want) FAIL("find last=%d hn=%zu nn=%zu got=%lld want=%lld", last, hn, nn, (long long)f, (long long)want);
        checks++;
    }
}

static uint64_t rng = 0x9E3779B97F4A7C15ull;
static uint64_t next(void) { rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17; return rng; }

int main(int argc, char **argv) {
    if (argc < 3) FAIL("usage: %s provider expect_level [random_cases]", argv[0]);
    const int expect = atoi(argv[2]);
    const int random_cases = argc > 3 ? atoi(argv[3]) : 20000;
    void *lib = LOAD(argv[1]);
    if (!lib) FAIL("load %s", argv[1]);
    simple_vector_query_fn_v1 query = (simple_vector_query_fn_v1)(uintptr_t)SYM(lib, "simple_provider_query_v1");
    apply = (simple_vector_apply_fn_v1)(uintptr_t)SYM(lib, "simple_vector_apply_v1");
    int32_t (*level_fn)(void) = (int32_t (*)(void))(uintptr_t)SYM(lib, "simple_vector_selected_level_v1");
    if (!query || !apply || !level_fn) FAIL("missing export");
    uint8_t pq[44] = {0}, pr[84];
    simple_vector_wr32(pq, 44); simple_vector_wr64(pq + 4, SIMPLE_VECTOR_KERNELS_V1_INTERFACE);
    simple_vector_wr32(pq + 12, 1); simple_vector_wr64(pq + 20, 1);
    simple_vector_wr64(pq + 36, SIMPLE_VECTOR_TEXT_CAPS | 15);
    if (query((uintptr_t)pq, (uintptr_t)pr) != 0) FAIL("text caps query refused");
    handle = (int64_t)simple_vector_rd64(pr + 16);
    level = level_fn();
    if (level != expect) FAIL("level %d expected %d", level, expect);

    static uint8_t buf[MAXN + 2 * PAD], out[MAXN + 2 * PAD], nd[96];
    /* Wire refusals (independent of level). */
    {
        int64_t f; uint64_t w;
        simple_vector_wr64(pq + 36, 15);
        if (query((uintptr_t)pq, (uintptr_t)pr) != 0) FAIL("bitmap-only query");
        const int64_t no_text = (int64_t)simple_vector_rd64(pr + 16);
        memset(buf, 'a', 128);
        if (call_h(no_text, SIMPLE_VECTOR_TEXT_UTF8_VALIDATE, buf, 64, NULL, 0, NULL, 0, &f, NULL) != SIMPLE_VECTOR_CAPABILITY_DENIED)
            FAIL("text op without text capability not denied");
        if (call_h(handle, 13, buf, 64, NULL, 0, NULL, 0, &f, NULL) != SIMPLE_VECTOR_UNSUPPORTED_OPERATION)
            FAIL("opcode 13 not unsupported");
        if (call_h(handle, SIMPLE_VECTOR_TEXT_ASCII_UPPER, buf, 64, NULL, 0, buf + 1, 64, &f, &w) != SIMPLE_VECTOR_RANGE_INVALID)
            FAIL("partial overlap not refused");
        if (call_h(handle, SIMPLE_VECTOR_TEXT_ASCII_UPPER, buf, 64, NULL, 0, out, 63, &f, &w) != SIMPLE_VECTOR_RANGE_INVALID)
            FAIL("short output not refused");
        if (call_h(handle, SIMPLE_VECTOR_TEXT_UTF8_COUNT, buf, 64, buf, 4, NULL, 0, &f, NULL) != SIMPLE_VECTOR_RANGE_INVALID)
            FAIL("stray needle not refused");
        if (call_h(handle, SIMPLE_VECTOR_TEXT_FIND, buf, 64, NULL, 0, out, 64, &f, NULL) != SIMPLE_VECTOR_RANGE_INVALID)
            FAIL("stray output on find not refused");
        checks += 6;
    }
    static const struct { const char *b; unsigned n; } bad[] = {
        {"\x80", 1}, {"\xBF", 1}, {"\xC0\x80", 2}, {"\xC1\xBF", 2}, {"\xE0\x80\x80", 3},
        {"\xE0\x9F\xBF", 3}, {"\xF0\x80\x80\x80", 4}, {"\xF0\x8F\xBF\xBF", 4}, {"\xED\xA0\x80", 3},
        {"\xED\xBF\xBF", 3}, {"\xF4\x90\x80\x80", 4}, {"\xF5\x80\x80\x80", 4}, {"\xF8\x88\x80\x80", 4},
        {"\xFE", 1}, {"\xFF", 1}, {"\xC2", 1}, {"\xE2\x82", 2}, {"\xF0\x9F\x98", 3},
        {"\xC2\x41", 2}, {"\xE2\x28\xA1", 3}, {"\xF0\x9F\x28\x80", 4}, {"\xC3\xC3", 2}};
    static const struct { const char *b; unsigned n; } good[] = {
        {"\xC2\x80", 2}, {"\xDF\xBF", 2}, {"\xE0\xA0\x80", 3}, {"\xED\x9F\xBF", 3}, {"\xEE\x80\x80", 3},
        {"\xEF\xBF\xBF", 3}, {"\xF0\x90\x80\x80", 4}, {"\xF4\x8F\xBF\xBF", 4}, {"\xF0\x9F\x98\x80", 4}};
    const size_t nbad = sizeof(bad) / sizeof(bad[0]), ngood = sizeof(good) / sizeof(good[0]);
    const size_t maxlen = 2 * 64 + 3;
    /* Backgrounds: ASCII and a valid 2-byte mix, so a bad sequence lands both
     * in an all-ASCII block and mid-way through multibyte text. Every start
     * offset in 0..63 is exercised across the sweep (misaligned loads). */
    for (int bg = 0; bg < 2; bg++)
    for (size_t n = 0; n <= maxlen; n++) {
        const size_t off = (n * 7 + (size_t)bg * 13) % 64;
        uint8_t *p = buf + off;
        for (size_t i = 0; i < n + PAD; i++) p[i] = bg ? (uint8_t)((i % 3 == 2) ? 'm' : (i % 3 == 0 ? 0xC3 : 0xA9)) : 'a';
        if (bg && n % 3 == 1) p[n - 1] = 'z'; /* keep the background itself valid */
        p[n] = 0xFF; /* past-the-span byte must never matter */
        check_utf8(p, n, "background");
        check_case(p, n, out);
        for (size_t pos = 0; pos < n; pos++) {
            for (size_t k = 0; k < nbad; k++) {
                uint8_t save[4]; const size_t l = bad[k].n;
                memcpy(save, p + pos, 4);
                for (size_t j = 0; j < l && pos + j < n; j++) p[pos + j] = (uint8_t)bad[k].b[j];
                check_utf8(p, n, "bad");
                memcpy(p + pos, save, 4);
            }
            for (size_t k = 0; k < ngood && !bg; k++) {
                const size_t l = good[k].n;
                if (pos + l > n) { /* truncated by the span end: must be invalid */
                    memcpy(p + pos, good[k].b, l); check_utf8(p, n, "cut"); memset(p + pos, 'a', l); continue;
                }
                memcpy(p + pos, good[k].b, l); check_utf8(p, n, "straddle"); memset(p + pos, 'a', l);
            }
        }
        p[n] = bg ? 'm' : 'a';
    }
    /* ASCII case: every byte value in every lane position; in place too. */
    for (size_t n = 0; n <= maxlen; n++) {
        uint8_t *p = buf + (n % 64);
        for (size_t i = 0; i < n; i++) p[i] = (uint8_t)(i * 37 + n);
        check_case(p, n, out);
        if (level > 0 && n) {
            uint8_t want[MAXN];
            for (size_t i = 0; i < n; i++) want[i] = ref_case(p[i], 1);
            uint64_t w = 0;
            if (call_h(handle, SIMPLE_VECTOR_TEXT_ASCII_UPPER, p, n, NULL, 0, p, n, NULL, &w) != SIMPLE_VECTOR_OK ||
                memcmp(p, want, n)) FAIL("in-place upper n=%zu", n);
            checks++;
        }
    }
    /* Search: needle at every position (incl. crossing the end), traps where
     * first and last bytes match but the middle does not, needle past span. */
    for (size_t hn = 0; hn <= maxlen; hn++) {
        uint8_t *h = buf + (hn % 61);
        for (size_t nn = 1; nn <= 70 && nn <= hn + 1; nn += (nn < 6 ? 1 : 7)) {
            for (size_t i = 0; i < nn; i++) nd[i] = (uint8_t)('A' + i % 23);
            memset(h, 'x', hn + nn + 1);
            check_find(h, hn, nd, nn);
            memcpy(h + hn, nd, nn); /* just past the span: must not match */
            check_find(h, hn, nd, nn);
            memset(h + hn, 'x', nn);
            for (size_t pos = 0; pos + nn <= hn; pos += (hn > 40 ? 3 : 1)) {
                memcpy(h + pos, nd, nn);
                if (nn > 2) h[pos + nn / 2] ^= 1; /* trap */
                check_find(h, hn, nd, nn);
                if (nn > 2) h[pos + nn / 2] ^= 1;
                check_find(h, hn, nd, nn);
                if (pos + 2 * nn <= hn) { memcpy(h + hn - nn, nd, nn); check_find(h, hn, nd, nn); memset(h + hn - nn, 'x', nn); }
                memset(h + pos, 'x', nn);
            }
        }
    }
    /* Random: near-valid UTF-8 mixes, raw bytes, substring needles. */
    static const char *atoms[] = {"a", "Z", "\xC3\xA9", "\xE4\xB8\x96", "\xF0\x9F\x98\x80", "\xED\x9F\xBF", "\x80", "\xF4\x90\x80\x80", "\xC2", "\n"};
    for (int c = 0; c < random_cases; c++) {
        const size_t off = next() % 64, n = next() % MAXN;
        uint8_t *p = buf + off;
        const int raw = (int)(next() % 8 == 0), clean = (int)(next() % 2);
        for (size_t i = 0; i < n;) {
            if (raw) { p[i++] = (uint8_t)next(); continue; }
            const char *a = atoms[next() % (clean ? 6 : 10)]; size_t l = strlen(a);
            for (size_t j = 0; j < l && i < n; j++) p[i++] = (uint8_t)a[j];
        }
        check_utf8(p, n, "random");
        if (c % 4 == 0) check_case(p, n, out);
        if (n) {
            const size_t s = next() % n, nn = 1 + next() % (n - s < 40 ? n - s : 40);
            memcpy(nd, p + s, nn);
            check_find(p, n, nd, nn);
        }
    }
    printf("PASS level=%d text_parity_checks=%llu\n", level, checks);
    return 0;
}
