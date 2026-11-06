/* Runtime text route: links the production runtime_simd_utf8.c +
 * runtime_simd_case.c (SPL_SIMD_TEXT_CASE_PROVIDER) + runtime_simd_search.c
 * and checks, in ONE process (admission is once per process):
 *   1. the admission outcome is exactly the expected one
 *      (simd_text_provider_status / _level), and
 *   2. every public text entry point returns the reference answer, whether
 *      the route ended up provider-backed or scalar (absent / refused DSO
 *      must fall back, never crash, never be wrong).
 * Usage: text_simd_provider_route_selfcheck <expect_status> <expect_level>
 * The provider path/pin come from SIMPLE_VECTOR_PROVIDER_PATH/_SHA256. */
#include "../runtime_simd_dispatch.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

extern int64_t rt_text_validate_utf8(int64_t);
extern int64_t rt_text_validate_utf8_bytes(const uint8_t *, uint64_t);
extern int64_t rt_text_find_invalid_utf8(int64_t);
extern int64_t rt_text_count_codepoints(int64_t);
extern int64_t rt_text_is_ascii(int64_t);
extern int64_t rt_text_to_upper_ascii(int64_t);
extern int64_t rt_text_to_lower_ascii(int64_t);
extern int64_t rt_simd_str_search(int64_t, int64_t);
extern int64_t rt_simd_str_last_index_of(int64_t, int64_t);

#define FAIL(...) do { fprintf(stderr, "FAIL line=%d: ", __LINE__); fprintf(stderr, __VA_ARGS__); \
    fputc('\n', stderr); exit(1); } while (0)
static unsigned long checks;

static size_t wf_len(const uint8_t *p, size_t avail) {
    const uint8_t b = p[0];
    if (b < 0x80) return 1;
    uint8_t lo = 0x80, hi = 0xBF; size_t need;
    if (b >= 0xC2 && b <= 0xDF) need = 2;
    else if (b == 0xE0) { need = 3; lo = 0xA0; }
    else if (b == 0xED) { need = 3; hi = 0x9F; }
    else if (b >= 0xE1 && b <= 0xEF) need = 3;
    else if (b == 0xF0) { need = 4; lo = 0x90; }
    else if (b == 0xF4) { need = 4; hi = 0x8F; }
    else if (b >= 0xF1 && b <= 0xF3) need = 4;
    else return 0;
    if (avail < need || p[1] < lo || p[1] > hi) return 0;
    for (size_t j = 2; j < need; j++) if (p[j] < 0x80 || p[j] > 0xBF) return 0;
    return need;
}
static int64_t ref_invalid(const uint8_t *p, size_t n) {
    for (size_t i = 0; i < n;) { size_t l = wf_len(p + i, n - i); if (!l) return (int64_t)i; i += l; }
    return -1;
}
static int64_t ref_find(const uint8_t *h, size_t hn, const uint8_t *nd, size_t nn, int last) {
    int64_t r = -1;
    for (size_t i = 0; i + nn <= hn; i++) if (!memcmp(h + i, nd, nn)) { if (!last) return (int64_t)i; r = (int64_t)i; }
    return r;
}

static RtCoreStringSimd *str(size_t cap) {
    RtCoreStringSimd *s = malloc(sizeof(*s) + cap + 1);
    if (!s) FAIL("oom");
    s->kind = RT_VALUE_HEAP_STRING_SIMD; s->reserved = 0; s->len = 0;
    return s;
}
static int64_t V(RtCoreStringSimd *s) { return (int64_t)((uintptr_t)s | RT_VALUE_TAG_HEAP_SIMD); }

static void check(RtCoreStringSimd *s, RtCoreStringSimd *nd) {
    const uint8_t *p = (const uint8_t *)s->data; const size_t n = s->len;
    const int64_t inv = ref_invalid(p, n);
    int64_t cnt = 0; int ascii = 1;
    for (size_t i = 0; i < n; i++) { cnt += (p[i] & 0xC0) != 0x80; if (p[i] & 0x80) ascii = 0; }
    s->reserved = 0;
    if (rt_text_validate_utf8(V(s)) != (inv < 0)) FAIL("validate n=%zu", n);
    if (rt_text_validate_utf8_bytes(p, n) != (inv < 0)) FAIL("validate_bytes n=%zu", n);
    s->reserved = 0;
    if (rt_text_find_invalid_utf8(V(s)) != inv) FAIL("find_invalid n=%zu", n);
    s->reserved = 0;
    if (rt_text_count_codepoints(V(s)) != cnt) FAIL("count n=%zu", n);
    s->reserved = 0;
    if (rt_text_is_ascii(V(s)) != ascii) FAIL("is_ascii n=%zu", n);
    for (int upper = 0; upper <= 1; upper++) {
        s->reserved = 0;
        int64_t o = upper ? rt_text_to_upper_ascii(V(s)) : rt_text_to_lower_ascii(V(s));
        RtCoreStringSimd *t = simd_as_string(o);
        if (!t || t->len != n) FAIL("case len n=%zu", n);
        for (size_t i = 0; i < n; i++) {
            uint8_t c = p[i], w = upper ? ((c >= 'a' && c <= 'z') ? c - 32 : c) : ((c >= 'A' && c <= 'Z') ? c + 32 : c);
            if ((uint8_t)t->data[i] != w) FAIL("case upper=%d n=%zu i=%zu", upper, n, i);
        }
        if (t != s) free(t);
    }
    if (nd->len && rt_simd_str_search(V(s), V(nd)) != ref_find(p, n, (const uint8_t *)nd->data, nd->len, 0))
        FAIL("search n=%zu nn=%llu", n, (unsigned long long)nd->len);
    if (nd->len && rt_simd_str_last_index_of(V(s), V(nd)) != ref_find(p, n, (const uint8_t *)nd->data, nd->len, 1))
        FAIL("search_last n=%zu", n);
    checks++;
}

int main(int argc, char **argv) {
    if (argc < 3) FAIL("usage: %s expect_status expect_level", argv[0]);
    if (g_simd_text.utf8_validate) FAIL("eager text initialization");
    const int64_t want_status = atoll(argv[1]), want_level = atoll(argv[2]);
    const int64_t status = simd_text_provider_status(), level = simd_text_provider_level();
    if (status != want_status || level != want_level)
        FAIL("route status=%lld level=%lld, expected status=%lld level=%lld",
             (long long)status, (long long)level, (long long)want_status, (long long)want_level);
    RtCoreStringSimd *s = str(400), *nd = str(64);
    static const char *bad[] = {"\x80", "\xC0\x80", "\xE0\x9F\xBF", "\xED\xA0\x80", "\xF4\x90\x80\x80", "\xF0\x9F\x98", "\xC2", "\xFF"};
    /* Around the provider threshold (64) and the 16/32/64-byte blocks. */
    for (size_t n = 0; n <= 2 * 64 + 3; n++) {
        for (size_t i = 0; i < n; i++) s->data[i] = (char)("aBc-\xc3\xa9Z"[i % 7]);
        if (n % 7 == 5) s->data[n - 1] = 'q'; /* do not end on a lone 0xC3 */
        s->len = n;
        memcpy(nd->data, "Z", 1); nd->len = 1;
        check(s, nd);
        memcpy(nd->data, "\xa9Za", 3); nd->len = 3;
        check(s, nd);
        for (size_t pos = 0; pos < n; pos += (n > 70 ? 5 : 1))
            for (size_t k = 0; k < sizeof(bad) / sizeof(bad[0]); k++) {
                char save[4]; size_t l = strlen(bad[k]);
                memcpy(save, s->data + pos, 4);
                for (size_t j = 0; j < l && pos + j < n; j++) s->data[pos + j] = bad[k][j];
                check(s, nd);
                memcpy(s->data + pos, save, 4);
            }
    }
    printf("PASS route status=%lld level=%lld checks=%lu\n", (long long)status, (long long)level, checks);
    return 0;
}
