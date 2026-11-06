/* Runtime text hot path timing through the PUBLIC rt_* entry points (the
 * route compiled code takes), so provider call overhead is included.
 * Links runtime_simd_utf8.c + runtime_simd_case.c (SPL_SIMD_TEXT_CASE_PROVIDER)
 * + runtime_simd_search.c. Usage: text_simd_route_bench [reps]
 * Prints one line per op: best-of-7 ns per call, plus the route that ran. */
#include "../runtime_simd_dispatch.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

extern int64_t rt_text_validate_utf8(int64_t);
extern int64_t rt_text_find_invalid_utf8(int64_t);
extern int64_t rt_text_count_codepoints(int64_t);
extern int64_t rt_text_to_upper_ascii(int64_t);
extern int64_t rt_text_to_lower_ascii(int64_t);
extern int64_t rt_simd_str_search(int64_t, int64_t);
extern int64_t rt_simd_str_last_index_of(int64_t, int64_t);
#ifdef SIMPLE_TEXT_PROVIDER_ROUTE
extern int64_t simd_text_provider_level(void);
extern int64_t simd_text_provider_status(void);
#endif

#define BIG (1u << 20)

static double now_ns(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec * 1e9 + (double)ts.tv_nsec;
}
static RtCoreStringSimd *mk(size_t n) {
    RtCoreStringSimd *s = malloc(sizeof(*s) + n + 1);
    if (!s) exit(2);
    s->kind = RT_VALUE_HEAP_STRING_SIMD; s->reserved = 0; s->len = n; s->data[n] = 0;
    return s;
}
static int64_t val(RtCoreStringSimd *s) { return (int64_t)((uintptr_t)s | RT_VALUE_TAG_HEAP_SIMD); }

static volatile int64_t sink;
#define BEST(label, reps, setup, body) do { double best = 1e30; \
    for (int k = 0; k < 7; k++) { double t0 = now_ns(); \
        for (int i = 0; i < (reps); i++) { setup; sink += (body); __asm__ volatile("" ::: "memory"); } \
        double ns = (now_ns() - t0) / (reps); if (ns < best) best = ns; } \
    printf(" %s=%.0f", label, best); } while (0)

int main(int argc, char **argv) {
    int reps = argc > 1 ? atoi(argv[1]) : 40;
    RtCoreStringSimd *ascii = mk(BIG), *page = mk(4096), *mixed = mk(BIG), *small = mk(24), *needle = mk(16), *sneedle = mk(4);
    memset(ascii->data, 'a', BIG);
    memset(page->data, 'Q', 4096);
    for (size_t i = 0; i < BIG;) { /* ~1/3 non-ASCII: a, e-acute, CJK, emoji */
        static const char *pat[] = { "abcdefgh", "\xc3\xa9", "\xe4\xb8\x96", "\xf0\x9f\x98\x80" };
        const char *p = pat[(i / 7) % 4]; size_t l = strlen(p);
        if (i + l > BIG) { mixed->data[i++] = 'z'; continue; }
        memcpy(mixed->data + i, p, l); i += l;
    }
    memcpy(small->data, "hello, simple runtime!!!", 24);
    memcpy(needle->data, "needle-at-end-xy", 16);
    memcpy(ascii->data + BIG - 16, needle->data, 16);
    memcpy(sneedle->data, "!!!!", 4);
    int64_t A = val(ascii), P = val(page),M = val(mixed), S = val(small), N = val(needle), SN = val(sneedle);
    if (rt_text_validate_utf8(M) != 1 || rt_text_validate_utf8(A) != 1) { puts("FAIL corpus"); return 1; }
    if (rt_simd_str_search(A, N) != (int64_t)(BIG - 16)) { puts("FAIL search"); return 1; }
#ifdef SIMPLE_TEXT_PROVIDER_ROUTE
    printf("route level=%lld status=%lld", (long long)simd_text_provider_level(), (long long)simd_text_provider_status());
#else
    printf("route static-dispatch");
#endif
    BEST("validate_ascii_1mib_ns", reps, ascii->reserved = 0, rt_text_validate_utf8(A));
    BEST("validate_mixed_1mib_ns", reps, mixed->reserved = 0, rt_text_validate_utf8(M));
    BEST("find_invalid_mixed_1mib_ns", reps, mixed->reserved = 0, rt_text_find_invalid_utf8(M));
    BEST("count_mixed_1mib_ns", reps, mixed->reserved = 0, rt_text_count_codepoints(M));
    BEST("upper_ascii_1mib_ns", reps, (void)0, (free((void *)(uintptr_t)(rt_text_to_upper_ascii(A) & ~7LL)), 0));
    BEST("lower_ascii_4kib_ns", reps * 100, (void)0, (free((void *)(uintptr_t)(rt_text_to_lower_ascii(P) & ~7LL)), 0));
    BEST("search_1mib_ns", reps, (void)0, rt_simd_str_search(A, N));
    BEST("search_last_1mib_ns", reps, (void)0, rt_simd_str_last_index_of(A, N));
    BEST("validate_24b_ns", reps * 2000, small->reserved = 0, rt_text_validate_utf8(S));
    BEST("count_24b_ns", reps * 2000, small->reserved = 0, rt_text_count_codepoints(S));
    BEST("search_24b_ns", reps * 2000, (void)0, rt_simd_str_search(S, SN));
    putchar('\n');
    return 0;
}
