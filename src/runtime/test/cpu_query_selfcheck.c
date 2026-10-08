#include "runtime_simd_dispatch.h"
#include <pthread.h>
#include <stdio.h>
#include <stdlib.h>
extern bool rt_simd_has_sse(void);
extern bool rt_simd_has_avx(void);
extern bool rt_simd_has_avx2(void);
static unsigned expected;
static unsigned public_features(void) {
    return rt_simd_has_sse() | (rt_simd_has_avx() << 1) | (rt_simd_has_avx2() << 2);
}
static void *concurrent_queries(void *unused) {
    (void)unused;
    for (unsigned i = 0; i < 1000; ++i)
        if (public_features() != expected) return (void *)1;
    return NULL;
}
int main(void) {
    unsigned checks = 0;
    const unsigned leaves[] = {0, 1, 6, 7, 8};
    for (unsigned leaf = 0; leaf < 5; ++leaf)
        for (unsigned bits = 0; bits < 32; ++bits)
            for (unsigned state = 0; state < 8; ++state) {
                unsigned ecx = ((bits & 1) ? 1U << 26 : 0) |
                               ((bits & 2) ? 1U << 27 : 0) |
                               ((bits & 4) ? 1U << 28 : 0);
                unsigned edx = (bits & 8) ? 1U << 25 : 0;
                unsigned ebx = (bits & 16) ? 1U << 5 : 0;
                unsigned want = leaves[leaf] && (bits & 8) ? 1 : 0;
                if (leaves[leaf] && (bits & 7) == 7 && (state & 6) == 6) {
                    want |= 2;
                    if (leaves[leaf] >= 7 && (bits & 16)) want |= 4;
                }
                if (simd_x86_features_from_raw(leaves[leaf], ecx, edx, ebx, state) != want)
                    return 10;
                ++checks;
            }
    expected = public_features();
#ifdef SIMPLE_RUNTIME_FORCE_NO_AVX2
    if (simd_detect_avx2() != 0) return 11;
#else
    if (simd_detect_avx2() != !!(expected & 4)) return 12;
#endif
    pthread_t threads[4];
    for (unsigned i = 0; i < 4; ++i)
        if (pthread_create(&threads[i], NULL, concurrent_queries, NULL)) return 13;
    for (unsigned i = 0; i < 4; ++i) {
        void *result;
        if (pthread_join(threads[i], &result) || result) return 14;
    }
    printf("features=%u raw_checks=%u concurrent_queries=4000\n", expected, checks);
    return 0;
}
