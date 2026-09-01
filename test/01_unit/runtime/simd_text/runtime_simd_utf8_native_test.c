/* Forced-backend correctness and performance evidence for runtime_simd_utf8.c. */
#define _POSIX_C_SOURCE 200809L
#include <assert.h>
#include <inttypes.h>
#include <stdio.h>
#include <string.h>
#include <time.h>
#include <sys/resource.h>

/* Static kernels intentionally remain visible to this test translation unit. */
#include "../../../../src/runtime/runtime_simd_utf8.c"

static uint64_t now_ns(void) {
    struct timespec ts;
    assert(clock_gettime(CLOCK_MONOTONIC, &ts) == 0);
    return (uint64_t)ts.tv_sec * UINT64_C(1000000000) + (uint64_t)ts.tv_nsec;
}

static void check_one(const uint8_t *data, uint64_t len, int valid,
                      int64_t invalid, int64_t count) {
    assert(scalar_utf8_validate(data, len) == valid);
    assert(scalar_utf8_find_invalid(data, len) == invalid);
    if (valid) assert(scalar_utf8_count_codepoints(data, len) == count);
#if SIMD_HAS_SSE2
    assert(sse2_utf8_validate(data, len) == valid);
    assert(sse2_utf8_find_invalid(data, len) == invalid);
    if (valid) assert(sse2_utf8_count_codepoints(data, len) == count);
#endif
#if SIMD_CAN_AVX2
    if (simd_detect_avx2()) {
        assert(avx2_utf8_validate(data, len) == valid);
        int64_t avx_invalid = avx2_utf8_find_invalid(data, len);
        if (avx_invalid != invalid) {
            fprintf(stderr, "avx2_find_invalid mismatch len=%" PRIu64
                    " expected=%" PRId64 " actual=%" PRId64 " first=%u\n",
                    len, invalid, avx_invalid, len ? (unsigned)data[0] : 0u);
        }
        assert(avx_invalid == invalid);
        if (valid) assert(avx2_utf8_count_codepoints(data, len) == count);
    }
#endif
}

static void correctness(void) {
    static const uint8_t empty[] = {0};
    static const uint8_t ascii[] = "Simple UTF-8 ASCII";
    static const uint8_t mixed[] = {
        'A', 0xC3, 0xA9, 0xE4, 0xB8, 0x96, 0xF0, 0x9F, 0x98, 0x80, 'Z'
    };
    static const uint8_t lone[] = {0x80};
    static const uint8_t overlong2[] = {0xC0, 0x80};
    static const uint8_t trunc2[] = {0xC2};
    static const uint8_t overlong3[] = {0xE0, 0x80, 0x80};
    static const uint8_t surrogate[] = {0xED, 0xA0, 0x80};
    static const uint8_t trunc4[] = {0xF0, 0x9F, 0x98};
    static const uint8_t too_high[] = {0xF4, 0x90, 0x80, 0x80};
    check_one(empty, 0, 1, -1, 0);
    check_one(ascii, sizeof(ascii) - 1, 1, -1, (int64_t)sizeof(ascii) - 1);
    check_one(mixed, sizeof(mixed), 1, -1, 5);
    check_one(lone, sizeof(lone), 0, 0, 0);
    check_one(overlong2, sizeof(overlong2), 0, 0, 0);
    check_one(trunc2, sizeof(trunc2), 0, 0, 0);
    check_one(overlong3, sizeof(overlong3), 0, 0, 0);
    check_one(surrogate, sizeof(surrogate), 0, 0, 0);
    check_one(trunc4, sizeof(trunc4), 0, 0, 0);
    check_one(too_high, sizeof(too_high), 0, 0, 0);

    uint8_t boundary[96];
    memset(boundary, 'x', sizeof(boundary));
    for (size_t at = 15; at <= 65; at++) {
        boundary[at] = 0x80;
        check_one(boundary, sizeof(boundary), 0, (int64_t)at, 0);
        boundary[at] = 'x';
    }
    assert(rt_text_validate_utf8_bytes(NULL, 0) == 1);
    assert(rt_text_validate_utf8_bytes(ascii, sizeof(ascii) - 1) == 1);
    assert(rt_text_validate_utf8_bytes(lone, sizeof(lone)) == 0);
}

typedef int (*validate_fn)(const uint8_t *, uint64_t);

static uint64_t bench(validate_fn fn, const uint8_t *data, uint64_t len,
                      uint64_t iterations, volatile uint64_t *checksum) {
    uint64_t begin = now_ns();
    for (uint64_t i = 0; i < iterations; i++) *checksum += (uint64_t)fn(data, len);
    return now_ns() - begin;
}

static void sort7(uint64_t values[7]) {
    for (int i = 1; i < 7; i++) {
        uint64_t value = values[i];
        int j = i - 1;
        while (j >= 0 && values[j] > value) {
            values[j + 1] = values[j];
            j--;
        }
        values[j + 1] = value;
    }
}

int main(void) {
    correctness();
    static uint8_t corpus[1024 * 1024];
    memset(corpus, 'a', sizeof(corpus));
    const uint64_t iterations = 64;
    const uint64_t bytes = (uint64_t)sizeof(corpus) * iterations;
    volatile uint64_t checksum = 0;
    uint64_t scalar_ns[7] = {0};
    uint64_t sse2_ns[7] = {0};
    uint64_t avx2_ns[7] = {0};
    for (int sample = 0; sample < 7; sample++) {
        scalar_ns[sample] = bench(scalar_utf8_validate, corpus, sizeof(corpus), iterations, &checksum);
#if SIMD_HAS_SSE2
        sse2_ns[sample] = bench(sse2_utf8_validate, corpus, sizeof(corpus), iterations, &checksum);
#endif
#if SIMD_CAN_AVX2
        if (simd_detect_avx2())
            avx2_ns[sample] = bench(avx2_utf8_validate, corpus, sizeof(corpus), iterations, &checksum);
#endif
    }
    sort7(scalar_ns);
    sort7(sse2_ns);
    sort7(avx2_ns);
    struct rusage usage;
    assert(getrusage(RUSAGE_SELF, &usage) == 0);
    printf("text_perf operation=runtime_simd_utf8_native samples=7 iterations_per_sample=%" PRIu64
           " input_bytes=%zu processed_bytes=%" PRIu64
           " scalar_p50_ns=%" PRIu64 " scalar_p95_ns=%" PRIu64
           " sse2_p50_ns=%" PRIu64 " sse2_p95_ns=%" PRIu64
           " avx2_p50_ns=%" PRIu64 " avx2_p95_ns=%" PRIu64
           " active_avx2=%d process_hwm_kib=%ld allocation_count=0"
           " allocated_bytes=0 transient_bytes=%zu retained_bytes=0 checksum=%" PRIu64 "\n",
           iterations, sizeof(corpus), bytes, scalar_ns[3], scalar_ns[6],
           sse2_ns[3], sse2_ns[6], avx2_ns[3], avx2_ns[6],
           simd_detect_avx2(), usage.ru_maxrss, sizeof(corpus), checksum);
    assert(scalar_ns[3] > 0);
#if SIMD_HAS_SSE2
    assert(sse2_ns[3] > 0);
#endif
    return 0;
}
