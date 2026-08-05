#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include "../../../fixtures/crypto/x25519mlkem768/ntt_fixture.h"

#if !defined(_WIN32)
#include <pthread.h>
#endif

#include "runtime.h"

#if defined(__riscv) && defined(__riscv_vector)
#include <riscv_vector.h>
#endif

typedef struct {
    uint8_t kind;
    uint8_t flags;
    uint8_t reserved[6];
    int64_t len;
    int64_t cap;
    int64_t *data;
} TestArray;

static TestArray output_array;
static int64_t output_coefficients[768];

int64_t rt_array_len(SplArray *array) {
    return array ? ((TestArray *)array)->len : 0;
}

int64_t rt_array_data_ptr(SplArray *array) {
    return array ? (int64_t)(uintptr_t)((TestArray *)array)->data : 0;
}

SplArray *rt_array_new_uninit(int64_t cap) {
    if (cap < 0 || cap > 768) return NULL;
    memset(output_coefficients, 0, sizeof(output_coefficients));
    output_array = (TestArray){0, 0, {0}, 0, cap, output_coefficients};
    return (SplArray *)&output_array;
}

int64_t rt_array_header_ptr(SplArray *array) {
    return (int64_t)(uintptr_t)array;
}

int8_t rt_array_set_len_known(int64_t header_ptr, int64_t len) {
    ((TestArray *)(uintptr_t)header_ptr)->len = len;
    return 1;
}

static const int32_t zetas[128] = {
       1, 1729, 2580, 3289, 2642,  630, 1897,  848,
    1062, 1919,  193,  797, 2786, 3260,  569, 1746,
     296, 2447, 1339, 1476, 3046,   56, 2240, 1333,
    1426, 2094,  535, 2882, 2393, 2879, 1974,  821,
     289,  331, 3253, 1756, 1197, 2304, 2277, 2055,
     650, 1977, 2513,  632, 2865,   33, 1320, 1915,
    2319, 1435,  807,  452, 1438, 2868, 1534, 2402,
    2647, 2617, 1481,  648, 2474, 3110, 1227,  910,
      17, 2761,  583, 2649, 1637,  723, 2288, 1100,
    1409, 2662, 3281,  233,  756, 2156, 3015, 3050,
    1703, 1651, 2789, 1789, 1847,  952, 1461, 2687,
     939, 2308, 2437, 2388,  733, 2337,  268,  641,
    1584, 2298, 2037, 3220,  375, 2549, 2090, 1645,
    1063,  319, 2773,  757, 2099,  561, 2466, 2594,
    2804, 1092,  403, 1026, 1143, 2150, 2775,  886,
    1722, 1212, 1874, 1029, 2110, 2935,  885, 2154
};

static int32_t modq(int64_t value) {
    int64_t reduced = value % 3329;
    return (int32_t)(reduced < 0 ? reduced + 3329 : reduced);
}

static void scalar_ntt(int32_t f[256]) {
    int k = 1;
    for (int len = 128; len >= 2; len /= 2) {
        for (int start = 0; start < 256; start += 2 * len) {
            int32_t zeta = zetas[k++];
            for (int j = start; j < start + len; j++) {
                int32_t product = modq((int64_t)zeta * f[j + len]);
                int32_t lower = f[j];
                f[j] = modq((int64_t)lower + product);
                f[j + len] = modq((int64_t)lower - product);
            }
        }
    }
}

static void scalar_intt(int32_t f[256]) {
    int k = 127;
    for (int len = 2; len <= 128; len *= 2) {
        for (int start = 0; start < 256; start += 2 * len) {
            int32_t zeta = zetas[k--];
            for (int j = start; j < start + len; j++) {
                int32_t lower = f[j];
                int32_t upper = f[j + len];
                f[j] = modq((int64_t)lower + upper);
                f[j + len] = modq((int64_t)zeta * modq((int64_t)upper - lower));
            }
        }
    }
    for (int i = 0; i < 256; i++) f[i] = modq((int64_t)f[i] * 3303);
}

static int compare_tagged(const int64_t *actual, const int32_t *expected,
                          int64_t count) {
    for (int64_t i = 0; i < count; i++) {
        int32_t value = (int32_t)((int64_t)actual[i] >> 3);
        if (value != expected[i]) {
            fprintf(stderr, "mismatch index=%lld expected=%d actual=%d\n",
                    (long long)i, expected[i], value);
            return 0;
        }
    }
    return 1;
}

static uint64_t monotonic_ns(void) {
    struct timespec value;
    if (clock_gettime(CLOCK_MONOTONIC, &value) != 0) return 0;
    return (uint64_t)value.tv_sec * 1000000000ULL + (uint64_t)value.tv_nsec;
}

#if !defined(_WIN32)
static void *check_fresh_thread_receipt(void *opaque) {
    int *ok = (int *)opaque;
    *ok = rt_mlkem_ntt_simd_hits() == 0 &&
        rt_mlkem_ntt_simd_observed_rvv_vlen_bits() == 0;
    rt_mlkem_ntt_simd_reset();
    if (rt_mlkem_ntt_simd_hits() != 0) *ok = 0;
    if (rt_mlkem_ntt_simd_observed_rvv_vlen_bits() != 0) *ok = 0;
    return NULL;
}
#endif

static void run_benchmark(const int64_t *tagged_input, int64_t iterations) {
    if (iterations < 1) return;
    int32_t scalar_work[768];
    volatile int64_t checksum = 0;
    uint64_t scalar_start = monotonic_ns();
    for (int64_t sample = 0; sample < iterations; sample++) {
        for (int i = 0; i < 768; i++)
            scalar_work[i] = (int32_t)(tagged_input[i] >> 3);
        for (int poly = 0; poly < 3; poly++)
            scalar_ntt(scalar_work + poly * 256);
        checksum += scalar_work[sample % 768];
    }
    uint64_t scalar_end = monotonic_ns();
    TestArray input = {0, 0, {0}, 768, 768, (int64_t *)tagged_input};
    uint64_t simd_start = monotonic_ns();
    for (int64_t sample = 0; sample < iterations; sample++) {
        SplArray *result = rt_mlkem_ntt_simd_batch((SplArray *)&input, false);
        if (!result || rt_array_len(result) != 768) exit(20);
        checksum += output_coefficients[sample % 768] >> 3;
    }
    uint64_t simd_end = monotonic_ns();
    uint64_t operations = (uint64_t)iterations * 3;
    uint64_t scalar_elapsed = scalar_end - scalar_start;
    uint64_t simd_elapsed = simd_end - simd_start;
    uint64_t scalar_ns = (scalar_end - scalar_start) / operations;
    uint64_t simd_ns = (simd_end - simd_start) / operations;
    double speedup = simd_ns == 0 ? 0.0 : (double)scalar_ns / (double)simd_ns;
    uint64_t speedup_milli = simd_elapsed == 0 ? 0 :
        (scalar_elapsed > UINT64_MAX / 1000u ? UINT64_MAX :
            (scalar_elapsed * 1000u) / simd_elapsed);
    puts("mlkem_ntt_benchmark_scope=focused-primitive-mean-not-full-mlkem-promotion");
    printf("mlkem_ntt_scalar_ns_per_op=%llu\n", (unsigned long long)scalar_ns);
    printf("mlkem_ntt_simd_ns_per_op=%llu\n", (unsigned long long)simd_ns);
    printf("mlkem_ntt_simd_speedup=%.3f\n", speedup);
    printf("mlkem_ntt_simd_speedup_milli=%llu\n",
           (unsigned long long)speedup_milli);
    printf("mlkem_ntt_benchmark_checksum=%lld\n", (long long)checksum);
}

int main(void) {
    int64_t tagged_input[768];
    int32_t expected_forward[768];
    int32_t expected_inverse[768];
    for (int poly = 0; poly < 3; poly++) {
        for (int i = 0; i < 256; i++) {
            int32_t value = x25519mlkem768_ntt_fixture_coefficient(poly, i);
            tagged_input[poly * 256 + i] = (int64_t)value << 3;
            expected_forward[poly * 256 + i] = value;
        }
        scalar_ntt(expected_forward + poly * 256);
        memcpy(expected_inverse + poly * 256, expected_forward + poly * 256,
               256 * sizeof(int32_t));
        scalar_intt(expected_inverse + poly * 256);
    }

    TestArray input = {0, 0, {0}, 768, 768, tagged_input};
    int64_t backend = rt_mlkem_ntt_simd_backend();
    printf("mlkem_ntt_simd_backend=%lld\n", (long long)backend);
#if defined(__riscv) && defined(__riscv_vector)
    printf("mlkem_ntt_simd_rvv_e32m1_lanes=%zu\n",
           __riscv_vsetvl_e32m1(256));
#endif
    if (backend == 0) return 77;
    if (backend == 1) {
        int64_t reduction_mismatches = rt_mlkem_modq_avx2_selfcheck();
        printf("mlkem_ntt_avx2_reduction_mismatches=%lld\n",
               (long long)reduction_mismatches);
        if (reduction_mismatches != 0) return 8;
    }

    rt_mlkem_ntt_simd_reset();
    if (rt_mlkem_ntt_simd_observed_rvv_vlen_bits() != 0) return 15;
    SplArray *forward = rt_mlkem_ntt_simd_batch((SplArray *)&input, false);
    if (!forward || rt_array_len(forward) != 768) return 1;
    if (!compare_tagged(output_coefficients, expected_forward, 768)) return 2;
    int64_t forward_hits = rt_mlkem_ntt_simd_hits();
    if (forward_hits <= 0) return 3;
    int64_t observed_rvv_vlen_bits =
        rt_mlkem_ntt_simd_observed_rvv_vlen_bits();
    printf("mlkem_ntt_simd_observed_rvv_vlen_bits=%lld\n",
           (long long)observed_rvv_vlen_bits);
#if defined(__riscv) && defined(__riscv_vector)
    if (backend == 3 && observed_rvv_vlen_bits !=
            (int64_t)(__riscv_vsetvlmax_e32m1() * 32u)) return 16;
#else
    if (observed_rvv_vlen_bits != 0) return 16;
#endif

    int64_t forward_copy[768];
    memcpy(forward_copy, output_coefficients, sizeof(forward_copy));
    TestArray transformed = {0, 0, {0}, 768, 768, forward_copy};
    SplArray *inverse = rt_mlkem_ntt_simd_batch((SplArray *)&transformed, true);
    if (!inverse || rt_array_len(inverse) != 768) return 4;
    if (!compare_tagged(output_coefficients, expected_inverse, 768)) return 5;
    int64_t total_hits = rt_mlkem_ntt_simd_hits();
    if (total_hits <= forward_hits) return 6;
    if (rt_mlkem_ntt_simd_observed_rvv_vlen_bits() !=
            observed_rvv_vlen_bits) return 17;

#if !defined(_WIN32)
    int fresh_thread_receipt_ok = 0;
    pthread_t receipt_thread;
    if (pthread_create(&receipt_thread, NULL, check_fresh_thread_receipt,
                       &fresh_thread_receipt_ok) != 0) return 11;
    if (pthread_join(receipt_thread, NULL) != 0) return 12;
    if (!fresh_thread_receipt_ok) return 13;
    if (rt_mlkem_ntt_simd_hits() != total_hits) return 14;
    if (rt_mlkem_ntt_simd_observed_rvv_vlen_bits() !=
            observed_rvv_vlen_bits) return 18;
#endif

    /* The public batch boundary must canonicalize arbitrary integer
       representatives before entering reciprocal-reduction kernels. */
    int64_t noncanonical_tagged[256];
    int32_t canonical_expected[256];
    for (int i = 0; i < 256; i++) {
        int64_t representative = (i % 3 == 0) ? i - 6658 :
            ((i % 3 == 1) ? i + 3329 : i + 9987);
        noncanonical_tagged[i] = representative * 8;
        canonical_expected[i] = modq(representative);
    }
    scalar_ntt(canonical_expected);
    TestArray noncanonical = {
        0, 0, {0}, 256, 256, noncanonical_tagged};
    SplArray *canonicalized = rt_mlkem_ntt_simd_batch(
        (SplArray *)&noncanonical, false);
    if (!canonicalized || rt_array_len(canonicalized) != 256) return 9;
    if (!compare_tagged(output_coefficients, canonical_expected, 256)) return 10;

    printf("mlkem_ntt_simd_forward_hits=%lld\n", (long long)forward_hits);
    printf("mlkem_ntt_simd_total_hits=%lld\n", (long long)total_hits);
    printf("mlkem_ntt_fixture_id=%s\n", X25519MLKEM768_NTT_FIXTURE_ID);
    puts("mlkem_ntt_simd_thread_local_receipt=pass");
    const char *benchmark_env = getenv("MLKEM_SIMD_BENCH_ITERS");
    run_benchmark(tagged_input, benchmark_env ? atoll(benchmark_env) : 0);
    puts("MLKEM_NTT_SIMD_C_TEST: PASS");
    return 0;
}
