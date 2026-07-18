/*
 * Standalone bit-exactness gate for the engine2d C SIMD row kernels.
 *
 * This test exercises the REAL helper math from
 *   src/runtime/runtime_simd_dispatch.c
 *     - engine2d_fill_into
 *     - engine2d_copy_into
 *     - engine2d_blend_pixel
 *     - engine2d_blend_into  (the NEON-vectorized path on aarch64)
 *
 * Those four helpers depend on nothing from the full runtime (only
 * int64_t/uint32_t and NEON intrinsics), so the gate runner slices that
 * block out of the source verbatim into a generated header and we #include
 * it here. That means there is a SINGLE source of truth and drift is
 * impossible -- if the kernels change, this test recompiles against the new
 * code automatically.
 *
 * Build/run via: scripts/check/check-engine2d-simd-c-kernels.shs
 *
 * The scalar reference math below is written INDEPENDENTLY of the helpers
 * (it does NOT call engine2d_blend_pixel); otherwise the test would be a
 * tautology that proves nothing.
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <stdatomic.h>

#if defined(__aarch64__) || defined(_M_ARM64)
#  include <arm_neon.h>
#endif

#if defined(__riscv) && defined(__riscv_vector)
#  include <riscv_vector.h>
#endif

/* The x86 branch of fill_into/copy_into references simd_detect_avx2(); it is
 * dead on aarch64 but must resolve if this gate is ever compiled on x86. */
#if defined(__x86_64__) || defined(_M_X64)
#  include <immintrin.h>
static int simd_detect_avx2(void) { return 0; }
#endif

/* Pull in the REAL kernel helpers, sliced verbatim from
 * src/runtime/runtime_simd_dispatch.c by the gate runner.
 * MUST stay in sync with src/runtime/runtime_simd_dispatch.c (kept in sync
 * automatically by re-extracting on every run). */
#include "engine2d_simd_helpers.generated.h"

/* -------------------------------------------------------------------------
 * Independent scalar references (the "spec"). Do NOT use the kernel helpers.
 * ------------------------------------------------------------------------- */

/* src-over blend reference, truncating floor formula. s/d are packed
 * 0xAARRGGBB in the low 32 bits of an int64_t. */
static int64_t ref_blend_pixel(int64_t s, int64_t d) {
    uint32_t sp = (uint32_t)(uint64_t)s;
    uint32_t dp = (uint32_t)(uint64_t)d;
    uint32_t sa = (sp >> 24) & 0xFFu;
    if (sa == 255u) return (int64_t)(uint64_t)sp;          /* full src pixel */
    if (sa == 0u)   return (int64_t)(uint64_t)dp;          /* full dst pixel */
    uint32_t inv = 255u - sa;
    uint32_t da = (dp >> 24) & 0xFFu;
    uint32_t dst_weight = (da * inv) / 255u;
    uint32_t out_a = sa + dst_weight;
    uint32_t sr = (sp >> 16) & 0xFFu, sg = (sp >> 8) & 0xFFu, sb = sp & 0xFFu;
    uint32_t dr = (dp >> 16) & 0xFFu, dg = (dp >> 8) & 0xFFu, db = dp & 0xFFu;
    uint32_t r = (sr * sa + dr * dst_weight) / out_a;
    uint32_t g = (sg * sa + dg * dst_weight) / out_a;
    uint32_t b = (sb * sa + db * dst_weight) / out_a;
    uint32_t out = (out_a << 24) | (r << 16) | (g << 8) | b;
    return (int64_t)(uint64_t)out;
}

static int g_failures = 0;

static void fail(const char* what, long long extra) {
    if (g_failures < 20) {
        fprintf(stderr, "  MISMATCH: %s (%lld)\n", what, extra);
    }
    g_failures++;
}

/* -------------------------------------------------------------------------
 * Tests
 * ------------------------------------------------------------------------- */

static const int64_t kSizes[] = {0, 1, 2, 3, 4, 7, 8, 16, 17, 255, 256, 1000};
static const int kNumSizes = (int)(sizeof(kSizes) / sizeof(kSizes[0]));

static void test_fill(void) {
    /* a few distinct colors, including ones with high bits set */
    int64_t colors[] = {0x00000000LL, 0xFFFFFFFFLL, 0x12345678LL, 0xDEADBEEFLL};
    int nc = (int)(sizeof(colors) / sizeof(colors[0]));
    for (int si = 0; si < kNumSizes; si++) {
        int64_t n = kSizes[si];
        for (int ci = 0; ci < nc; ci++) {
            int64_t color = colors[ci];
            int64_t color_word = color & 0xffffffffLL;
            int64_t* out = (int64_t*)calloc((size_t)(n > 0 ? n : 1), sizeof(int64_t));
            /* poison */
            for (int64_t i = 0; i < n; i++) out[i] = 0x7777777777777777LL;
            engine2d_fill_into(out, n, color);
            for (int64_t i = 0; i < n; i++) {
                if (out[i] != color_word) { fail("fill value", (long long)(n * 100 + i)); }
            }
            free(out);
        }
    }
}

static void test_copy(void) {
    for (int si = 0; si < kNumSizes; si++) {
        int64_t n = kSizes[si];
        int64_t* src = (int64_t*)calloc((size_t)(n > 0 ? n : 1), sizeof(int64_t));
        int64_t* out = (int64_t*)calloc((size_t)(n > 0 ? n : 1), sizeof(int64_t));
        for (int64_t i = 0; i < n; i++) {
            /* deterministic pseudo-random 32-bit values */
            src[i] = (int64_t)(uint64_t)((uint32_t)(0x9E3779B9u * (uint32_t)(i + 1)));
            out[i] = 0x5555555555555555LL; /* poison */
        }
        engine2d_copy_into(out, src, n);
        if (n > 0 && memcmp(out, src, (size_t)n * sizeof(int64_t)) != 0) {
            for (int64_t i = 0; i < n; i++) {
                if (out[i] != src[i]) { fail("copy value", (long long)(n * 100 + i)); }
            }
        }
        free(src);
        free(out);
    }
}

/* Drive the vectorized engine2d_blend_into over the size list so both the
 * 2-pixel NEON body and the scalar tail are exercised, comparing each pixel
 * against the independent reference. */
static void test_blend_into(void) {
    for (int si = 0; si < kNumSizes; si++) {
        int64_t n = kSizes[si];
        int64_t* dst = (int64_t*)calloc((size_t)(n > 0 ? n : 1), sizeof(int64_t));
        int64_t* src = (int64_t*)calloc((size_t)(n > 0 ? n : 1), sizeof(int64_t));
        int64_t* out = (int64_t*)calloc((size_t)(n > 0 ? n : 1), sizeof(int64_t));
        for (int64_t i = 0; i < n; i++) {
            /* vary alpha across pixels including 0 and 255 boundary cases;
               destination alpha includes transparent and translucent pixels */
            uint32_t sa = (uint32_t)((i * 37) & 0xFF);
            uint32_t sr = (uint32_t)((i * 11) & 0xFF);
            uint32_t sg = (uint32_t)((i * 23) & 0xFF);
            uint32_t sb = (uint32_t)((i * 47) & 0xFF);
            uint32_t da = (uint32_t)((i * 3) & 0xFF);
            uint32_t dr = (uint32_t)((i * 17) & 0xFF);
            uint32_t dg = (uint32_t)((i * 29) & 0xFF);
            uint32_t db = (uint32_t)((i * 53) & 0xFF);
            src[i] = (int64_t)(uint64_t)((sa << 24) | (sr << 16) | (sg << 8) | sb);
            dst[i] = (int64_t)(uint64_t)((da << 24) | (dr << 16) | (dg << 8) | db);
            out[i] = 0x3333333333333333LL; /* poison */
        }
        /* Real kernel: engine2d_blend_into(out, dst, src, n). */
        engine2d_blend_into(out, dst, src, n);
        for (int64_t i = 0; i < n; i++) {
            int64_t want = ref_blend_pixel(src[i], dst[i]);
            if (out[i] != want) { fail("blend_into pixel", (long long)(n * 100 + i)); }
        }
        free(dst);
        free(src);
        free(out);
    }
}

/* Exhaustive scalar math: for every sa in 0..255 and every (s_ch, d_ch) pair
 * in one channel, assert engine2d_blend_pixel matches the floor formula.
 * 256 * 256 * 256 = 16.7M combinations. We drive the blue channel (lowest)
 * with R=G=0 so the per-channel math is isolated. */
static void test_blend_exhaustive(void) {
    for (int sa = 0; sa <= 255; sa++) {
        for (int sch = 0; sch <= 255; sch++) {
            uint32_t sp = ((uint32_t)sa << 24) | (uint32_t)sch; /* blue = sch */
            int64_t s = (int64_t)(uint64_t)sp;
            for (int dch = 0; dch <= 255; dch++) {
                uint32_t dp = (0xFFu << 24) | (uint32_t)dch;    /* dst alpha=255 */
                int64_t d = (int64_t)(uint64_t)dp;
                int64_t got = engine2d_blend_pixel(s, d);
                /* independent expectation */
                int64_t want;
                if (sa == 255) {
                    want = (int64_t)(uint64_t)sp;
                } else if (sa == 0) {
                    want = (int64_t)(uint64_t)dp;
                } else {
                    uint32_t inv = 255u - (uint32_t)sa;
                    uint32_t b = ((uint32_t)sch * (uint32_t)sa + (uint32_t)dch * inv) / 255u;
                    want = (int64_t)(uint64_t)((0xFFu << 24) | b);
                }
                if (got != want) {
                    fail("blend exhaustive", (long long)((sa << 16) | (sch << 8) | dch));
                    if (g_failures > 50) return; /* don't spew */
                }
            }
        }
    }
}

int main(void) {
#if defined(__aarch64__) || defined(_M_ARM64)
    fprintf(stderr, "ENGINE2D_SIMD_C_TEST: NEON path active (aarch64)\n");
#elif defined(__x86_64__) || defined(_M_X64)
    fprintf(stderr, "ENGINE2D_SIMD_C_TEST: x86_64 path (SSE2 fallback unless AVX2)\n");
#else
    fprintf(stderr, "ENGINE2D_SIMD_C_TEST: scalar path\n");
#endif

    test_fill();
    test_copy();
    test_blend_into();
    test_blend_exhaustive();

    if (g_failures == 0) {
        printf("ENGINE2D_SIMD_C_TEST: PASS\n");
        return 0;
    }
    printf("ENGINE2D_SIMD_C_TEST: FAIL (%d mismatches)\n", g_failures);
    return 1;
}
