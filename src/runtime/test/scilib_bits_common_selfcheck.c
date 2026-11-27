/*
 * Characterization selfcheck for scilib_bits_common.h, the helpers shared by
 * mock_shim.c and openblas_shim.c: the double <-> int64 bit codecs, the
 * rt_scilib_openblas_{ddot,dgemm,dgemv}_bits delegation to the shim's own
 * rt_scilib_cuda_* twins, and the host-memory rt_cuda_* stubs.
 *
 *   clang -O1 src/runtime/test/scilib_bits_common_selfcheck.c -o sc -lm && ./sc
 */
#include "../scilib/mock_shim.c"

#include <stdio.h>

static int failures = 0;

static void expect_near(const char *what, double got, double want)
{
    if (fabs(got - want) > 1e-12) {
        printf("FAIL %s: got %.17g want %.17g\n", what, got, want);
        failures++;
    }
}

static void expect_i64(const char *what, int64_t got, int64_t want)
{
    if (got != want) {
        printf("FAIL %s: got %lld want %lld\n", what, (long long)got, (long long)want);
        failures++;
    }
}

#define ADDR(p) ((int64_t)(uintptr_t)(p))

int main(void)
{
    /* Bit codecs round-trip exactly, including the sign of zero and NaN payload. */
    const double samples[] = {0.0, -0.0, 1.0, -2.5, 1e300, 5e-324, 0.1};
    for (size_t i = 0; i < sizeof(samples) / sizeof(samples[0]); ++i) {
        int64_t bits = scilib_double_to_bits(samples[i]);
        double back = scilib_bits_to_double(bits);
        if (memcmp(&back, &samples[i], sizeof(double)) != 0) {
            printf("FAIL bits round-trip for sample %zu\n", i);
            failures++;
        }
    }
    expect_i64("double_to_bits(1.0)", scilib_double_to_bits(1.0), INT64_C(0x3ff0000000000000));

    /* ddot: openblas entry delegates to the cuda twin -> identical bits. */
    double x[3] = {1.0, 2.0, 3.0}, y[3] = {4.0, 5.0, 6.0};
    int64_t xb[3], yb[3];
    for (int i = 0; i < 3; ++i) { xb[i] = scilib_double_to_bits(x[i]); yb[i] = scilib_double_to_bits(y[i]); }
    int64_t cuda_dot = rt_scilib_cuda_ddot_bits(ADDR(xb), 3, ADDR(yb));
    int64_t ob_dot = rt_scilib_openblas_ddot_bits(ADDR(xb), 3, ADDR(yb));
    expect_near("cuda ddot", scilib_bits_to_double(cuda_dot), 32.0);
    expect_i64("openblas ddot == cuda ddot", ob_dot, cuda_dot);

    /* dgemm: C = alpha*A*B + beta*C with A 2x2, B 2x2. */
    double a[4] = {1.0, 2.0, 3.0, 4.0}, b[4] = {5.0, 6.0, 7.0, 8.0}, c[4] = {1.0, 1.0, 1.0, 1.0};
    int64_t ab[4], bb[4], cb[4], out_cuda[4], out_ob[4];
    for (int i = 0; i < 4; ++i) {
        ab[i] = scilib_double_to_bits(a[i]); bb[i] = scilib_double_to_bits(b[i]);
        cb[i] = scilib_double_to_bits(c[i]);
    }
    int64_t gemm_params[5] = {2, 2, 2, scilib_double_to_bits(2.0), scilib_double_to_bits(0.5)};
    expect_i64("cuda dgemm rc", rt_scilib_cuda_dgemm_bits(ADDR(gemm_params), ADDR(ab), ADDR(bb), ADDR(cb), ADDR(out_cuda)), 1);
    expect_i64("openblas dgemm rc", rt_scilib_openblas_dgemm_bits(ADDR(gemm_params), ADDR(ab), ADDR(bb), ADDR(cb), ADDR(out_ob)), 1);
    /* 2*[19 22; 43 50] + 0.5*1 */
    expect_near("dgemm c00", scilib_bits_to_double(out_cuda[0]), 38.5);
    expect_near("dgemm c01", scilib_bits_to_double(out_cuda[1]), 44.5);
    expect_near("dgemm c10", scilib_bits_to_double(out_cuda[2]), 86.5);
    expect_near("dgemm c11", scilib_bits_to_double(out_cuda[3]), 100.5);
    for (int i = 0; i < 4; ++i) expect_i64("openblas dgemm == cuda dgemm", out_ob[i], out_cuda[i]);
    int64_t bad_gemm[5] = {-1, 2, 2, 0, 0};
    expect_i64("dgemm negative dim rejected", rt_scilib_openblas_dgemm_bits(ADDR(bad_gemm), ADDR(ab), ADDR(bb), ADDR(cb), ADDR(out_ob)), 0);

    /* dgemv: y = alpha*A*x + beta*y, A 2x2. */
    double xv[2] = {1.0, 1.0}, yv[2] = {10.0, 20.0};
    int64_t xvb[2], yvb[2], gv_cuda[2], gv_ob[2];
    for (int i = 0; i < 2; ++i) { xvb[i] = scilib_double_to_bits(xv[i]); yvb[i] = scilib_double_to_bits(yv[i]); }
    int64_t gemv_params[4] = {2, 2, scilib_double_to_bits(1.0), scilib_double_to_bits(0.0)};
    expect_i64("cuda dgemv rc", rt_scilib_cuda_dgemv_bits(ADDR(gemv_params), ADDR(ab), ADDR(xvb), ADDR(yvb), ADDR(gv_cuda)), 1);
    expect_i64("openblas dgemv rc", rt_scilib_openblas_dgemv_bits(ADDR(gemv_params), ADDR(ab), ADDR(xvb), ADDR(yvb), ADDR(gv_ob)), 1);
    expect_near("dgemv y0", scilib_bits_to_double(gv_cuda[0]), 3.0);
    expect_near("dgemv y1", scilib_bits_to_double(gv_cuda[1]), 7.0);
    for (int i = 0; i < 2; ++i) expect_i64("openblas dgemv == cuda dgemv", gv_ob[i], gv_cuda[i]);

    /* Host-memory cuda stubs: a round trip through "device" memory is a copy. */
    int64_t dev = rt_cuda_malloc(sizeof(double) * 3);
    if (dev == 0) { printf("FAIL rt_cuda_malloc returned 0\n"); failures++; }
    else {
        double back[3] = {0, 0, 0};
        rt_cuda_memcpy_htod(dev, x, sizeof(double) * 3);
        rt_cuda_memcpy_dtoh(back, dev, sizeof(double) * 3);
        for (int i = 0; i < 3; ++i) expect_near("cuda memcpy round trip", back[i], x[i]);
        rt_cuda_free(dev);
    }
    rt_cuda_free(0); /* free(NULL) is a no-op */

    printf("scilib bits common selfcheck: %s\n", failures == 0 ? "PASS" : "FAIL");
    return failures == 0 ? 0 : 1;
}
