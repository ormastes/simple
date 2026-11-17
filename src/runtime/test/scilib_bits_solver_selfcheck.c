/*
 * Selfcheck for the shared bit-encoded LAPACK entry points
 * (rt_scilib_{cuda,openblas}_dgesv_bits, rt_scilib_openblas_dgetrf_bits)
 * through the host mock shim.
 *
 *   clang -O1 src/runtime/test/scilib_bits_solver_selfcheck.c -o sc -lm && ./sc
 */
#include "../scilib/mock_shim.c"

#include <stdio.h>

static int failures = 0;

static void expect_near(const char *what, double got, double want)
{
    if (fabs(got - want) > 1e-9) {
        printf("FAIL %s: got %.12g want %.12g\n", what, got, want);
        failures++;
    }
}

int main(void)
{
    /* A = [[2,1],[1,3]], b = [3,5] -> x = [0.8, 1.4] */
    double a[4] = {2.0, 1.0, 1.0, 3.0};
    double b[2] = {3.0, 5.0};
    int64_t a_bits[4], b_bits[2], out_bits[4], piv[2];
    for (int i = 0; i < 4; ++i) a_bits[i] = scilib_double_to_bits(a[i]);
    for (int i = 0; i < 2; ++i) b_bits[i] = scilib_double_to_bits(b[i]);
    int64_t params[2] = {2, 1};

    int64_t info = rt_scilib_cuda_dgesv_bits((int64_t)(uintptr_t)params,
        (int64_t)(uintptr_t)a_bits, (int64_t)(uintptr_t)b_bits, (int64_t)(uintptr_t)out_bits);
    if (info != 0) { printf("FAIL cuda dgesv info=%lld\n", (long long)info); failures++; }
    expect_near("cuda dgesv x0", scilib_bits_to_double(out_bits[0]), 0.8);
    expect_near("cuda dgesv x1", scilib_bits_to_double(out_bits[1]), 1.4);

    out_bits[0] = out_bits[1] = 0;
    info = rt_scilib_openblas_dgesv_bits((int64_t)(uintptr_t)params,
        (int64_t)(uintptr_t)a_bits, (int64_t)(uintptr_t)b_bits, (int64_t)(uintptr_t)out_bits);
    if (info != 0) { printf("FAIL openblas dgesv info=%lld\n", (long long)info); failures++; }
    expect_near("openblas dgesv x0", scilib_bits_to_double(out_bits[0]), 0.8);
    expect_near("openblas dgesv x1", scilib_bits_to_double(out_bits[1]), 1.4);

    /* dgetrf: L*U must reproduce P*A. With partial pivoting row 0 (|2|) stays. */
    info = rt_scilib_openblas_dgetrf_bits((int64_t)(uintptr_t)params,
        (int64_t)(uintptr_t)a_bits, (int64_t)(uintptr_t)out_bits, (int64_t)(uintptr_t)piv);
    if (info != 0) { printf("FAIL dgetrf info=%lld\n", (long long)info); failures++; }
    double lu[4];
    for (int i = 0; i < 4; ++i) lu[i] = scilib_bits_to_double(out_bits[i]);
    expect_near("dgetrf u00", lu[0], 2.0);
    expect_near("dgetrf u01", lu[1], 1.0);
    expect_near("dgetrf l10", lu[2], 0.5);
    expect_near("dgetrf u11", lu[3], 2.5);

    /* singular: info > 0 */
    double s[4] = {1.0, 2.0, 2.0, 4.0};
    for (int i = 0; i < 4; ++i) a_bits[i] = scilib_double_to_bits(s[i]);
    info = rt_scilib_cuda_dgesv_bits((int64_t)(uintptr_t)params,
        (int64_t)(uintptr_t)a_bits, (int64_t)(uintptr_t)b_bits, (int64_t)(uintptr_t)out_bits);
    if (info <= 0) { printf("FAIL singular dgesv info=%lld\n", (long long)info); failures++; }

    int64_t bad[2] = {-1, 1};
    if (rt_scilib_cuda_dgesv_bits((int64_t)(uintptr_t)bad, 0, 0, 0) != -1) {
        printf("FAIL negative n\n");
        failures++;
    }

    printf(failures ? "scilib bits solver selfcheck: FAIL (%d)\n"
                    : "scilib bits solver selfcheck: PASS%.0d\n", failures);
    return failures ? 1 : 0;
}
