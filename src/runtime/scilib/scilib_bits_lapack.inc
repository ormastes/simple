/*
 * scilib_bits_lapack.inc — bit-encoded LAPACK entry points shared by
 * mock_shim.c and openblas_shim.c.
 *
 * Textually included by a shim AFTER it defines the static helpers
 * scilib_bits_to_double / scilib_double_to_bits; it calls the shim's own
 * rt_lapack_dgetrf / rt_lapack_dgesv (declared in scilib_shim.h).
 */

int64_t rt_scilib_openblas_dgetrf_bits(int64_t params_addr,
                                       int64_t a_bits_addr,
                                       int64_t out_bits_addr,
                                       int64_t pivot_out_addr)
{
    const int64_t *params = (const int64_t *)(uintptr_t)params_addr;
    const int64_t *a_bits = (const int64_t *)(uintptr_t)a_bits_addr;
    int64_t *out_bits = (int64_t *)(uintptr_t)out_bits_addr;
    int64_t *pivot_out = (int64_t *)(uintptr_t)pivot_out_addr;
    int64_t n = params[0];
    if (n < 0) return -1;
    size_t a_count = (size_t)(n * n);
    double *a = (double *)malloc(sizeof(double) * a_count);
    int64_t *ipiv = (int64_t *)malloc(sizeof(int64_t) * (size_t)n);
    if (a == NULL || ipiv == NULL) {
        free(a);
        free(ipiv);
        return -1000;
    }
    for (size_t i = 0; i < a_count; ++i) a[i] = scilib_bits_to_double(a_bits[i]);
    int64_t info = 0;
    rt_lapack_dgetrf(n, n, a, n, ipiv, &info);
    if (info == 0) {
        for (size_t i = 0; i < a_count; ++i) out_bits[i] = scilib_double_to_bits(a[i]);
        for (int64_t i = 0; i < n; ++i) pivot_out[i] = ipiv[i];
    }
    free(a);
    free(ipiv);
    return info;
}

int64_t rt_scilib_cuda_dgesv_bits(int64_t params_addr,
                                  int64_t a_bits_addr,
                                  int64_t b_bits_addr,
                                  int64_t out_bits_addr)
{
    const int64_t *params = (const int64_t *)(uintptr_t)params_addr;
    const int64_t *a_bits = (const int64_t *)(uintptr_t)a_bits_addr;
    const int64_t *b_bits = (const int64_t *)(uintptr_t)b_bits_addr;
    int64_t *out_bits = (int64_t *)(uintptr_t)out_bits_addr;
    int64_t n = params[0];
    int64_t nrhs = params[1];
    if (n < 0 || nrhs < 0) return -1;
    size_t a_count = (size_t)(n * n);
    size_t b_count = (size_t)(n * nrhs);
    double *a = (double *)malloc(sizeof(double) * a_count);
    double *b = (double *)malloc(sizeof(double) * b_count);
    int64_t *ipiv = (int64_t *)malloc(sizeof(int64_t) * (size_t)n);
    if (a == NULL || b == NULL || ipiv == NULL) {
        free(a);
        free(b);
        free(ipiv);
        return -1000;
    }
    for (size_t i = 0; i < a_count; ++i) a[i] = scilib_bits_to_double(a_bits[i]);
    for (size_t i = 0; i < b_count; ++i) b[i] = scilib_bits_to_double(b_bits[i]);
    int64_t info = 0;
    rt_lapack_dgesv(n, nrhs, a, n, ipiv, b, nrhs, &info);
    if (info == 0) {
        for (size_t i = 0; i < b_count; ++i) out_bits[i] = scilib_double_to_bits(b[i]);
    }
    free(a);
    free(b);
    free(ipiv);
    return info;
}

int64_t rt_scilib_openblas_dgesv_bits(int64_t params_addr,
                                      int64_t a_bits_addr,
                                      int64_t b_bits_addr,
                                      int64_t out_bits_addr)
{
    return rt_scilib_cuda_dgesv_bits(params_addr, a_bits_addr, b_bits_addr, out_bits_addr);
}
