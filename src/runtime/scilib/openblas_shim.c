/*
 * openblas_shim.c — OpenBLAS/LAPACKE host backend for Simple scilib.
 *
 * The real path is enabled only when both cblas.h and lapacke.h are available
 * at compile time. CPU-only developer machines without those headers still get
 * a buildable unavailable backend that reuses the scalar mock implementation
 * and identifies itself as non-real through rt_scilib_is_real().
 */

#include "scilib_shim.h"

#include <stdint.h>
#include <string.h>

#ifndef __has_include
#define __has_include(x) 0
#endif

#if __has_include(<cblas.h>) && __has_include(<lapacke.h>)
#define SIMPLE_SCILIB_HAVE_OPENBLAS 1
#include <cblas.h>
#include <lapacke.h>
#include <stdlib.h>
#include <string.h>
#else
#define SIMPLE_SCILIB_HAVE_OPENBLAS 0
#endif

#if SIMPLE_SCILIB_HAVE_OPENBLAS

const char *rt_scilib_backend_name(void) { return "openblas"; }
int rt_scilib_is_real(void) { return 1; }
int64_t rt_scilib_cuda_available(void) { return 0; }
int64_t rt_scilib_openblas_available(void) { return 1; }

static int64_t scilib_double_to_bits(double value)
{
    int64_t bits = 0;
    memcpy(&bits, &value, sizeof(bits));
    return bits;
}

static double scilib_bits_to_double(int64_t bits)
{
    double value = 0.0;
    memcpy(&value, &bits, sizeof(value));
    return value;
}

static CBLAS_TRANSPOSE scilib_transpose(int trans)
{
    if (trans == 1) return CblasTrans;
    if (trans == 2) return CblasConjTrans;
    return CblasNoTrans;
}

void rt_blas_daxpy(int64_t n,
                   double alpha,
                   const double *x, int64_t incx,
                   double *y, int64_t incy)
{
    cblas_daxpy((int)n, alpha, x, (int)incx, y, (int)incy);
}

double rt_blas_ddot(int64_t n,
                    const double *x, int64_t incx,
                    const double *y, int64_t incy)
{
    return cblas_ddot((int)n, x, (int)incx, y, (int)incy);
}

int64_t rt_scilib_cuda_ddot_bits(int64_t x_bits_addr,
                                 int64_t n,
                                 int64_t y_bits_addr)
{
    const int64_t *x_bits = (const int64_t *)(uintptr_t)x_bits_addr;
    const int64_t *y_bits = (const int64_t *)(uintptr_t)y_bits_addr;
    double *x = (double *)malloc(sizeof(double) * (size_t)n);
    double *y = (double *)malloc(sizeof(double) * (size_t)n);
    if (x == NULL || y == NULL) {
        free(x);
        free(y);
        return scilib_double_to_bits(0.0);
    }
    for (int64_t i = 0; i < n; ++i) {
        x[i] = scilib_bits_to_double(x_bits[i]);
        y[i] = scilib_bits_to_double(y_bits[i]);
    }
    double result = rt_blas_ddot(n, x, 1, y, 1);
    free(x);
    free(y);
    return scilib_double_to_bits(result);
}

int64_t rt_scilib_cuda_dgemm_bits(int64_t params_addr,
                                  int64_t a_bits_addr,
                                  int64_t b_bits_addr,
                                  int64_t c_bits_addr,
                                  int64_t out_bits_addr)
{
    const int64_t *params = (const int64_t *)(uintptr_t)params_addr;
    const int64_t *a_bits = (const int64_t *)(uintptr_t)a_bits_addr;
    const int64_t *b_bits = (const int64_t *)(uintptr_t)b_bits_addr;
    const int64_t *c_bits = (const int64_t *)(uintptr_t)c_bits_addr;
    int64_t *out_bits = (int64_t *)(uintptr_t)out_bits_addr;
    int64_t m = params[0];
    int64_t n = params[1];
    int64_t k = params[2];
    int64_t alpha_bits = params[3];
    int64_t beta_bits = params[4];
    if (m < 0 || n < 0 || k < 0) return 0;
    size_t a_count = (size_t)(m * k);
    size_t b_count = (size_t)(k * n);
    size_t c_count = (size_t)(m * n);
    double *a = (double *)malloc(sizeof(double) * a_count);
    double *b = (double *)malloc(sizeof(double) * b_count);
    double *c = (double *)malloc(sizeof(double) * c_count);
    if (a == NULL || b == NULL || c == NULL) {
        free(a);
        free(b);
        free(c);
        return 0;
    }
    for (size_t i = 0; i < a_count; ++i) a[i] = scilib_bits_to_double(a_bits[i]);
    for (size_t i = 0; i < b_count; ++i) b[i] = scilib_bits_to_double(b_bits[i]);
    for (size_t i = 0; i < c_count; ++i) c[i] = scilib_bits_to_double(c_bits[i]);
    rt_blas_dgemm(0, 0, m, n, k,
                  scilib_bits_to_double(alpha_bits), a, k, b, n,
                  scilib_bits_to_double(beta_bits), c, n);
    for (size_t i = 0; i < c_count; ++i) out_bits[i] = scilib_double_to_bits(c[i]);
    free(a);
    free(b);
    free(c);
    return 1;
}

int64_t rt_scilib_cuda_dgemv_bits(int64_t params_addr,
                                  int64_t a_bits_addr,
                                  int64_t x_bits_addr,
                                  int64_t y_bits_addr,
                                  int64_t out_bits_addr)
{
    const int64_t *params = (const int64_t *)(uintptr_t)params_addr;
    const int64_t *a_bits = (const int64_t *)(uintptr_t)a_bits_addr;
    const int64_t *x_bits = (const int64_t *)(uintptr_t)x_bits_addr;
    const int64_t *y_bits = (const int64_t *)(uintptr_t)y_bits_addr;
    int64_t *out_bits = (int64_t *)(uintptr_t)out_bits_addr;
    int64_t m = params[0];
    int64_t n = params[1];
    double alpha = scilib_bits_to_double(params[2]);
    double beta = scilib_bits_to_double(params[3]);
    if (m < 0 || n < 0) return 0;
    size_t a_count = (size_t)(m * n);
    double *a = (double *)malloc(sizeof(double) * a_count);
    double *x = (double *)malloc(sizeof(double) * (size_t)n);
    double *y = (double *)malloc(sizeof(double) * (size_t)m);
    if (a == NULL || x == NULL || y == NULL) {
        free(a);
        free(x);
        free(y);
        return 0;
    }
    for (size_t i = 0; i < a_count; ++i) a[i] = scilib_bits_to_double(a_bits[i]);
    for (int64_t i = 0; i < n; ++i) x[i] = scilib_bits_to_double(x_bits[i]);
    for (int64_t i = 0; i < m; ++i) y[i] = scilib_bits_to_double(y_bits[i]);
    rt_blas_dgemv(0, m, n, alpha, a, n, x, 1, beta, y, 1);
    for (int64_t i = 0; i < m; ++i) out_bits[i] = scilib_double_to_bits(y[i]);
    free(a);
    free(x);
    free(y);
    return 1;
}

int64_t rt_scilib_openblas_ddot_bits(int64_t x_bits_addr,
                                     int64_t n,
                                     int64_t y_bits_addr)
{
    return rt_scilib_cuda_ddot_bits(x_bits_addr, n, y_bits_addr);
}

int64_t rt_scilib_openblas_daxpy_bits(int64_t params_addr,
                                      int64_t x_bits_addr,
                                      int64_t y_bits_addr,
                                      int64_t out_bits_addr)
{
    const int64_t *params = (const int64_t *)(uintptr_t)params_addr;
    const int64_t *x_bits = (const int64_t *)(uintptr_t)x_bits_addr;
    const int64_t *y_bits = (const int64_t *)(uintptr_t)y_bits_addr;
    int64_t *out_bits = (int64_t *)(uintptr_t)out_bits_addr;
    int64_t n = params[0];
    double alpha = scilib_bits_to_double(params[1]);
    if (n < 0) return 0;
    double *x = (double *)malloc(sizeof(double) * (size_t)n);
    double *out = (double *)malloc(sizeof(double) * (size_t)n);
    if (x == NULL || out == NULL) {
        free(x);
        free(out);
        return 0;
    }
    for (int64_t i = 0; i < n; ++i) {
        x[i] = scilib_bits_to_double(x_bits[i]);
        out[i] = scilib_bits_to_double(y_bits[i]);
    }
    rt_blas_daxpy(n, alpha, x, 1, out, 1);
    for (int64_t i = 0; i < n; ++i) out_bits[i] = scilib_double_to_bits(out[i]);
    free(x);
    free(out);
    return 1;
}

int64_t rt_scilib_openblas_dgemm_bits(int64_t params_addr,
                                      int64_t a_bits_addr,
                                      int64_t b_bits_addr,
                                      int64_t c_bits_addr,
                                      int64_t out_bits_addr)
{
    return rt_scilib_cuda_dgemm_bits(params_addr, a_bits_addr, b_bits_addr,
                                     c_bits_addr, out_bits_addr);
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

void rt_blas_dscal(int64_t n, double alpha, double *x, int64_t incx)
{
    cblas_dscal((int)n, alpha, x, (int)incx);
}

int64_t rt_blas_idamax(int64_t n, const double *x, int64_t incx)
{
    return (int64_t)cblas_idamax((int)n, x, (int)incx);
}

double rt_blas_dnrm2(int64_t n, const double *x, int64_t incx)
{
    return cblas_dnrm2((int)n, x, (int)incx);
}

void rt_blas_dgemv(int trans,
                   int64_t m, int64_t n,
                   double alpha,
                   const double *A, int64_t lda,
                   const double *x, int64_t incx,
                   double beta,
                   double *y, int64_t incy)
{
    cblas_dgemv(CblasRowMajor, scilib_transpose(trans), (int)m, (int)n,
                alpha, A, (int)lda, x, (int)incx, beta, y, (int)incy);
}

void rt_blas_dgemm(int trans_a, int trans_b,
                   int64_t m, int64_t n, int64_t k,
                   double alpha,
                   const double *A, int64_t lda,
                   const double *B, int64_t ldb,
                   double beta,
                   double *C, int64_t ldc)
{
    cblas_dgemm(CblasRowMajor, scilib_transpose(trans_a), scilib_transpose(trans_b),
                (int)m, (int)n, (int)k, alpha, A, (int)lda, B, (int)ldb,
                beta, C, (int)ldc);
}

static lapack_int *copy_pivots_to_lapack(const int64_t *src, int64_t n)
{
    lapack_int *out = (lapack_int *)malloc(sizeof(lapack_int) * (size_t)n);
    if (out == NULL) return NULL;
    for (int64_t i = 0; i < n; ++i) out[i] = (lapack_int)src[i];
    return out;
}

static void copy_pivots_from_lapack(int64_t *dst, const lapack_int *src, int64_t n)
{
    for (int64_t i = 0; i < n; ++i) dst[i] = (int64_t)src[i];
}

void rt_lapack_dgetrf(int64_t m, int64_t n,
                      double *A, int64_t lda,
                      int64_t *ipiv,
                      int64_t *info)
{
    int64_t min_mn = (m < n) ? m : n;
    lapack_int *piv = (lapack_int *)malloc(sizeof(lapack_int) * (size_t)min_mn);
    if (piv == NULL) {
        *info = -1000;
        return;
    }
    *info = (int64_t)LAPACKE_dgetrf(LAPACK_ROW_MAJOR, (lapack_int)m,
                                    (lapack_int)n, A, (lapack_int)lda, piv);
    copy_pivots_from_lapack(ipiv, piv, min_mn);
    free(piv);
}

void rt_lapack_dgetrs(int trans,
                      int64_t n, int64_t nrhs,
                      const double *A, int64_t lda,
                      const int64_t *ipiv,
                      double *B, int64_t ldb,
                      int64_t *info)
{
    lapack_int *piv = copy_pivots_to_lapack(ipiv, n);
    if (piv == NULL) {
        *info = -1000;
        return;
    }
    *info = (int64_t)LAPACKE_dgetrs(LAPACK_ROW_MAJOR,
                                    trans == 0 ? 'N' : 'T',
                                    (lapack_int)n, (lapack_int)nrhs, A,
                                    (lapack_int)lda, piv, B, (lapack_int)ldb);
    free(piv);
}

void rt_lapack_dgesv(int64_t n, int64_t nrhs,
                     double *A, int64_t lda,
                     int64_t *ipiv,
                     double *B, int64_t ldb,
                     int64_t *info)
{
    lapack_int *piv = (lapack_int *)malloc(sizeof(lapack_int) * (size_t)n);
    if (piv == NULL) {
        *info = -1000;
        return;
    }
    *info = (int64_t)LAPACKE_dgesv(LAPACK_ROW_MAJOR, (lapack_int)n,
                                   (lapack_int)nrhs, A, (lapack_int)lda,
                                   piv, B, (lapack_int)ldb);
    copy_pivots_from_lapack(ipiv, piv, n);
    free(piv);
}

int64_t rt_cuda_malloc(int64_t bytes)
{
    return (int64_t)malloc((size_t)bytes);
}

void rt_cuda_free(int64_t dev_ptr)
{
    free((void *)dev_ptr);
}

void rt_cuda_memcpy_htod(int64_t dev_dst, const void *host_src, int64_t bytes)
{
    memcpy((void *)dev_dst, host_src, (size_t)bytes);
}

void rt_cuda_memcpy_dtoh(void *host_dst, int64_t dev_src, int64_t bytes)
{
    memcpy(host_dst, (void *)dev_src, (size_t)bytes);
}

#else

#define rt_scilib_backend_name scilib_openblas_fallback_mock_backend_name
#define rt_scilib_is_real scilib_openblas_fallback_mock_is_real
#include "mock_shim.c"
#undef rt_scilib_backend_name
#undef rt_scilib_is_real

const char *rt_scilib_backend_name(void) { return "openblas-unavailable"; }
int rt_scilib_is_real(void) { return 0; }

#endif
