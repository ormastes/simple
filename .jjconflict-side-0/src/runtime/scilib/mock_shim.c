/*
 * mock_shim.c — CPU-correct BLAS + LAPACK + cuda-mem stubs
 *
 * T-CUDA-02: implements all symbols declared in scilib_shim.h using plain
 * C (no CUDA dependency).  Interpreter-mode linalg specs run against this
 * backend so it MUST produce correct values for small N (AC-7).
 *
 * Row-major convention (OQ-C): A[i*lda + j] for row i, column j.
 * ipiv convention: 1-based pivot indices, matching LAPACK / cuSOLVER.
 */

#include "scilib_shim.h"

#include <math.h>     /* hypot, sqrt, fabs */
#include <stdlib.h>   /* malloc, free */
#include <string.h>   /* memcpy */

/* =========================================================================
 * Backend identification
 * ========================================================================= */

const char *rt_scilib_backend_name(void) { return "mock"; }
int         rt_scilib_is_real(void)      { return 0; }

/* =========================================================================
 * BLAS Level-1
 * ========================================================================= */

/* y[i*incy] += alpha * x[i*incx]  for i in [0, n) */
void rt_blas_daxpy(int64_t n,
                   double alpha,
                   const double *x, int64_t incx,
                   double *y,       int64_t incy)
{
    for (int64_t i = 0; i < n; ++i)
        y[i * incy] += alpha * x[i * incx];
}

/* sum( x[i*incx] * y[i*incy] ) */
double rt_blas_ddot(int64_t n,
                    const double *x, int64_t incx,
                    const double *y, int64_t incy)
{
    double s = 0.0;
    for (int64_t i = 0; i < n; ++i)
        s += x[i * incx] * y[i * incy];
    return s;
}

/* x[i*incx] *= alpha */
void rt_blas_dscal(int64_t n, double alpha, double *x, int64_t incx)
{
    for (int64_t i = 0; i < n; ++i)
        x[i * incx] *= alpha;
}

/* Returns 0-based index of element with max |x[i*incx]| */
int64_t rt_blas_idamax(int64_t n, const double *x, int64_t incx)
{
    if (n <= 0) return 0;
    int64_t best = 0;
    double  best_abs = fabs(x[0]);
    for (int64_t i = 1; i < n; ++i) {
        double a = fabs(x[i * incx]);
        if (a > best_abs) { best_abs = a; best = i; }
    }
    return best;
}

/* ||x||_2 via hypot to avoid intermediate overflow */
double rt_blas_dnrm2(int64_t n, const double *x, int64_t incx)
{
    double acc = 0.0;
    for (int64_t i = 0; i < n; ++i)
        acc = hypot(acc, x[i * incx]);
    return acc;
}

/* =========================================================================
 * BLAS Level-2
 * ========================================================================= */

/*
 * rt_blas_dgemv — y = alpha * op(A) * x + beta * y
 *
 * A is m×n row-major (stride lda).
 * trans=0: op(A)=A  (m×n), x has n elems, y has m elems
 * trans=1: op(A)=A^T (n×m), x has m elems, y has n elems
 */
void rt_blas_dgemv(int trans,
                   int64_t m, int64_t n,
                   double alpha,
                   const double *A, int64_t lda,
                   const double *x, int64_t incx,
                   double beta,
                   double *y,       int64_t incy)
{
    if (trans == 0) {
        /* y[i] = alpha * sum_j A[i*lda+j] * x[j*incx] + beta*y[i] */
        for (int64_t i = 0; i < m; ++i) {
            double s = 0.0;
            for (int64_t j = 0; j < n; ++j)
                s += A[i * lda + j] * x[j * incx];
            y[i * incy] = alpha * s + beta * y[i * incy];
        }
    } else {
        /* y[j] = alpha * sum_i A[i*lda+j] * x[i*incx] + beta*y[j] */
        for (int64_t j = 0; j < n; ++j) {
            double s = 0.0;
            for (int64_t i = 0; i < m; ++i)
                s += A[i * lda + j] * x[i * incx];
            y[j * incy] = alpha * s + beta * y[j * incy];
        }
    }
}

/* =========================================================================
 * BLAS Level-3
 * ========================================================================= */

/*
 * rt_blas_dgemm — C = alpha * op(A) * op(B) + beta * C
 *
 * Dimensions after applying trans flags:
 *   op(A) is m×k,  op(B) is k×n,  C is m×n (row-major, stride ldc)
 *
 * Row-major storage:
 *   trans=0: A stored as m×k (lda >= k), element (i,p) = A[i*lda+p]
 *   trans=1: A stored as k×m (lda >= m), element (i,p) of op(A) = A[p*lda+i]
 *   Same rule for B / trans_b, but dimensions are k×n (no-trans) / n×k (trans).
 */
void rt_blas_dgemm(int trans_a, int trans_b,
                   int64_t m, int64_t n, int64_t k,
                   double alpha,
                   const double *A, int64_t lda,
                   const double *B, int64_t ldb,
                   double beta,
                   double *C, int64_t ldc)
{
    for (int64_t i = 0; i < m; ++i) {
        for (int64_t j = 0; j < n; ++j) {
            double s = 0.0;
            for (int64_t p = 0; p < k; ++p) {
                double a_ip = trans_a ? A[p * lda + i] : A[i * lda + p];
                double b_pj = trans_b ? B[j * ldb + p] : B[p * ldb + j];
                s += a_ip * b_pj;
            }
            C[i * ldc + j] = alpha * s + beta * C[i * ldc + j];
        }
    }
}

/* =========================================================================
 * LAPACK helpers: LU factorization and solve
 * ========================================================================= */

/*
 * rt_lapack_dgetrf — in-place LU factorization with partial pivoting
 *
 * A (m×n, row-major lda) is overwritten with L (lower, unit diag) and U (upper).
 * ipiv[k] = 1-based row index that was swapped to row k (LAPACK convention).
 * *info = 0 on success; *info = k+1 (1-based) on first zero pivot at step k.
 */
void rt_lapack_dgetrf(int64_t m, int64_t n,
                      double *A, int64_t lda,
                      int64_t *ipiv,
                      int64_t *info)
{
    int64_t min_mn = (m < n) ? m : n;
    *info = 0;

    for (int64_t k = 0; k < min_mn; ++k) {
        /* Find pivot: row with max |A[r, k]| for r >= k */
        int64_t pivot_row = k;
        double  pivot_abs = fabs(A[k * lda + k]);
        for (int64_t r = k + 1; r < m; ++r) {
            double a = fabs(A[r * lda + k]);
            if (a > pivot_abs) { pivot_abs = a; pivot_row = r; }
        }
        ipiv[k] = pivot_row + 1;  /* store 1-based */

        /* Swap rows k and pivot_row */
        if (pivot_row != k) {
            for (int64_t j = 0; j < n; ++j) {
                double tmp          = A[k         * lda + j];
                A[k         * lda + j] = A[pivot_row * lda + j];
                A[pivot_row * lda + j] = tmp;
            }
        }

        /* Check for zero pivot */
        if (A[k * lda + k] == 0.0) {
            *info = k + 1;  /* 1-based position of first zero pivot */
            return;
        }

        /* Eliminate below diagonal in column k */
        double diag_inv = 1.0 / A[k * lda + k];
        for (int64_t i = k + 1; i < m; ++i) {
            A[i * lda + k] *= diag_inv;          /* multiplier → L */
            for (int64_t j = k + 1; j < n; ++j)
                A[i * lda + j] -= A[i * lda + k] * A[k * lda + j];
        }
    }
}

/*
 * rt_lapack_dgetrs — solve using a pre-factored LU from dgetrf
 *
 * trans=0: solve A*X = B,   trans=1: solve A^T*X = B
 * B is n×nrhs row-major (stride ldb); overwritten with X.
 * ipiv: 1-based pivot array from dgetrf.
 */
void rt_lapack_dgetrs(int trans,
                      int64_t n, int64_t nrhs,
                      const double *A, int64_t lda,
                      const int64_t *ipiv,
                      double *B, int64_t ldb,
                      int64_t *info)
{
    *info = 0;

    if (trans == 0) {
        /* --- Apply row permutations to B (P*B) --- */
        for (int64_t k = 0; k < n; ++k) {
            int64_t prow = ipiv[k] - 1;  /* convert to 0-based */
            if (prow != k) {
                for (int64_t j = 0; j < nrhs; ++j) {
                    double tmp      = B[k    * ldb + j];
                    B[k    * ldb + j] = B[prow * ldb + j];
                    B[prow * ldb + j] = tmp;
                }
            }
        }

        /* --- Forward substitution: solve L*Y = B (L is unit lower) --- */
        for (int64_t j = 0; j < nrhs; ++j) {
            for (int64_t i = 1; i < n; ++i) {
                for (int64_t p = 0; p < i; ++p)
                    B[i * ldb + j] -= A[i * lda + p] * B[p * ldb + j];
            }
        }

        /* --- Back substitution: solve U*X = Y --- */
        for (int64_t j = 0; j < nrhs; ++j) {
            for (int64_t i = n - 1; i >= 0; --i) {
                for (int64_t p = i + 1; p < n; ++p)
                    B[i * ldb + j] -= A[i * lda + p] * B[p * ldb + j];
                B[i * ldb + j] /= A[i * lda + i];
            }
        }
    } else {
        /* trans=1: solve A^T * X = B
         * Equivalent to: U^T * (L^T * (P^T * X)) = B
         * Steps: (1) solve U^T * Z = B, (2) solve L^T * W = Z, (3) X = P*W */

        /* (1) Forward substitution with U^T (unit diagonal of U) */
        for (int64_t j = 0; j < nrhs; ++j) {
            for (int64_t i = 0; i < n; ++i) {
                for (int64_t p = 0; p < i; ++p)
                    B[i * ldb + j] -= A[p * lda + i] * B[p * ldb + j];
                B[i * ldb + j] /= A[i * lda + i];
            }
        }

        /* (2) Back substitution with L^T (unit diag — no divide) */
        for (int64_t j = 0; j < nrhs; ++j) {
            for (int64_t i = n - 2; i >= 0; --i) {
                for (int64_t p = i + 1; p < n; ++p)
                    B[i * ldb + j] -= A[p * lda + i] * B[p * ldb + j];
            }
        }

        /* (3) Apply inverse permutation: P^T permutes columns, swap in reverse */
        for (int64_t k = n - 1; k >= 0; --k) {
            int64_t prow = ipiv[k] - 1;
            if (prow != k) {
                for (int64_t j = 0; j < nrhs; ++j) {
                    double tmp      = B[k    * ldb + j];
                    B[k    * ldb + j] = B[prow * ldb + j];
                    B[prow * ldb + j] = tmp;
                }
            }
        }
    }
}

/*
 * rt_lapack_dgesv — solve A*X = B (combines dgetrf + dgetrs)
 *
 * n×n A, n×nrhs B; both row-major.  A overwritten with LU; B overwritten with X.
 */
void rt_lapack_dgesv(int64_t n, int64_t nrhs,
                     double *A, int64_t lda,
                     int64_t *ipiv,
                     double *B, int64_t ldb,
                     int64_t *info)
{
    rt_lapack_dgetrf(n, n, A, lda, ipiv, info);
    if (*info != 0) return;
    rt_lapack_dgetrs(0, n, nrhs, A, lda, ipiv, B, ldb, info);
}

/* =========================================================================
 * CUDA memory helpers (mock: delegate to malloc / free / memcpy)
 * ========================================================================= */

int64_t rt_cuda_malloc(int64_t bytes)
{
    void *p = malloc((size_t)bytes);
    return (int64_t)p;   /* 0 (NULL) on failure */
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
