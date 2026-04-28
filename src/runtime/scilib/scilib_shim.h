#ifndef SCILIB_SHIM_H
#define SCILIB_SHIM_H

#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/* === BLAS ===
 *
 * All dimension and stride parameters use int64_t for cuBLAS _64 API parity
 * (cublasDgemm_64, cublasDgemv_64, etc., require 64-bit indices).
 * trans_a / trans_b / trans flags are plain int (0=no-trans, 1=trans).
 *
 * Row-major vs column-major: callers pass row-major arrays; the cublas_shim
 * implementation swaps operands via the (AB)^T = B^T A^T identity to satisfy
 * cuBLAS's column-major convention (OQ-C).
 */

/* Multiply: C = alpha * op(A) * op(B) + beta * C
 * trans_a, trans_b: 0=no-trans, 1=trans */
void rt_blas_dgemm(int trans_a, int trans_b,
                   int64_t m, int64_t n, int64_t k,
                   double alpha,
                   const double *A, int64_t lda,
                   const double *B, int64_t ldb,
                   double beta,
                   double *C, int64_t ldc);

/* Matrix-vector: y = alpha * op(A) * x + beta * y
 * trans: 0=no-trans, 1=trans */
void rt_blas_dgemv(int trans,
                   int64_t m, int64_t n,
                   double alpha,
                   const double *A, int64_t lda,
                   const double *x, int64_t incx,
                   double beta,
                   double *y, int64_t incy);

/* Vector add: y = alpha * x + y */
void rt_blas_daxpy(int64_t n,
                   double alpha,
                   const double *x, int64_t incx,
                   double *y, int64_t incy);

/* Dot product: returns x . y */
double rt_blas_ddot(int64_t n,
                    const double *x, int64_t incx,
                    const double *y, int64_t incy);

/* Scale: x = alpha * x */
void rt_blas_dscal(int64_t n, double alpha, double *x, int64_t incx);

/* Index of max absolute value — returns 0-based index.
 * NOTE: cuBLAS cublasIdamax_64 returns a 1-based (Fortran-heritage) index;
 * cublas_shim.c subtracts 1 before returning so callers always get 0-based. */
int64_t rt_blas_idamax(int64_t n, const double *x, int64_t incx);

/* Euclidean norm: returns ||x||_2 */
double rt_blas_dnrm2(int64_t n, const double *x, int64_t incx);

/* === LAPACK ===
 *
 * Solve and factorize routines. ipiv arrays hold int64_t pivot indices.
 * info is an output parameter: 0 = success, >0 = singular / error.
 * trans flag: 0=no-trans, 1=trans (same convention as BLAS above).
 */

/* Solve A*X = B using LU factorization (combines getrf + getrs).
 * On return A is overwritten by the LU factors; ipiv holds row permutations. */
void rt_lapack_dgesv(int64_t n, int64_t nrhs,
                     double *A, int64_t lda,
                     int64_t *ipiv,
                     double *B, int64_t ldb,
                     int64_t *info);

/* LU factorization: A = P * L * U
 * On return A is overwritten; ipiv holds pivot row indices. */
void rt_lapack_dgetrf(int64_t m, int64_t n,
                      double *A, int64_t lda,
                      int64_t *ipiv,
                      int64_t *info);

/* Solve using a pre-factored LU from dgetrf.
 * trans: 0 = solve A*X=B, 1 = solve A^T*X=B */
void rt_lapack_dgetrs(int trans,
                      int64_t n, int64_t nrhs,
                      const double *A, int64_t lda,
                      const int64_t *ipiv,
                      double *B, int64_t ldb,
                      int64_t *info);

/* === CUDA memory helpers ===
 *
 * Device pointers are returned / accepted as opaque int64_t handles.
 * They are NOT host-deref'able — never cast the returned value to a C pointer
 * on the host side. Pass them back to rt_cuda_memcpy_dtoh / rt_cuda_free.
 *
 * mock_shim.c implements these as malloc/free/memcpy so interpreter-mode
 * tests remain green on non-GPU hosts (OQ-D / AC-7).
 */

/* Allocate `bytes` on the device. Returns opaque device handle, or 0 on error. */
int64_t rt_cuda_malloc(int64_t bytes);

/* Free a device allocation previously returned by rt_cuda_malloc. */
void rt_cuda_free(int64_t dev_ptr);

/* Copy `bytes` bytes from host buffer host_src to device address dev_dst. */
void rt_cuda_memcpy_htod(int64_t dev_dst, const void *host_src, int64_t bytes);

/* Copy `bytes` bytes from device address dev_src to host buffer host_dst. */
void rt_cuda_memcpy_dtoh(void *host_dst, int64_t dev_src, int64_t bytes);

/* === Backend identification ===
 *
 * rt_scilib_backend_name: human-readable string e.g. "mock", "cublas", "cusolver"
 * rt_scilib_is_real: 0 = mock (CPU), 1 = real GPU backend (cublas or cusolver)
 */
const char *rt_scilib_backend_name(void);
int rt_scilib_is_real(void);

#ifdef __cplusplus
}
#endif

#endif /* SCILIB_SHIM_H */
