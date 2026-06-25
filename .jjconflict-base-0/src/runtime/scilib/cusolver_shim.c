/* cusolver_shim.c — Real cuSOLVER LAPACK backend for Simple scilib
 *
 * Exports: rt_lapack_dgesv, rt_lapack_dgetrf, rt_lapack_dgetrs
 *          rt_cuda_malloc, rt_cuda_free, rt_cuda_memcpy_htod, rt_cuda_memcpy_dtoh
 *          rt_scilib_backend_name, rt_scilib_is_real
 *
 * Column-major convention (v1):
 *   cuSOLVER is column-major (Fortran-heritage). Callers of rt_lapack_* must
 *   pass data in column-major layout. No automatic transposition is performed
 *   here (contrast with cublas_shim which does OQ-C operand-swap for gemm).
 *
 * ipiv ABI:
 *   The shim ABI uses int64_t* for ipiv (opaque device handle from Simple's
 *   view). The device buffer behind that handle must be sized as
 *   n * sizeof(int) bytes — NOT n * sizeof(int64_t). This is a contract the
 *   Simple-side dispatch layer (rt_lapack_dgetrf/dgetrs callers) must respect.
 *
 * T-CUDA-06
 */

#include "scilib_shim.h"
#include <cusolverDn.h>
#include <cuda_runtime.h>
#include <limits.h>
#include <stddef.h>
#include <stdlib.h>

/* -----------------------------------------------------------------------
 * Singleton handle
 * ----------------------------------------------------------------------- */

static cusolverDnHandle_t g_handle = NULL;

static cusolverDnHandle_t get_handle(void) {
    if (!g_handle) {
        cusolverDnCreate(&g_handle);
    }
    return g_handle;
}

/* -----------------------------------------------------------------------
 * CUDA memory helpers
 * ----------------------------------------------------------------------- */

int64_t rt_cuda_malloc(int64_t bytes) {
    void *ptr = NULL;
    cudaError_t err = cudaMalloc(&ptr, (size_t)bytes);
    if (err != cudaSuccess) return 0;
    return (int64_t)(uintptr_t)ptr;
}

void rt_cuda_free(int64_t dev_ptr) {
    if (dev_ptr) {
        cudaFree((void *)(uintptr_t)dev_ptr);
    }
}

void rt_cuda_memcpy_htod(int64_t dev_dst, const void *host_src, int64_t bytes) {
    cudaMemcpy((void *)(uintptr_t)dev_dst, host_src,
               (size_t)bytes, cudaMemcpyHostToDevice);
}

void rt_cuda_memcpy_dtoh(void *host_dst, int64_t dev_src, int64_t bytes) {
    cudaMemcpy(host_dst, (const void *)(uintptr_t)dev_src,
               (size_t)bytes, cudaMemcpyDeviceToHost);
}

/* -----------------------------------------------------------------------
 * LAPACK: dgetrf — LU factorization A = P * L * U
 *
 * A    (device): m×n matrix, column-major, overwritten with LU factors
 * lda  : leading dimension of A (>= m)
 * ipiv (device): caller-allocated buffer of n * sizeof(int) bytes; holds
 *                pivot indices (1-based, cuSOLVER convention)
 * info (host):   output — 0 on success, >0 if A is singular at info-th pivot
 * ----------------------------------------------------------------------- */

void rt_lapack_dgetrf(int64_t m, int64_t n,
                      double *A, int64_t lda,
                      int64_t *ipiv,
                      int64_t *info) {
    *info = 0;

    /* Bounds guard — cuSOLVER uses int */
    if (m > INT_MAX || n > INT_MAX || lda > INT_MAX) { *info = -1; return; }
    int im  = (int)m;
    int in  = (int)n;
    int ild = (int)lda;

    cusolverDnHandle_t h = get_handle();

    /* Query workspace size (Lwork is element count, not bytes) */
    int Lwork = 0;
    cusolverStatus_t st = cusolverDnDgetrf_bufferSize(h, im, in, A, ild, &Lwork);
    if (st != CUSOLVER_STATUS_SUCCESS) { *info = -(int64_t)st; return; }

    /* Allocate workspace */
    double *workspace = NULL;
    cudaError_t cerr = cudaMalloc((void **)&workspace, (size_t)Lwork * sizeof(double));
    if (cerr != cudaSuccess) { *info = -1; return; }

    /* Device info scalar */
    int *devInfo = NULL;
    cerr = cudaMalloc((void **)&devInfo, sizeof(int));
    if (cerr != cudaSuccess) { cudaFree(workspace); *info = -1; return; }

    /* LU factorize — ipiv is int* device buffer (sized n * sizeof(int)) */
    st = cusolverDnDgetrf(h, im, in, A, ild, workspace, (int *)ipiv, devInfo);

    /* Copy devInfo back to host */
    int host_info = 0;
    cudaMemcpy(&host_info, devInfo, sizeof(int), cudaMemcpyDeviceToHost);
    cudaDeviceSynchronize();

    cudaFree(workspace);
    cudaFree(devInfo);

    if (st != CUSOLVER_STATUS_SUCCESS) { *info = -(int64_t)st; return; }
    *info = (int64_t)host_info;
}

/* -----------------------------------------------------------------------
 * LAPACK: dgetrs — Solve A*X = B using pre-factored LU from dgetrf
 *
 * trans (0=no-trans, 1=trans): whether to solve A*X=B or A^T*X=B
 * A    (device): m×n LU-factored matrix from dgetrf (column-major)
 * ipiv (device): pivot indices from dgetrf (int* buffer)
 * B    (device): n×nrhs right-hand side, overwritten with solution X
 * info (host):   0 on success
 * ----------------------------------------------------------------------- */

void rt_lapack_dgetrs(int trans,
                      int64_t n, int64_t nrhs,
                      const double *A, int64_t lda,
                      const int64_t *ipiv,
                      double *B, int64_t ldb,
                      int64_t *info) {
    *info = 0;

    if (n > INT_MAX || nrhs > INT_MAX || lda > INT_MAX || ldb > INT_MAX) {
        *info = -1; return;
    }
    int in    = (int)n;
    int inrhs = (int)nrhs;
    int ild   = (int)lda;
    int ildb  = (int)ldb;

    cublasOperation_t op = (trans == 0) ? CUBLAS_OP_N : CUBLAS_OP_T;

    cusolverDnHandle_t h = get_handle();

    /* Device info scalar */
    int *devInfo = NULL;
    cudaError_t cerr = cudaMalloc((void **)&devInfo, sizeof(int));
    if (cerr != cudaSuccess) { *info = -1; return; }

    cusolverStatus_t st = cusolverDnDgetrs(h, op, in, inrhs,
                                           A, ild,
                                           (const int *)ipiv,
                                           B, ildb,
                                           devInfo);

    int host_info = 0;
    cudaMemcpy(&host_info, devInfo, sizeof(int), cudaMemcpyDeviceToHost);
    cudaDeviceSynchronize();
    cudaFree(devInfo);

    if (st != CUSOLVER_STATUS_SUCCESS) { *info = -(int64_t)st; return; }
    *info = (int64_t)host_info;
}

/* -----------------------------------------------------------------------
 * LAPACK: dgesv — Solve A*X = B (combines dgetrf + dgetrs internally)
 *
 * A    (device): n×n coefficient matrix, column-major; overwritten with LU
 * ipiv (device): caller-allocated int* buffer of n * sizeof(int) bytes
 * B    (device): n×nrhs right-hand side, overwritten with solution X
 * info (host):   0 on success, >0 if A is singular
 * ----------------------------------------------------------------------- */

void rt_lapack_dgesv(int64_t n, int64_t nrhs,
                     double *A, int64_t lda,
                     int64_t *ipiv,
                     double *B, int64_t ldb,
                     int64_t *info) {
    /* Step 1-3: LU factorize */
    rt_lapack_dgetrf(n, n, A, lda, ipiv, info);
    if (*info != 0) return;

    /* Step 4: Solve with the LU factors */
    rt_lapack_dgetrs(0 /* no-trans */, n, nrhs, A, lda, ipiv, B, ldb, info);
}

/* -----------------------------------------------------------------------
 * Backend identification
 * ----------------------------------------------------------------------- */

const char *rt_scilib_backend_name(void) { return "cusolver"; }
int         rt_scilib_is_real(void)       { return 1; }
