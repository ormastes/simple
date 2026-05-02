/*
 * cublas_shim.c — Real cuBLAS_64 backend for Simple scilib
 *
 * Exports the BLAS symbols declared in scilib_shim.h, implemented via
 * cuBLAS _64 API (64-bit index, CUDA 11.7+, available in CUDA 13.0).
 *
 * POINTER CONVENTION (T-BLAS-13 risk):
 *   All double* parameters for A/B/C/x/y are device pointers cast through
 *   the C type system for ABI compatibility. On x86_64, pointers and int64_t
 *   occupy the same 8-byte register slot, so no bits are lost.
 *   Callers must allocate device memory via rt_cuda_malloc and populate it
 *   via rt_cuda_memcpy_htod BEFORE calling any BLAS function. The shim never
 *   auto-stages host↔device copies inside BLAS calls.
 *
 * ROW-MAJOR vs COLUMN-MAJOR (OQ-C):
 *   cuBLAS uses column-major order. Callers pass row-major arrays. We use
 *   the identity (AB)^T = B^T A^T to fix dgemm: swap A↔B operands and
 *   m↔n in the cuBLAS call. The row-major leading dimensions equal the
 *   column-major leading dimensions of the transposed matrices, so lda/ldb
 *   are passed through unchanged. For dgemv, the trans flag is flipped
 *   (CUBLAS_OP_T when caller says no-trans, CUBLAS_OP_N when caller says trans)
 *   and user m↔n swap into cuBLAS m/n slots.
 *
 * HANDLE LIFECYCLE:
 *   A singleton cublasHandle_t is created on first use via pthread_once.
 *   It is never destroyed (process-lifetime). Pointer mode is set to
 *   CUBLAS_POINTER_MODE_HOST so alpha/beta are read from the host stack.
 *
 * Compile: gcc -shared -fPIC -I. -I/usr/local/cuda-13.0/targets/x86_64-linux/include
 *          -o libspl_scilib_cublas.so cublas_shim.c
 *          -L/usr/local/cuda-13.0/targets/x86_64-linux/lib -lcublas -lcudart
 */

#include "scilib_shim.h"

#include <cublas_v2.h>
#include <cuda_runtime.h>

#include <pthread.h>
#include <stdio.h>
#include <stdlib.h>

/* -----------------------------------------------------------------------
 * Singleton handle
 * ----------------------------------------------------------------------- */

static cublasHandle_t g_handle = NULL;
static pthread_once_t g_handle_once = PTHREAD_ONCE_INIT;

static void init_handle(void) {
    cublasStatus_t st = cublasCreate(&g_handle);
    if (st != CUBLAS_STATUS_SUCCESS) {
        fprintf(stderr, "cublas_shim: cublasCreate failed (status=%d)\n", st);
        g_handle = NULL;
        return;
    }
    /* Ensure alpha/beta scalars are read from host memory (the default,
     * but set explicitly for clarity). */
    st = cublasSetPointerMode(g_handle, CUBLAS_POINTER_MODE_HOST);
    if (st != CUBLAS_STATUS_SUCCESS) {
        fprintf(stderr, "cublas_shim: cublasSetPointerMode failed (status=%d)\n", st);
    }
}

/* Returns the singleton handle (or NULL if init failed). */
static cublasHandle_t get_handle(void) {
    pthread_once(&g_handle_once, init_handle);
    return g_handle;
}

/* -----------------------------------------------------------------------
 * CUDA memory helpers — real cudaMalloc/cudaFree/cudaMemcpy
 * ----------------------------------------------------------------------- */

int64_t rt_cuda_malloc(int64_t bytes) {
    void *ptr = NULL;
    cudaError_t err = cudaMalloc(&ptr, (size_t)bytes);
    if (err != cudaSuccess) {
        fprintf(stderr, "cublas_shim: cudaMalloc(%lld) failed: %s\n",
                (long long)bytes, cudaGetErrorString(err));
        return 0;
    }
    return (int64_t)(uintptr_t)ptr;
}

void rt_cuda_free(int64_t dev_ptr) {
    cudaFree((void *)(uintptr_t)dev_ptr);
}

void rt_cuda_memcpy_htod(int64_t dev_dst, const void *host_src, int64_t bytes) {
    cudaError_t err = cudaMemcpy((void *)(uintptr_t)dev_dst,
                                 host_src,
                                 (size_t)bytes,
                                 cudaMemcpyHostToDevice);
    if (err != cudaSuccess) {
        fprintf(stderr, "cublas_shim: cudaMemcpy HtoD failed: %s\n",
                cudaGetErrorString(err));
    }
}

void rt_cuda_memcpy_dtoh(void *host_dst, int64_t dev_src, int64_t bytes) {
    cudaError_t err = cudaMemcpy(host_dst,
                                 (const void *)(uintptr_t)dev_src,
                                 (size_t)bytes,
                                 cudaMemcpyDeviceToHost);
    if (err != cudaSuccess) {
        fprintf(stderr, "cublas_shim: cudaMemcpy DtoH failed: %s\n",
                cudaGetErrorString(err));
    }
}

/* -----------------------------------------------------------------------
 * BLAS: dgemm — C = alpha * op(A) * op(B) + beta * C  (row-major caller)
 *
 * Row-major↔col-major fix: call cuBLAS as
 *   cublasDgemm(handle, transb, transa, n, m, k, &alpha, B, ldb, A, lda, &beta, C, ldc)
 * This computes C^T = beta*C^T + alpha * op(B)^T * op(A)^T, which viewed
 * row-major is C = beta*C + alpha * op(A) * op(B).  lda/ldb pass through
 * unchanged because the row-major leading dimension equals the column-major
 * leading dimension of the transpose.
 * ----------------------------------------------------------------------- */
void rt_blas_dgemm(int trans_a, int trans_b,
                   int64_t m, int64_t n, int64_t k,
                   double alpha,
                   const double *A, int64_t lda,
                   const double *B, int64_t ldb,
                   double beta,
                   double *C, int64_t ldc) {
    cublasHandle_t h = get_handle();
    if (!h) return;

    cublasOperation_t opa = trans_a ? CUBLAS_OP_T : CUBLAS_OP_N;
    cublasOperation_t opb = trans_b ? CUBLAS_OP_T : CUBLAS_OP_N;

    /* Operand swap: pass B first, then A; swap m↔n */
    cublasStatus_t st = cublasDgemm_64(h,
        opb, opa,          /* transb, transa — swapped */
        n, m, k,           /* n, m — swapped; k unchanged */
        &alpha,
        B, ldb,            /* B first */
        A, lda,            /* then A */
        &beta,
        C, ldc);

    if (st != CUBLAS_STATUS_SUCCESS) {
        fprintf(stderr, "cublas_shim: cublasDgemm_64 failed (status=%d)\n", st);
    }
}

/* -----------------------------------------------------------------------
 * BLAS: dgemv — y = alpha * op(A) * x + beta * y  (row-major caller)
 *
 * Row-major fix: flip trans flag and swap user m↔n in cuBLAS m/n slots.
 * When caller says no-trans (op(A)=A, result dim = m rows),
 * cuBLAS must treat A^T as its matrix and use CUBLAS_OP_T on the stored
 * column-major data (which IS A^T from cuBLAS's perspective).
 * So: op_cublas = user_trans ? CUBLAS_OP_N : CUBLAS_OP_T
 * cuBLAS m param = n_user, cuBLAS n param = m_user.
 * ----------------------------------------------------------------------- */
void rt_blas_dgemv(int trans,
                   int64_t m, int64_t n,
                   double alpha,
                   const double *A, int64_t lda,
                   const double *x, int64_t incx,
                   double beta,
                   double *y, int64_t incy) {
    cublasHandle_t h = get_handle();
    if (!h) return;

    /* Flip the trans flag; swap m↔n into cuBLAS slots */
    cublasOperation_t op = trans ? CUBLAS_OP_N : CUBLAS_OP_T;

    cublasStatus_t st = cublasDgemv_64(h,
        op,
        n, m,   /* cuBLAS m=n_user, n=m_user */
        &alpha,
        A, lda,
        x, incx,
        &beta,
        y, incy);

    if (st != CUBLAS_STATUS_SUCCESS) {
        fprintf(stderr, "cublas_shim: cublasDgemv_64 failed (status=%d)\n", st);
    }
}

/* -----------------------------------------------------------------------
 * BLAS: daxpy — y = alpha * x + y
 * No row/col distinction for pure vectors.
 * ----------------------------------------------------------------------- */
void rt_blas_daxpy(int64_t n,
                   double alpha,
                   const double *x, int64_t incx,
                   double *y, int64_t incy) {
    cublasHandle_t h = get_handle();
    if (!h) return;

    cublasStatus_t st = cublasDaxpy_64(h, n, &alpha, x, incx, y, incy);
    if (st != CUBLAS_STATUS_SUCCESS) {
        fprintf(stderr, "cublas_shim: cublasDaxpy_64 failed (status=%d)\n", st);
    }
}

/* -----------------------------------------------------------------------
 * BLAS: ddot — result = x . y
 * Result is written to host via CUBLAS_POINTER_MODE_HOST.
 * ----------------------------------------------------------------------- */
double rt_blas_ddot(int64_t n,
                    const double *x, int64_t incx,
                    const double *y, int64_t incy) {
    cublasHandle_t h = get_handle();
    if (!h) return 0.0;

    double result = 0.0;
    cublasStatus_t st = cublasDdot_64(h, n, x, incx, y, incy, &result);
    if (st != CUBLAS_STATUS_SUCCESS) {
        fprintf(stderr, "cublas_shim: cublasDdot_64 failed (status=%d)\n", st);
    }
    return result;
}

/* -----------------------------------------------------------------------
 * BLAS: dscal — x = alpha * x
 * ----------------------------------------------------------------------- */
void rt_blas_dscal(int64_t n, double alpha, double *x, int64_t incx) {
    cublasHandle_t h = get_handle();
    if (!h) return;

    cublasStatus_t st = cublasDscal_64(h, n, &alpha, x, incx);
    if (st != CUBLAS_STATUS_SUCCESS) {
        fprintf(stderr, "cublas_shim: cublasDscal_64 failed (status=%d)\n", st);
    }
}

/* -----------------------------------------------------------------------
 * BLAS: idamax — 0-based index of element with max absolute value.
 *
 * cuBLAS cublasIdamax_64 returns a 1-based (Fortran-heritage) index.
 * We subtract 1 before returning.  Callers must guarantee n > 0;
 * for n <= 0 cuBLAS may return 0, and we clamp to 0.
 * ----------------------------------------------------------------------- */
int64_t rt_blas_idamax(int64_t n, const double *x, int64_t incx) {
    cublasHandle_t h = get_handle();
    if (!h || n <= 0) return 0;

    int64_t result = 0;
    cublasStatus_t st = cublasIdamax_64(h, n, x, incx, &result);
    if (st != CUBLAS_STATUS_SUCCESS) {
        fprintf(stderr, "cublas_shim: cublasIdamax_64 failed (status=%d)\n", st);
        return 0;
    }
    /* Convert 1-based to 0-based; guard against unexpected 0 return */
    return (result > 0) ? (result - 1) : 0;
}

/* -----------------------------------------------------------------------
 * BLAS: dnrm2 — Euclidean norm ||x||_2
 * ----------------------------------------------------------------------- */
double rt_blas_dnrm2(int64_t n, const double *x, int64_t incx) {
    cublasHandle_t h = get_handle();
    if (!h) return 0.0;

    double result = 0.0;
    cublasStatus_t st = cublasDnrm2_64(h, n, x, incx, &result);
    if (st != CUBLAS_STATUS_SUCCESS) {
        fprintf(stderr, "cublas_shim: cublasDnrm2_64 failed (status=%d)\n", st);
    }
    return result;
}

/* -----------------------------------------------------------------------
 * LAPACK stubs — NOT implemented here; these are cusolver_shim.c's scope.
 * Symbols are NOT exported from this .so; cusolver_shim.so owns them.
 * ----------------------------------------------------------------------- */

/* -----------------------------------------------------------------------
 * Backend identification
 * ----------------------------------------------------------------------- */
const char *rt_scilib_backend_name(void) {
    return "cublas";
}

int rt_scilib_is_real(void) {
    return 1;
}
