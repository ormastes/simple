/*
 * cublas_shim.c — Real cuBLAS_64 backend for Simple scilib
 *
 * Exports the BLAS symbols declared in scilib_shim.h, implemented via
 * cuBLAS _64 API (64-bit index, CUDA 11.7+, available in CUDA 13.0).
 *
 * POINTER CONVENTION (T-BLAS-13 risk):
 *   Low-level rt_blas_* functions receive CUDA device pointers cast through
 *   the C type system for ABI compatibility. The public Simple dynamic FFI
 *   wrappers, rt_scilib_cuda_*_bits, receive host staging-buffer addresses as
 *   int64_t values, copy through private CUDA-runtime helpers, and write host
 *   results back before returning.
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
 *          -L/usr/local/cuda-13.0/targets/x86_64-linux/lib -lcublas -lcudart -ldl
 */

#include "scilib_shim.h"

#include <cublas_v2.h>
#include <cusolverDn.h>
#include <cuda_runtime.h>

#include <dlfcn.h>
#include <limits.h>
#include <pthread.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

extern int64_t rt_ptr_read_i64(int64_t addr, int64_t offset) __attribute__((weak));
extern void rt_ptr_write_i64(int64_t addr, int64_t offset, int64_t value) __attribute__((weak));

typedef int64_t (*rt_ptr_read_i64_fn)(int64_t addr, int64_t offset);
typedef void (*rt_ptr_write_i64_fn)(int64_t addr, int64_t offset, int64_t value);

static rt_ptr_read_i64_fn scilib_runtime_read_i64(void)
{
    if (rt_ptr_read_i64) return rt_ptr_read_i64;
    return (rt_ptr_read_i64_fn)dlsym(RTLD_DEFAULT, "rt_ptr_read_i64");
}

static rt_ptr_write_i64_fn scilib_runtime_write_i64(void)
{
    if (rt_ptr_write_i64) return rt_ptr_write_i64;
    return (rt_ptr_write_i64_fn)dlsym(RTLD_DEFAULT, "rt_ptr_write_i64");
}

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

static cusolverDnHandle_t g_solver_handle = NULL;
static pthread_once_t g_solver_handle_once = PTHREAD_ONCE_INIT;

static void init_solver_handle(void) {
    cusolverStatus_t st = cusolverDnCreate(&g_solver_handle);
    if (st != CUSOLVER_STATUS_SUCCESS) {
        fprintf(stderr, "cublas_shim: cusolverDnCreate failed (status=%d)\n", st);
        g_solver_handle = NULL;
    }
}

static cusolverDnHandle_t get_solver_handle(void) {
    pthread_once(&g_solver_handle_once, init_solver_handle);
    return g_solver_handle;
}

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

static int64_t scilib_read_i64_arg(int64_t addr, int64_t index)
{
    rt_ptr_read_i64_fn read_i64 = scilib_runtime_read_i64();
    if (read_i64) {
        return read_i64(addr, index * (int64_t)sizeof(int64_t));
    }
    const int64_t *ptr = (const int64_t *)(uintptr_t)addr;
    return ptr[index];
}

static void scilib_write_i64_arg(int64_t addr, int64_t index, int64_t value)
{
    rt_ptr_write_i64_fn write_i64 = scilib_runtime_write_i64();
    if (write_i64) {
        write_i64(addr, index * (int64_t)sizeof(int64_t), value);
        return;
    }
    int64_t *ptr = (int64_t *)(uintptr_t)addr;
    ptr[index] = value;
}

int64_t rt_scilib_cuda_available(void)
{
    return get_handle() ? 1 : 0;
}

/* -----------------------------------------------------------------------
 * CUDA memory helpers — real cudaMalloc/cudaFree/cudaMemcpy
 * ----------------------------------------------------------------------- */

static int64_t scilib_cuda_malloc_impl(int64_t bytes) {
    void *ptr = NULL;
    cudaError_t err = cudaMalloc(&ptr, (size_t)bytes);
    if (err != cudaSuccess) {
        fprintf(stderr, "cublas_shim: cudaMalloc(%lld) failed: %s\n",
                (long long)bytes, cudaGetErrorString(err));
        return 0;
    }
    return (int64_t)(uintptr_t)ptr;
}

static void scilib_cuda_free_impl(int64_t dev_ptr) {
    cudaFree((void *)(uintptr_t)dev_ptr);
}

/* Use private helper names internally. The public rt_cuda_memcpy_* symbol names
 * can be interposed by the Simple runtime's CUDA-driver shims when this library
 * is loaded into the interpreter process. */
static void scilib_cuda_memcpy_htod_impl(int64_t dev_dst, const void *host_src, int64_t bytes) {
    cudaError_t err = cudaMemcpy((void *)(uintptr_t)dev_dst,
                                 host_src,
                                 (size_t)bytes,
                                 cudaMemcpyHostToDevice);
    if (err != cudaSuccess) {
        fprintf(stderr, "cublas_shim: cudaMemcpy HtoD failed: %s\n",
                cudaGetErrorString(err));
    }
}

static void scilib_cuda_memcpy_dtoh_impl(void *host_dst, int64_t dev_src, int64_t bytes) {
    cudaError_t err = cudaMemcpy(host_dst,
                                 (const void *)(uintptr_t)dev_src,
                                 (size_t)bytes,
                                 cudaMemcpyDeviceToHost);
    if (err != cudaSuccess) {
        fprintf(stderr, "cublas_shim: cudaMemcpy DtoH failed: %s\n",
                cudaGetErrorString(err));
    }
}

int64_t rt_cuda_malloc(int64_t bytes) {
    return scilib_cuda_malloc_impl(bytes);
}

void rt_cuda_free(int64_t dev_ptr) {
    scilib_cuda_free_impl(dev_ptr);
}

void rt_cuda_memcpy_htod(int64_t dev_dst, const void *host_src, int64_t bytes) {
    scilib_cuda_memcpy_htod_impl(dev_dst, host_src, bytes);
}

void rt_cuda_memcpy_dtoh(void *host_dst, int64_t dev_src, int64_t bytes) {
    scilib_cuda_memcpy_dtoh_impl(host_dst, dev_src, bytes);
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
        return;
    }
    cudaError_t sync_err = cudaDeviceSynchronize();
    if (sync_err != cudaSuccess) {
        fprintf(stderr, "cublas_shim: cudaDeviceSynchronize after dgemm failed: %s\n",
                cudaGetErrorString(sync_err));
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
        return;
    }
    cudaError_t sync_err = cudaDeviceSynchronize();
    if (sync_err != cudaSuccess) {
        fprintf(stderr, "cublas_shim: cudaDeviceSynchronize after dgemv failed: %s\n",
                cudaGetErrorString(sync_err));
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
        return;
    }
    cudaError_t sync_err = cudaDeviceSynchronize();
    if (sync_err != cudaSuccess) {
        fprintf(stderr, "cublas_shim: cudaDeviceSynchronize after daxpy failed: %s\n",
                cudaGetErrorString(sync_err));
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
        return result;
    }
    cudaError_t sync_err = cudaDeviceSynchronize();
    if (sync_err != cudaSuccess) {
        fprintf(stderr, "cublas_shim: cudaDeviceSynchronize after ddot failed: %s\n",
                cudaGetErrorString(sync_err));
    }
    return result;
}

int64_t rt_scilib_cuda_ddot_bits(int64_t x_bits_addr,
                                 int64_t n,
                                 int64_t y_bits_addr) {
    if (n <= 0) return scilib_double_to_bits(0.0);

    int64_t bytes = n * (int64_t)sizeof(double);
    int64_t *x_host = (int64_t *)malloc((size_t)bytes);
    int64_t *y_host = (int64_t *)malloc((size_t)bytes);
    if (x_host == NULL || y_host == NULL) {
        free(x_host);
        free(y_host);
        return scilib_double_to_bits(0.0);
    }
    for (int64_t i = 0; i < n; ++i) {
        x_host[i] = scilib_read_i64_arg(x_bits_addr, i);
        y_host[i] = scilib_read_i64_arg(y_bits_addr, i);
    }
    int64_t x_dev = scilib_cuda_malloc_impl(bytes);
    int64_t y_dev = scilib_cuda_malloc_impl(bytes);
    if (x_dev == 0 || y_dev == 0) {
        scilib_cuda_free_impl(x_dev);
        scilib_cuda_free_impl(y_dev);
        free(x_host);
        free(y_host);
        return scilib_double_to_bits(0.0);
    }

    scilib_cuda_memcpy_htod_impl(x_dev, x_host, bytes);
    scilib_cuda_memcpy_htod_impl(y_dev, y_host, bytes);
    cudaDeviceSynchronize();
    double result = rt_blas_ddot(n,
                                 (const double *)(uintptr_t)x_dev, 1,
                                 (const double *)(uintptr_t)y_dev, 1);
    scilib_cuda_free_impl(x_dev);
    scilib_cuda_free_impl(y_dev);
    free(x_host);
    free(y_host);
    return scilib_double_to_bits(result);
}

int64_t rt_scilib_cuda_dgemm_bits(int64_t params_addr,
                                  int64_t a_bits_addr,
                                  int64_t b_bits_addr,
                                  int64_t c_bits_addr,
                                  int64_t out_bits_addr) {
    int64_t m = scilib_read_i64_arg(params_addr, 0);
    int64_t n = scilib_read_i64_arg(params_addr, 1);
    int64_t k = scilib_read_i64_arg(params_addr, 2);
    int64_t alpha_bits = scilib_read_i64_arg(params_addr, 3);
    int64_t beta_bits = scilib_read_i64_arg(params_addr, 4);
    if (m < 0 || n < 0 || k < 0) return 0;

    int64_t a_bytes = m * k * (int64_t)sizeof(double);
    int64_t b_bytes = k * n * (int64_t)sizeof(double);
    int64_t c_bytes = m * n * (int64_t)sizeof(double);
    int64_t *a_host = (int64_t *)malloc((size_t)a_bytes);
    int64_t *b_host = (int64_t *)malloc((size_t)b_bytes);
    int64_t *c_host = (int64_t *)malloc((size_t)c_bytes);
    int64_t *out_host = (int64_t *)malloc((size_t)c_bytes);
    if (a_host == NULL || b_host == NULL || c_host == NULL || out_host == NULL) {
        free(a_host);
        free(b_host);
        free(c_host);
        free(out_host);
        return 0;
    }
    for (int64_t i = 0; i < m * k; ++i) {
        a_host[i] = scilib_read_i64_arg(a_bits_addr, i);
    }
    for (int64_t i = 0; i < k * n; ++i) {
        b_host[i] = scilib_read_i64_arg(b_bits_addr, i);
    }
    for (int64_t i = 0; i < m * n; ++i) {
        c_host[i] = scilib_read_i64_arg(c_bits_addr, i);
    }
    int64_t a_dev = scilib_cuda_malloc_impl(a_bytes);
    int64_t b_dev = scilib_cuda_malloc_impl(b_bytes);
    int64_t c_dev = scilib_cuda_malloc_impl(c_bytes);
    if (a_dev == 0 || b_dev == 0 || c_dev == 0) {
        scilib_cuda_free_impl(a_dev);
        scilib_cuda_free_impl(b_dev);
        scilib_cuda_free_impl(c_dev);
        free(a_host);
        free(b_host);
        free(c_host);
        free(out_host);
        return 0;
    }

    scilib_cuda_memcpy_htod_impl(a_dev, a_host, a_bytes);
    scilib_cuda_memcpy_htod_impl(b_dev, b_host, b_bytes);
    scilib_cuda_memcpy_htod_impl(c_dev, c_host, c_bytes);
    rt_blas_dgemm(0, 0, m, n, k,
                  scilib_bits_to_double(alpha_bits),
                  (const double *)(uintptr_t)a_dev, k,
                  (const double *)(uintptr_t)b_dev, n,
                  scilib_bits_to_double(beta_bits),
                  (double *)(uintptr_t)c_dev, n);
    scilib_cuda_memcpy_dtoh_impl(out_host, c_dev, c_bytes);
    for (int64_t i = 0; i < m * n; ++i) {
        scilib_write_i64_arg(out_bits_addr, i, out_host[i]);
    }
    scilib_cuda_free_impl(a_dev);
    scilib_cuda_free_impl(b_dev);
    scilib_cuda_free_impl(c_dev);
    free(a_host);
    free(b_host);
    free(c_host);
    free(out_host);
    return 1;
}

int64_t rt_scilib_cuda_dgemv_bits(int64_t params_addr,
                                  int64_t a_bits_addr,
                                  int64_t x_bits_addr,
                                  int64_t y_bits_addr,
                                  int64_t out_bits_addr) {
    int64_t m = scilib_read_i64_arg(params_addr, 0);
    int64_t n = scilib_read_i64_arg(params_addr, 1);
    int64_t alpha_bits = scilib_read_i64_arg(params_addr, 2);
    int64_t beta_bits = scilib_read_i64_arg(params_addr, 3);
    if (m < 0 || n < 0) return 0;

    int64_t a_bytes = m * n * (int64_t)sizeof(double);
    int64_t x_bytes = n * (int64_t)sizeof(double);
    int64_t y_bytes = m * (int64_t)sizeof(double);
    int64_t *a_host = (int64_t *)malloc((size_t)a_bytes);
    int64_t *x_host = (int64_t *)malloc((size_t)x_bytes);
    int64_t *y_host = (int64_t *)malloc((size_t)y_bytes);
    int64_t *out_host = (int64_t *)malloc((size_t)y_bytes);
    if (a_host == NULL || x_host == NULL || y_host == NULL || out_host == NULL) {
        free(a_host);
        free(x_host);
        free(y_host);
        free(out_host);
        return 0;
    }

    for (int64_t i = 0; i < m * n; ++i) {
        a_host[i] = scilib_read_i64_arg(a_bits_addr, i);
    }
    for (int64_t i = 0; i < n; ++i) {
        x_host[i] = scilib_read_i64_arg(x_bits_addr, i);
    }
    for (int64_t i = 0; i < m; ++i) {
        y_host[i] = scilib_read_i64_arg(y_bits_addr, i);
    }

    int64_t a_dev = scilib_cuda_malloc_impl(a_bytes);
    int64_t x_dev = scilib_cuda_malloc_impl(x_bytes);
    int64_t y_dev = scilib_cuda_malloc_impl(y_bytes);
    if (a_dev == 0 || x_dev == 0 || y_dev == 0) {
        scilib_cuda_free_impl(a_dev);
        scilib_cuda_free_impl(x_dev);
        scilib_cuda_free_impl(y_dev);
        free(a_host);
        free(x_host);
        free(y_host);
        free(out_host);
        return 0;
    }

    scilib_cuda_memcpy_htod_impl(a_dev, a_host, a_bytes);
    scilib_cuda_memcpy_htod_impl(x_dev, x_host, x_bytes);
    scilib_cuda_memcpy_htod_impl(y_dev, y_host, y_bytes);
    rt_blas_dgemv(0, m, n,
                  scilib_bits_to_double(alpha_bits),
                  (const double *)(uintptr_t)a_dev, n,
                  (const double *)(uintptr_t)x_dev, 1,
                  scilib_bits_to_double(beta_bits),
                  (double *)(uintptr_t)y_dev, 1);
    scilib_cuda_memcpy_dtoh_impl(out_host, y_dev, y_bytes);
    for (int64_t i = 0; i < m; ++i) {
        scilib_write_i64_arg(out_bits_addr, i, out_host[i]);
    }

    scilib_cuda_free_impl(a_dev);
    scilib_cuda_free_impl(x_dev);
    scilib_cuda_free_impl(y_dev);
    free(a_host);
    free(x_host);
    free(y_host);
    free(out_host);
    return 1;
}

static int64_t scilib_cuda_dgesv_device(int64_t n,
                                        int64_t nrhs,
                                        double *a_dev,
                                        double *b_dev) {
    if (n > INT_MAX || nrhs > INT_MAX) return -1;

    cusolverDnHandle_t h = get_solver_handle();
    if (!h) return -2;

    int in = (int)n;
    int inrhs = (int)nrhs;
    int lwork = 0;
    cusolverStatus_t st = cusolverDnDgetrf_bufferSize(h, in, in, a_dev, in, &lwork);
    if (st != CUSOLVER_STATUS_SUCCESS) return -(int64_t)st;

    double *workspace = NULL;
    int *ipiv = NULL;
    int *dev_info = NULL;
    cudaError_t cerr = cudaMalloc((void **)&workspace, (size_t)lwork * sizeof(double));
    if (cerr != cudaSuccess) return -1001;
    cerr = cudaMalloc((void **)&ipiv, (size_t)n * sizeof(int));
    if (cerr != cudaSuccess) {
        cudaFree(workspace);
        return -1001;
    }
    cerr = cudaMalloc((void **)&dev_info, sizeof(int));
    if (cerr != cudaSuccess) {
        cudaFree(workspace);
        cudaFree(ipiv);
        return -1001;
    }

    st = cusolverDnDgetrf(h, in, in, a_dev, in, workspace, ipiv, dev_info);
    int host_info = 0;
    cudaMemcpy(&host_info, dev_info, sizeof(int), cudaMemcpyDeviceToHost);
    cudaDeviceSynchronize();
    if (st == CUSOLVER_STATUS_SUCCESS && host_info == 0) {
        st = cusolverDnDgetrs(h, CUBLAS_OP_N, in, inrhs, a_dev, in, ipiv, b_dev, in, dev_info);
        cudaMemcpy(&host_info, dev_info, sizeof(int), cudaMemcpyDeviceToHost);
        cudaDeviceSynchronize();
    }

    cudaFree(workspace);
    cudaFree(ipiv);
    cudaFree(dev_info);

    if (st != CUSOLVER_STATUS_SUCCESS) return -(int64_t)st;
    return (int64_t)host_info;
}

int64_t rt_scilib_cuda_dgesv_bits(int64_t params_addr,
                                  int64_t a_bits_addr,
                                  int64_t b_bits_addr,
                                  int64_t out_bits_addr) {
    int64_t n = scilib_read_i64_arg(params_addr, 0);
    int64_t nrhs = scilib_read_i64_arg(params_addr, 1);
    if (n < 0 || nrhs < 0) return -1;

    int64_t a_count = n * n;
    int64_t b_count = n * nrhs;
    int64_t a_bytes = a_count * (int64_t)sizeof(double);
    int64_t b_bytes = b_count * (int64_t)sizeof(double);
    double *a_host = (double *)malloc((size_t)a_bytes);
    double *b_host = (double *)malloc((size_t)b_bytes);
    double *out_host = (double *)malloc((size_t)b_bytes);
    if (a_host == NULL || b_host == NULL || out_host == NULL) {
        free(a_host);
        free(b_host);
        free(out_host);
        return -1000;
    }

    for (int64_t row = 0; row < n; ++row) {
        for (int64_t col = 0; col < n; ++col) {
            int64_t bits = scilib_read_i64_arg(a_bits_addr, row * n + col);
            a_host[col * n + row] = scilib_bits_to_double(bits);
        }
    }
    for (int64_t row = 0; row < n; ++row) {
        for (int64_t col = 0; col < nrhs; ++col) {
            int64_t bits = scilib_read_i64_arg(b_bits_addr, row * nrhs + col);
            b_host[col * n + row] = scilib_bits_to_double(bits);
        }
    }

    int64_t a_dev = scilib_cuda_malloc_impl(a_bytes);
    int64_t b_dev = scilib_cuda_malloc_impl(b_bytes);
    if (a_dev == 0 || b_dev == 0) {
        scilib_cuda_free_impl(a_dev);
        scilib_cuda_free_impl(b_dev);
        free(a_host);
        free(b_host);
        free(out_host);
        return -1001;
    }

    scilib_cuda_memcpy_htod_impl(a_dev, a_host, a_bytes);
    scilib_cuda_memcpy_htod_impl(b_dev, b_host, b_bytes);
    int64_t info = scilib_cuda_dgesv_device(n, nrhs,
                                            (double *)(uintptr_t)a_dev,
                                            (double *)(uintptr_t)b_dev);
    if (info == 0) {
        scilib_cuda_memcpy_dtoh_impl(out_host, b_dev, b_bytes);
        for (int64_t row = 0; row < n; ++row) {
            for (int64_t col = 0; col < nrhs; ++col) {
                scilib_write_i64_arg(out_bits_addr, row * nrhs + col,
                                     scilib_double_to_bits(out_host[col * n + row]));
            }
        }
    }

    scilib_cuda_free_impl(a_dev);
    scilib_cuda_free_impl(b_dev);
    free(a_host);
    free(b_host);
    free(out_host);
    return info;
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
 * LAPACK scope
 *
 * This combined Simple-facing shim exports rt_scilib_cuda_dgesv_bits above for
 * the staged Float64 vector solve path. The lower-level rt_lapack_* symbols
 * remain owned by cusolver_shim.c.
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
