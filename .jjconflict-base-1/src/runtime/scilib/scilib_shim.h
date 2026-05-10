/*
 * scilib_shim.h — shared C ABI for Simple science-library backends.
 *
 * Buffers use row-major layout unless a backend-specific implementation states
 * otherwise internally. Pivot arrays use LAPACK-compatible 1-based indices.
 */

#ifndef SIMPLE_SCILIB_SHIM_H
#define SIMPLE_SCILIB_SHIM_H

#include <stdint.h>

const char *rt_scilib_backend_name(void);
int rt_scilib_is_real(void);

void rt_blas_daxpy(int64_t n, double alpha,
                   const double *x, int64_t incx,
                   double *y, int64_t incy);
double rt_blas_ddot(int64_t n,
                    const double *x, int64_t incx,
                    const double *y, int64_t incy);
void rt_blas_dscal(int64_t n, double alpha, double *x, int64_t incx);
int64_t rt_blas_idamax(int64_t n, const double *x, int64_t incx);
double rt_blas_dnrm2(int64_t n, const double *x, int64_t incx);
void rt_blas_dgemv(int trans,
                   int64_t m, int64_t n,
                   double alpha,
                   const double *A, int64_t lda,
                   const double *x, int64_t incx,
                   double beta,
                   double *y, int64_t incy);
void rt_blas_dgemm(int trans_a, int trans_b,
                   int64_t m, int64_t n, int64_t k,
                   double alpha,
                   const double *A, int64_t lda,
                   const double *B, int64_t ldb,
                   double beta,
                   double *C, int64_t ldc);

void rt_lapack_dgetrf(int64_t m, int64_t n,
                      double *A, int64_t lda,
                      int64_t *ipiv,
                      int64_t *info);
void rt_lapack_dgetrs(int trans,
                      int64_t n, int64_t nrhs,
                      const double *A, int64_t lda,
                      const int64_t *ipiv,
                      double *B, int64_t ldb,
                      int64_t *info);
void rt_lapack_dgesv(int64_t n, int64_t nrhs,
                     double *A, int64_t lda,
                     int64_t *ipiv,
                     double *B, int64_t ldb,
                     int64_t *info);

int64_t rt_cuda_malloc(int64_t bytes);
void rt_cuda_free(int64_t dev_ptr);
void rt_cuda_memcpy_htod(int64_t dev_dst, const void *host_src, int64_t bytes);
void rt_cuda_memcpy_dtoh(void *host_dst, int64_t dev_src, int64_t bytes);

int64_t rt_scilib_cuda_available(void);
int64_t rt_scilib_cuda_ddot_bits(int64_t x_bits_addr,
                                 int64_t n,
                                 int64_t y_bits_addr);
int64_t rt_scilib_cuda_dgemm_bits(int64_t params_addr,
                                  int64_t a_bits_addr,
                                  int64_t b_bits_addr,
                                  int64_t c_bits_addr,
                                  int64_t out_bits_addr);
int64_t rt_scilib_cuda_dgemv_bits(int64_t params_addr,
                                  int64_t a_bits_addr,
                                  int64_t x_bits_addr,
                                  int64_t y_bits_addr,
                                  int64_t out_bits_addr);
int64_t rt_scilib_cuda_dgesv_bits(int64_t params_addr,
                                  int64_t a_bits_addr,
                                  int64_t b_bits_addr,
                                  int64_t out_bits_addr);

int64_t rt_scilib_openblas_available(void);
int64_t rt_scilib_openblas_ddot_bits(int64_t x_bits_addr,
                                     int64_t n,
                                     int64_t y_bits_addr);
int64_t rt_scilib_openblas_daxpy_bits(int64_t params_addr,
                                      int64_t x_bits_addr,
                                      int64_t y_bits_addr,
                                      int64_t out_bits_addr);
int64_t rt_scilib_openblas_dgemm_bits(int64_t params_addr,
                                      int64_t a_bits_addr,
                                      int64_t b_bits_addr,
                                      int64_t c_bits_addr,
                                      int64_t out_bits_addr);
int64_t rt_scilib_openblas_dgesv_bits(int64_t params_addr,
                                      int64_t a_bits_addr,
                                      int64_t b_bits_addr,
                                      int64_t out_bits_addr);

#endif
