/*
 * scilib_bits_common.h -- helpers shared by mock_shim.c and openblas_shim.c.
 *
 * Private to the scilib shims: include it once per shim translation unit after
 * scilib_shim.h, <stdint.h>, <stdlib.h> and <string.h>. (openblas_shim.c's
 * unavailable branch textually includes mock_shim.c, so the include guard is
 * what keeps that build to one copy.)
 *
 * Carries exactly the parts both shims defined identically:
 *   - the static double <-> int64 bit-pattern codecs that every *_bits entry
 *     point and scilib_bits_lapack.inc rely on;
 *   - the rt_scilib_openblas_{ddot,dgemm,dgemv}_bits entry points, which on
 *     both backends delegate to the shim's own rt_scilib_cuda_* twins;
 *   - the host-memory rt_cuda_{malloc,free,memcpy_htod,memcpy_dtoh} stubs
 *     (plain malloc / free / memcpy on both backends).
 * Pinned by src/runtime/test/scilib_bits_common_selfcheck.c.
 */
#ifndef SIMPLE_SCILIB_BITS_COMMON_H
#define SIMPLE_SCILIB_BITS_COMMON_H

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

int64_t rt_scilib_openblas_ddot_bits(int64_t x_bits_addr,
                                     int64_t n,
                                     int64_t y_bits_addr)
{
    return rt_scilib_cuda_ddot_bits(x_bits_addr, n, y_bits_addr);
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

int64_t rt_scilib_openblas_dgemv_bits(int64_t params_addr,
                                      int64_t a_bits_addr,
                                      int64_t x_bits_addr,
                                      int64_t y_bits_addr,
                                      int64_t out_bits_addr)
{
    return rt_scilib_cuda_dgemv_bits(params_addr, a_bits_addr, x_bits_addr,
                                     y_bits_addr, out_bits_addr);
}

/* Host-memory "device" buffers: 0 (NULL) on allocation failure. */
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

#endif /* SIMPLE_SCILIB_BITS_COMMON_H */
