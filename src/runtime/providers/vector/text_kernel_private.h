#ifndef SIMPLE_TEXT_KERNEL_PRIVATE_H
#define SIMPLE_TEXT_KERNEL_PRIVATE_H
/* Text kernels of the levelled vector provider (Stage 1 of moving CPU-level
 * specific SIMD out of the static runtime). Opcodes and wire semantics are in
 * simple_vector_kernel_abi_v1.h (SIMPLE_VECTOR_TEXT_*). Every level object is
 * text_level_kernels.c compiled with that level's -march and renamed with
 * -Dsimple_text_kernel=simple_text_kernel_lN; text_level_dispatch.c owns the
 * unsuffixed entry point. Libc-free: the compile lane has no sysroot. */
#include "../../simple_vector_kernel_abi_v1.h"
#if defined(SIMPLE_VECTOR_LEVELLED) && !defined(SIMPLE_VECTOR_NO_TEXT)
#define SIMPLE_VECTOR_ENABLE_TEXT 1
#endif
/* Validated spans only (the apply owner checks ranges first). Returns 0 and
 * stores the op result in *result, or -1 for an opcode this object lacks.
 * Upper/lower write exactly n bytes to out (out == input or disjoint). */
int simple_text_kernel(uint32_t opcode, const uint8_t *input, size_t n,
    const uint8_t *needle, size_t needle_n, uint8_t *out, int64_t *result);
#endif
