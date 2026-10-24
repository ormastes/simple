#ifndef SIMPLE_VECTOR_LEVEL_PRIVATE_H
#define SIMPLE_VECTOR_LEVEL_PRIVATE_H
/* Levelled provider: one DSO, one kernel object per SIMD level, one baseline
 * dispatcher (vector_level_dispatch.c). Level 0 = no vector kernel admitted.
 *   x86_64 : 1=x86-64 (SSE2) 2=x86-64-v2 3=x86-64-v3 (AVX2) 4=x86-64-v4 (AVX-512)
 *   aarch64: 1=NEON/ASIMD 2=SVE 3=SVE2
 *   riscv64: 1=RVV (scalar rv64gc is level 0: never labelled SIMD)
 * Each kernel object is the normal simple_{bitmap,http}_kernel TU renamed with
 * -Dsimple_bitmap_kernel=simple_bitmap_kernel_lN at build time. */
#include "bitmap_kernel_private.h"
#ifndef SIMPLE_VECTOR_MAX_LEVEL
#define SIMPLE_VECTOR_MAX_LEVEL 4
#endif
#define SIMPLE_VECTOR_LEVEL_DECL(n) \
    uint64_t simple_bitmap_kernel_l##n(uint32_t,const uint32_t *,const uint32_t *,uint32_t *,size_t); \
    uint64_t simple_http_kernel_l##n(uint32_t,const uint8_t *,size_t,uint8_t,int64_t *);
#if defined(__x86_64__)
SIMPLE_VECTOR_LEVEL_DECL(1) SIMPLE_VECTOR_LEVEL_DECL(2)
SIMPLE_VECTOR_LEVEL_DECL(3) SIMPLE_VECTOR_LEVEL_DECL(4)
#elif defined(__aarch64__)
SIMPLE_VECTOR_LEVEL_DECL(1) SIMPLE_VECTOR_LEVEL_DECL(2) SIMPLE_VECTOR_LEVEL_DECL(3)
#elif defined(__riscv) && __riscv_xlen == 64
SIMPLE_VECTOR_LEVEL_DECL(1)
#endif
/* Highest level the CPU and OS both enable, capped by SIMPLE_VECTOR_MAX_LEVEL.
 * Computed once; never executes a wide instruction itself. */
int simple_vector_selected_level(void);
#endif
