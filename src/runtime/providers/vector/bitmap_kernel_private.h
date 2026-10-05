#ifndef SIMPLE_BITMAP_KERNEL_PRIVATE_H
#define SIMPLE_BITMAP_KERNEL_PRIVATE_H
#include "../../simple_vector_kernel_abi_v1.h"
/* Preserve the original x86 build switch; other targets opt in explicitly. */
#if defined(SIMPLE_VECTOR_ENABLE_HTTP_AVX512) && !defined(SIMPLE_VECTOR_ENABLE_HTTP)
#define SIMPLE_VECTOR_ENABLE_HTTP 1
#endif
/* The guarded baseline owner is the only caller. Returns vector iterations. */
uint64_t simple_bitmap_kernel(uint32_t opcode,const uint32_t *left,
    const uint32_t *right,uint32_t *output,size_t words);
#ifdef SIMPLE_VECTOR_ENABLE_HTTP
uint64_t simple_http_kernel(uint32_t opcode,const uint8_t *input,size_t bytes,
    uint8_t needle,int64_t *found);
#endif
#endif
