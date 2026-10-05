#ifndef SIMPLE_BITMAP_KERNEL_PRIVATE_H
#define SIMPLE_BITMAP_KERNEL_PRIVATE_H
#include "../../simple_vector_kernel_abi_v1.h"
/* The guarded baseline owner is the only caller. Returns vector iterations. */
uint64_t simple_bitmap_kernel(uint32_t opcode,const uint32_t *left,
    const uint32_t *right,uint32_t *output,size_t words);
#endif
