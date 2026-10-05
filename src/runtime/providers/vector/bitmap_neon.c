#include "bitmap_kernel_private.h"
#include <arm_neon.h>
uint64_t simple_bitmap_kernel(uint32_t op,const uint32_t *a,const uint32_t *b,
        uint32_t *out,size_t n) {
    size_t i=0; uint64_t iterations=0;
    for(;n-i>=4;i+=4) {
        uint32x4_t x=vld1q_u32(a+i),y=vld1q_u32(b+i);
        vst1q_u32(out+i,op==SIMPLE_VECTOR_BITMAP_AND_U32?vandq_u32(x,y):vorrq_u32(x,y));
        iterations++;
    }
    for(;i<n;i++) out[i]=op==SIMPLE_VECTOR_BITMAP_AND_U32?(a[i]&b[i]):(a[i]|b[i]);
    return iterations;
}
