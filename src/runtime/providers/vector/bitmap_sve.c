/* Scalable u32 bitmap operations shared by SVE and SVE2-required artifacts.
 * AND/OR need only SVE; compiling with +sve2 does not prove SVE2-only opcodes. */
#include "bitmap_kernel_private.h"
#include <arm_sve.h>
#if !defined(__aarch64__) || !defined(__ARM_FEATURE_SVE)
#error "bitmap_sve.c requires an AArch64 SVE target"
#endif
uint64_t simple_bitmap_kernel(uint32_t op, const uint32_t *left,
        const uint32_t *right, uint32_t *output, size_t words) {
    if(op!=SIMPLE_VECTOR_BITMAP_AND_U32 && op!=SIMPLE_VECTOR_BITMAP_OR_U32)
        return UINT64_MAX;
    uint64_t iterations=0;
    const size_t lanes=svcntw();
    for(size_t i=0;i<words;i+=lanes) {
        const svbool_t active=svwhilelt_b32_u64((uint64_t)i,(uint64_t)words);
        const svuint32_t a=svld1_u32(active,left+i);
        const svuint32_t b=svld1_u32(active,right+i);
        const svuint32_t value=op==SIMPLE_VECTOR_BITMAP_AND_U32
            ? svand_u32_x(active,a,b) : svorr_u32_x(active,a,b);
        svst1_u32(active,output+i,value);
        ++iterations;
    }
    return iterations;
}
