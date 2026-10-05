#include "bitmap_kernel_private.h"
#include <riscv_vector.h>
uint64_t simple_bitmap_kernel(uint32_t op,const uint32_t *a,const uint32_t *b,
        uint32_t *out,size_t n) {
    size_t i=0; uint64_t iterations=0;
    while(i<n) {
        size_t vl=__riscv_vsetvl_e32m1(n-i);
        if(!vl) return UINT64_MAX;
        vuint32m1_t x=__riscv_vle32_v_u32m1(a+i,vl),y=__riscv_vle32_v_u32m1(b+i,vl);
        vuint32m1_t z=op==SIMPLE_VECTOR_BITMAP_AND_U32?
            __riscv_vand_vv_u32m1(x,y,vl):__riscv_vor_vv_u32m1(x,y,vl);
        __riscv_vse32_v_u32m1(out+i,z,vl);
        i+=vl; iterations++;
    }
    return iterations;
}
