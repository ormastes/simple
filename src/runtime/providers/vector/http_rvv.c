#include "bitmap_kernel_private.h"
#include <riscv_vector.h>
/* vl bounds candidate starts; CRLF's shifted LF load has the same vl. */
uint64_t simple_http_kernel(uint32_t op,const uint8_t *input,size_t bytes,
        uint8_t needle,int64_t *found) {
    *found=-1;
    if(op!=SIMPLE_VECTOR_HTTP_FIND_BYTE && op!=SIMPLE_VECTOR_HTTP_FIND_CRLF)
        return UINT64_MAX;
    const int pair=op==SIMPLE_VECTOR_HTTP_FIND_CRLF;
    const size_t candidates=pair?(bytes?bytes-1:0):bytes;
    size_t i=0; uint64_t iterations=0;
    while(i<candidates) {
        size_t vl=__riscv_vsetvl_e8m1(candidates-i);
        if(!vl) return UINT64_MAX;
        vuint8m1_t data=__riscv_vle8_v_u8m1(input+i,vl);
        vbool8_t hits=__riscv_vmseq_vx_u8m1_b8(data,pair?13:needle,vl);
        if(pair) {
            vbool8_t lf=__riscv_vmseq_vx_u8m1_b8(__riscv_vle8_v_u8m1(input+i+1,vl),10,vl);
            hits=__riscv_vmand_mm_b8(hits,lf,vl);
        }
        ++iterations;
        long first=__riscv_vfirst_m_b8(hits,vl);
        if(first>=0) { *found=(int64_t)(i+(size_t)first); return iterations; }
        i+=vl;
    }
    return iterations;
}
