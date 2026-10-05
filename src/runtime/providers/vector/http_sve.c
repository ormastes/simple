#include "bitmap_kernel_private.h"
#include <arm_sve.h>
/* Predicates cover candidate starts, not the full input for CRLF. The shifted
 * LF load therefore never activates a lane beyond the borrowed input span. */
uint64_t simple_http_kernel(uint32_t op,const uint8_t *input,size_t bytes,
        uint8_t needle,int64_t *found) {
    *found=-1;
    if(op!=SIMPLE_VECTOR_HTTP_FIND_BYTE && op!=SIMPLE_VECTOR_HTTP_FIND_CRLF)
        return UINT64_MAX;
    const int pair=op==SIMPLE_VECTOR_HTTP_FIND_CRLF;
    const size_t candidates=pair?(bytes?bytes-1:0):bytes;
    uint64_t iterations=0;
    for(size_t i=0;i<candidates;i+=svcntb()) {
        const svbool_t active=svwhilelt_b8_u64((uint64_t)i,(uint64_t)candidates);
        svbool_t hits=svcmpeq_n_u8(active,svld1_u8(active,input+i),pair?13:needle);
        if(pair) hits=svand_b_z(active,hits,svcmpeq_n_u8(active,svld1_u8(active,input+i+1),10));
        ++iterations;
        if(svptest_any(active,hits)) {
            *found=(int64_t)(i+svcntp_b8(active,svbrkb_z(active,hits)));
            return iterations;
        }
    }
    return iterations;
}
