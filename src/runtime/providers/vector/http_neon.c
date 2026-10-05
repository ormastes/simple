#include "bitmap_kernel_private.h"
#include <arm_neon.h>
/* Sixteen candidate bytes; shifted CRLF load requires seventeen input bytes. */
uint64_t simple_http_kernel(uint32_t op,const uint8_t *input,size_t bytes,
        uint8_t needle,int64_t *found) {
    *found=-1;
    if(op!=SIMPLE_VECTOR_HTTP_FIND_BYTE && op!=SIMPLE_VECTOR_HTTP_FIND_CRLF)
        return UINT64_MAX;
    const size_t extra=op==SIMPLE_VECTOR_HTTP_FIND_CRLF?1:0;
    size_t i=0; uint64_t iterations=0;
    const uint8x16_t target=vdupq_n_u8(extra?13:needle);
    for(;bytes-i>=16+extra;i+=16) {
        uint8x16_t hits=vceqq_u8(vld1q_u8(input+i),target);
        if(extra) hits=vandq_u8(hits,vceqq_u8(vld1q_u8(input+i+1),vdupq_n_u8(10)));
        ++iterations;
        if(vmaxvq_u8(hits)) {
            uint8_t lanes[16]; vst1q_u8(lanes,hits);
            for(size_t lane=0;lane<16;lane++) if(lanes[lane]) {
                *found=(int64_t)(i+lane); return iterations;
            }
        }
    }
    for(;bytes-i>extra;i++) if(extra ? input[i]==13&&input[i+1]==10 : input[i]==needle) {
        *found=(int64_t)i; break;
    }
    return iterations;
}
