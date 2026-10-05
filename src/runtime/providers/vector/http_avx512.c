/* AVX512BW is independently admitted by the baseline provider. No wide load
 * crosses the borrowed span: CRLF uses 64 candidate starts only with >=65
 * bytes remaining, so the shifted LF load is also entirely within bounds. */
#include "bitmap_kernel_private.h"
#include <immintrin.h>
#if !defined(__x86_64__) || !(defined(__GNUC__) || defined(__clang__))
#error "HTTP AVX512 kernel requires x86_64 GCC/Clang"
#endif
__attribute__((target("avx512f,avx512bw")))
uint64_t simple_http_kernel(uint32_t op,const uint8_t *input,size_t bytes,
        uint8_t needle,int64_t *found) {
    *found=-1;
    size_t i=0; uint64_t iterations=0;
    if(op==SIMPLE_VECTOR_HTTP_FIND_BYTE) {
        const __m512i target=_mm512_set1_epi8((char)needle);
        for(;bytes-i>=64;i+=64) {
            const __m512i data=_mm512_loadu_si512((const void *)(input+i));
            const uint64_t hits=(uint64_t)_mm512_cmpeq_epi8_mask(data,target);
            ++iterations;
            if(hits) { *found=(int64_t)(i+(size_t)__builtin_ctzll(hits)); return iterations; }
        }
        for(;i<bytes;i++) if(input[i]==needle) { *found=(int64_t)i; break; }
    } else if(op==SIMPLE_VECTOR_HTTP_FIND_CRLF) {
        const __m512i cr=_mm512_set1_epi8('\r'),lf=_mm512_set1_epi8('\n');
        for(;bytes-i>=65;i+=64) {
            const __m512i first=_mm512_loadu_si512((const void *)(input+i));
            const __m512i second=_mm512_loadu_si512((const void *)(input+i+1));
            const uint64_t hits=(uint64_t)(_mm512_cmpeq_epi8_mask(first,cr)&_mm512_cmpeq_epi8_mask(second,lf));
            ++iterations;
            if(hits) { *found=(int64_t)(i+(size_t)__builtin_ctzll(hits)); return iterations; }
        }
        for(;bytes-i>=2;i++) if(input[i]=='\r'&&input[i+1]=='\n') { *found=(int64_t)i; break; }
    } else return UINT64_MAX;
    return iterations;
}
