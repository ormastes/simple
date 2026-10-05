/* Test harness only: compile the unchanged production TU, call its real kernel. */
#include "runtime_simd_dispatch.c"
#include <inttypes.h>
#include <stdio.h>
#include <string.h>

static uint32_t oracle(uint32_t a, uint32_t b) {
    uint64_t result = 0, place = 1;
    for (unsigned bit = 0; bit < 32; ++bit) {
        if (a % 2 == 1 && b % 2 == 1) result += place;
        a /= 2; b /= 2; place *= 2;
    }
    return (uint32_t)result;
}

int main(void) {
#if !SIMD_CAN_AVX2
    fprintf(stderr, "UNSUPPORTED: production AVX512 kernel compiled out\n");
    return 77;
#else
    if (!db_bitmap_cpu_has_avx512f() || !rt_x86_avx512_os_state_usable()) {
        fprintf(stderr, "UNSUPPORTED: AVX512F CPU/OS-state guard failed\n");
        return 77;
    }
    void (*volatile kernel)(const int64_t*, const int64_t*, int64_t*, int64_t) = db_bitmap_and_avx512;
    const size_t lengths[] = {0,1,7,8,9,15,16,17,31,32,33,63,64,65,127,128,129};
    const uint32_t patterns[] = {0,1,UINT32_C(0x80000000),UINT32_MAX,UINT32_C(0xaaaaaaaa),UINT32_C(0x55555555)};
    const int64_t sentinel = INT64_C(0x6badf00d12345678);
    int64_t left[160], right[160], out[160], original_left[160], original_right[160];
    size_t cases = 0, words = 0, canaries = 0;
    for (size_t k=0; k<sizeof lengths/sizeof lengths[0]; ++k) {
        size_t n=lengths[k];
        for (size_t offset=0; offset<8; ++offset) {
            size_t begin=offset+1;
            for (size_t rotation=0; rotation<6; ++rotation) {
                for (size_t i=0; i<160; ++i) left[i]=right[i]=out[i]=sentinel;
                for (size_t i=0; i<n; ++i) {
                    left[begin+i]=(int64_t)((uint64_t)patterns[i%6]*8);
                    right[begin+i]=(int64_t)((uint64_t)patterns[(i+rotation)%6]*8);
                }
                memcpy(original_left,left,sizeof left); memcpy(original_right,right,sizeof right);
                kernel(left+begin,right+begin,out+begin,(int64_t)n);
                for (size_t i=0; i<n; ++i) {
                    int64_t expected=(int64_t)((uint64_t)oracle(patterns[i%6],patterns[(i+rotation)%6])*8);
                    if (out[begin+i]!=expected) {
                        fprintf(stderr,"FAIL n=%zu offset=%zu rotation=%zu word=%zu actual=%" PRId64 " expected=%" PRId64 "\n",n,offset,rotation,i,out[begin+i],expected);
                        return 1;
                    }
                    ++words;
                }
                for (size_t i=0; i<160; ++i) {
                    if ((i<begin || i>=begin+n) && out[i]!=sentinel) return 2;
                    if (left[i]!=original_left[i] || right[i]!=original_right[i]) return 3;
                    ++canaries;
                }
                ++cases;
            }
        }
    }
    printf("PASS forced_production_kernel=db_bitmap_and_avx512 cpu_avx512f=1 os_xstate=1 cases=%zu words=%zu canary_slots=%zu\n",cases,words,canaries);
    return 0;
#endif
}
