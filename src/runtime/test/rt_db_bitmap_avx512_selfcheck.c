/* Actual default C public APIs; no copied dispatch/kernel implementation. */
#include "runtime.h"
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
extern SplArray *rt_db_bitmap_and_u32(SplArray*,SplArray*,int64_t);
extern SplArray *rt_engine2d_blend_mask_span_u32(SplArray*,int64_t,SplArray*,int64_t,int64_t,int64_t);
extern SplArray *rt_engine2d_blend_cov_span_u32(SplArray*,int64_t,SplArray*,int64_t,int64_t,int64_t);
extern SplArray *rt_bytes_alloc(int64_t);
extern int8_t rt_bytes_u8_set(SplArray*,int64_t,int64_t);
static unsigned checks;
#define CHECK(c) do { ++checks; if (!(c)) { fprintf(stderr,"FAIL line=%d check=%u\n",__LINE__,checks); return 1; } } while(0)
static uint32_t pixel(unsigned i) { return (i*UINT32_C(0x17234567)) ^ UINT32_C(0x1280ff00); }
static uint32_t blend(uint32_t d,uint32_t s,int a,int scale) {
    if (!a) return d;
    uint32_t out=0xff000000u;
    for(int shift=0;shift<=16;shift+=8)
        out|=(uint32_t)((((s>>shift)&255)*a+((d>>shift)&255)*(scale-a))/scale)<<shift;
    return out;
}
int main(void) {
    const int lengths[]={1,3,4,7,8,9,17,65};
    const unsigned masks[]={0,1,127,254,255};
    const int32_t covers[]={-256,-1,0,1,128,255,256};
    for(unsigned c=0;c<sizeof(lengths)/sizeof(*lengths);++c) {
        int n=lengths[c];
        SplArray *d=rt_array_new(n+2),*r=rt_array_new(n+2),*m=rt_array_new(n+2),*p=rt_bytes_alloc(n+2),*cov=rt_array_new(n);
        CHECK(d&&r&&m&&p&&cov);
        for(int i=0;i<n+2;++i) {
            CHECK(rt_array_push(d,rt_value_int(pixel(i))));
            CHECK(rt_array_push(r,rt_value_int(~pixel(i))));
            CHECK(rt_array_push(m,rt_value_int(masks[i%5])));
            CHECK(rt_bytes_u8_set(p,i,masks[i%5]));
            if(i<n) CHECK(rt_array_push(cov,rt_value_int(covers[i%7])));
        }
        CHECK(!rt_db_bitmap_and_u32(d,r,0));
        SplArray *b=rt_db_bitmap_and_u32(d,r,n);
        CHECK(b&&b!=d&&b!=r&&rt_array_len(b)==n);
        for(int i=0;i<n;++i) CHECK(rt_array_get(b,i)==rt_value_int(0));
        /* Add non-complement operands/high bits, preserving fresh output semantics. */
        b=rt_db_bitmap_and_u32(d,d,n);
        CHECK(b&&b!=d&&rt_array_len(b)==n);
        for(int i=0;i<n;++i) CHECK(rt_array_get(b,i)==rt_value_int(pixel(i)));
        for(int packed=0;packed<2;++packed) {
            SplArray *out=rt_engine2d_blend_mask_span_u32(d,1,packed?p:m,1,n,0x91a2b3);
            CHECK(out&&out!=d&&rt_array_len(out)==n);
            for(int i=0;i<n;++i) CHECK(rt_array_get(out,i)==rt_value_int(blend(pixel(i+1),0x91a2b3,masks[(i+1)%5],255)));
        }
        SplArray *out=rt_engine2d_blend_cov_span_u32(d,1,cov,n,256*1024+255,0x91a2b3);
        CHECK(out&&out!=d&&rt_array_len(out)==n);
        for(int i=0;i<n;++i) CHECK(rt_array_get(out,i)==rt_value_int(blend(pixel(i+1),0x91a2b3,covers[i%7]>0?covers[i%7]:0,256)));
        for(int i=0;i<n+2;++i) {
            CHECK(rt_array_get(d,i)==rt_value_int(pixel(i)));
            CHECK(rt_array_get(r,i)==rt_value_int(~pixel(i)));
            CHECK(rt_array_get(m,i)==rt_value_int(masks[i%5]));
        }
    }
    printf("PASS default_c_public_apis cases=8 checks=%u bitmap_and=1 mask_packed=1 mask_slots=1 signed_coverage=1 inputs_preserved=1\n",checks);
    return 0;
}