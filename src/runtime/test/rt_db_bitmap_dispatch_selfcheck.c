#include "runtime.h"
#include <stdint.h>
#include <stdio.h>

extern SplArray* rt_db_bitmap_and_u32(SplArray*, SplArray*, int64_t);

static uint32_t expected_and(uint32_t a, uint32_t b) {
    uint64_t result=0, place=1;
    for (unsigned bit=0;bit<32;++bit) {
        if (a%2==1 && b%2==1) result+=place;
        a/=2; b/=2; place*=2;
    }
    return (uint32_t)result;
}

int main(void) {
    const size_t lengths[]={8,9,17};
    const uint32_t values[]={0,UINT32_MAX,UINT32_C(0x80000000),UINT32_C(0xaaaaaaaa),UINT32_C(0x55555555),1};
    size_t checked=0;
    for (size_t c=0;c<3;++c) {
        int64_t n=(int64_t)lengths[c];
        SplArray *left=rt_array_new(n), *right=rt_array_new(n);
        if (!left || !right) return 1;
        for (int64_t i=0;i<n;++i) {
            if (!rt_array_push(left,rt_value_int(values[i%6]))) return 2;
            if (!rt_array_push(right,rt_value_int(values[(i+2)%6]))) return 3;
        }
        SplArray *out=rt_db_bitmap_and_u32(left,right,n);
        if (!out || out==left || out==right || rt_array_len(out)!=n) return 4;
        for (int64_t i=0;i<n;++i) {
            uint32_t a=values[i%6], b=values[(i+2)%6];
            if (rt_array_get(out,i)!=rt_value_int(expected_and(a,b))) return 5;
            if (rt_array_get(left,i)!=rt_value_int(a) || rt_array_get(right,i)!=rt_value_int(b)) return 6;
            ++checked;
        }
    }
    printf("PASS public_rt_db_bitmap_and_u32 arrays=6 cases=3 word_checks=%zu input_preservation=1 fresh_output=1\n",checked);
    return 0;
}
