#include <stdint.h>
#include <stdio.h>

#include "runtime.h"

typedef struct {
    uint8_t kind;
    uint8_t flags;
    uint8_t reserved[6];
    int64_t len;
    int64_t cap;
    int64_t *data;
} TestArray;

int64_t rt_array_len(SplArray *array) {
    return ((TestArray *)array)->len;
}

int64_t rt_array_data_ptr(SplArray *array) {
    return (int64_t)(uintptr_t)((TestArray *)array)->data;
}

extern SplArray *rt_engine2d_simd_fill_span_u32(SplArray *, int64_t, int64_t, int64_t);
extern int64_t rt_simd_engine2d_neon_hits(void);
extern int64_t rt_simd_engine2d_neon_reset(void);

int main(void) {
    int64_t pixels[16] = {0};
    TestArray array = {0, 0, {0}, 16, 16, pixels};
    rt_simd_engine2d_neon_reset();
    SplArray *result = rt_engine2d_simd_fill_span_u32((SplArray *)&array, 8, 8, 0xff102030);
    if (result != (SplArray *)&array) return 1;
    if (pixels[7] != 0 || pixels[8] != 0xff102030 || pixels[15] != 0xff102030) return 2;
#if defined(__x86_64__) || defined(_M_X64) || defined(__aarch64__) || defined(_M_ARM64) || \
    (defined(__riscv) && defined(__riscv_vector))
    if (rt_simd_engine2d_neon_hits() <= 0) return 3;
#else
    if (rt_simd_engine2d_neon_hits() != 0) return 3;
#endif
    puts("ENGINE2D_SIMD_FILL_SPAN_TEST: PASS");
    return 0;
}
