/* Optional x86_64 AVX512F kernel TU. Compile separately from bitmap_provider.c
 * without global -mavx512 flags; the baseline dispatcher checks CPU and OS
 * state before calling this target-attributed function. */
#include "bitmap_kernel_private.h"
#include <immintrin.h>

#if !defined(__x86_64__) || !(defined(__GNUC__) || defined(__clang__))
#error "bitmap_avx512.c requires an x86_64 GCC/Clang target"
#endif

__attribute__((target("avx512f")))
uint64_t simple_bitmap_kernel(uint32_t op, const uint32_t *left,
        const uint32_t *right, uint32_t *output, size_t words) {
    if (op != SIMPLE_VECTOR_BITMAP_AND_U32 &&
            op != SIMPLE_VECTOR_BITMAP_OR_U32)
        return UINT64_MAX;

    size_t i = 0;
    uint64_t vector_iterations = 0;
    for (; words - i >= 16; i += 16) {
        const __m512i a = _mm512_loadu_si512((const void *)(left + i));
        const __m512i b = _mm512_loadu_si512((const void *)(right + i));
        const __m512i result = op == SIMPLE_VECTOR_BITMAP_AND_U32
            ? _mm512_and_si512(a, b)
            : _mm512_or_si512(a, b);
        _mm512_storeu_si512((void *)(output + i), result);
        ++vector_iterations;
    }
    for (; i < words; ++i) {
        output[i] = op == SIMPLE_VECTOR_BITMAP_AND_U32
            ? left[i] & right[i]
            : left[i] | right[i];
    }
    return vector_iterations;
}
