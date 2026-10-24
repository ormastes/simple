/* Portable level kernel: plain C written so clang auto-vectorizes it for the
 * -march level this object is compiled with (x86-64 / -v2 / -v3). Blocks have
 * no early exit inside them, so the compare/reduce body vectorizes; a hit is
 * resolved by a scalar rescan of that one block. Returns block iterations,
 * the same unit the intrinsic kernels report. Build renames the entry points
 * per level (-Dsimple_bitmap_kernel=simple_bitmap_kernel_lN). */
#include "bitmap_kernel_private.h"

#define BITMAP_BLOCK_WORDS 16u
#define HTTP_BLOCK_BYTES 64u

uint64_t simple_bitmap_kernel(uint32_t op, const uint32_t *restrict left,
        const uint32_t *restrict right, uint32_t *restrict output, size_t words) {
    if (op != SIMPLE_VECTOR_BITMAP_AND_U32 && op != SIMPLE_VECTOR_BITMAP_OR_U32)
        return UINT64_MAX;
    size_t i = 0;
    uint64_t iterations = 0;
    if (op == SIMPLE_VECTOR_BITMAP_AND_U32) {
        for (; words - i >= BITMAP_BLOCK_WORDS; i += BITMAP_BLOCK_WORDS, ++iterations)
            for (size_t j = 0; j < BITMAP_BLOCK_WORDS; ++j)
                output[i + j] = left[i + j] & right[i + j];
    } else {
        for (; words - i >= BITMAP_BLOCK_WORDS; i += BITMAP_BLOCK_WORDS, ++iterations)
            for (size_t j = 0; j < BITMAP_BLOCK_WORDS; ++j)
                output[i + j] = left[i + j] | right[i + j];
    }
    for (; i < words; ++i)
        output[i] = op == SIMPLE_VECTOR_BITMAP_AND_U32 ? left[i] & right[i] : left[i] | right[i];
    return iterations;
}

/* No load crosses the borrowed span: CRLF blocks need 65 remaining bytes. */
uint64_t simple_http_kernel(uint32_t op, const uint8_t *input, size_t bytes,
        uint8_t needle, int64_t *found) {
    *found = -1;
    if (op != SIMPLE_VECTOR_HTTP_FIND_BYTE && op != SIMPLE_VECTOR_HTTP_FIND_CRLF)
        return UINT64_MAX;
    const size_t extra = op == SIMPLE_VECTOR_HTTP_FIND_CRLF ? 1 : 0;
    size_t i = 0;
    uint64_t iterations = 0;
    for (; bytes - i >= HTTP_BLOCK_BYTES + extra; i += HTTP_BLOCK_BYTES) {
        const uint8_t *p = input + i;
        uint8_t any = 0;
        if (extra) {
            for (size_t j = 0; j < HTTP_BLOCK_BYTES; ++j)
                any |= (uint8_t)((p[j] == '\r') & (p[j + 1] == '\n'));
        } else {
            for (size_t j = 0; j < HTTP_BLOCK_BYTES; ++j)
                any |= (uint8_t)(p[j] == needle);
        }
        ++iterations;
        if (any) {
            for (size_t j = 0; j < HTTP_BLOCK_BYTES; ++j)
                if (extra ? (p[j] == '\r' && p[j + 1] == '\n') : p[j] == needle) {
                    *found = (int64_t)(i + j);
                    return iterations;
                }
        }
    }
    for (; bytes - i > extra; ++i)
        if (extra ? (input[i] == '\r' && input[i + 1] == '\n') : input[i] == needle) {
            *found = (int64_t)i;
            break;
        }
    return iterations;
}
