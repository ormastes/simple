#include "runtime.h"

#include <stdbool.h>
#include <stdint.h>
#include <string.h>

void rt_fb_fill32(uint64_t dst_addr, uint64_t pixel_count, uint64_t color) {
    if (dst_addr == 0 || pixel_count == 0 || pixel_count > SIZE_MAX / sizeof(uint32_t)) {
        return;
    }

    uint8_t* dst = (uint8_t*)(uintptr_t)dst_addr;
    const uint32_t pixel = (uint32_t)color;
    for (size_t i = 0; i < (size_t)pixel_count; i++) {
        memcpy(dst + i * sizeof(pixel), &pixel, sizeof(pixel));
    }
}

void rt_fb_blit32(uint64_t dst_addr, uint64_t dst_stride_pixels,
                  uint64_t src_addr, uint64_t src_stride_pixels,
                  uint64_t copy_w, uint64_t copy_h) {
    if (dst_addr == 0 || src_addr == 0 || copy_w == 0 || copy_h == 0 ||
        dst_stride_pixels < copy_w || src_stride_pixels < copy_w ||
        copy_w > SIZE_MAX / sizeof(uint32_t)) {
        return;
    }

    const size_t row_bytes = (size_t)copy_w * sizeof(uint32_t);
    if (copy_h - 1 > SIZE_MAX / sizeof(uint32_t) / dst_stride_pixels ||
        copy_h - 1 > SIZE_MAX / sizeof(uint32_t) / src_stride_pixels) {
        return;
    }
    const size_t dst_last_offset = (size_t)(copy_h - 1) * (size_t)dst_stride_pixels * sizeof(uint32_t);
    const size_t src_last_offset = (size_t)(copy_h - 1) * (size_t)src_stride_pixels * sizeof(uint32_t);
    if (dst_last_offset > SIZE_MAX - row_bytes || src_last_offset > SIZE_MAX - row_bytes ||
        dst_addr > UINTPTR_MAX - (dst_last_offset + row_bytes) ||
        src_addr > UINTPTR_MAX - (src_last_offset + row_bytes)) {
        return;
    }

    uint8_t* dst = (uint8_t*)(uintptr_t)dst_addr;
    const uint8_t* src = (const uint8_t*)(uintptr_t)src_addr;
    const uintptr_t src_end = (uintptr_t)src + src_last_offset + row_bytes;
    const bool copy_bottom_up = (uintptr_t)dst > (uintptr_t)src && (uintptr_t)dst < src_end;

    for (size_t row_index = 0; row_index < (size_t)copy_h; row_index++) {
        const size_t row = copy_bottom_up ? (size_t)copy_h - 1 - row_index : row_index;
        memmove(dst + row * (size_t)dst_stride_pixels * sizeof(uint32_t),
                src + row * (size_t)src_stride_pixels * sizeof(uint32_t),
                row_bytes);
    }
}
