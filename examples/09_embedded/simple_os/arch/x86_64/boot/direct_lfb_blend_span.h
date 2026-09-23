#ifndef SIMPLEOS_DIRECT_LFB_BLEND_SPAN_H
#define SIMPLEOS_DIRECT_LFB_BLEND_SPAN_H

#ifndef SIMPLEOS_LFB_DST_READ
#define SIMPLEOS_LFB_DST_READ(ptr) (*(ptr))
#endif
#ifndef SIMPLEOS_LFB_DST_WRITE
#define SIMPLEOS_LFB_DST_WRITE(ptr, value) (*(ptr) = (value))
#endif

static inline RuntimeValue _bm_direct_lfb_blend_span8(
    uint64_t registered_addr, uint32_t registered_width,
    uint32_t registered_height, uint32_t registered_pitch,
    RuntimeValue framebuffer_addr, RuntimeValue width, RuntimeValue height,
    RuntimeValue pitch, RuntimeValue xy, RuntimeValue src,
    RuntimeValue src_offset, RuntimeValue count)
{
    RuntimeArray *a = _bm_pixel_array_from_abi(src);
    uint32_t x = (uint32_t)((uint64_t)xy >> 32);
    uint32_t y = (uint32_t)(uint64_t)xy;
    int64_t off = (int64_t)src_offset;
    int64_t n = (int64_t)count;
    uint64_t row_bytes = (uint64_t)registered_width * sizeof(uint32_t);
    if ((uint64_t)framebuffer_addr != registered_addr ||
        (uint64_t)width != registered_width ||
        (uint64_t)height != registered_height ||
        (uint64_t)pitch != registered_pitch ||
        !a || a->hdr.type != HEAP_ARRAY || !registered_addr ||
        !registered_width || !registered_height ||
        registered_pitch < row_bytes ||
        registered_pitch % sizeof(uint32_t) != 0u ||
        x >= registered_width || y >= registered_height ||
        off < 0 || n <= 0 || (uint64_t)off > a->len ||
        (uint64_t)n > a->len - (uint64_t)off ||
        (uint64_t)n > (uint64_t)registered_width - x) return 0;

    RuntimeValue *items = runtime_array_items(a);
    if (!items) return 0;
    uint64_t row_offset = (uint64_t)y * registered_pitch;
    uint64_t pixel_offset = (uint64_t)x * sizeof(uint32_t);
    uint64_t span_bytes = (uint64_t)n * sizeof(uint32_t);
    if (row_offset > UINT64_MAX - pixel_offset) return 0;
    uint64_t byte_offset = row_offset + pixel_offset;
    if (byte_offset > UINTPTR_MAX ||
        span_bytes - 1u > UINTPTR_MAX - byte_offset ||
        registered_addr > UINTPTR_MAX - (byte_offset + span_bytes - 1u))
        return 0;
    volatile uint32_t *dst = (volatile uint32_t *)(uintptr_t)
                             (registered_addr + byte_offset);
    for (int64_t i = 0; i < n; i++) {
        uint32_t source = _bm_unbox_pixel(items[off + i]);
        uint32_t alpha = source >> 24;
        if (alpha == 0u) continue;
        if (alpha == 255u) {
            SIMPLEOS_LFB_DST_WRITE(dst + i, source);
            continue;
        }
        uint32_t destination = SIMPLEOS_LFB_DST_READ(dst + i);
        SIMPLEOS_LFB_DST_WRITE(dst + i,
                               _bm_blend_pixel(source, destination));
    }
    return 1;
}

#ifdef SIMPLEOS_DEFINE_RT_GUI_BLEND_SPAN8
RuntimeValue rt_gui_blend_span8(RuntimeValue framebuffer_addr, RuntimeValue width,
                                RuntimeValue height, RuntimeValue pitch,
                                RuntimeValue xy, RuntimeValue src,
                                RuntimeValue src_offset, RuntimeValue count)
{
    return _bm_direct_lfb_blend_span8(
        g_fb_addr, g_fb_width, g_fb_height, g_fb_pitch,
        framebuffer_addr, width, height, pitch, xy, src, src_offset, count);
}
#endif

#endif
