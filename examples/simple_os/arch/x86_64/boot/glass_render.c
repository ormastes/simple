/*
 * Glass Rendering Primitives for SimpleOS
 *
 * Alpha blending, box blur, gradients, and shadows for glassmorphism UI.
 *
 * ACCELERATION STRATEGY:
 *   All effects operate on a CPU-side shadow buffer (g_shadow_buf) in normal
 *   RAM -- NOT on MMIO framebuffer directly. This avoids the massive penalty
 *   of volatile MMIO reads (each one traps into QEMU host), which makes blur
 *   (millions of reads) practical.
 *
 *   Rendering flow:
 *     1. rt_gui_begin_frame() — copies MMIO framebuffer → shadow buffer
 *        (or just clears if starting fresh)
 *     2. All rt_gui_* effects operate on shadow buffer (fast RAM access)
 *     3. rt_gui_present() — bulk-copies shadow buffer → MMIO framebuffer
 *        (single memcpy, or dirty-rect transfer for partial updates)
 *
 *   For VirtIO-GPU: shadow buffer IS the DMA backing memory, so
 *   present() just calls TRANSFER_TO_HOST_2D + RESOURCE_FLUSH.
 *
 * Packing convention (same as rt_gui_fill4):
 *   xy = (x << 32) | y
 *   wh = (w << 32) | h
 */

#include <stdint.h>
#include <stddef.h>

typedef int64_t RuntimeValue;

/* Globals from baremetal_stubs.c */
extern uint64_t g_fb_addr;
extern uint64_t g_fb_w;
extern void *malloc(size_t);

/* Screen dimensions */
#define SCREEN_W_MAX 1024
#define SCREEN_H 768

/* ===================================================================
 * Shadow buffer — CPU-side framebuffer for fast read/write
 *
 * The MMIO framebuffer (g_fb_addr) is mapped to device memory. Each
 * read/write is a volatile operation that traps into QEMU. The shadow
 * buffer lives in normal RAM where reads are ~100x faster.
 *
 * Dirty tracking: g_dirty_* records the bounding box of all writes
 * since last present(), enabling partial MMIO transfer.
 * =================================================================== */

static uint32_t *g_shadow_buf = 0;
static uint32_t  g_shadow_w = 0;
static uint32_t  g_shadow_h = 0;
static int       g_shadow_ready = 0;

/* Dirty region tracking for partial present */
static uint32_t g_dirty_x1 = 0xFFFFFFFF;
static uint32_t g_dirty_y1 = 0xFFFFFFFF;
static uint32_t g_dirty_x2 = 0;
static uint32_t g_dirty_y2 = 0;

/* VirtIO-GPU acceleration flag — set by Simple code when GPU detected.
 * When enabled, present() uses the shadow buffer as DMA backing memory
 * and skips the MMIO memcpy (QEMU reads from DMA directly). */
static int g_use_virtio_gpu = 0;
static uint64_t g_virtio_gpu_resource_id = 0;

/* Called from Simple code to enable GPU-accelerated present */
RuntimeValue rt_gui_set_gpu_mode(RuntimeValue enabled, RuntimeValue resource_id,
                                  RuntimeValue unused1, RuntimeValue unused2)
{
    (void)unused1; (void)unused2;
    g_use_virtio_gpu = (int)(uint64_t)enabled;
    g_virtio_gpu_resource_id = (uint64_t)resource_id;
    return 0;
}

static void dirty_mark(uint32_t x, uint32_t y, uint32_t w, uint32_t h)
{
    if (x < g_dirty_x1) g_dirty_x1 = x;
    if (y < g_dirty_y1) g_dirty_y1 = y;
    uint32_t x2 = x + w;
    uint32_t y2 = y + h;
    if (x2 > g_dirty_x2) g_dirty_x2 = x2;
    if (y2 > g_dirty_y2) g_dirty_y2 = y2;
}

static void dirty_reset(void)
{
    g_dirty_x1 = 0xFFFFFFFF;
    g_dirty_y1 = 0xFFFFFFFF;
    g_dirty_x2 = 0;
    g_dirty_y2 = 0;
}

/* ===================================================================
 * Pixel helpers — operate on shadow buffer (fast) or MMIO (fallback)
 * =================================================================== */

static inline uint32_t fb_read(uint32_t x, uint32_t y)
{
    if (g_shadow_ready && x < g_shadow_w && y < g_shadow_h)
        return g_shadow_buf[y * g_shadow_w + x];
    /* Fallback to MMIO (slow) */
    uint64_t off = ((uint64_t)y * g_fb_w + x) * 4;
    return *(volatile uint32_t *)(uintptr_t)(g_fb_addr + off);
}

static inline void fb_write(uint32_t x, uint32_t y, uint32_t color)
{
    if (g_shadow_ready && x < g_shadow_w && y < g_shadow_h) {
        g_shadow_buf[y * g_shadow_w + x] = color;
        return;
    }
    /* Fallback to MMIO (slow) */
    uint64_t off = ((uint64_t)y * g_fb_w + x) * 4;
    *(volatile uint32_t *)(uintptr_t)(g_fb_addr + off) = color;
}

/* ===================================================================
 * Frame lifecycle — begin_frame / present
 * =================================================================== */

/* rt_gui_begin_frame(width, height, _, _)
 * Allocates shadow buffer (once) and marks frame start.
 * Call before any rendering. */
RuntimeValue rt_gui_begin_frame(RuntimeValue w_rv, RuntimeValue h_rv,
                                 RuntimeValue unused1, RuntimeValue unused2)
{
    (void)unused1; (void)unused2;
    uint32_t w = (uint32_t)(uint64_t)w_rv;
    uint32_t h = (uint32_t)(uint64_t)h_rv;
    if (w > SCREEN_W_MAX) w = SCREEN_W_MAX;
    if (h > SCREEN_H) h = SCREEN_H;

    /* Allocate shadow buffer once */
    if (!g_shadow_buf || g_shadow_w != w || g_shadow_h != h) {
        g_shadow_buf = (uint32_t *)malloc((size_t)w * h * 4);
        g_shadow_w = w;
        g_shadow_h = h;
    }
    if (!g_shadow_buf) return 0;

    g_shadow_ready = 1;
    dirty_reset();
    return 0;
}

/* rt_gui_present(_, _, _, _)
 * Copies shadow buffer to MMIO framebuffer.
 * Uses dirty rect tracking: only copies changed region.
 * TODO: GPU_ACCEL — for VirtIO-GPU, call TRANSFER_TO_HOST_2D + FLUSH
 *       with dirty rect bounds instead of MMIO memcpy. */
RuntimeValue rt_gui_present(RuntimeValue unused1, RuntimeValue unused2,
                             RuntimeValue unused3, RuntimeValue unused4)
{
    (void)unused1; (void)unused2; (void)unused3; (void)unused4;
    if (!g_shadow_ready || !g_shadow_buf) return 0;

    /* GPU fast path: shadow buffer IS the DMA backing.
     * Just signal the GPU to read from DMA (no copy needed).
     * TODO: GPU_ACCEL — call VirtIO-GPU TRANSFER_TO_HOST_2D + RESOURCE_FLUSH
     * This requires the VirtIO controlq to be accessible from C.
     * For now, the Simple-side GpuAccelerator.present_dirty() handles this. */
    if (g_use_virtio_gpu) {
        /* When GPU mode is active, the shadow buffer was allocated at the
         * GPU DMA address. No MMIO copy needed — return immediately.
         * The Simple code calls gpu.flush_rect() after present(). */
        dirty_reset();
        return 0;
    }

    /* Determine transfer region */
    uint32_t x1 = 0, y1 = 0, x2 = g_shadow_w, y2 = g_shadow_h;
    if (g_dirty_x1 < g_dirty_x2 && g_dirty_y1 < g_dirty_y2) {
        /* Use dirty rect (clamped) */
        x1 = g_dirty_x1;
        y1 = g_dirty_y1;
        x2 = g_dirty_x2 < g_shadow_w ? g_dirty_x2 : g_shadow_w;
        y2 = g_dirty_y2 < g_shadow_h ? g_dirty_y2 : g_shadow_h;
    }

    /* Bulk copy dirty region to MMIO framebuffer (row by row) */
    for (uint32_t row = y1; row < y2; row++) {
        uint64_t mmio_row = g_fb_addr + ((uint64_t)row * g_fb_w + x1) * 4;
        uint32_t *src_row = &g_shadow_buf[row * g_shadow_w + x1];
        uint32_t cols = x2 - x1;
        for (uint32_t col = 0; col < cols; col++) {
            *(volatile uint32_t *)(uintptr_t)(mmio_row + col * 4) = src_row[col];
        }
    }

    dirty_reset();
    return 0;
}

/* Alpha blend: dst over src with alpha [0..255]
 * result = (src * alpha + dst * (255 - alpha)) / 255
 * Uses (x + 128) >> 8 approximation for speed */
static inline uint32_t alpha_blend(uint32_t dst, uint32_t src, uint8_t alpha)
{
    if (alpha == 255) return src;
    if (alpha == 0) return dst;

    uint32_t inv = 255 - alpha;

    uint32_t sr = (src >> 16) & 0xFF;
    uint32_t sg = (src >> 8) & 0xFF;
    uint32_t sb = src & 0xFF;

    uint32_t dr = (dst >> 16) & 0xFF;
    uint32_t dg = (dst >> 8) & 0xFF;
    uint32_t db = dst & 0xFF;

    uint32_t rr = (sr * alpha + dr * inv + 128) >> 8;
    uint32_t rg = (sg * alpha + dg * inv + 128) >> 8;
    uint32_t rb = (sb * alpha + db * inv + 128) >> 8;

    return 0xFF000000u | (rr << 16) | (rg << 8) | rb;
}

/* Linear interpolation between two colors */
static inline uint32_t lerp_color(uint32_t c1, uint32_t c2, uint32_t t, uint32_t max)
{
    if (max == 0) return c1;
    uint32_t r1 = (c1 >> 16) & 0xFF, g1 = (c1 >> 8) & 0xFF, b1 = c1 & 0xFF;
    uint32_t r2 = (c2 >> 16) & 0xFF, g2 = (c2 >> 8) & 0xFF, b2 = c2 & 0xFF;
    uint32_t r = r1 + ((r2 - r1) * t + max / 2) / max;
    uint32_t g = g1 + ((g2 - g1) * t + max / 2) / max;
    uint32_t b = b1 + ((b2 - b1) * t + max / 2) / max;
    /* Clamp (handles underflow from unsigned subtraction) */
    if (r > 255) r = (r2 > r1) ? 255 : 0;
    if (g > 255) g = (g2 > g1) ? 255 : 0;
    if (b > 255) b = (b2 > b1) ? 255 : 0;
    return 0xFF000000u | (r << 16) | (g << 8) | b;
}

/* ===================================================================
 * 1. Alpha-blended rectangle fill
 *    rt_gui_blend_fill(xy, wh, color, alpha)
 *    // TODO: GPU_ACCEL — offload to GPU blit with per-pixel alpha
 * =================================================================== */

RuntimeValue rt_gui_blend_fill(RuntimeValue xy, RuntimeValue wh,
                                RuntimeValue color_rv, RuntimeValue alpha_rv)
{
    uint32_t x = (uint32_t)((uint64_t)xy >> 32);
    uint32_t y = (uint32_t)((uint64_t)xy & 0xFFFFFFFF);
    uint32_t w = (uint32_t)((uint64_t)wh >> 32);
    uint32_t h = (uint32_t)((uint64_t)wh & 0xFFFFFFFF);
    uint32_t src = (uint32_t)(uint64_t)color_rv;
    uint8_t  alpha = (uint8_t)(uint64_t)alpha_rv;

    /* Clamp to screen */
    if (x >= g_fb_w || y >= SCREEN_H) return 0;
    if (x + w > g_fb_w) w = (uint32_t)g_fb_w - x;
    if (y + h > SCREEN_H) h = SCREEN_H - y;

    dirty_mark(x, y, w, h);

    for (uint32_t row = 0; row < h; row++) {
        for (uint32_t col = 0; col < w; col++) {
            uint32_t dst = fb_read(x + col, y + row);
            fb_write(x + col, y + row, alpha_blend(dst, src, alpha));
        }
    }
    return 0;
}

/* ===================================================================
 * 24. Noise texture blend — adds ordered dither noise to glass surfaces
 *     rt_gui_noise_blend(xy, wh, intensity, unused)
 *     Adds a subtle noise pattern (like macOS frosted glass grain)
 * =================================================================== */
RuntimeValue rt_gui_noise_blend(RuntimeValue xy, RuntimeValue wh,
                                 RuntimeValue intensity_rv, RuntimeValue unused)
{
    (void)unused;
    uint32_t x = (uint32_t)((uint64_t)xy >> 32);
    uint32_t y = (uint32_t)((uint64_t)xy & 0xFFFFFFFF);
    uint32_t w = (uint32_t)((uint64_t)wh >> 32);
    uint32_t h = (uint32_t)((uint64_t)wh & 0xFFFFFFFF);
    uint8_t intensity = (uint8_t)(uint64_t)intensity_rv;

    if (x >= g_fb_w || y >= SCREEN_H || w == 0 || h == 0) return 0;

    dirty_mark(x, y, w, h);

    /* Pseudo-random noise using hash function */
    for (uint32_t row = 0; row < h; row++) {
        uint32_t py = y + row;
        if (py >= SCREEN_H) break;
        for (uint32_t col = 0; col < w; col++) {
            uint32_t px = x + col;
            if (px >= g_fb_w) break;

            /* Simple hash for pseudo-random noise */
            uint32_t hash = (px * 2654435761u) ^ (py * 2246822519u);
            hash = ((hash >> 16) ^ hash) * 0x45d9f3b;
            hash = ((hash >> 16) ^ hash);

            /* Only apply to ~30% of pixels for subtlety */
            if ((hash & 7) < 3) {
                uint32_t dst = fb_read(px, py);
                uint8_t noise_val = (hash >> 8) & 1; /* 0 or 1 = darken or lighten */
                uint32_t noise_color = noise_val ? 0x00FFFFFF : 0x00000000;
                fb_write(px, py, alpha_blend(dst, noise_color, intensity));
            }
        }
    }
    return 0;
}

/* ===================================================================
 * 2. Single pixel alpha blend
 *    rt_gui_blend_pixel(pack(x,y), pack(color,alpha), _, _)
 * =================================================================== */

RuntimeValue rt_gui_blend_pixel(RuntimeValue x_y, RuntimeValue color_alpha,
                                 RuntimeValue unused1, RuntimeValue unused2)
{
    (void)unused1; (void)unused2;
    uint32_t x = (uint32_t)((uint64_t)x_y >> 32);
    uint32_t y = (uint32_t)((uint64_t)x_y & 0xFFFFFFFF);
    uint32_t src = (uint32_t)((uint64_t)color_alpha >> 32);
    uint8_t  alpha = (uint8_t)((uint64_t)color_alpha & 0xFF);

    if (x >= g_fb_w || y >= SCREEN_H) return 0;
    uint32_t dst = fb_read(x, y);
    fb_write(x, y, alpha_blend(dst, src, alpha));
    return 0;
}

/* ===================================================================
 * 3. Box blur (3-pass approximation of Gaussian)
 *    rt_gui_box_blur(xy, wh, radius, _)
 *    // TODO: GPU_ACCEL — offload to GPU compute shader (10-50x speedup)
 * =================================================================== */

/* Scratch buffer for blur passes — static to avoid stack overflow.
 * Max dimension = 1024 pixels. */
static uint32_t blur_row_r[1024];
static uint32_t blur_row_g[1024];
static uint32_t blur_row_b[1024];

static void box_blur_h(uint32_t x0, uint32_t y0, uint32_t w, uint32_t h, uint32_t r)
{
    if (r == 0 || w == 0) return;
    uint32_t d = 2 * r + 1;

    for (uint32_t row = 0; row < h; row++) {
        uint32_t py = y0 + row;
        if (py >= SCREEN_H) break;

        /* Build initial accumulator for first pixel */
        uint32_t acc_r = 0, acc_g = 0, acc_b = 0;
        for (uint32_t i = 0; i < d && i < w; i++) {
            uint32_t px = x0 + (i < r ? 0 : i - r);
            if (px >= g_fb_w) px = (uint32_t)g_fb_w - 1;
            uint32_t c = fb_read(px, py);
            acc_r += (c >> 16) & 0xFF;
            acc_g += (c >> 8) & 0xFF;
            acc_b += c & 0xFF;
        }

        /* Slide window across row */
        for (uint32_t col = 0; col < w; col++) {
            blur_row_r[col] = acc_r / d;
            blur_row_g[col] = acc_g / d;
            blur_row_b[col] = acc_b / d;

            /* Remove left pixel, add right pixel */
            int32_t left = (int32_t)(x0 + col) - (int32_t)r;
            int32_t right = (int32_t)(x0 + col) + (int32_t)r + 1;
            if (left < (int32_t)x0) left = (int32_t)x0;
            if (right >= (int32_t)g_fb_w) right = (int32_t)g_fb_w - 1;
            if (right >= (int32_t)(x0 + w)) right = (int32_t)(x0 + w - 1);

            uint32_t cl = fb_read((uint32_t)left, py);
            uint32_t cr = fb_read((uint32_t)right, py);
            acc_r += ((cr >> 16) & 0xFF) - ((cl >> 16) & 0xFF);
            acc_g += ((cr >> 8) & 0xFF) - ((cl >> 8) & 0xFF);
            acc_b += (cr & 0xFF) - (cl & 0xFF);
        }

        /* Write blurred row back */
        for (uint32_t col = 0; col < w; col++) {
            uint32_t px = x0 + col;
            if (px >= g_fb_w) break;
            fb_write(px, py,
                0xFF000000u | (blur_row_r[col] << 16) | (blur_row_g[col] << 8) | blur_row_b[col]);
        }
    }
}

static void box_blur_v(uint32_t x0, uint32_t y0, uint32_t w, uint32_t h, uint32_t r)
{
    if (r == 0 || h == 0) return;
    uint32_t d = 2 * r + 1;

    for (uint32_t col = 0; col < w; col++) {
        uint32_t px = x0 + col;
        if (px >= g_fb_w) break;

        uint32_t acc_r = 0, acc_g = 0, acc_b = 0;
        for (uint32_t i = 0; i < d && i < h; i++) {
            uint32_t py = y0 + (i < r ? 0 : i - r);
            if (py >= SCREEN_H) py = SCREEN_H - 1;
            uint32_t c = fb_read(px, py);
            acc_r += (c >> 16) & 0xFF;
            acc_g += (c >> 8) & 0xFF;
            acc_b += c & 0xFF;
        }

        /* Use blur_row arrays as column buffer (max 768 < 1024) */
        for (uint32_t row = 0; row < h; row++) {
            blur_row_r[row] = acc_r / d;
            blur_row_g[row] = acc_g / d;
            blur_row_b[row] = acc_b / d;

            int32_t top = (int32_t)(y0 + row) - (int32_t)r;
            int32_t bot = (int32_t)(y0 + row) + (int32_t)r + 1;
            if (top < (int32_t)y0) top = (int32_t)y0;
            if (bot >= (int32_t)SCREEN_H) bot = SCREEN_H - 1;
            if (bot >= (int32_t)(y0 + h)) bot = (int32_t)(y0 + h - 1);

            uint32_t ct = fb_read(px, (uint32_t)top);
            uint32_t cb = fb_read(px, (uint32_t)bot);
            acc_r += ((cb >> 16) & 0xFF) - ((ct >> 16) & 0xFF);
            acc_g += ((cb >> 8) & 0xFF) - ((ct >> 8) & 0xFF);
            acc_b += (cb & 0xFF) - (ct & 0xFF);
        }

        for (uint32_t row = 0; row < h; row++) {
            uint32_t py = y0 + row;
            if (py >= SCREEN_H) break;
            fb_write(px, py,
                0xFF000000u | (blur_row_r[row] << 16) | (blur_row_g[row] << 8) | blur_row_b[row]);
        }
    }
}

RuntimeValue rt_gui_box_blur(RuntimeValue xy, RuntimeValue wh,
                              RuntimeValue radius_rv, RuntimeValue unused)
{
    (void)unused;
    uint32_t x = (uint32_t)((uint64_t)xy >> 32);
    uint32_t y = (uint32_t)((uint64_t)xy & 0xFFFFFFFF);
    uint32_t w = (uint32_t)((uint64_t)wh >> 32);
    uint32_t h = (uint32_t)((uint64_t)wh & 0xFFFFFFFF);
    uint32_t r = (uint32_t)(uint64_t)radius_rv;

    if (r == 0 || w == 0 || h == 0) return 0;
    if (r > 20) r = 20; /* Clamp kernel to 41 (radius 20) — prevents artifacts with large blurs */
    if (x >= g_fb_w || y >= SCREEN_H) return 0;
    if (x + w > g_fb_w) w = (uint32_t)g_fb_w - x;
    if (y + h > SCREEN_H) h = SCREEN_H - y;

    /* 3-pass box blur: H -> V -> H (approximates Gaussian) */
    box_blur_h(x, y, w, h, r);
    box_blur_v(x, y, w, h, r);
    box_blur_h(x, y, w, h, r);

    return 0;
}

/* ===================================================================
 * 4. Horizontal linear gradient
 *    rt_gui_gradient_h(xy, wh, color1, color2)
 *    // TODO: GPU_ACCEL — trivially parallelizable pixel shader
 * =================================================================== */

RuntimeValue rt_gui_gradient_h(RuntimeValue xy, RuntimeValue wh,
                                RuntimeValue c1_rv, RuntimeValue c2_rv)
{
    uint32_t x = (uint32_t)((uint64_t)xy >> 32);
    uint32_t y = (uint32_t)((uint64_t)xy & 0xFFFFFFFF);
    uint32_t w = (uint32_t)((uint64_t)wh >> 32);
    uint32_t h = (uint32_t)((uint64_t)wh & 0xFFFFFFFF);
    uint32_t c1 = (uint32_t)(uint64_t)c1_rv;
    uint32_t c2 = (uint32_t)(uint64_t)c2_rv;

    if (x >= g_fb_w || y >= SCREEN_H) return 0;
    if (x + w > g_fb_w) w = (uint32_t)g_fb_w - x;
    if (y + h > SCREEN_H) h = SCREEN_H - y;

    for (uint32_t col = 0; col < w; col++) {
        uint32_t color = lerp_color(c1, c2, col, w > 1 ? w - 1 : 1);
        for (uint32_t row = 0; row < h; row++) {
            fb_write(x + col, y + row, color);
        }
    }
    return 0;
}

/* ===================================================================
 * 5. Vertical linear gradient
 *    rt_gui_gradient_v(xy, wh, color1, color2)
 *    // TODO: GPU_ACCEL — trivially parallelizable pixel shader
 * =================================================================== */

RuntimeValue rt_gui_gradient_v(RuntimeValue xy, RuntimeValue wh,
                                RuntimeValue c1_rv, RuntimeValue c2_rv)
{
    uint32_t x = (uint32_t)((uint64_t)xy >> 32);
    uint32_t y = (uint32_t)((uint64_t)xy & 0xFFFFFFFF);
    uint32_t w = (uint32_t)((uint64_t)wh >> 32);
    uint32_t h = (uint32_t)((uint64_t)wh & 0xFFFFFFFF);
    uint32_t c1 = (uint32_t)(uint64_t)c1_rv;
    uint32_t c2 = (uint32_t)(uint64_t)c2_rv;

    if (x >= g_fb_w || y >= SCREEN_H) return 0;
    if (x + w > g_fb_w) w = (uint32_t)g_fb_w - x;
    if (y + h > SCREEN_H) h = SCREEN_H - y;

    dirty_mark(x, y, w, h);

    for (uint32_t row = 0; row < h; row++) {
        uint32_t color = lerp_color(c1, c2, row, h > 1 ? h - 1 : 1);
        for (uint32_t col = 0; col < w; col++) {
            fb_write(x + col, y + row, color);
        }
    }
    return 0;
}

/* ===================================================================
 * 6. Drop shadow
 *    rt_gui_shadow(xy, wh, blur_radius, alpha)
 *    Draws a dark blurred rectangle offset from the window position.
 *    // TODO: GPU_ACCEL — offload blur pass to GPU compute
 * =================================================================== */

RuntimeValue rt_gui_shadow(RuntimeValue xy, RuntimeValue wh,
                            RuntimeValue blur_alpha, RuntimeValue offset_rv)
{
    uint32_t x = (uint32_t)((uint64_t)xy >> 32);
    uint32_t y = (uint32_t)((uint64_t)xy & 0xFFFFFFFF);
    uint32_t w = (uint32_t)((uint64_t)wh >> 32);
    uint32_t h = (uint32_t)((uint64_t)wh & 0xFFFFFFFF);
    uint32_t blur_r = (uint32_t)((uint64_t)blur_alpha >> 32);
    uint32_t alpha = (uint32_t)((uint64_t)blur_alpha & 0xFFFFFFFF);
    uint32_t offset = (uint32_t)(uint64_t)offset_rv;

    /* 1.5x stronger shadow alpha */
    alpha = alpha * 3 / 2;
    if (alpha > 255) alpha = 255;
    if (blur_r > 45) blur_r = 45;
    if (offset == 0) offset = 6;

    /* Shadow position: offset down and right, slightly larger */
    uint32_t sx = x + offset;
    uint32_t sy = y + offset;
    uint32_t sw = w + offset;
    uint32_t sh = h + offset;

    /* Clamp */
    if (sx >= g_fb_w || sy >= SCREEN_H) return 0;
    if (sx + sw > g_fb_w) sw = (uint32_t)g_fb_w - sx;
    if (sy + sh > SCREEN_H) sh = SCREEN_H - sy;

    /* Draw dark rectangle */
    for (uint32_t row = 0; row < sh; row++) {
        for (uint32_t col = 0; col < sw; col++) {
            uint32_t dst = fb_read(sx + col, sy + row);
            fb_write(sx + col, sy + row, alpha_blend(dst, 0x00000000, (uint8_t)alpha));
        }
    }

    /* Blur the shadow */
    if (blur_r > 0) {
        box_blur_h(sx, sy, sw, sh, blur_r);
        box_blur_v(sx, sy, sw, sh, blur_r);
    }

    /* Extra soft outer glow for diffusion */
    if (blur_r > 4) {
        uint32_t ex = (sx > 2) ? sx - 2 : 0;
        uint32_t ey = (sy > 2) ? sy - 2 : 0;
        uint32_t ew = sw + 4;
        uint32_t eh = sh + 4;
        if (ex + ew <= g_fb_w && ey + eh <= SCREEN_H) {
            /* Top edge */
            for (uint32_t c = 0; c < ew && ex + c < g_fb_w; c++) {
                if (ey < SCREEN_H) {
                    uint32_t dst = fb_read(ex + c, ey);
                    fb_write(ex + c, ey, alpha_blend(dst, 0x00000000, alpha / 6));
                }
            }
            /* Bottom edge */
            uint32_t bot = ey + eh - 1;
            if (bot < SCREEN_H) {
                for (uint32_t c = 0; c < ew && ex + c < g_fb_w; c++) {
                    uint32_t dst = fb_read(ex + c, bot);
                    fb_write(ex + c, bot, alpha_blend(dst, 0x00000000, alpha / 6));
                }
            }
        }
    }

    return 0;
}

/* ===================================================================
 * 7. Read pixel
 *    rt_gui_read_pixel(pack(x,y), _, _, _)
 * =================================================================== */

RuntimeValue rt_gui_read_pixel(RuntimeValue x_y, RuntimeValue u1,
                                RuntimeValue u2, RuntimeValue u3)
{
    (void)u1; (void)u2; (void)u3;
    uint32_t x = (uint32_t)((uint64_t)x_y >> 32);
    uint32_t y = (uint32_t)((uint64_t)x_y & 0xFFFFFFFF);
    if (x >= g_fb_w || y >= SCREEN_H) return 0;
    return (RuntimeValue)fb_read(x, y);
}

/* ===================================================================
 * 8. Rounded rectangle (approximate with filled rects)
 *    rt_gui_rounded_rect(xy, wh, color_radius, alpha)
 *    // TODO: GPU_ACCEL — Bezier curve rasterization on GPU
 * =================================================================== */

RuntimeValue rt_gui_rounded_rect(RuntimeValue xy, RuntimeValue wh,
                                  RuntimeValue color_radius, RuntimeValue alpha_rv)
{
    uint32_t x = (uint32_t)((uint64_t)xy >> 32);
    uint32_t y = (uint32_t)((uint64_t)xy & 0xFFFFFFFF);
    uint32_t w = (uint32_t)((uint64_t)wh >> 32);
    uint32_t h = (uint32_t)((uint64_t)wh & 0xFFFFFFFF);
    uint32_t color = (uint32_t)((uint64_t)color_radius >> 32);
    uint32_t radius = (uint32_t)((uint64_t)color_radius & 0xFFFFFFFF);
    uint8_t alpha = (uint8_t)(uint64_t)alpha_rv;

    if (radius > w / 2) radius = w / 2;
    if (radius > h / 2) radius = h / 2;
    if (x >= g_fb_w || y >= SCREEN_H) return 0;

    /* Draw rounded rectangle using circle-quarter masks at corners */
    for (uint32_t row = 0; row < h; row++) {
        uint32_t py = y + row;
        if (py >= SCREEN_H) break;

        /* Determine row start/end considering rounded corners */
        uint32_t x_start = 0;
        uint32_t x_end = w;

        if (row < radius) {
            /* Top corners */
            uint32_t dy = radius - row;
            /* Circle equation: dx^2 + dy^2 <= r^2 => dx = sqrt(r^2 - dy^2) */
            uint32_t dx = 0;
            while ((dx + 1) * (dx + 1) + dy * dy <= radius * radius) dx++;
            x_start = radius - dx;
            x_end = w - (radius - dx);
        } else if (row >= h - radius) {
            /* Bottom corners */
            uint32_t dy = row - (h - radius - 1);
            uint32_t dx = 0;
            while ((dx + 1) * (dx + 1) + dy * dy <= radius * radius) dx++;
            x_start = radius - dx;
            x_end = w - (radius - dx);
        }

        for (uint32_t col = x_start; col < x_end; col++) {
            uint32_t px = x + col;
            if (px >= g_fb_w) break;
            if (alpha == 255) {
                fb_write(px, py, 0xFF000000u | color);
            } else {
                uint32_t dst = fb_read(px, py);
                fb_write(px, py, alpha_blend(dst, color, alpha));
            }
        }
    }
    return 0;
}

/* ===================================================================
 * 9. Gradient blend (vertical gradient with alpha)
 *    rt_gui_gradient_blend_v(xy, wh, c1_alpha1, c2_alpha2)
 *    Blends a vertical gradient with varying alpha onto framebuffer
 * =================================================================== */

RuntimeValue rt_gui_gradient_blend_v(RuntimeValue xy, RuntimeValue wh,
                                      RuntimeValue c1_a1, RuntimeValue c2_a2)
{
    uint32_t x = (uint32_t)((uint64_t)xy >> 32);
    uint32_t y = (uint32_t)((uint64_t)xy & 0xFFFFFFFF);
    uint32_t w = (uint32_t)((uint64_t)wh >> 32);
    uint32_t h = (uint32_t)((uint64_t)wh & 0xFFFFFFFF);
    uint32_t c1 = (uint32_t)((uint64_t)c1_a1 >> 32);
    uint32_t a1 = (uint32_t)((uint64_t)c1_a1 & 0xFF);
    uint32_t c2 = (uint32_t)((uint64_t)c2_a2 >> 32);
    uint32_t a2 = (uint32_t)((uint64_t)c2_a2 & 0xFF);

    if (x >= g_fb_w || y >= SCREEN_H) return 0;
    if (x + w > g_fb_w) w = (uint32_t)g_fb_w - x;
    if (y + h > SCREEN_H) h = SCREEN_H - y;

    for (uint32_t row = 0; row < h; row++) {
        uint32_t color = lerp_color(c1, c2, row, h > 1 ? h - 1 : 1);
        uint32_t alpha = a1 + (a2 - a1) * row / (h > 1 ? h - 1 : 1);
        if (alpha > 255) alpha = 255;
        for (uint32_t col = 0; col < w; col++) {
            uint32_t px = x + col;
            uint32_t py = y + row;
            uint32_t dst = fb_read(px, py);
            fb_write(px, py, alpha_blend(dst, color, (uint8_t)alpha));
        }
    }
    return 0;
}

/* ===================================================================
 * 10. Shadow-buffer-aware solid fill
 *     rt_gui_shadow_fill(xy, wh, color, _)
 *     Like rt_gui_fill4 but writes to shadow buffer, not MMIO.
 * =================================================================== */

RuntimeValue rt_gui_shadow_fill(RuntimeValue xy, RuntimeValue wh,
                                 RuntimeValue color_rv, RuntimeValue unused)
{
    (void)unused;
    uint32_t x = (uint32_t)((uint64_t)xy >> 32);
    uint32_t y = (uint32_t)((uint64_t)xy & 0xFFFFFFFF);
    uint32_t w = (uint32_t)((uint64_t)wh >> 32);
    uint32_t h = (uint32_t)((uint64_t)wh & 0xFFFFFFFF);
    uint32_t c = (uint32_t)(uint64_t)color_rv;

    if (x >= g_fb_w || y >= SCREEN_H) return 0;
    if (x + w > g_fb_w) w = (uint32_t)g_fb_w - x;
    if (y + h > SCREEN_H) h = SCREEN_H - y;

    dirty_mark(x, y, w, h);

    for (uint32_t row = 0; row < h; row++) {
        for (uint32_t col = 0; col < w; col++) {
            fb_write(x + col, y + row, c);
        }
    }
    return 0;
}

/* ===================================================================
 * 11. Partial present for dirty regions only
 *     rt_gui_present_rect(x, y, w, h)
 *     Copies a rectangular region from shadow buffer to MMIO framebuffer.
 *     Used for incremental updates when only a small area changed.
 * =================================================================== */

RuntimeValue rt_gui_present_rect(RuntimeValue x_rv, RuntimeValue y_rv,
                                  RuntimeValue w_rv, RuntimeValue h_rv)
{
    uint32_t x = (uint32_t)(uint64_t)x_rv;
    uint32_t y = (uint32_t)(uint64_t)y_rv;
    uint32_t w = (uint32_t)(uint64_t)w_rv;
    uint32_t h = (uint32_t)(uint64_t)h_rv;

    if (!g_shadow_ready || !g_shadow_buf) return 0;
    if (x + w > g_shadow_w) w = g_shadow_w - x;
    if (y + h > g_shadow_h) h = g_shadow_h - y;

    for (uint32_t row = y; row < y + h; row++) {
        uint64_t mmio_row = g_fb_addr + ((uint64_t)row * g_fb_w + x) * 4;
        uint32_t *src = &g_shadow_buf[row * g_shadow_w + x];
        for (uint32_t col = 0; col < w; col++) {
            *(volatile uint32_t *)(uintptr_t)(mmio_row + col * 4) = src[col];
        }
    }
    return 0;
}

/* ===================================================================
 * 12. Rounded rectangle — top corners only
 *     rt_gui_rounded_rect_top(xy, wh, color_radius, alpha)
 *     For title bars: rounded at top, flat at bottom.
 *     Same pack as rt_gui_rounded_rect.
 * =================================================================== */

RuntimeValue rt_gui_rounded_rect_top(RuntimeValue xy, RuntimeValue wh,
                                      RuntimeValue color_radius, RuntimeValue alpha_rv)
{
    uint32_t x = (uint32_t)((uint64_t)xy >> 32);
    uint32_t y = (uint32_t)((uint64_t)xy & 0xFFFFFFFF);
    uint32_t w = (uint32_t)((uint64_t)wh >> 32);
    uint32_t h = (uint32_t)((uint64_t)wh & 0xFFFFFFFF);
    uint32_t color = (uint32_t)((uint64_t)color_radius >> 32);
    uint32_t radius = (uint32_t)((uint64_t)color_radius & 0xFFFFFFFF);
    uint8_t alpha = (uint8_t)(uint64_t)alpha_rv;

    if (radius > w / 2) radius = w / 2;
    if (radius > h) radius = h;
    if (x >= g_fb_w || y >= SCREEN_H) return 0;

    dirty_mark(x, y, w, h);

    for (uint32_t row = 0; row < h; row++) {
        uint32_t py = y + row;
        if (py >= SCREEN_H) break;

        uint32_t x_start = 0;
        uint32_t x_end = w;

        if (row < radius) {
            /* Top corners only — bottom is flat */
            uint32_t dy = radius - row;
            uint32_t dx = 0;
            while ((dx + 1) * (dx + 1) + dy * dy <= radius * radius) dx++;
            x_start = radius - dx;
            x_end = w - (radius - dx);
        }
        /* No bottom corner rounding — rows >= h-radius are full width */

        for (uint32_t col = x_start; col < x_end; col++) {
            uint32_t px = x + col;
            if (px >= g_fb_w) break;
            if (alpha == 255) {
                fb_write(px, py, 0xFF000000u | color);
            } else {
                uint32_t dst = fb_read(px, py);
                fb_write(px, py, alpha_blend(dst, color, alpha));
            }
        }
    }
    return 0;
}

/* ===================================================================
 * 13. Filled circle (Bresenham midpoint)
 *     rt_gui_filled_circle(pack(cx,cy), pack(diameter,color), alpha, _)
 *     Draws a filled circle centered at (cx, cy) with given diameter.
 * =================================================================== */

RuntimeValue rt_gui_filled_circle(RuntimeValue cx_cy, RuntimeValue diam_color,
                                   RuntimeValue alpha_rv, RuntimeValue unused)
{
    (void)unused;
    uint32_t cx = (uint32_t)((uint64_t)cx_cy >> 32);
    uint32_t cy = (uint32_t)((uint64_t)cx_cy & 0xFFFFFFFF);
    uint32_t diameter = (uint32_t)((uint64_t)diam_color >> 32);
    uint32_t color = (uint32_t)((uint64_t)diam_color & 0xFFFFFFFF);
    uint8_t alpha = (uint8_t)(uint64_t)alpha_rv;

    if (diameter == 0) return 0;
    uint32_t r = diameter / 2;
    /* Center of circle */
    uint32_t ox = cx + r;
    uint32_t oy = cy + r;

    if (ox >= g_fb_w + r || oy >= SCREEN_H + r) return 0;
    dirty_mark(cx, cy, diameter, diameter);

    /* Filled circle via scanline: for each row, compute x span */
    for (uint32_t row = 0; row < diameter; row++) {
        int32_t dy = (int32_t)row - (int32_t)r;
        /* x^2 + y^2 <= r^2 => x = sqrt(r^2 - y^2) */
        int32_t r2 = (int32_t)(r * r);
        int32_t dy2 = dy * dy;
        if (dy2 > r2) continue;

        /* Integer sqrt approximation */
        uint32_t dx = 0;
        while ((int32_t)((dx + 1) * (dx + 1)) <= r2 - dy2) dx++;

        uint32_t py = cy + row;
        if (py >= SCREEN_H) continue;

        uint32_t x_left = ox > dx ? ox - dx : 0;
        uint32_t x_right = ox + dx;
        if (x_right >= g_fb_w) x_right = (uint32_t)g_fb_w - 1;

        for (uint32_t px = x_left; px <= x_right; px++) {
            if (alpha == 255) {
                fb_write(px, py, 0xFF000000u | color);
            } else {
                uint32_t dst = fb_read(px, py);
                fb_write(px, py, alpha_blend(dst, color, alpha));
            }
        }
    }
    return 0;
}

/* ===================================================================
 * 14. Procedural wallpaper generator
 *     rt_gui_draw_wallpaper(pack(width,height), style, _, _)
 *     Generates macOS-like abstract gradient wallpaper with color blobs.
 *     style: 0=dark aurora, 1=light pastel
 * =================================================================== */

static void draw_blob(uint32_t bx, uint32_t by, uint32_t br,
                       uint32_t color, uint8_t max_alpha,
                       uint32_t sw, uint32_t sh)
{
    /* Radial gradient blob — alpha falls off quadratically from center */
    uint32_t x1 = bx > br ? bx - br : 0;
    uint32_t y1 = by > br ? by - br : 0;
    uint32_t x2 = bx + br < sw ? bx + br : sw;
    uint32_t y2 = by + br < sh ? by + br : sh;

    uint32_t r2 = br * br;
    if (r2 == 0) return;

    for (uint32_t row = y1; row < y2; row++) {
        int32_t dy = (int32_t)row - (int32_t)by;
        uint32_t dy2 = (uint32_t)(dy * dy);
        for (uint32_t col = x1; col < x2; col++) {
            int32_t dx = (int32_t)col - (int32_t)bx;
            uint32_t dist2 = (uint32_t)(dx * dx) + dy2;
            if (dist2 >= r2) continue;

            /* Quadratic falloff: alpha = max_alpha * (1 - dist2/r2) */
            uint32_t alpha = (uint32_t)max_alpha * (r2 - dist2) / r2;
            if (alpha > 255) alpha = 255;
            if (alpha < 2) continue;

            uint32_t dst = fb_read(col, row);
            fb_write(col, row, alpha_blend(dst, color, (uint8_t)alpha));
        }
    }
}

RuntimeValue rt_gui_draw_wallpaper(RuntimeValue wh, RuntimeValue style_rv,
                                    RuntimeValue unused1, RuntimeValue unused2)
{
    (void)unused1; (void)unused2;
    uint32_t sw = (uint32_t)((uint64_t)wh >> 32);
    uint32_t sh = (uint32_t)((uint64_t)wh & 0xFFFFFFFF);
    uint32_t style = (uint32_t)(uint64_t)style_rv;

    if (sw > SCREEN_W_MAX) sw = SCREEN_W_MAX;
    if (sh > SCREEN_H) sh = SCREEN_H;
    if (sw == 0 || sh == 0) return 0;

    dirty_mark(0, 0, sw, sh);

    if (style == 0) {
        /* Dark Aurora — deep space with colorful nebula blobs */

        /* Base gradient: midnight blue → deep purple */
        for (uint32_t row = 0; row < sh; row++) {
            uint32_t color = lerp_color(0x00060612, 0x001A0830, row, sh > 1 ? sh - 1 : 1);
            for (uint32_t col = 0; col < sw; col++) {
                fb_write(col, row, 0xFF000000u | color);
            }
        }

        /* Star field — scattered bright points (400 stars, brighter) */
        for (uint32_t i = 0; i < 400; i++) {
            uint32_t sx = ((i * 2654435761u) ^ (i * 340573321u)) % sw;
            uint32_t sy = ((i * 1103515245u) ^ (i * 12345u)) % sh;
            uint8_t brightness = 80 + (((i * 48271u) ^ (i * 65537u)) % 80);
            fb_write(sx, sy, alpha_blend(fb_read(sx, sy), 0x00FFFFFF, brightness));
            /* Every 3rd star is 3px for variation */
            if (i % 3 == 0 && sx + 1 < sw) {
                fb_write(sx + 1, sy, alpha_blend(fb_read(sx + 1, sy), 0x00FFFFFF, brightness / 2));
                if (sx + 2 < sw) {
                    fb_write(sx + 2, sy, alpha_blend(fb_read(sx + 2, sy), 0x00FFFFFF, brightness / 3));
                }
            }
        }

        /* Subtle horizon glow — brighter band in lower third */
        for (uint32_t row = sh * 2 / 3; row < sh * 2 / 3 + sh / 8; row++) {
            for (uint32_t col = 0; col < sw; col++) {
                uint32_t dist = row - sh * 2 / 3;
                uint32_t max_dist = sh / 8;
                uint32_t alpha = 12 * (max_dist - dist) / max_dist;
                if (alpha > 0) {
                    uint32_t dst = fb_read(col, row);
                    fb_write(col, row, alpha_blend(dst, 0x002040A0, (uint8_t)alpha));
                }
            }
        }

        /* Nebula blobs — larger (1.5x radius) and brighter (1.3x alpha) */
        draw_blob(sw * 3 / 4, sh / 4, 330, 0x000A84FF, 39, sw, sh);   /* Blue (top-right) */
        draw_blob(sw / 5, sh * 2 / 3, 300, 0x00BB86FC, 33, sw, sh);   /* Purple (bottom-left) */
        draw_blob(sw / 2, sh / 2, 270, 0x0000D4AA, 23, sw, sh);       /* Teal (center) */
        draw_blob(sw * 4 / 5, sh * 3 / 4, 240, 0x00FF6B9D, 26, sw, sh); /* Pink (bottom-right) */
        draw_blob(sw / 3, sh / 5, 210, 0x00FFD700, 20, sw, sh);       /* Gold (top-left) */
        draw_blob(sw / 8, sh / 8, 180, 0x004ECDC4, 16, sw, sh);       /* Teal-mint (top-left) */
        draw_blob(sw * 5 / 8, sh / 3, 225, 0x00E040FB, 21, sw, sh);   /* Neon purple (center-right) */
        draw_blob(sw / 2, sh * 4 / 5, 195, 0x00FF7043, 18, sw, sh);   /* Coral (bottom-center) */

        /* Extra detail blobs for visual richness — larger (1.5x) and brighter (1.3x) */
        draw_blob(sw / 6, sh * 3 / 5, 150, 0x00FFFFFF, 10, sw, sh);   /* White highlight */
        draw_blob(sw * 7 / 8, sh / 6, 135, 0x0064B5F6, 13, sw, sh);  /* Light blue accent */
        draw_blob(sw * 2 / 5, sh / 10, 120, 0x00CE93D8, 13, sw, sh);  /* Light purple */

        /* Extra bright nebula cores for dramatic effect */
        draw_blob(sw / 3, sh / 3, 200, 0x006020A0, 50, sw, sh);      /* Purple core */
        draw_blob(sw * 2 / 3, sh * 2 / 3, 180, 0x002040C0, 45, sw, sh);  /* Blue core */
        draw_blob(sw / 2, sh / 4, 150, 0x00A03060, 35, sw, sh);      /* Magenta accent */

        /* Subtle blur pass to soften blobs */
        box_blur_h(0, 0, sw, sh, 8);
        box_blur_v(0, 0, sw, sh, 8);

        /* Aurora horizon glow — bright band across lower third */
        for (uint32_t ay = sh * 2 / 3; ay < sh; ay++) {
            uint32_t intensity = (ay - sh * 2 / 3) * 40 / (sh / 3);
            for (uint32_t ax = 0; ax < sw; ax++) {
                uint32_t pixel = fb_read(ax, ay);
                uint8_t r = (pixel >> 16) & 0xFF;
                uint8_t g = (pixel >> 8) & 0xFF;
                uint8_t b = pixel & 0xFF;
                /* Add warm purple-blue glow */
                uint8_t gr = r + (intensity * 3 / 5 > 255 - r ? 255 - r : intensity * 3 / 5);
                uint8_t gg = g + (intensity / 4 > 255 - g ? 255 - g : intensity / 4);
                uint8_t gb = b + (intensity > 255 - b ? 255 - b : intensity);
                fb_write(ax, ay, 0xFF000000u | ((uint32_t)gr << 16) | ((uint32_t)gg << 8) | gb);
            }
        }

        /* Subtle noise overlay for texture */
        for (uint32_t row = 0; row < sh; row++) {
            for (uint32_t col = 0; col < sw; col++) {
                /* Simple hash-based noise */
                uint32_t noise = ((col * 2654435761u) ^ (row * 2246822519u)) & 0xFF;
                if (noise > 240) {
                    uint32_t dst = fb_read(col, row);
                    fb_write(col, row, alpha_blend(dst, 0x00FFFFFF, 6));
                }
            }
        }

        /* Vignette — darken edges for depth */
        for (uint32_t row = 0; row < sh; row++) {
            for (uint32_t col = 0; col < sw; col++) {
                int32_t dx = (int32_t)col - (int32_t)(sw / 2);
                int32_t dy = (int32_t)row - (int32_t)(sh / 2);
                uint32_t dist2 = (uint32_t)(dx * dx + dy * dy);
                uint32_t max_dist2 = (sw / 2) * (sw / 2) + (sh / 2) * (sh / 2);
                if (dist2 > max_dist2 / 3) {
                    uint32_t alpha = (dist2 - max_dist2 / 3) * 40 / (max_dist2 * 2 / 3);
                    if (alpha > 40) alpha = 40;
                    uint32_t dst = fb_read(col, row);
                    fb_write(col, row, alpha_blend(dst, 0x00000000, (uint8_t)alpha));
                }
            }
        }

    } else {
        /* Light Pastel — soft gradient with gentle color washes */

        /* Base gradient: lavender → soft white */
        for (uint32_t row = 0; row < sh; row++) {
            uint32_t color = lerp_color(0x00C8B8E8, 0x00F0ECF5, row, sh > 1 ? sh - 1 : 1);
            for (uint32_t col = 0; col < sw; col++) {
                fb_write(col, row, 0xFF000000u | color);
            }
        }

        /* Sun glow — warm circle in upper area */
        draw_blob(sw / 2, sh / 4, 300, 0x00FFFFFF, 15, sw, sh);

        /* Pastel blobs */
        draw_blob(sw * 2 / 3, sh / 3, 250, 0x00FFB5C5, 25, sw, sh);   /* Pink (top-right) */
        draw_blob(sw / 4, sh / 2, 220, 0x0099CCFF, 22, sw, sh);       /* Sky blue (left) */
        draw_blob(sw / 2, sh * 3 / 4, 200, 0x00B5FFD9, 20, sw, sh);   /* Mint (bottom-center) */
        draw_blob(sw * 3 / 4, sh * 2 / 3, 180, 0x00E8C5FF, 18, sw, sh); /* Lilac (right) */
        draw_blob(sw / 6, sh / 4, 180, 0x00FFE0B2, 18, sw, sh);       /* Peach (top-left) */
        draw_blob(sw * 3 / 4, sh / 5, 160, 0x00B2EBF2, 16, sw, sh);   /* Ice blue (top-right) */
        draw_blob(sw / 3, sh * 4 / 5, 140, 0x00F8BBD0, 14, sw, sh);   /* Rose (bottom-left) */

        /* Extra detail blobs */
        draw_blob(sw / 2, sh / 6, 160, 0x00FFFFFF, 12, sw, sh);       /* Central white glow */
        draw_blob(sw * 4 / 5, sh * 3 / 4, 120, 0x00E1BEE7, 10, sw, sh); /* Lilac accent */
        draw_blob(sw / 8, sh * 4 / 5, 100, 0x00B3E5FC, 10, sw, sh);   /* Sky blue */

        /* Soft pastel clouds for light theme */
        draw_blob(sw / 4, sh / 3, 300, 0x00FFF0F8, 12, sw, sh);      /* White-pink cloud */
        draw_blob(sw * 3 / 4, sh / 2, 250, 0x00F0F0FF, 10, sw, sh);  /* White-blue cloud */
        draw_blob(sw / 2, sh * 2 / 3, 280, 0x00F8F0FF, 8, sw, sh);   /* Soft purple cloud */

        /* Soften */
        box_blur_h(0, 0, sw, sh, 10);
        box_blur_v(0, 0, sw, sh, 10);

        /* Subtle noise overlay for texture */
        for (uint32_t row = 0; row < sh; row++) {
            for (uint32_t col = 0; col < sw; col++) {
                uint32_t noise = ((col * 2654435761u) ^ (row * 2246822519u)) & 0xFF;
                if (noise > 240) {
                    uint32_t dst = fb_read(col, row);
                    fb_write(col, row, alpha_blend(dst, 0x00000000, 4));
                }
            }
        }

        /* Subtle vignette for depth */
        for (uint32_t row = 0; row < sh; row++) {
            for (uint32_t col = 0; col < sw; col++) {
                int32_t dx = (int32_t)col - (int32_t)(sw / 2);
                int32_t dy = (int32_t)row - (int32_t)(sh / 2);
                uint32_t dist2 = (uint32_t)(dx * dx + dy * dy);
                uint32_t max_dist2 = (sw / 2) * (sw / 2) + (sh / 2) * (sh / 2);
                if (dist2 > max_dist2 / 2) {
                    uint32_t alpha = (dist2 - max_dist2 / 2) * 20 / (max_dist2 / 2);
                    if (alpha > 20) alpha = 20;
                    uint32_t dst = fb_read(col, row);
                    fb_write(col, row, alpha_blend(dst, 0x00000000, (uint8_t)alpha));
                }
            }
        }
    }

    return 0;
}

/* ===================================================================
 * 15. Anti-aliased rounded rectangle
 *     Same signature as rt_gui_rounded_rect but with smooth edge blending.
 *     At corner edges, computes distance to circle boundary and uses
 *     fractional alpha for sub-pixel smoothing.
 * =================================================================== */
RuntimeValue rt_gui_rounded_rect_aa(RuntimeValue xy, RuntimeValue wh,
                                     RuntimeValue color_radius, RuntimeValue alpha_rv)
{
    uint32_t x = (uint32_t)((uint64_t)xy >> 32);
    uint32_t y = (uint32_t)((uint64_t)xy & 0xFFFFFFFF);
    uint32_t w = (uint32_t)((uint64_t)wh >> 32);
    uint32_t h = (uint32_t)((uint64_t)wh & 0xFFFFFFFF);
    uint32_t color = (uint32_t)((uint64_t)color_radius >> 32);
    uint32_t radius = (uint32_t)((uint64_t)color_radius & 0xFFFFFFFF);
    uint8_t alpha = (uint8_t)(uint64_t)alpha_rv;

    if (radius > w / 2) radius = w / 2;
    if (radius > h / 2) radius = h / 2;
    if (x >= g_fb_w || y >= SCREEN_H || w == 0 || h == 0) return 0;

    dirty_mark(x, y, w, h);

    /* Pre-compute r^4 for superellipse test using 64-bit to avoid overflow */
    uint64_t r2 = (uint64_t)radius * radius;
    uint64_t r4 = r2 * r2;

    for (uint32_t row = 0; row < h; row++) {
        uint32_t py = y + row;
        if (py >= SCREEN_H) break;

        for (uint32_t col = 0; col < w; col++) {
            uint32_t px = x + col;
            if (px >= g_fb_w) break;

            /* Check which corner region this pixel is in */
            int in_corner = 0;
            uint32_t cx = 0, cy = 0; /* distance from corner center */

            if (col < radius && row < radius) {
                /* Top-left corner */
                cx = radius - col;
                cy = radius - row;
                in_corner = 1;
            } else if (col >= w - radius && row < radius) {
                /* Top-right corner */
                cx = col - (w - radius - 1);
                cy = radius - row;
                in_corner = 1;
            } else if (col < radius && row >= h - radius) {
                /* Bottom-left corner */
                cx = radius - col;
                cy = row - (h - radius - 1);
                in_corner = 1;
            } else if (col >= w - radius && row >= h - radius) {
                /* Bottom-right corner */
                cx = col - (w - radius - 1);
                cy = row - (h - radius - 1);
                in_corner = 1;
            }

            if (in_corner) {
                /* Superellipse distance: (cx/r)^4 + (cy/r)^4 vs 1.0
                 * Equivalent: cx^4 + cy^4 vs r^4 (all integer) */
                uint64_t cx2 = (uint64_t)cx * cx;
                uint64_t cy2 = (uint64_t)cy * cy;
                uint64_t cx4 = cx2 * cx2;
                uint64_t cy4 = cy2 * cy2;
                uint64_t dist4 = cx4 + cy4;

                if (dist4 > r4) {
                    /* Outside — skip this pixel */
                    continue;
                }

                /* Anti-aliasing: compute edge proximity
                 * Use the ratio dist4/r4 to determine alpha near edge
                 * Edge is at dist4 == r4, so closeness = (r4 - dist4) / r4
                 * For AA band: when dist4 is within 85-100% of r4 */
                uint64_t threshold = r4 - r4 / 5; /* 80% of r4 = start of AA band */
                if (dist4 > threshold) {
                    /* In AA band — compute edge alpha */
                    uint64_t edge_range = r4 - threshold; /* size of AA band */
                    uint64_t edge_pos = r4 - dist4;       /* distance from outer edge */
                    uint32_t edge_alpha = (uint32_t)(edge_pos * alpha / edge_range);
                    if (edge_alpha > alpha) edge_alpha = alpha;
                    if (edge_alpha > 0) {
                        uint32_t dst = fb_read(px, py);
                        fb_write(px, py, alpha_blend(dst, color, (uint8_t)edge_alpha));
                    }
                    continue;
                }
            }

            /* Inside the shape — draw pixel */
            if (alpha == 255) {
                fb_write(px, py, 0xFF000000u | color);
            } else {
                uint32_t dst = fb_read(px, py);
                fb_write(px, py, alpha_blend(dst, color, alpha));
            }
        }
    }
    return 0;
}

/* ===================================================================
 * 16. Line drawing (Bresenham)
 *     rt_gui_line(pack(x1,y1), pack(x2,y2), pack(color,thickness), alpha)
 * =================================================================== */
RuntimeValue rt_gui_line(RuntimeValue p1, RuntimeValue p2,
                          RuntimeValue color_thick, RuntimeValue alpha_rv)
{
    int32_t x1 = (int32_t)((uint64_t)p1 >> 32);
    int32_t y1 = (int32_t)((uint64_t)p1 & 0xFFFFFFFF);
    int32_t x2 = (int32_t)((uint64_t)p2 >> 32);
    int32_t y2 = (int32_t)((uint64_t)p2 & 0xFFFFFFFF);
    uint32_t color = (uint32_t)((uint64_t)color_thick >> 32);
    uint32_t thick = (uint32_t)((uint64_t)color_thick & 0xFFFFFFFF);
    uint8_t alpha = (uint8_t)(uint64_t)alpha_rv;

    if (thick == 0) thick = 1;

    int32_t dx = x2 > x1 ? x2 - x1 : x1 - x2;
    int32_t dy = y2 > y1 ? y2 - y1 : y1 - y2;
    int32_t sx = x1 < x2 ? 1 : -1;
    int32_t sy = y1 < y2 ? 1 : -1;
    int32_t err = dx - dy;

    while (1) {
        /* Draw thick pixel (square brush) */
        for (uint32_t ty = 0; ty < thick; ty++) {
            for (uint32_t tx = 0; tx < thick; tx++) {
                int32_t px = x1 + (int32_t)tx - (int32_t)(thick / 2);
                int32_t py = y1 + (int32_t)ty - (int32_t)(thick / 2);
                if (px >= 0 && px < (int32_t)g_fb_w && py >= 0 && py < (int32_t)SCREEN_H) {
                    if (alpha == 255) {
                        fb_write((uint32_t)px, (uint32_t)py, 0xFF000000u | color);
                    } else {
                        uint32_t dst = fb_read((uint32_t)px, (uint32_t)py);
                        fb_write((uint32_t)px, (uint32_t)py, alpha_blend(dst, color, alpha));
                    }
                }
            }
        }

        if (x1 == x2 && y1 == y2) break;
        int32_t e2 = 2 * err;
        if (e2 > -dy) { err -= dy; x1 += sx; }
        if (e2 < dx) { err += dx; y1 += sy; }
    }

    dirty_mark(x1 < x2 ? (uint32_t)x1 : (uint32_t)x2,
               y1 < y2 ? (uint32_t)y1 : (uint32_t)y2,
               (uint32_t)dx + thick, (uint32_t)dy + thick);
    return 0;
}

/* ===================================================================
 * 17. Circle outline (ring)
 *     rt_gui_ring(pack(cx,cy), pack(diameter,thickness), pack(color,0), alpha)
 * =================================================================== */
RuntimeValue rt_gui_ring(RuntimeValue cx_cy, RuntimeValue diam_thick,
                          RuntimeValue color_rv, RuntimeValue alpha_rv)
{
    uint32_t cx = (uint32_t)((uint64_t)cx_cy >> 32);
    uint32_t cy = (uint32_t)((uint64_t)cx_cy & 0xFFFFFFFF);
    uint32_t diameter = (uint32_t)((uint64_t)diam_thick >> 32);
    uint32_t thick = (uint32_t)((uint64_t)diam_thick & 0xFFFFFFFF);
    uint32_t color = (uint32_t)((uint64_t)color_rv >> 32);
    uint8_t alpha = (uint8_t)(uint64_t)alpha_rv;

    if (diameter == 0 || thick == 0) return 0;
    uint32_t r_outer = diameter / 2;
    uint32_t r_inner = r_outer > thick ? r_outer - thick : 0;
    uint32_t r_outer2 = r_outer * r_outer;
    uint32_t r_inner2 = r_inner * r_inner;

    dirty_mark(cx, cy, diameter, diameter);

    for (uint32_t row = 0; row < diameter; row++) {
        int32_t dy = (int32_t)row - (int32_t)r_outer;
        uint32_t dy2 = (uint32_t)(dy * dy);
        for (uint32_t col = 0; col < diameter; col++) {
            int32_t dx = (int32_t)col - (int32_t)r_outer;
            uint32_t dist2 = (uint32_t)(dx * dx) + dy2;
            if (dist2 <= r_outer2 && dist2 >= r_inner2) {
                uint32_t px = cx + col;
                uint32_t py = cy + row;
                if (px < g_fb_w && py < SCREEN_H) {
                    if (alpha == 255) {
                        fb_write(px, py, 0xFF000000u | color);
                    } else {
                        uint32_t dst = fb_read(px, py);
                        fb_write(px, py, alpha_blend(dst, color, alpha));
                    }
                }
            }
        }
    }
    return 0;
}

/* ===================================================================
 * 18. Rounded rectangle with vertical gradient
 *     rt_gui_gradient_rect(xy, wh, color_radius, c2_alpha)
 *     Draws rounded rect with vertical gradient from color (high bits of
 *     color_radius) to c2 (high bits of c2_alpha). Alpha from low byte of c2_alpha.
 * =================================================================== */
RuntimeValue rt_gui_gradient_rect(RuntimeValue xy, RuntimeValue wh,
                                   RuntimeValue color_radius, RuntimeValue c2_alpha)
{
    uint32_t x = (uint32_t)((uint64_t)xy >> 32);
    uint32_t y = (uint32_t)((uint64_t)xy & 0xFFFFFFFF);
    uint32_t w = (uint32_t)((uint64_t)wh >> 32);
    uint32_t h = (uint32_t)((uint64_t)wh & 0xFFFFFFFF);
    uint32_t c1 = (uint32_t)((uint64_t)color_radius >> 32);
    uint32_t radius = (uint32_t)((uint64_t)color_radius & 0xFFFFFFFF);
    uint32_t c2 = (uint32_t)((uint64_t)c2_alpha >> 32);
    uint8_t alpha = (uint8_t)(uint64_t)c2_alpha;

    if (radius > w / 2) radius = w / 2;
    if (radius > h / 2) radius = h / 2;
    if (x >= g_fb_w || y >= SCREEN_H) return 0;

    dirty_mark(x, y, w, h);

    for (uint32_t row = 0; row < h; row++) {
        uint32_t py = y + row;
        if (py >= SCREEN_H) break;

        uint32_t color = lerp_color(c1, c2, row, h > 1 ? h - 1 : 1);

        uint32_t x_start = 0;
        uint32_t x_end = w;

        if (row < radius) {
            uint32_t dy = radius - row;
            uint32_t dx = 0;
            while ((dx + 1) * (dx + 1) + dy * dy <= radius * radius) dx++;
            x_start = radius - dx;
            x_end = w - (radius - dx);
        } else if (row >= h - radius) {
            uint32_t dy = row - (h - radius - 1);
            uint32_t dx = 0;
            while ((dx + 1) * (dx + 1) + dy * dy <= radius * radius) dx++;
            x_start = radius - dx;
            x_end = w - (radius - dx);
        }

        for (uint32_t col = x_start; col < x_end; col++) {
            uint32_t px = x + col;
            if (px >= g_fb_w) break;
            if (alpha == 255) {
                fb_write(px, py, 0xFF000000u | color);
            } else {
                uint32_t dst = fb_read(px, py);
                fb_write(px, py, alpha_blend(dst, color, alpha));
            }
        }
    }
    return 0;
}

/* ===================================================================
 * 19. Bitmap font text rendering
 *     rt_gui_draw_text(xy, text_ptr_len, color_size, alpha)
 *
 *     Renders ASCII text using built-in 8x16 bitmap font.
 *     xy = pack(x, y)
 *     text_ptr_len = pack(ptr_to_string, length)  -- RuntimeValue string
 *     color_size = pack(color, 0)  -- color in high 32 bits
 *     alpha = alpha value
 *
 *     Since Simple strings are RuntimeValue (tagged pointer), we receive
 *     the raw string data pointer and length from the Simple side.
 * =================================================================== */

/* Standard VGA 8x16 bitmap font for ASCII 32-126 (95 printable chars)
 * Each character is 8 pixels wide, 16 pixels tall.
 * Stored as 16 bytes per char (1 byte per row, 8 bits used).
 * This is the CP437 8x16 font used by BIOS/EFI for high-quality text. */
static const uint8_t font_8x16[95][16] = {
    /* ' ' (32) */ {0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00},
    /* '!' (33) */ {0x00,0x00,0x18,0x3C,0x3C,0x3C,0x18,0x18,0x18,0x00,0x18,0x18,0x00,0x00,0x00,0x00},
    /* '"' (34) */ {0x00,0x66,0x66,0x66,0x24,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00},
    /* '#' (35) */ {0x00,0x00,0x00,0x6C,0x6C,0xFE,0x6C,0x6C,0x6C,0xFE,0x6C,0x6C,0x00,0x00,0x00,0x00},
    /* '$' (36) */ {0x18,0x18,0x7C,0xC6,0xC2,0xC0,0x7C,0x06,0x06,0x86,0xC6,0x7C,0x18,0x18,0x00,0x00},
    /* '%' (37) */ {0x00,0x00,0x00,0x00,0xC2,0xC6,0x0C,0x18,0x30,0x60,0xC6,0x86,0x00,0x00,0x00,0x00},
    /* '&' (38) */ {0x00,0x00,0x38,0x6C,0x6C,0x38,0x76,0xDC,0xCC,0xCC,0xCC,0x76,0x00,0x00,0x00,0x00},
    /* '\'' (39)*/ {0x00,0x30,0x30,0x30,0x60,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00},
    /* '(' (40) */ {0x00,0x00,0x0C,0x18,0x30,0x30,0x30,0x30,0x30,0x30,0x18,0x0C,0x00,0x00,0x00,0x00},
    /* ')' (41) */ {0x00,0x00,0x30,0x18,0x0C,0x0C,0x0C,0x0C,0x0C,0x0C,0x18,0x30,0x00,0x00,0x00,0x00},
    /* '*' (42) */ {0x00,0x00,0x00,0x00,0x00,0x66,0x3C,0xFF,0x3C,0x66,0x00,0x00,0x00,0x00,0x00,0x00},
    /* '+' (43) */ {0x00,0x00,0x00,0x00,0x00,0x18,0x18,0x7E,0x18,0x18,0x00,0x00,0x00,0x00,0x00,0x00},
    /* ',' (44) */ {0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x18,0x18,0x18,0x30,0x00,0x00,0x00},
    /* '-' (45) */ {0x00,0x00,0x00,0x00,0x00,0x00,0x00,0xFE,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00},
    /* '.' (46) */ {0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x18,0x18,0x00,0x00,0x00,0x00},
    /* '/' (47) */ {0x00,0x00,0x00,0x00,0x02,0x06,0x0C,0x18,0x30,0x60,0xC0,0x80,0x00,0x00,0x00,0x00},
    /* '0' (48) */ {0x00,0x00,0x7C,0xC6,0xC6,0xCE,0xDE,0xF6,0xE6,0xC6,0xC6,0x7C,0x00,0x00,0x00,0x00},
    /* '1' (49) */ {0x00,0x00,0x18,0x38,0x78,0x18,0x18,0x18,0x18,0x18,0x18,0x7E,0x00,0x00,0x00,0x00},
    /* '2' (50) */ {0x00,0x00,0x7C,0xC6,0x06,0x0C,0x18,0x30,0x60,0xC0,0xC6,0xFE,0x00,0x00,0x00,0x00},
    /* '3' (51) */ {0x00,0x00,0x7C,0xC6,0x06,0x06,0x3C,0x06,0x06,0x06,0xC6,0x7C,0x00,0x00,0x00,0x00},
    /* '4' (52) */ {0x00,0x00,0x0C,0x1C,0x3C,0x6C,0xCC,0xFE,0x0C,0x0C,0x0C,0x1E,0x00,0x00,0x00,0x00},
    /* '5' (53) */ {0x00,0x00,0xFE,0xC0,0xC0,0xC0,0xFC,0x06,0x06,0x06,0xC6,0x7C,0x00,0x00,0x00,0x00},
    /* '6' (54) */ {0x00,0x00,0x38,0x60,0xC0,0xC0,0xFC,0xC6,0xC6,0xC6,0xC6,0x7C,0x00,0x00,0x00,0x00},
    /* '7' (55) */ {0x00,0x00,0xFE,0xC6,0x06,0x06,0x0C,0x18,0x30,0x30,0x30,0x30,0x00,0x00,0x00,0x00},
    /* '8' (56) */ {0x00,0x00,0x7C,0xC6,0xC6,0xC6,0x7C,0xC6,0xC6,0xC6,0xC6,0x7C,0x00,0x00,0x00,0x00},
    /* '9' (57) */ {0x00,0x00,0x7C,0xC6,0xC6,0xC6,0x7E,0x06,0x06,0x06,0x0C,0x78,0x00,0x00,0x00,0x00},
    /* ':' (58) */ {0x00,0x00,0x00,0x00,0x18,0x18,0x00,0x00,0x00,0x18,0x18,0x00,0x00,0x00,0x00,0x00},
    /* ';' (59) */ {0x00,0x00,0x00,0x00,0x18,0x18,0x00,0x00,0x00,0x18,0x18,0x30,0x00,0x00,0x00,0x00},
    /* '<' (60) */ {0x00,0x00,0x00,0x06,0x0C,0x18,0x30,0x60,0x30,0x18,0x0C,0x06,0x00,0x00,0x00,0x00},
    /* '=' (61) */ {0x00,0x00,0x00,0x00,0x00,0x7E,0x00,0x00,0x7E,0x00,0x00,0x00,0x00,0x00,0x00,0x00},
    /* '>' (62) */ {0x00,0x00,0x00,0x60,0x30,0x18,0x0C,0x06,0x0C,0x18,0x30,0x60,0x00,0x00,0x00,0x00},
    /* '?' (63) */ {0x00,0x00,0x7C,0xC6,0xC6,0x0C,0x18,0x18,0x18,0x00,0x18,0x18,0x00,0x00,0x00,0x00},
    /* '@' (64) */ {0x00,0x00,0x00,0x7C,0xC6,0xC6,0xDE,0xDE,0xDE,0xDC,0xC0,0x7C,0x00,0x00,0x00,0x00},
    /* 'A' (65) */ {0x00,0x00,0x10,0x38,0x6C,0xC6,0xC6,0xFE,0xC6,0xC6,0xC6,0xC6,0x00,0x00,0x00,0x00},
    /* 'B' (66) */ {0x00,0x00,0xFC,0x66,0x66,0x66,0x7C,0x66,0x66,0x66,0x66,0xFC,0x00,0x00,0x00,0x00},
    /* 'C' (67) */ {0x00,0x00,0x3C,0x66,0xC2,0xC0,0xC0,0xC0,0xC0,0xC2,0x66,0x3C,0x00,0x00,0x00,0x00},
    /* 'D' (68) */ {0x00,0x00,0xF8,0x6C,0x66,0x66,0x66,0x66,0x66,0x66,0x6C,0xF8,0x00,0x00,0x00,0x00},
    /* 'E' (69) */ {0x00,0x00,0xFE,0x66,0x62,0x68,0x78,0x68,0x60,0x62,0x66,0xFE,0x00,0x00,0x00,0x00},
    /* 'F' (70) */ {0x00,0x00,0xFE,0x66,0x62,0x68,0x78,0x68,0x60,0x60,0x60,0xF0,0x00,0x00,0x00,0x00},
    /* 'G' (71) */ {0x00,0x00,0x3C,0x66,0xC2,0xC0,0xC0,0xDE,0xC6,0xC6,0x66,0x3A,0x00,0x00,0x00,0x00},
    /* 'H' (72) */ {0x00,0x00,0xC6,0xC6,0xC6,0xC6,0xFE,0xC6,0xC6,0xC6,0xC6,0xC6,0x00,0x00,0x00,0x00},
    /* 'I' (73) */ {0x00,0x00,0x3C,0x18,0x18,0x18,0x18,0x18,0x18,0x18,0x18,0x3C,0x00,0x00,0x00,0x00},
    /* 'J' (74) */ {0x00,0x00,0x1E,0x0C,0x0C,0x0C,0x0C,0x0C,0xCC,0xCC,0xCC,0x78,0x00,0x00,0x00,0x00},
    /* 'K' (75) */ {0x00,0x00,0xE6,0x66,0x66,0x6C,0x78,0x78,0x6C,0x66,0x66,0xE6,0x00,0x00,0x00,0x00},
    /* 'L' (76) */ {0x00,0x00,0xF0,0x60,0x60,0x60,0x60,0x60,0x60,0x62,0x66,0xFE,0x00,0x00,0x00,0x00},
    /* 'M' (77) */ {0x00,0x00,0xC6,0xEE,0xFE,0xFE,0xD6,0xC6,0xC6,0xC6,0xC6,0xC6,0x00,0x00,0x00,0x00},
    /* 'N' (78) */ {0x00,0x00,0xC6,0xE6,0xF6,0xFE,0xDE,0xCE,0xC6,0xC6,0xC6,0xC6,0x00,0x00,0x00,0x00},
    /* 'O' (79) */ {0x00,0x00,0x7C,0xC6,0xC6,0xC6,0xC6,0xC6,0xC6,0xC6,0xC6,0x7C,0x00,0x00,0x00,0x00},
    /* 'P' (80) */ {0x00,0x00,0xFC,0x66,0x66,0x66,0x7C,0x60,0x60,0x60,0x60,0xF0,0x00,0x00,0x00,0x00},
    /* 'Q' (81) */ {0x00,0x00,0x7C,0xC6,0xC6,0xC6,0xC6,0xC6,0xC6,0xD6,0xDE,0x7C,0x0C,0x0E,0x00,0x00},
    /* 'R' (82) */ {0x00,0x00,0xFC,0x66,0x66,0x66,0x7C,0x6C,0x66,0x66,0x66,0xE6,0x00,0x00,0x00,0x00},
    /* 'S' (83) */ {0x00,0x00,0x7C,0xC6,0xC6,0x60,0x38,0x0C,0x06,0xC6,0xC6,0x7C,0x00,0x00,0x00,0x00},
    /* 'T' (84) */ {0x00,0x00,0xFF,0xDB,0x99,0x18,0x18,0x18,0x18,0x18,0x18,0x3C,0x00,0x00,0x00,0x00},
    /* 'U' (85) */ {0x00,0x00,0xC6,0xC6,0xC6,0xC6,0xC6,0xC6,0xC6,0xC6,0xC6,0x7C,0x00,0x00,0x00,0x00},
    /* 'V' (86) */ {0x00,0x00,0xC6,0xC6,0xC6,0xC6,0xC6,0xC6,0xC6,0x6C,0x38,0x10,0x00,0x00,0x00,0x00},
    /* 'W' (87) */ {0x00,0x00,0xC6,0xC6,0xC6,0xC6,0xD6,0xD6,0xD6,0xFE,0xEE,0x6C,0x00,0x00,0x00,0x00},
    /* 'X' (88) */ {0x00,0x00,0xC6,0xC6,0x6C,0x7C,0x38,0x38,0x7C,0x6C,0xC6,0xC6,0x00,0x00,0x00,0x00},
    /* 'Y' (89) */ {0x00,0x00,0xCC,0xCC,0xCC,0xCC,0x78,0x30,0x30,0x30,0x30,0x78,0x00,0x00,0x00,0x00},
    /* 'Z' (90) */ {0x00,0x00,0xFE,0xC6,0x86,0x0C,0x18,0x30,0x60,0xC2,0xC6,0xFE,0x00,0x00,0x00,0x00},
    /* '[' (91) */ {0x00,0x00,0x3C,0x30,0x30,0x30,0x30,0x30,0x30,0x30,0x30,0x3C,0x00,0x00,0x00,0x00},
    /* '\\' (92)*/ {0x00,0x00,0x00,0x80,0xC0,0xE0,0x70,0x38,0x1C,0x0E,0x06,0x02,0x00,0x00,0x00,0x00},
    /* ']' (93) */ {0x00,0x00,0x3C,0x0C,0x0C,0x0C,0x0C,0x0C,0x0C,0x0C,0x0C,0x3C,0x00,0x00,0x00,0x00},
    /* '^' (94) */ {0x10,0x38,0x6C,0xC6,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00},
    /* '_' (95) */ {0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0xFF,0x00,0x00},
    /* '`' (96) */ {0x30,0x30,0x18,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00},
    /* 'a' (97) */ {0x00,0x00,0x00,0x00,0x00,0x78,0x0C,0x7C,0xCC,0xCC,0xCC,0x76,0x00,0x00,0x00,0x00},
    /* 'b' (98) */ {0x00,0x00,0xE0,0x60,0x60,0x78,0x6C,0x66,0x66,0x66,0x66,0x7C,0x00,0x00,0x00,0x00},
    /* 'c' (99) */ {0x00,0x00,0x00,0x00,0x00,0x7C,0xC6,0xC0,0xC0,0xC0,0xC6,0x7C,0x00,0x00,0x00,0x00},
    /* 'd' (100)*/ {0x00,0x00,0x1C,0x0C,0x0C,0x3C,0x6C,0xCC,0xCC,0xCC,0xCC,0x76,0x00,0x00,0x00,0x00},
    /* 'e' (101)*/ {0x00,0x00,0x00,0x00,0x00,0x7C,0xC6,0xFE,0xC0,0xC0,0xC6,0x7C,0x00,0x00,0x00,0x00},
    /* 'f' (102)*/ {0x00,0x00,0x1C,0x36,0x32,0x30,0x78,0x30,0x30,0x30,0x30,0x78,0x00,0x00,0x00,0x00},
    /* 'g' (103)*/ {0x00,0x00,0x00,0x00,0x00,0x76,0xCC,0xCC,0xCC,0xCC,0xCC,0x7C,0x0C,0xCC,0x78,0x00},
    /* 'h' (104)*/ {0x00,0x00,0xE0,0x60,0x60,0x6C,0x76,0x66,0x66,0x66,0x66,0xE6,0x00,0x00,0x00,0x00},
    /* 'i' (105)*/ {0x00,0x00,0x18,0x18,0x00,0x38,0x18,0x18,0x18,0x18,0x18,0x3C,0x00,0x00,0x00,0x00},
    /* 'j' (106)*/ {0x00,0x00,0x06,0x06,0x00,0x0E,0x06,0x06,0x06,0x06,0x06,0x06,0x66,0x66,0x3C,0x00},
    /* 'k' (107)*/ {0x00,0x00,0xE0,0x60,0x60,0x66,0x6C,0x78,0x78,0x6C,0x66,0xE6,0x00,0x00,0x00,0x00},
    /* 'l' (108)*/ {0x00,0x00,0x38,0x18,0x18,0x18,0x18,0x18,0x18,0x18,0x18,0x3C,0x00,0x00,0x00,0x00},
    /* 'm' (109)*/ {0x00,0x00,0x00,0x00,0x00,0xEC,0xFE,0xD6,0xD6,0xD6,0xD6,0xC6,0x00,0x00,0x00,0x00},
    /* 'n' (110)*/ {0x00,0x00,0x00,0x00,0x00,0xDC,0x66,0x66,0x66,0x66,0x66,0x66,0x00,0x00,0x00,0x00},
    /* 'o' (111)*/ {0x00,0x00,0x00,0x00,0x00,0x7C,0xC6,0xC6,0xC6,0xC6,0xC6,0x7C,0x00,0x00,0x00,0x00},
    /* 'p' (112)*/ {0x00,0x00,0x00,0x00,0x00,0xDC,0x66,0x66,0x66,0x66,0x66,0x7C,0x60,0x60,0xF0,0x00},
    /* 'q' (113)*/ {0x00,0x00,0x00,0x00,0x00,0x76,0xCC,0xCC,0xCC,0xCC,0xCC,0x7C,0x0C,0x0C,0x1E,0x00},
    /* 'r' (114)*/ {0x00,0x00,0x00,0x00,0x00,0xDC,0x76,0x66,0x60,0x60,0x60,0xF0,0x00,0x00,0x00,0x00},
    /* 's' (115)*/ {0x00,0x00,0x00,0x00,0x00,0x7C,0xC6,0x60,0x38,0x0C,0xC6,0x7C,0x00,0x00,0x00,0x00},
    /* 't' (116)*/ {0x00,0x00,0x10,0x30,0x30,0xFC,0x30,0x30,0x30,0x30,0x36,0x1C,0x00,0x00,0x00,0x00},
    /* 'u' (117)*/ {0x00,0x00,0x00,0x00,0x00,0xCC,0xCC,0xCC,0xCC,0xCC,0xCC,0x76,0x00,0x00,0x00,0x00},
    /* 'v' (118)*/ {0x00,0x00,0x00,0x00,0x00,0xC6,0xC6,0xC6,0xC6,0xC6,0x6C,0x38,0x00,0x00,0x00,0x00},
    /* 'w' (119)*/ {0x00,0x00,0x00,0x00,0x00,0xC6,0xC6,0xD6,0xD6,0xD6,0xFE,0x6C,0x00,0x00,0x00,0x00},
    /* 'x' (120)*/ {0x00,0x00,0x00,0x00,0x00,0xC6,0x6C,0x38,0x38,0x38,0x6C,0xC6,0x00,0x00,0x00,0x00},
    /* 'y' (121)*/ {0x00,0x00,0x00,0x00,0x00,0xC6,0xC6,0xC6,0xC6,0xC6,0xC6,0x7E,0x06,0x0C,0xF8,0x00},
    /* 'z' (122)*/ {0x00,0x00,0x00,0x00,0x00,0xFE,0xCC,0x18,0x30,0x60,0xC6,0xFE,0x00,0x00,0x00,0x00},
    /* '{' (123)*/ {0x00,0x00,0x0E,0x18,0x18,0x18,0x70,0x18,0x18,0x18,0x18,0x0E,0x00,0x00,0x00,0x00},
    /* '|' (124)*/ {0x00,0x00,0x18,0x18,0x18,0x18,0x00,0x18,0x18,0x18,0x18,0x18,0x00,0x00,0x00,0x00},
    /* '}' (125)*/ {0x00,0x00,0x70,0x18,0x18,0x18,0x0E,0x18,0x18,0x18,0x18,0x70,0x00,0x00,0x00,0x00},
    /* '~' (126)*/ {0x00,0x00,0x76,0xDC,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00},
};

/* rt_gui_draw_text(pack(x,y), pack(ptr,len), pack(color,0), alpha)
 * Simple uses tagged RuntimeValue for strings. The caller must pass
 * the raw char pointer and byte length separately.
 * If ptr is a RuntimeValue string, the Simple side extracts data+len. */
RuntimeValue rt_gui_draw_text(RuntimeValue xy, RuntimeValue ptr_len,
                               RuntimeValue color_rv, RuntimeValue alpha_rv)
{
    uint32_t x = (uint32_t)((uint64_t)xy >> 32);
    uint32_t y = (uint32_t)((uint64_t)xy & 0xFFFFFFFF);
    uint64_t ptr_val = (uint64_t)ptr_len >> 32;
    uint32_t len = (uint32_t)((uint64_t)ptr_len & 0xFFFFFFFF);
    uint32_t color = (uint32_t)((uint64_t)color_rv >> 32);
    uint8_t alpha = (uint8_t)(uint64_t)alpha_rv;

    /* ptr_val is the high 32 bits — won't work for 64-bit pointers.
     * Instead, treat ptr_len as: high 32 = char count, low 32 = unused.
     * The actual string data comes through a different mechanism.
     *
     * For baremetal simplicity: use a static text buffer approach.
     * The Simple side calls rt_gui_set_text() first, then rt_gui_draw_text(). */

    if (x >= g_fb_w || y >= SCREEN_H) return 0;

    const char *text = (const char *)(uintptr_t)ptr_val;
    if (!text || len == 0) return 0;
    if (len > 256) len = 256;

    uint32_t cx = x;
    for (uint32_t i = 0; i < len; i++) {
        uint8_t ch = (uint8_t)text[i];
        if (ch < 32 || ch > 126) ch = '?';
        uint32_t idx = ch - 32;

        /* Draw character glyph (8x16 bitmap) */
        for (uint32_t row = 0; row < 16; row++) {
            uint8_t bits = font_8x16[idx][row];
            uint32_t py = y + row;
            if (py >= SCREEN_H) break;
            for (uint32_t col = 0; col < 8; col++) {
                if (bits & (0x80 >> col)) {
                    uint32_t px = cx + col;
                    if (px >= g_fb_w) break;
                    if (alpha == 255) {
                        fb_write(px, py, 0xFF000000u | color);
                    } else {
                        uint32_t dst = fb_read(px, py);
                        fb_write(px, py, alpha_blend(dst, color, alpha));
                    }
                }
            }
        }
        cx += 8; /* Advance to next character */
        if (cx >= g_fb_w) break;
    }

    dirty_mark(x, y, cx - x, 16);
    return 0;
}

/* Static text buffer for inter-function text passing */
static char g_text_buf[256];
static uint32_t g_text_len = 0;

/* rt_gui_set_text_buf(char_values_packed, _, _, _)
 * Store up to 8 characters per call from packed u64.
 * Call multiple times then rt_gui_draw_text_buf to render.
 * char_values = 8 bytes packed into u64 (byte 0 in bits 56-63, etc.) */
RuntimeValue rt_gui_set_text_buf(RuntimeValue chars, RuntimeValue offset_rv,
                                  RuntimeValue unused1, RuntimeValue unused2)
{
    (void)unused1; (void)unused2;
    uint32_t offset = (uint32_t)(uint64_t)offset_rv;
    uint64_t c = (uint64_t)chars;

    for (int i = 0; i < 8 && offset + i < 256; i++) {
        uint8_t ch = (uint8_t)(c >> (56 - i * 8));
        if (ch == 0) break;
        g_text_buf[offset + i] = (char)ch;
        if (offset + i + 1 > g_text_len) g_text_len = offset + i + 1;
    }
    return 0;
}

/* rt_gui_draw_text_buf(pack(x,y), pack(color,len), alpha, _)
 * Renders text from the static buffer at given position. */
RuntimeValue rt_gui_draw_text_buf(RuntimeValue xy, RuntimeValue color_len,
                                   RuntimeValue alpha_rv, RuntimeValue unused)
{
    (void)unused;
    uint32_t x = (uint32_t)((uint64_t)xy >> 32);
    uint32_t y = (uint32_t)((uint64_t)xy & 0xFFFFFFFF);
    uint32_t color = (uint32_t)((uint64_t)color_len >> 32);
    uint32_t len = (uint32_t)((uint64_t)color_len & 0xFFFFFFFF);
    uint8_t alpha = (uint8_t)(uint64_t)alpha_rv;

    if (len == 0) len = g_text_len;
    if (len > 256) len = 256;
    if (x >= g_fb_w || y >= SCREEN_H) return 0;

    uint32_t cx = x;
    for (uint32_t i = 0; i < len; i++) {
        uint8_t ch = (uint8_t)g_text_buf[i];
        if (ch < 32 || ch > 126) ch = '?';
        uint32_t idx = ch - 32;

        for (uint32_t row = 0; row < 16; row++) {
            uint8_t bits = font_8x16[idx][row];
            uint32_t py = y + row;
            if (py >= SCREEN_H) break;
            for (uint32_t col = 0; col < 8; col++) {
                if (bits & (0x80 >> col)) {
                    uint32_t px = cx + col;
                    if (px >= g_fb_w) break;
                    if (alpha == 255) {
                        fb_write(px, py, 0xFF000000u | color);
                    } else {
                        uint32_t dst = fb_read(px, py);
                        fb_write(px, py, alpha_blend(dst, color, alpha));
                    }
                }
            }
        }
        cx += 8;
        if (cx >= g_fb_w) break;
    }

    dirty_mark(x, y, cx - x, 16);
    g_text_len = 0; /* Reset buffer */
    return 0;
}

/* ===================================================================
 * 21. Text with shadow (pseudo anti-aliased appearance)
 *     rt_gui_draw_text_shadow(pack(x,y), pack(color,len), alpha, shadow_alpha)
 *     Renders text twice: shadow at (x+1,y+1) then foreground at (x,y)
 * =================================================================== */
RuntimeValue rt_gui_draw_text_shadow(RuntimeValue xy, RuntimeValue color_len,
                                      RuntimeValue alpha_rv, RuntimeValue shadow_rv)
{
    uint32_t x = (uint32_t)((uint64_t)xy >> 32);
    uint32_t y = (uint32_t)((uint64_t)xy & 0xFFFFFFFF);
    uint32_t color = (uint32_t)((uint64_t)color_len >> 32);
    uint32_t len = (uint32_t)((uint64_t)color_len & 0xFFFFFFFF);
    uint8_t alpha = (uint8_t)(uint64_t)alpha_rv;
    uint8_t shadow_alpha = (uint8_t)(uint64_t)shadow_rv;

    if (len == 0) len = g_text_len;
    if (len > 256) len = 256;
    if (x >= g_fb_w || y >= SCREEN_H) return 0;

    /* Pass 0: Soft shadow at (x+1, y+1) with half alpha (pseudo-AA fringe) */
    uint32_t cx = x + 1;
    uint8_t soft_alpha = shadow_alpha / 2;
    for (uint32_t i = 0; i < len; i++) {
        uint8_t ch = (uint8_t)g_text_buf[i];
        if (ch < 32 || ch > 126) ch = '?';
        uint32_t idx = ch - 32;
        for (uint32_t row = 0; row < 16; row++) {
            uint8_t bits = font_8x16[idx][row];
            uint32_t py = y + 1 + row;
            if (py >= SCREEN_H) break;
            for (uint32_t col = 0; col < 8; col++) {
                if (bits & (0x80 >> col)) {
                    uint32_t px = cx + col;
                    if (px < g_fb_w) {
                        uint32_t dst = fb_read(px, py);
                        fb_write(px, py, alpha_blend(dst, 0x00000000, soft_alpha));
                    }
                }
            }
        }
        cx += 8;
    }

    /* Pass 1: Main shadow at (x+2, y+2) in dark color (larger offset) */
    cx = x + 2;
    for (uint32_t i = 0; i < len; i++) {
        uint8_t ch = (uint8_t)g_text_buf[i];
        if (ch < 32 || ch > 126) ch = '?';
        uint32_t idx = ch - 32;
        for (uint32_t row = 0; row < 16; row++) {
            uint8_t bits = font_8x16[idx][row];
            uint32_t py = y + 2 + row;
            if (py >= SCREEN_H) break;
            for (uint32_t col = 0; col < 8; col++) {
                if (bits & (0x80 >> col)) {
                    uint32_t px = cx + col;
                    if (px < g_fb_w) {
                        uint32_t dst = fb_read(px, py);
                        fb_write(px, py, alpha_blend(dst, 0x00000000, shadow_alpha));
                    }
                }
            }
        }
        cx += 8;
    }

    /* Pass 2: Foreground at (x, y) */
    cx = x;
    for (uint32_t i = 0; i < len; i++) {
        uint8_t ch = (uint8_t)g_text_buf[i];
        if (ch < 32 || ch > 126) ch = '?';
        uint32_t idx = ch - 32;
        for (uint32_t row = 0; row < 16; row++) {
            uint8_t bits = font_8x16[idx][row];
            uint32_t py = y + row;
            if (py >= SCREEN_H) break;
            for (uint32_t col = 0; col < 8; col++) {
                if (bits & (0x80 >> col)) {
                    uint32_t px = cx + col;
                    if (px < g_fb_w) {
                        if (alpha == 255) {
                            fb_write(px, py, 0xFF000000u | color);
                        } else {
                            uint32_t dst = fb_read(px, py);
                            fb_write(px, py, alpha_blend(dst, color, alpha));
                        }
                    }
                }
            }
        }
        cx += 8;
    }

    dirty_mark(x, y, cx - x + 1, 18);
    g_text_len = 0;
    return 0;
}

/* ===================================================================
 * 22. Bold text (pseudo-bold via double render at x and x+1)
 *     rt_gui_draw_text_bold(pack(x,y), pack(color,len), alpha, _)
 *     Renders text twice: once at (x,y), once at (x+1,y) for thickness.
 *     Does NOT reset g_text_buf so caller can chain with shadow.
 * =================================================================== */
RuntimeValue rt_gui_draw_text_bold(RuntimeValue xy, RuntimeValue color_len,
                                    RuntimeValue alpha_rv, RuntimeValue unused)
{
    (void)unused;
    uint32_t x = (uint32_t)((uint64_t)xy >> 32);
    uint32_t y = (uint32_t)((uint64_t)xy & 0xFFFFFFFF);
    uint32_t color = (uint32_t)((uint64_t)color_len >> 32);
    uint32_t len = (uint32_t)((uint64_t)color_len & 0xFFFFFFFF);
    uint8_t alpha = (uint8_t)(uint64_t)alpha_rv;

    if (len == 0) len = g_text_len;
    if (len > 256) len = 256;
    if (x >= g_fb_w || y >= SCREEN_H) return 0;

    /* Draw at (x, y) — first pass */
    uint32_t cx = x;
    for (uint32_t i = 0; i < len; i++) {
        uint8_t ch = (uint8_t)g_text_buf[i];
        if (ch < 32 || ch > 126) ch = '?';
        uint32_t idx = ch - 32;
        for (uint32_t row = 0; row < 16; row++) {
            uint8_t bits = font_8x16[idx][row];
            uint32_t py = y + row;
            if (py >= SCREEN_H) break;
            for (uint32_t col = 0; col < 8; col++) {
                if (bits & (0x80 >> col)) {
                    uint32_t px = cx + col;
                    if (px >= g_fb_w) break;
                    if (alpha == 255) {
                        fb_write(px, py, 0xFF000000u | color);
                    } else {
                        uint32_t dst = fb_read(px, py);
                        fb_write(px, py, alpha_blend(dst, color, alpha));
                    }
                }
            }
        }
        cx += 8;
        if (cx >= g_fb_w) break;
    }

    /* Draw at (x+1, y) — bold effect (thicker strokes) */
    cx = x + 1;
    for (uint32_t i = 0; i < len; i++) {
        uint8_t ch = (uint8_t)g_text_buf[i];
        if (ch < 32 || ch > 126) ch = '?';
        uint32_t idx = ch - 32;
        for (uint32_t row = 0; row < 16; row++) {
            uint8_t bits = font_8x16[idx][row];
            uint32_t py = y + row;
            if (py >= SCREEN_H) break;
            for (uint32_t col = 0; col < 8; col++) {
                if (bits & (0x80 >> col)) {
                    uint32_t px = cx + col;
                    if (px >= g_fb_w) break;
                    if (alpha == 255) {
                        fb_write(px, py, 0xFF000000u | color);
                    } else {
                        uint32_t dst = fb_read(px, py);
                        fb_write(px, py, alpha_blend(dst, color, alpha));
                    }
                }
            }
        }
        cx += 8;
        if (cx >= g_fb_w) break;
    }

    dirty_mark(x, y, cx - x + 1, 16);
    g_text_len = 0;
    return 0;
}

/* ===================================================================
 * 23. Scaled text (2x) — renders each font pixel as a 2x2 block
 *     rt_gui_draw_text_2x(pack(x,y), pack(color,len), alpha, shadow_alpha)
 *     Output: 16x32 per character (2x the 8x16 base font)
 *     With drop shadow for readability.
 * =================================================================== */
RuntimeValue rt_gui_draw_text_2x(RuntimeValue xy, RuntimeValue color_len,
                                  RuntimeValue alpha_rv, RuntimeValue shadow_rv)
{
    uint32_t x = (uint32_t)((uint64_t)xy >> 32);
    uint32_t y = (uint32_t)((uint64_t)xy & 0xFFFFFFFF);
    uint32_t color = (uint32_t)((uint64_t)color_len >> 32);
    uint32_t len = (uint32_t)((uint64_t)color_len & 0xFFFFFFFF);
    uint8_t alpha = (uint8_t)(uint64_t)alpha_rv;
    uint8_t shadow_alpha = (uint8_t)(uint64_t)shadow_rv;

    if (len == 0) len = g_text_len;
    if (len > 256) len = 256;
    if (x >= g_fb_w || y >= SCREEN_H) return 0;

    /* Shadow pass at (x+2, y+2) */
    if (shadow_alpha > 0) {
        uint32_t cx = x + 2;
        for (uint32_t i = 0; i < len; i++) {
            uint8_t ch = (uint8_t)g_text_buf[i];
            if (ch < 32 || ch > 126) ch = '?';
            uint32_t idx = ch - 32;
            for (uint32_t row = 0; row < 16; row++) {
                uint8_t bits = font_8x16[idx][row];
                for (uint32_t col = 0; col < 8; col++) {
                    if (bits & (0x80 >> col)) {
                        /* 2x2 block for shadow */
                        for (int dy = 0; dy < 2; dy++) {
                            uint32_t py = y + 2 + row * 2 + dy;
                            if (py >= SCREEN_H) continue;
                            for (int dx = 0; dx < 2; dx++) {
                                uint32_t px = cx + col * 2 + dx;
                                if (px < g_fb_w) {
                                    uint32_t dst = fb_read(px, py);
                                    fb_write(px, py, alpha_blend(dst, 0x00000000, shadow_alpha));
                                }
                            }
                        }
                    }
                }
            }
            cx += 16; /* 8 * 2 = 16 pixels per char */
            if (cx >= g_fb_w) break;
        }
    }

    /* Foreground pass at (x, y) — 2x scaled */
    uint32_t cx = x;
    for (uint32_t i = 0; i < len; i++) {
        uint8_t ch = (uint8_t)g_text_buf[i];
        if (ch < 32 || ch > 126) ch = '?';
        uint32_t idx = ch - 32;
        for (uint32_t row = 0; row < 16; row++) {
            uint8_t bits = font_8x16[idx][row];
            for (uint32_t col = 0; col < 8; col++) {
                if (bits & (0x80 >> col)) {
                    /* 2x2 block */
                    for (int dy = 0; dy < 2; dy++) {
                        uint32_t py = y + row * 2 + dy;
                        if (py >= SCREEN_H) continue;
                        for (int dx = 0; dx < 2; dx++) {
                            uint32_t px = cx + col * 2 + dx;
                            if (px < g_fb_w) {
                                if (alpha == 255) {
                                    fb_write(px, py, 0xFF000000u | color);
                                } else {
                                    uint32_t dst = fb_read(px, py);
                                    fb_write(px, py, alpha_blend(dst, color, alpha));
                                }
                            }
                        }
                    }
                }
            }
        }
        cx += 16;
        if (cx >= g_fb_w) break;
    }

    dirty_mark(x, y, cx - x + 2, 34);
    g_text_len = 0;
    return 0;
}

/* ===================================================================
 * 20. Layout Engine — Flexbox-style HStack/VStack
 *
 * Flat array of layout nodes. Simple side builds the tree via
 * function calls, then runs compute_layout, then reads results.
 *
 * Usage from Simple:
 *   rt_layout_reset(0, 0, 0, 0)
 *   val root = rt_layout_add(LAYOUT_VSTACK, -1, 0, 0)  // parent=-1 = root
 *   val bar = rt_layout_add(LAYOUT_HSTACK, root, 0, 0)
 *   rt_layout_set_size(bar, pack(FIXED, 28), pack(FILL, 0))  // h=28 fixed, w=fill
 *   rt_layout_set_padding(bar, pack(8, 8), pack(4, 4))       // lr=8, tb=4
 *   rt_layout_compute(pack(1024, 768), 0, 0, 0)              // screen size
 *   val bar_x = rt_layout_get(bar, 0, 0, 0) >> 32            // x in high bits
 *   val bar_y = rt_layout_get(bar, 0, 0, 0) & 0xFFFFFFFF     // y in low bits
 *   val bar_w = rt_layout_get_size(bar, 0, 0, 0) >> 32       // w
 *   val bar_h = rt_layout_get_size(bar, 0, 0, 0) & 0xFFFFFFFF // h
 * =================================================================== */

#define MAX_LAYOUT_NODES 128

typedef enum {
    LT_NONE = 0,
    LT_HSTACK = 1,    /* Horizontal: children laid out left-to-right */
    LT_VSTACK = 2,    /* Vertical: children laid out top-to-bottom */
    LT_ZSTACK = 3     /* Overlay: children stacked on top of each other */
} LayoutType;

typedef enum {
    SM_FIXED = 0,       /* Fixed pixel size */
    SM_FILL = 1,        /* Fill remaining space (weight-based) */
    SM_AUTO = 2         /* Size to content */
} SizeMode;

typedef enum {
    ALIGN_START = 0,
    ALIGN_CENTER = 1,
    ALIGN_END = 2
} LayoutAlign;

typedef struct {
    int active;          /* 1 if node is in use */
    int parent;          /* Parent node index (-1 = root) */
    LayoutType type;

    /* Size specification */
    SizeMode w_mode, h_mode;
    uint32_t w_value, h_value; /* Fixed size or weight */

    /* Padding */
    uint32_t pad_left, pad_right, pad_top, pad_bottom;

    /* Spacing between children */
    uint32_t spacing;

    /* Alignment of children on cross axis */
    LayoutAlign h_align, v_align;

    /* Computed results */
    int32_t cx, cy;       /* Position (relative to screen) */
    uint32_t cw, ch;      /* Computed size */

    /* Children tracking */
    int children[32];     /* Child indices */
    int child_count;

    /* Intrinsic size (from content or children) */
    uint32_t intrinsic_w, intrinsic_h;
} LayoutNode;

static LayoutNode g_layout[MAX_LAYOUT_NODES];
static int g_layout_count = 0;

/* Reset layout tree */
RuntimeValue rt_layout_reset(RuntimeValue u1, RuntimeValue u2,
                              RuntimeValue u3, RuntimeValue u4)
{
    (void)u1; (void)u2; (void)u3; (void)u4;
    for (int i = 0; i < MAX_LAYOUT_NODES; i++) {
        g_layout[i].active = 0;
        g_layout[i].child_count = 0;
    }
    g_layout_count = 0;
    return 0;
}

/* Add a node: rt_layout_add(type, parent_id, _, _) -> node_id */
RuntimeValue rt_layout_add(RuntimeValue type_rv, RuntimeValue parent_rv,
                            RuntimeValue u1, RuntimeValue u2)
{
    (void)u1; (void)u2;
    if (g_layout_count >= MAX_LAYOUT_NODES) return (RuntimeValue)-1;

    int id = g_layout_count++;
    LayoutNode *n = &g_layout[id];
    n->active = 1;
    n->type = (LayoutType)(uint64_t)type_rv;
    n->parent = (int)(int64_t)parent_rv;
    n->w_mode = SM_AUTO;
    n->h_mode = SM_AUTO;
    n->w_value = 0;
    n->h_value = 0;
    n->pad_left = n->pad_right = n->pad_top = n->pad_bottom = 0;
    n->spacing = 0;
    n->h_align = ALIGN_START;
    n->v_align = ALIGN_START;
    n->cx = n->cy = 0;
    n->cw = n->ch = 0;
    n->child_count = 0;
    n->intrinsic_w = n->intrinsic_h = 0;

    /* Register as child of parent */
    if (n->parent >= 0 && n->parent < MAX_LAYOUT_NODES) {
        LayoutNode *p = &g_layout[n->parent];
        if (p->child_count < 32) {
            p->children[p->child_count++] = id;
        }
    }

    return (RuntimeValue)id;
}

/* Set size: rt_layout_set_size(id, pack(w_mode, w_value), pack(h_mode, h_value), _) */
RuntimeValue rt_layout_set_size(RuntimeValue id_rv, RuntimeValue w_spec,
                                 RuntimeValue h_spec, RuntimeValue u)
{
    (void)u;
    int id = (int)(int64_t)id_rv;
    if (id < 0 || id >= g_layout_count) return 0;
    LayoutNode *n = &g_layout[id];

    n->w_mode = (SizeMode)((uint64_t)w_spec >> 32);
    n->w_value = (uint32_t)((uint64_t)w_spec & 0xFFFFFFFF);
    n->h_mode = (SizeMode)((uint64_t)h_spec >> 32);
    n->h_value = (uint32_t)((uint64_t)h_spec & 0xFFFFFFFF);

    return 0;
}

/* Set padding: rt_layout_set_padding(id, pack(left, right), pack(top, bottom), _) */
RuntimeValue rt_layout_set_padding(RuntimeValue id_rv, RuntimeValue lr,
                                    RuntimeValue tb, RuntimeValue u)
{
    (void)u;
    int id = (int)(int64_t)id_rv;
    if (id < 0 || id >= g_layout_count) return 0;
    LayoutNode *n = &g_layout[id];

    n->pad_left = (uint32_t)((uint64_t)lr >> 32);
    n->pad_right = (uint32_t)((uint64_t)lr & 0xFFFFFFFF);
    n->pad_top = (uint32_t)((uint64_t)tb >> 32);
    n->pad_bottom = (uint32_t)((uint64_t)tb & 0xFFFFFFFF);

    return 0;
}

/* Set spacing + alignment: rt_layout_set_props(id, spacing, pack(h_align, v_align), _) */
RuntimeValue rt_layout_set_props(RuntimeValue id_rv, RuntimeValue spacing_rv,
                                  RuntimeValue align_rv, RuntimeValue u)
{
    (void)u;
    int id = (int)(int64_t)id_rv;
    if (id < 0 || id >= g_layout_count) return 0;
    LayoutNode *n = &g_layout[id];

    n->spacing = (uint32_t)(uint64_t)spacing_rv;
    n->h_align = (LayoutAlign)((uint64_t)align_rv >> 32);
    n->v_align = (LayoutAlign)((uint64_t)align_rv & 0xFFFFFFFF);

    return 0;
}

/* Measure pass (bottom-up): compute intrinsic sizes */
static void layout_measure(int id)
{
    LayoutNode *n = &g_layout[id];
    if (!n->active) return;

    /* Measure children first */
    for (int i = 0; i < n->child_count; i++) {
        layout_measure(n->children[i]);
    }

    /* Compute intrinsic size based on children */
    uint32_t content_w = 0, content_h = 0;

    if (n->type == LT_HSTACK) {
        for (int i = 0; i < n->child_count; i++) {
            LayoutNode *c = &g_layout[n->children[i]];
            if (c->w_mode == SM_FIXED) content_w += c->w_value;
            else content_w += c->intrinsic_w;
            uint32_t ch = (c->h_mode == SM_FIXED) ? c->h_value : c->intrinsic_h;
            if (ch > content_h) content_h = ch;
        }
        if (n->child_count > 1) content_w += (n->child_count - 1) * n->spacing;
    } else if (n->type == LT_VSTACK) {
        for (int i = 0; i < n->child_count; i++) {
            LayoutNode *c = &g_layout[n->children[i]];
            if (c->h_mode == SM_FIXED) content_h += c->h_value;
            else content_h += c->intrinsic_h;
            uint32_t cw = (c->w_mode == SM_FIXED) ? c->w_value : c->intrinsic_w;
            if (cw > content_w) content_w = cw;
        }
        if (n->child_count > 1) content_h += (n->child_count - 1) * n->spacing;
    } else if (n->type == LT_ZSTACK) {
        for (int i = 0; i < n->child_count; i++) {
            LayoutNode *c = &g_layout[n->children[i]];
            uint32_t cw = (c->w_mode == SM_FIXED) ? c->w_value : c->intrinsic_w;
            uint32_t ch = (c->h_mode == SM_FIXED) ? c->h_value : c->intrinsic_h;
            if (cw > content_w) content_w = cw;
            if (ch > content_h) content_h = ch;
        }
    }

    n->intrinsic_w = content_w + n->pad_left + n->pad_right;
    n->intrinsic_h = content_h + n->pad_top + n->pad_bottom;
}

/* Layout pass (top-down): assign positions and final sizes */
static void layout_arrange(int id, int32_t x, int32_t y, uint32_t w, uint32_t h)
{
    LayoutNode *n = &g_layout[id];
    if (!n->active) return;

    n->cx = x;
    n->cy = y;
    n->cw = w;
    n->ch = h;

    if (n->child_count == 0) return;

    uint32_t content_w = w - n->pad_left - n->pad_right;
    uint32_t content_h = h - n->pad_top - n->pad_bottom;
    int32_t start_x = x + (int32_t)n->pad_left;
    int32_t start_y = y + (int32_t)n->pad_top;

    if (n->type == LT_HSTACK) {
        /* Calculate fixed vs fill space */
        uint32_t fixed_total = 0;
        uint32_t fill_weight_total = 0;
        for (int i = 0; i < n->child_count; i++) {
            LayoutNode *c = &g_layout[n->children[i]];
            if (c->w_mode == SM_FIXED) fixed_total += c->w_value;
            else if (c->w_mode == SM_FILL) fill_weight_total += (c->w_value > 0 ? c->w_value : 1);
            else fixed_total += c->intrinsic_w;
        }
        if (n->child_count > 1) fixed_total += (n->child_count - 1) * n->spacing;

        uint32_t free_space = (content_w > fixed_total) ? content_w - fixed_total : 0;

        int32_t cx = start_x;
        for (int i = 0; i < n->child_count; i++) {
            LayoutNode *c = &g_layout[n->children[i]];
            uint32_t cw, ch;

            if (c->w_mode == SM_FIXED) cw = c->w_value;
            else if (c->w_mode == SM_FILL) {
                uint32_t weight = (c->w_value > 0 ? c->w_value : 1);
                cw = (fill_weight_total > 0) ? (free_space * weight / fill_weight_total) : 0;
            } else cw = c->intrinsic_w;

            if (c->h_mode == SM_FIXED) ch = c->h_value;
            else if (c->h_mode == SM_FILL) ch = content_h;
            else ch = c->intrinsic_h;

            /* Cross-axis alignment */
            int32_t cy = start_y;
            if (n->v_align == ALIGN_CENTER) cy += (int32_t)(content_h - ch) / 2;
            else if (n->v_align == ALIGN_END) cy += (int32_t)(content_h - ch);

            layout_arrange(n->children[i], cx, cy, cw, ch);
            cx += (int32_t)cw + (int32_t)n->spacing;
        }
    } else if (n->type == LT_VSTACK) {
        uint32_t fixed_total = 0;
        uint32_t fill_weight_total = 0;
        for (int i = 0; i < n->child_count; i++) {
            LayoutNode *c = &g_layout[n->children[i]];
            if (c->h_mode == SM_FIXED) fixed_total += c->h_value;
            else if (c->h_mode == SM_FILL) fill_weight_total += (c->h_value > 0 ? c->h_value : 1);
            else fixed_total += c->intrinsic_h;
        }
        if (n->child_count > 1) fixed_total += (n->child_count - 1) * n->spacing;

        uint32_t free_space = (content_h > fixed_total) ? content_h - fixed_total : 0;

        int32_t cy = start_y;
        for (int i = 0; i < n->child_count; i++) {
            LayoutNode *c = &g_layout[n->children[i]];
            uint32_t cw, ch;

            if (c->h_mode == SM_FIXED) ch = c->h_value;
            else if (c->h_mode == SM_FILL) {
                uint32_t weight = (c->h_value > 0 ? c->h_value : 1);
                ch = (fill_weight_total > 0) ? (free_space * weight / fill_weight_total) : 0;
            } else ch = c->intrinsic_h;

            if (c->w_mode == SM_FIXED) cw = c->w_value;
            else if (c->w_mode == SM_FILL) cw = content_w;
            else cw = c->intrinsic_w;

            int32_t cx = start_x;
            if (n->h_align == ALIGN_CENTER) cx += (int32_t)(content_w - cw) / 2;
            else if (n->h_align == ALIGN_END) cx += (int32_t)(content_w - cw);

            layout_arrange(n->children[i], cx, cy, cw, ch);
            cy += (int32_t)ch + (int32_t)n->spacing;
        }
    } else if (n->type == LT_ZSTACK) {
        for (int i = 0; i < n->child_count; i++) {
            LayoutNode *c = &g_layout[n->children[i]];
            uint32_t cw = (c->w_mode == SM_FIXED) ? c->w_value : content_w;
            uint32_t ch = (c->h_mode == SM_FIXED) ? c->h_value : content_h;
            int32_t cx = start_x, cy = start_y;
            if (n->h_align == ALIGN_CENTER) cx += (int32_t)(content_w - cw) / 2;
            if (n->v_align == ALIGN_CENTER) cy += (int32_t)(content_h - ch) / 2;
            layout_arrange(n->children[i], cx, cy, cw, ch);
        }
    }
}

/* Compute layout: rt_layout_compute(pack(screen_w, screen_h), _, _, _) */
RuntimeValue rt_layout_compute(RuntimeValue wh, RuntimeValue u1,
                                RuntimeValue u2, RuntimeValue u3)
{
    (void)u1; (void)u2; (void)u3;
    uint32_t sw = (uint32_t)((uint64_t)wh >> 32);
    uint32_t sh = (uint32_t)((uint64_t)wh & 0xFFFFFFFF);

    if (g_layout_count == 0) return 0;

    /* Find root node (parent == -1) */
    int root = -1;
    for (int i = 0; i < g_layout_count; i++) {
        if (g_layout[i].active && g_layout[i].parent == -1) {
            root = i;
            break;
        }
    }
    if (root < 0) return 0;

    layout_measure(root);
    layout_arrange(root, 0, 0, sw, sh);

    return 0;
}

/* Get computed position: rt_layout_get(id, _, _, _) -> pack(x, y) */
RuntimeValue rt_layout_get(RuntimeValue id_rv, RuntimeValue u1,
                            RuntimeValue u2, RuntimeValue u3)
{
    (void)u1; (void)u2; (void)u3;
    int id = (int)(int64_t)id_rv;
    if (id < 0 || id >= g_layout_count) return 0;
    LayoutNode *n = &g_layout[id];
    uint64_t x = (uint32_t)n->cx;
    uint64_t y = (uint32_t)n->cy;
    return (RuntimeValue)((x << 32) | y);
}

/* Get computed size: rt_layout_get_size(id, _, _, _) -> pack(w, h) */
RuntimeValue rt_layout_get_size(RuntimeValue id_rv, RuntimeValue u1,
                                 RuntimeValue u2, RuntimeValue u3)
{
    (void)u1; (void)u2; (void)u3;
    int id = (int)(int64_t)id_rv;
    if (id < 0 || id >= g_layout_count) return 0;
    LayoutNode *n = &g_layout[id];
    return (RuntimeValue)(((uint64_t)n->cw << 32) | (uint64_t)n->ch);
}
