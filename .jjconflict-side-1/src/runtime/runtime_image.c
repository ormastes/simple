/*
 * Simple Runtime — Image loading subsystem (stb_image backend)
 *
 * Uses the vendored stb_image.h copy in this directory.
 * See THIRD_PARTY_NOTICES.md for redistribution details.
 * Build: cc -c -fPIC -O2 -std=gnu11 -I. runtime_image.c -o runtime_image.o
 */

#define STB_IMAGE_IMPLEMENTATION
#include "stb_image.h"

#include <stdint.h>
#include <stdlib.h>

/* ================================================================
 * Wrapper struct: keeps dimensions alongside pixel data
 * ================================================================ */

typedef struct {
    unsigned char* data;
    int w, h, ch;
} ImageData;

/* ================================================================
 * Load / Free
 * ================================================================ */

int64_t rt_image_load(const char* path) {
    if (!path) return 0;

    int w, h, ch;
    unsigned char* data = stbi_load(path, &w, &h, &ch, 0);
    if (!data) return 0;

    ImageData* img = (ImageData*)malloc(sizeof(ImageData));
    if (!img) {
        stbi_image_free(data);
        return 0;
    }

    img->data = data;
    img->w    = w;
    img->h    = h;
    img->ch   = ch;

    return (int64_t)(uintptr_t)img;
}

void rt_image_free(int64_t handle) {
    if (!handle) return;
    ImageData* img = (ImageData*)(uintptr_t)handle;
    if (img->data) stbi_image_free(img->data);
    free(img);
}

/* ================================================================
 * Accessors
 * ================================================================ */

int64_t rt_image_width(int64_t handle) {
    if (!handle) return 0;
    return (int64_t)((ImageData*)(uintptr_t)handle)->w;
}

int64_t rt_image_height(int64_t handle) {
    if (!handle) return 0;
    return (int64_t)((ImageData*)(uintptr_t)handle)->h;
}

int64_t rt_image_channels(int64_t handle) {
    if (!handle) return 0;
    return (int64_t)((ImageData*)(uintptr_t)handle)->ch;
}

int64_t rt_image_get_pixel(int64_t handle, int64_t x, int64_t y) {
    if (!handle) return 0;
    ImageData* img = (ImageData*)(uintptr_t)handle;

    if (x < 0 || x >= img->w || y < 0 || y >= img->h) return 0;

    int idx = (int)(y * img->w + x) * img->ch;
    unsigned char r = img->data[idx];
    unsigned char g = (img->ch > 1) ? img->data[idx + 1] : r;
    unsigned char b = (img->ch > 2) ? img->data[idx + 2] : r;
    unsigned char a = (img->ch > 3) ? img->data[idx + 3] : 255;

    /* Pack as 0xRRGGBBAA */
    return (int64_t)(((uint32_t)r << 24) | ((uint32_t)g << 16) |
                     ((uint32_t)b << 8)  | (uint32_t)a);
}
