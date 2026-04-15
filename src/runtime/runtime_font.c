/*
 * Simple Runtime — Font rendering subsystem (stb_truetype backend)
 *
 * Uses the vendored stb_truetype.h copy in this directory.
 * See THIRD_PARTY_NOTICES.md for redistribution details.
 * Build: cc -c -fPIC -O2 -std=gnu11 -I. -lm runtime_font.c -o runtime_font.o
 */

#define STB_TRUETYPE_IMPLEMENTATION
#include "stb_truetype.h"

#include <stdint.h>
#include <stdlib.h>
#include <stdio.h>
#include <math.h>

/* ================================================================
 * Wrapper structs
 * ================================================================ */

typedef struct {
    stbtt_fontinfo info;
    unsigned char* file_data;
} FontData;

typedef struct {
    unsigned char* data;
    int w, h;
} BitmapData;

/* ================================================================
 * Font load / free
 * ================================================================ */

int64_t rt_font_load(const char* path) {
    if (!path) return 0;

    FILE* f = fopen(path, "rb");
    if (!f) return 0;

    fseek(f, 0, SEEK_END);
    long size = ftell(f);
    fseek(f, 0, SEEK_SET);

    if (size <= 0) { fclose(f); return 0; }

    unsigned char* file_data = (unsigned char*)malloc((size_t)size);
    if (!file_data) { fclose(f); return 0; }

    size_t read = fread(file_data, 1, (size_t)size, f);
    fclose(f);
    if ((long)read != size) { free(file_data); return 0; }

    FontData* font = (FontData*)malloc(sizeof(FontData));
    if (!font) { free(file_data); return 0; }

    font->file_data = file_data;

    if (!stbtt_InitFont(&font->info, file_data,
                        stbtt_GetFontOffsetForIndex(file_data, 0))) {
        free(file_data);
        free(font);
        return 0;
    }

    return (int64_t)(uintptr_t)font;
}

void rt_font_free(int64_t handle) {
    if (!handle) return;
    FontData* font = (FontData*)(uintptr_t)handle;
    if (font->file_data) free(font->file_data);
    free(font);
}

/* ================================================================
 * Glyph bitmap
 * ================================================================ */

int64_t rt_font_glyph_bitmap(int64_t font_handle, int64_t codepoint, double size) {
    if (!font_handle || size <= 0.0) return 0;
    FontData* font = (FontData*)(uintptr_t)font_handle;

    float scale = stbtt_ScaleForPixelHeight(&font->info, (float)size);

    int w, h, xoff, yoff;
    unsigned char* pixels = stbtt_GetCodepointBitmap(
        &font->info, 0, scale, (int)codepoint, &w, &h, &xoff, &yoff);
    if (!pixels) return 0;

    BitmapData* bmp = (BitmapData*)malloc(sizeof(BitmapData));
    if (!bmp) {
        stbtt_FreeBitmap(pixels, NULL);
        return 0;
    }

    bmp->data = pixels;
    bmp->w    = w;
    bmp->h    = h;

    return (int64_t)(uintptr_t)bmp;
}

int64_t rt_font_glyph_index(int64_t font_handle, int64_t codepoint) {
    if (!font_handle) return 0;
    FontData* font = (FontData*)(uintptr_t)font_handle;
    return (int64_t)stbtt_FindGlyphIndex(&font->info, (int)codepoint);
}

int64_t rt_font_glyph_bitmap_index(int64_t font_handle, int64_t glyph_index, double size) {
    if (!font_handle || size <= 0.0 || glyph_index < 0) return 0;
    FontData* font = (FontData*)(uintptr_t)font_handle;

    float scale = stbtt_ScaleForPixelHeight(&font->info, (float)size);

    int w, h, xoff, yoff;
    unsigned char* pixels = stbtt_GetGlyphBitmap(
        &font->info, 0, scale, (int)glyph_index, &w, &h, &xoff, &yoff);
    if (!pixels) return 0;

    BitmapData* bmp = (BitmapData*)malloc(sizeof(BitmapData));
    if (!bmp) {
        stbtt_FreeBitmap(pixels, NULL);
        return 0;
    }

    bmp->data = pixels;
    bmp->w    = w;
    bmp->h    = h;

    return (int64_t)(uintptr_t)bmp;
}

int64_t rt_font_bitmap_width(int64_t bitmap_handle) {
    if (!bitmap_handle) return 0;
    return (int64_t)((BitmapData*)(uintptr_t)bitmap_handle)->w;
}

int64_t rt_font_bitmap_height(int64_t bitmap_handle) {
    if (!bitmap_handle) return 0;
    return (int64_t)((BitmapData*)(uintptr_t)bitmap_handle)->h;
}

int64_t rt_font_bitmap_get_pixel(int64_t bitmap_handle, int64_t x, int64_t y) {
    if (!bitmap_handle) return 0;
    BitmapData* bmp = (BitmapData*)(uintptr_t)bitmap_handle;

    if (x < 0 || x >= bmp->w || y < 0 || y >= bmp->h) return 0;

    return (int64_t)bmp->data[y * bmp->w + x];
}

void rt_font_bitmap_free(int64_t bitmap_handle) {
    if (!bitmap_handle) return;
    BitmapData* bmp = (BitmapData*)(uintptr_t)bitmap_handle;
    if (bmp->data) stbtt_FreeBitmap(bmp->data, NULL);
    free(bmp);
}

/* ================================================================
 * Glyph metrics
 * ================================================================ */

int64_t rt_font_glyph_advance(int64_t font_handle, int64_t codepoint, double size) {
    if (!font_handle || size <= 0.0) return 0;
    FontData* font = (FontData*)(uintptr_t)font_handle;

    float scale = stbtt_ScaleForPixelHeight(&font->info, (float)size);

    int advance, lsb;
    stbtt_GetCodepointHMetrics(&font->info, (int)codepoint, &advance, &lsb);

    return (int64_t)(advance * scale);
}

int64_t rt_font_glyph_advance_index(int64_t font_handle, int64_t glyph_index, double size) {
    if (!font_handle || size <= 0.0 || glyph_index < 0) return 0;
    FontData* font = (FontData*)(uintptr_t)font_handle;

    float scale = stbtt_ScaleForPixelHeight(&font->info, (float)size);

    int advance, lsb;
    stbtt_GetGlyphHMetrics(&font->info, (int)glyph_index, &advance, &lsb);

    return (int64_t)(advance * scale);
}

int64_t rt_font_line_height(int64_t font_handle, double size) {
    if (!font_handle || size <= 0.0) return 0;
    FontData* font = (FontData*)(uintptr_t)font_handle;

    float scale = stbtt_ScaleForPixelHeight(&font->info, (float)size);

    int ascent, descent, line_gap;
    stbtt_GetFontVMetrics(&font->info, &ascent, &descent, &line_gap);

    return (int64_t)((ascent - descent + line_gap) * scale);
}

int64_t rt_font_ascent(int64_t font_handle, double size) {
    if (!font_handle || size <= 0.0) return 0;
    FontData* font = (FontData*)(uintptr_t)font_handle;

    float scale = stbtt_ScaleForPixelHeight(&font->info, (float)size);

    int ascent, descent, line_gap;
    stbtt_GetFontVMetrics(&font->info, &ascent, &descent, &line_gap);
    return (int64_t)(ascent * scale);
}

int64_t rt_font_descent(int64_t font_handle, double size) {
    if (!font_handle || size <= 0.0) return 0;
    FontData* font = (FontData*)(uintptr_t)font_handle;

    float scale = stbtt_ScaleForPixelHeight(&font->info, (float)size);

    int ascent, descent, line_gap;
    stbtt_GetFontVMetrics(&font->info, &ascent, &descent, &line_gap);
    return (int64_t)(descent * scale);
}

int64_t rt_font_line_gap(int64_t font_handle, double size) {
    if (!font_handle || size <= 0.0) return 0;
    FontData* font = (FontData*)(uintptr_t)font_handle;

    float scale = stbtt_ScaleForPixelHeight(&font->info, (float)size);

    int ascent, descent, line_gap;
    stbtt_GetFontVMetrics(&font->info, &ascent, &descent, &line_gap);
    return (int64_t)(line_gap * scale);
}
