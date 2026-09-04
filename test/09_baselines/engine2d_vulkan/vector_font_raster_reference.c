#include "runtime.h"

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>

#define FIRST_CODEPOINT 32
#define LAST_CODEPOINT 126
#define SAMPLE_COUNT 31

static uint64_t monotonic_ns(void) {
    struct timespec now;
    if (clock_gettime(CLOCK_MONOTONIC, &now) != 0) return 0;
    return (uint64_t)now.tv_sec * 1000000000ULL + (uint64_t)now.tv_nsec;
}

static int compare_u64(const void *left, const void *right) {
    const uint64_t a = *(const uint64_t *)left;
    const uint64_t b = *(const uint64_t *)right;
    return (a > b) - (a < b);
}

int main(int argc, char **argv) {
    if (argc != 2) return 2;
    const int64_t font = rt_font_load(argv[1]);
    if (!font) return 2;

    uint64_t samples[SAMPLE_COUNT] = {0};
    uint64_t checksum = 1469598103934665603ULL;
    uint64_t coverage = 0;
    uint64_t output_pixels = 0;
    int64_t rendered_glyphs = 0;

    for (int sample = 0; sample < SAMPLE_COUNT; sample++) {
        const uint64_t start = monotonic_ns();
        for (int codepoint = FIRST_CODEPOINT; codepoint <= LAST_CODEPOINT; codepoint++) {
            const int64_t bitmap = rt_font_glyph_bitmap(font, codepoint, 24.0);
            if (!bitmap) continue;
            const int64_t width = rt_font_bitmap_width(bitmap);
            const int64_t height = rt_font_bitmap_height(bitmap);
            if (sample == SAMPLE_COUNT - 1) {
                const int64_t xoff = rt_font_bitmap_xoff(bitmap);
                const int64_t yoff = rt_font_bitmap_yoff(bitmap);
                const int64_t advance = rt_font_glyph_advance(font, codepoint, 24.0);
                rendered_glyphs++;
                output_pixels += (uint64_t)(width * height);
                checksum ^= (uint64_t)width;
                checksum *= 1099511628211ULL;
                checksum ^= (uint64_t)height;
                checksum *= 1099511628211ULL;
                checksum ^= (uint64_t)xoff;
                checksum *= 1099511628211ULL;
                checksum ^= (uint64_t)yoff;
                checksum *= 1099511628211ULL;
                checksum ^= (uint64_t)advance;
                checksum *= 1099511628211ULL;
                for (int64_t y = 0; y < height; y++) {
                    for (int64_t x = 0; x < width; x++) {
                        const uint64_t alpha =
                            (uint64_t)rt_font_bitmap_get_pixel(bitmap, x, y);
                        coverage += alpha;
                        checksum ^= alpha;
                        checksum *= 1099511628211ULL;
                    }
                }
            }
            rt_font_bitmap_free(bitmap);
        }
        samples[sample] = monotonic_ns() - start;
    }
    rt_font_free(font);

    qsort(samples, SAMPLE_COUNT, sizeof(samples[0]), compare_u64);
    printf("vector_font_reference_schema=stb-raster-v1\n");
    printf("vector_font_reference_glyphs=%lld\n", (long long)rendered_glyphs);
    printf("vector_font_reference_samples=%d\n", SAMPLE_COUNT);
    printf("vector_font_reference_p50_ns=%llu\n",
           (unsigned long long)samples[15]);
    printf("vector_font_reference_p95_ns=%llu\n",
           (unsigned long long)samples[29]);
    printf("vector_font_reference_output_pixels=%llu\n",
           (unsigned long long)output_pixels);
    printf("vector_font_reference_coverage=%llu\n",
           (unsigned long long)coverage);
    printf("vector_font_reference_checksum=%lld\n", (long long)checksum);
    /* U+0020 is advance-only and therefore has no bitmap. */
    return rendered_glyphs == LAST_CODEPOINT - FIRST_CODEPOINT && coverage > 0 ? 0 : 1;
}
