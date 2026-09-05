#include "../../../src/runtime/runtime.h"

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static unsigned char *read_file(const char *path, int64_t *size) {
    FILE *file = fopen(path, "rb");
    if (!file || fseek(file, 0, SEEK_END) != 0) return NULL;
    long length = ftell(file);
    if (length <= 0 || fseek(file, 0, SEEK_SET) != 0) { fclose(file); return NULL; }
    unsigned char *bytes = (unsigned char *)malloc((size_t)length);
    if (!bytes || fread(bytes, 1, (size_t)length, file) != (size_t)length) {
        free(bytes);
        fclose(file);
        return NULL;
    }
    fclose(file);
    *size = (int64_t)length;
    return bytes;
}

int main(void) {
    unsigned char bad_directory[12] = {0};
    unsigned char short_ttc[12] = {'t', 't', 'c', 'f'};
    if (rt_font_load_bytes(0, 12) != 0 ||
        rt_font_load_bytes((int64_t)(uintptr_t)bad_directory, 11) != 0 ||
        rt_font_load_bytes((int64_t)(uintptr_t)bad_directory, 12) != 0 ||
        rt_font_load_bytes((int64_t)(uintptr_t)short_ttc, 12) != 0) return 1;

    int64_t size = 0;
    unsigned char *bytes = read_file(
        "assets/fonts/google-fonts/ofl/unifrakturcook/UnifrakturCook-Bold.ttf", &size);
    if (!bytes) return 2;
    int64_t font = rt_font_load_bytes((int64_t)(uintptr_t)bytes, size);
    if (!font) { free(bytes); return 3; }
    memset(bytes, 0, (size_t)size);
    free(bytes);
    if (rt_font_glyph_index(font, 'A') <= 0) { rt_font_free(font); return 4; }
    int64_t bitmap = rt_font_glyph_bitmap(font, 'A', 24.0);
    if (!bitmap || rt_font_bitmap_width(bitmap) <= 0 || rt_font_bitmap_height(bitmap) <= 0) {
        rt_font_bitmap_free(bitmap);
        rt_font_free(font);
        return 5;
    }
    if (rt_font_bitmap_yoff(bitmap) >= 0 || rt_font_ascent(font, 24.0) <= 0) {
        rt_font_bitmap_free(bitmap);
        rt_font_free(font);
        return 6;
    }
    (void)rt_font_bitmap_xoff(bitmap);
    rt_font_bitmap_free(bitmap);
    rt_font_free(font);
    return 0;
}
