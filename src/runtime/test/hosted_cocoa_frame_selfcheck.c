/* Link with hosted_cocoa.c on macOS to exercise the real layer frame owner.
 * The array helpers below model the validated [u8] runtime ABI; the Simple
 * integration spec separately covers adapter ordering and surface state. */
#include <assert.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

typedef struct TestBytes {
    int64_t len;
    bool valid;
    uint8_t data[16];
} TestBytes;

const char *rt_string_data(int64_t value) { (void)value; return NULL; }
int64_t rt_string_len(int64_t value) { (void)value; return 0; }
int64_t rt_array_len_safe(int64_t value) {
    return value ? ((TestBytes *)(uintptr_t)value)->len : 0;
}
int64_t rt_array_bytes_copy_checked(int64_t value, uint8_t *out,
                                    int64_t capacity) {
    TestBytes *bytes = (TestBytes *)(uintptr_t)value;
    if (!bytes || !bytes->valid || capacity < bytes->len) return -22;
    memcpy(out, bytes->data, (size_t)bytes->len);
    return bytes->len;
}

int64_t rt_cocoa_layer_create(int64_t, int64_t, int64_t, int64_t);
bool rt_cocoa_layer_write_frame(int64_t, int64_t, int64_t, int64_t);
int64_t rt_cocoa_layer_read_pixel(int64_t, int64_t, int64_t);
bool rt_cocoa_layer_present(int64_t, int64_t);
bool rt_cocoa_layer_free(int64_t);

int main(void) {
#ifdef __APPLE__
    int64_t layer = rt_cocoa_layer_create(0, 2, 2, 0);
    assert(layer > 0);
    TestBytes pixels = {.len = 16, .valid = true,
        .data = {0x33, 0x22, 0x11, 0xff, 0x66, 0x55, 0x44, 0xff,
                 0x99, 0x88, 0x77, 0xff, 0xcc, 0xbb, 0xaa, 0xff}};
    assert(rt_cocoa_layer_write_frame(layer, 2, 2,
        (int64_t)(uintptr_t)&pixels));
    assert((uint32_t)rt_cocoa_layer_read_pixel(layer, 0, 0) == 0xFF112233u);
    pixels.data[0] = 0;
    pixels.valid = false;
    assert(!rt_cocoa_layer_write_frame(layer, 2, 2,
        (int64_t)(uintptr_t)&pixels));
    assert((uint32_t)rt_cocoa_layer_read_pixel(layer, 0, 0) == 0xFF112233u);
    pixels.valid = true;
    pixels.len = 12;
    assert(!rt_cocoa_layer_write_frame(layer, 2, 2,
        (int64_t)(uintptr_t)&pixels));
    pixels.len = 16;
    assert(!rt_cocoa_layer_write_frame(layer, 3, 2,
        (int64_t)(uintptr_t)&pixels));
    assert(!rt_cocoa_layer_present(999999997, layer));
    assert(rt_cocoa_layer_free(layer));
#else
    TestBytes pixels = {.len = 4, .valid = true};
    assert(!rt_cocoa_layer_write_frame(1, 1, 1,
        (int64_t)(uintptr_t)&pixels));
#endif
    puts("COCOA_FRAME_SELFCHECK_PASS");
    return 0;
}
