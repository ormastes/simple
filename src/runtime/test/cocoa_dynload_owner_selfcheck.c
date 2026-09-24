/* Verify the dynamic Cocoa owner without opening a window. */
#include <assert.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <dlfcn.h>

int main(int argc, char **argv) {
    if (argc != 2) return 2;
    void *runtime = dlopen(argv[1], RTLD_NOW | RTLD_LOCAL);
    if (!runtime) {
        fprintf(stderr, "Cocoa runtime load failed: %s\n", dlerror());
        return 1;
    }
    const char *names[] = {
        "window_new", "window_resize", "window_close", "layer_create",
        "layer_fill_rect", "layer_present", "layer_free", "layer_read_pixel",
        "layer_blend_rect", "layer_blur", "layer_gradient_v", "event_pump"
    };
    for (unsigned i = 0; i < sizeof(names) / sizeof(names[0]); ++i) {
        char symbol[64];
        snprintf(symbol, sizeof(symbol), "rt_cocoa_%s", names[i]);
        if (!dlsym(runtime, symbol)) {
            fprintf(stderr, "Cocoa runtime missing %s\n", symbol);
            dlclose(runtime);
            return 1;
        }
    }
    int64_t (*create)(int64_t, int64_t, int64_t, int64_t) =
        (int64_t (*)(int64_t, int64_t, int64_t, int64_t))dlsym(runtime, "rt_cocoa_layer_create");
    bool (*fill)(int64_t, int64_t, int64_t, int64_t, int64_t, int64_t) =
        (bool (*)(int64_t, int64_t, int64_t, int64_t, int64_t, int64_t))dlsym(runtime, "rt_cocoa_layer_fill_rect");
    int64_t (*read_pixel)(int64_t, int64_t, int64_t) =
        (int64_t (*)(int64_t, int64_t, int64_t))dlsym(runtime, "rt_cocoa_layer_read_pixel");
    bool (*free_layer)(int64_t) = (bool (*)(int64_t))dlsym(runtime, "rt_cocoa_layer_free");
    assert(create(0, 0, 2, 0) == -1);
    int64_t layer = create(0, 3, 2, 0xff112233);
    assert(layer != -1);
    assert(read_pixel(layer, 0, 0) == 0xff112233);
    assert(fill(layer, 1, 0, 1, 2, 0xffaabbcc));
    assert(read_pixel(layer, 1, 1) == 0xffaabbcc);
    assert(read_pixel(layer, 2, 1) == 0xff112233);
    assert(free_layer(layer));
    assert(!free_layer(layer));
    assert(read_pixel(layer, 0, 0) == 0);
    assert(dlclose(runtime) == 0);
    puts("Cocoa dynamic owner pixels: PASS");
    return 0;
}
