/* No GUI session is required: invalid handles exercise the real provider's
 * fail-closed API. Every entry point must come from the loaded runtime. */
#include <assert.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <dlfcn.h>

#define LOAD(name, result, args) \
    result (*name) args = (result (*) args)dlsym(runtime, #name); \
    assert(name != NULL)

int main(int argc, char **argv) {
    assert(argc == 2);
    void *runtime = dlopen(argv[1], RTLD_NOW | RTLD_LOCAL);
    if (!runtime) {
        fprintf(stderr, "runtime dlopen failed: %s\n", dlerror());
        return 1;
    }
    LOAD(rt_cocoa_window_new, int64_t, (int64_t, int64_t, int64_t));
    LOAD(rt_cocoa_window_resize, bool, (int64_t, int64_t, int64_t));
    LOAD(rt_cocoa_window_close, bool, (int64_t));
    LOAD(rt_cocoa_layer_create, int64_t, (int64_t, int64_t, int64_t, int64_t));
    LOAD(rt_cocoa_layer_fill_rect, bool, (int64_t, int64_t, int64_t, int64_t, int64_t, int64_t));
    LOAD(rt_cocoa_layer_present, bool, (int64_t, int64_t));
    LOAD(rt_cocoa_layer_free, bool, (int64_t));
    LOAD(rt_cocoa_layer_read_pixel, int64_t, (int64_t, int64_t, int64_t));
    LOAD(rt_cocoa_layer_blend_rect, bool, (int64_t, int64_t, int64_t, int64_t, int64_t, int64_t, int64_t));
    LOAD(rt_cocoa_layer_blur, bool, (int64_t, int64_t, int64_t, int64_t, int64_t, int64_t));
    LOAD(rt_cocoa_layer_gradient_v, bool, (int64_t, int64_t, int64_t, int64_t, int64_t, int64_t, int64_t));
    LOAD(rt_cocoa_event_pump, int64_t, (int64_t));
    assert(rt_cocoa_window_new(0, 1, 0) == -1);
    assert(!rt_cocoa_window_resize(-1, 1, 1));
    assert(!rt_cocoa_window_close(-1));
    assert(rt_cocoa_layer_create(-1, 0, 1, 0) == -1);
    assert(!rt_cocoa_layer_fill_rect(-1, 0, 0, 1, 1, 0));
    assert(!rt_cocoa_layer_present(-1, -1));
    assert(!rt_cocoa_layer_free(-1));
    assert(rt_cocoa_layer_read_pixel(-1, 0, 0) == 0);
    assert(!rt_cocoa_layer_blend_rect(-1, 0, 0, 1, 1, 0, 0));
    assert(!rt_cocoa_layer_blur(-1, 0, 0, 1, 1, 1));
    assert(!rt_cocoa_layer_gradient_v(-1, 0, 0, 1, 1, 0, 0));
    /* event_pump on the main thread initializes NSApplication even for an
     * invalid handle. Resolve its export above without creating a GUI. */
    /* An offscreen layer is intentionally independent of a window. Verify
     * real storage and drawing, so fallback stubs cannot satisfy this test. */
    int64_t layer = rt_cocoa_layer_create(-1, 2, 2, 0xff112233);
    assert(layer > 0);
    assert(rt_cocoa_layer_read_pixel(layer, 0, 0) == 0xff112233);
    assert(rt_cocoa_layer_fill_rect(layer, 1, 0, 1, 1, 0xff445566));
    assert(rt_cocoa_layer_read_pixel(layer, 1, 0) == 0xff445566);
    assert(rt_cocoa_layer_read_pixel(layer, 0, 0) == 0xff112233);
    assert(rt_cocoa_layer_free(layer));
    assert(!rt_cocoa_layer_free(layer));
    assert(dlclose(runtime) == 0);
    puts("Cocoa dylib exports, load and invalid-handle calls: PASS");
    return 0;
}
