/* No GUI session is required: invalid handles exercise the real provider's
 * fail-closed API. Every entry point must come from the loaded runtime. */
#include <assert.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <dlfcn.h>
#ifdef SIMPLE_COCOA_PROVIDER_ONLY
#include <string.h>
#include <mach-o/dyld.h>
#endif

#define LOAD(name, result, args) \
    result (*name) args = (result (*) args)dlsym(runtime, #name); \
    assert(name != NULL)

int main(int argc, char **argv) {
#ifdef SIMPLE_COCOA_PROVIDER_ONLY
    assert(argc == 2 || (argc == 3 && !strcmp(argv[2], "--window")));
#else
    assert(argc == 2);
#endif
#ifdef SIMPLE_COCOA_PROVIDER_ONLY
    /* The diagnostic loader itself has no UI dependency or startup effect. */
    for (uint32_t i = 0; i < _dyld_image_count(); i++) {
        const char *name = _dyld_get_image_name(i);
        assert(!strstr(name, "libspl_cocoa"));
        assert(!strstr(name, "/AppKit.framework/"));
    }
#endif
    void *runtime = dlopen(argv[1], RTLD_NOW | RTLD_LOCAL);
    if (!runtime) {
        fprintf(stderr, "runtime dlopen failed: %s\n", dlerror());
        return 1;
    }
#ifdef SIMPLE_COCOA_PROVIDER_ONLY
    LOAD(rt_cocoa_window_new_raw, int64_t, (int64_t, int64_t, const char *, int64_t));
    assert(dlsym(runtime, "rt_cocoa_window_new") == NULL);
    assert(rt_cocoa_window_new_raw(0, 1, NULL, 0) == -1);
    assert(rt_cocoa_window_new_raw(1, 1, NULL, 1) == -1);
    assert(rt_cocoa_window_new_raw(1, 1, "a", -1) == -1);
    assert(rt_cocoa_window_new_raw(1, 1, "a", 1048577) == -1);
    assert(rt_cocoa_window_new_raw(1, 1, "a\0b", 3) == -1);
#else
    LOAD(rt_cocoa_window_new, int64_t, (int64_t, int64_t, int64_t));
    assert(rt_cocoa_window_new(0, 1, 0) == -1);
#endif
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
#ifdef SIMPLE_COCOA_PROVIDER_ONLY
    if (argc == 3) {
        for (int cycle = 0; cycle < 3; cycle++) {
            /* No trailing NUL within the passed bound. */
            const char title[] = {'r', 'a', 'w', '-', 't', 'i', 't', 'l', 'e'};
            int64_t window = rt_cocoa_window_new_raw(160, 120, title, sizeof(title));
            assert(window > 0);
            int64_t frame = rt_cocoa_layer_create(window, 160, 120, 0xff224466);
            assert(frame > 0);
            assert(rt_cocoa_layer_present(window, frame));
            for (int event = 0; event < 10; event++) rt_cocoa_event_pump(window);
            assert(rt_cocoa_layer_free(frame));
            assert(rt_cocoa_window_close(window));
            assert(!rt_cocoa_window_close(window));
        }
        puts("Diagnostic provider: raw-title windows/present/event/close x3: PASS");
    }
    /* Objective-C registration is process-lived. Keep the mapping retained;
     * freeing the final layer does not prove the framework can be unloaded. */
    puts("Diagnostic provider: no-demand closure, raw title, offscreen operations, retained mapping: PASS");
#else
    assert(dlclose(runtime) == 0);
    puts("Cocoa dylib exports, load and invalid-handle calls: PASS");
#endif
    return 0;
}
