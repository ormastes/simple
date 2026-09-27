/* Load the admitted Cocoa provider without opening a GUI window. */
#include <dlfcn.h>
#include <stdint.h>
#include <stdio.h>

typedef int64_t (*window_new_fn)(int64_t, int64_t, int64_t);

int main(int argc, char **argv) {
    if (argc != 2) {
        fprintf(stderr, "usage: cocoa-owner <libsimple_runtime.dylib>\n");
        return 2;
    }
    void *runtime = dlopen(argv[1], RTLD_NOW | RTLD_LOCAL);
    if (runtime == NULL) {
        fprintf(stderr, "Cocoa runtime dlopen failed: %s\n", dlerror());
        return 1;
    }
    const char *names[] = {
        "rt_cocoa_window_new", "rt_cocoa_window_resize", "rt_cocoa_window_close",
        "rt_cocoa_layer_create", "rt_cocoa_layer_fill_rect",
        "rt_cocoa_layer_present", "rt_cocoa_layer_free",
        "rt_cocoa_layer_read_pixel", "rt_cocoa_layer_blend_rect",
        "rt_cocoa_layer_blur", "rt_cocoa_layer_gradient_v",
        "rt_cocoa_event_pump",
    };
    for (unsigned i = 0; i < sizeof(names) / sizeof(names[0]); ++i) {
        if (dlsym(runtime, names[i]) == NULL) {
            fprintf(stderr, "Cocoa runtime missing %s\n", names[i]);
            dlclose(runtime);
            return 1;
        }
    }
    window_new_fn window_new = (window_new_fn)dlsym(runtime, names[0]);
    if (window_new(-1, 0, 0) != -1) {
        fprintf(stderr, "Cocoa runtime accepted invalid window dimensions\n");
        dlclose(runtime);
        return 1;
    }
    if (dlclose(runtime) != 0) {
        fprintf(stderr, "Cocoa runtime dlclose failed: %s\n", dlerror());
        return 1;
    }
    return 0;
}
