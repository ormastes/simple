/* Compile hosted_cocoa.c with __APPLE__ unset: no runtime or ObjC dependency. */
#include <assert.h>
#define SIMPLE_COCOA_PROVIDER_ONLY
#include "../../../src/runtime/hosted_cocoa.c"

int main(void) {
    assert(rt_cocoa_window_new_raw(1, 1, "x", 1) == -1);
    assert(!rt_cocoa_window_resize(1, 1, 1));
    assert(!rt_cocoa_window_close(1));
    assert(rt_cocoa_layer_create(-1, 1, 1, 0) == -1);
    assert(!rt_cocoa_layer_fill_rect(1, 0, 0, 1, 1, 0));
    assert(!rt_cocoa_layer_present(1, 1));
    assert(!rt_cocoa_layer_free(1));
    assert(rt_cocoa_layer_read_pixel(1, 0, 0) == 0);
    assert(!rt_cocoa_layer_blend_rect(1, 0, 0, 1, 1, 0, 255));
    assert(!rt_cocoa_layer_blur(1, 0, 0, 1, 1, 1));
    assert(!rt_cocoa_layer_gradient_v(1, 0, 0, 1, 1, 0, 0));
    assert(rt_cocoa_event_pump(1) == 0);
    return 0;
}
