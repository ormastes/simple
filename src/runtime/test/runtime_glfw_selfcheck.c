#include "../runtime.h"

#include <stdint.h>

int64_t spl_array_get_i64(SplArray* array, int64_t index) {
    (void)array;
    (void)index;
    return 0;
}

int main(void) {
    if (rt_glfw_pump_events() != 0 || rt_glfw_pop_event() != 0) return 1;
    int64_t initialized = rt_glfw_init();
    if (rt_glfw_live_window_count() != 0 ||
        rt_glfw_queued_event_count() != 0) return 2;
    if (initialized) rt_glfw_terminate();
    if (rt_glfw_live_window_count() != 0 ||
        rt_glfw_queued_event_count() != 0) return 3;
    return initialized == 0 || initialized == 1 ? 0 : 1;
}
