#include "runtime.h"

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

int64_t rt_glfw_init(void);
void rt_glfw_terminate(void);
int64_t rt_glfw_create_window(const char*, int64_t, int64_t);
int64_t rt_glfw_destroy_window(int64_t);
int64_t rt_glfw_present_argb(int64_t, SplArray*, int64_t, int64_t);
int64_t rt_glfw_present_argb_words_raw(
    int64_t, int64_t, int64_t, int64_t, int64_t
);
int64_t rt_glfw_poll_event(void);
int64_t rt_glfw_pump_events(void);
int64_t rt_glfw_pop_event(void);
int64_t rt_glfw_event_key(void);
const char* rt_glfw_event_text(void);
int64_t rt_glfw_framebuffer_width(int64_t);
int64_t rt_glfw_framebuffer_height(int64_t);
int64_t rt_glfw_window_width(int64_t);
int64_t rt_glfw_window_height(int64_t);
int64_t rt_glfw_frame_sequence(int64_t);
int64_t rt_glfw_buffer_growth_count(int64_t);
int64_t rt_glfw_live_window_count(void);
int64_t rt_glfw_clipboard_set(int64_t, const char*);
const char* rt_glfw_clipboard_get(int64_t);

int64_t spl_array_get_i64(SplArray* array, int64_t index) {
    if (!array || index < 0 || index >= array->len) return 0;
    return array->items[index].as_int;
}

static void wait_10ms(void) {
    const struct timespec delay = {0, 10000000};
    nanosleep(&delay, NULL);
}

int main(void) {
    enum { width = 96, height = 64, count = width * height };
    uint8_t* storage = calloc(count * sizeof(uint32_t) + 4, 1);
    if (!storage) return 1;
    /* Valid ARGB32 alignment; intentionally rejects the old i64-word ABI. */
    uint32_t* pixels = (uint32_t*)(storage + 4);
    for (int i = 0; i < count; ++i) {
        pixels[i] = (i / width < height / 2)
            ? UINT32_C(0xff204080) : UINT32_C(0xffd06020);
    }

    if (rt_glfw_init() != 1) {
        puts("glfw_live_probe=unavailable runtime=missing-or-headless");
        return 77;
    }
    int64_t window = rt_glfw_create_window("SimpleGLFWProbe", width, height);
    if (!window || rt_glfw_live_window_count() != 1) return 3;
    if (rt_glfw_framebuffer_width(window) <= 0 ||
        rt_glfw_framebuffer_height(window) <= 0 ||
        rt_glfw_window_width(window) != width ||
        rt_glfw_window_height(window) != height) return 4;
    if (rt_glfw_present_argb_words_raw(
            window, 0, count, width, height
        ) != 5 ||
        rt_glfw_present_argb_words_raw(
            window, (int64_t)(uintptr_t)pixels, count - 1, width, height
        ) != 5 ||
        rt_glfw_present_argb_words_raw(
            window, (int64_t)(uintptr_t)pixels, count, width, height
        ) != 0 ||
        rt_glfw_present_argb_words_raw(
            window, (int64_t)(uintptr_t)pixels, count, width, height
        ) != 0 ||
        rt_glfw_frame_sequence(window) != 2 ||
        rt_glfw_buffer_growth_count(window) != 1) return 5;
    if (rt_glfw_clipboard_set(window, "Simple123") != 0 ||
        strcmp(rt_glfw_clipboard_get(window), "Simple123") != 0) return 6;

    int saw_key = 0, saw_text = 0, saw_pointer = 0, saw_button = 0;
    for (int i = 0; i < 300 && !(saw_key && saw_text &&
                                  saw_pointer && saw_button); ++i) {
        if (rt_glfw_pump_events() != 1) return 7;
        int64_t kind = rt_glfw_pop_event();
        while (kind != 0) {
            if (kind == 4 && rt_glfw_event_key() != 0) saw_key = 1;
            if (kind == 5 && rt_glfw_event_text()[0] != '\0') saw_text = 1;
            if (kind == 6) saw_pointer = 1;
            if (kind == 7) saw_button = 1;
            kind = rt_glfw_pop_event();
        }
        wait_10ms();
    }
    if (!(saw_key && saw_text && saw_pointer && saw_button)) return 7;
    if (rt_glfw_destroy_window(window) != 0 ||
        rt_glfw_destroy_window(window) != 3 ||
        rt_glfw_live_window_count() != 0) return 8;
    rt_glfw_terminate();
    rt_glfw_terminate();
    free(storage);
    puts("glfw_live_probe=pass packed_argb32=1 frames=2 native_input=key,text,pointer,button");
    return 0;
}
