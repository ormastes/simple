#include "runtime.h"
#include <stdio.h>
#include <string.h>
#include <time.h>

static void wait_10ms(void) {
    const struct timespec delay = {0, 10000000};
    nanosleep(&delay, NULL);
}

int main(void) {
    if (rt_sdl3_normalize_event_type(0x100) != 1 ||
        rt_sdl3_normalize_event_type(0x206) != 3 ||
        rt_sdl3_normalize_event_type(0x300) != 4 ||
        rt_sdl3_normalize_event_type(0x303) != 5 ||
        rt_sdl3_normalize_event_type(0x400) != 6 ||
        rt_sdl3_normalize_event_type(0x401) != 7 ||
        rt_sdl3_normalize_event_type(0x403) != 8 ||
        rt_sdl3_normalize_event_type(0x9999) != 0) return 5;
    int64_t available = rt_sdl3_available();
    if (available != rt_sdl3_available()) return 1;
    int64_t initialized = rt_sdl3_init();
    if (!available && initialized) return 2;
    if (rt_sdl3_live_window_count() != 0) return 3;
    if (!initialized && rt_sdl3_pop_event() != 0) return 4;
    if (!initialized) {
        printf("sdl3_available=%lld initialized=0 windows=0\n",
               (long long)available);
        rt_sdl3_quit();
        return 77;
    }

    int64_t window = rt_sdl3_create_window("SimpleSDL3Probe", 96, 64);
    if (!window || rt_sdl3_live_window_count() != 1) return 6;
    int saw_key = 0, saw_text = 0, saw_pointer = 0, saw_button = 0;
    for (int i = 0; i < 300 && !(saw_key && saw_text && saw_pointer && saw_button); ++i) {
        int64_t kind = rt_sdl3_pop_event();
        while (kind != 0) {
            if (rt_sdl3_event_window() != 0 && rt_sdl3_event_timestamp_ns() <= 0) return 7;
            if (kind == 4 && rt_sdl3_event_key() != 0) saw_key = 1;
            if (kind == 5 && rt_sdl3_event_text()[0] != '\0') saw_text = 1;
            if (kind == 6) saw_pointer = 1;
            if (kind == 7) saw_button = 1;
            kind = rt_sdl3_pop_event();
        }
        wait_10ms();
    }
    if (!(saw_key && saw_text && saw_pointer && saw_button)) {
        fprintf(stderr, "sdl3_input_missing key=%d text=%d pointer=%d button=%d last_error=%s\n",
                saw_key, saw_text, saw_pointer, saw_button, rt_sdl3_last_error());
        return 8;
    }
    if (rt_sdl3_destroy_window(window) != 0 ||
        rt_sdl3_destroy_window(window) != 3 ||
        rt_sdl3_live_window_count() != 0) return 9;
    printf("sdl3_live_probe=pass windows=1 native_input=key,text,pointer,button\n");
    rt_sdl3_quit();
    return 0;
}
