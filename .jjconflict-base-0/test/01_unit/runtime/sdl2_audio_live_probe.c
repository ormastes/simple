#include "runtime.h"

#include <assert.h>
#include <stdint.h>
#include <stdio.h>

int main(void) {
    double pcm[8] = {0.25, -0.25, 2.0, -2.0, 0.5, -0.5, 0.0, 0.0};

    int64_t first = rt_audio_sdl2_init();
    assert(first > 0);
    assert(rt_audio_sdl2_init() == first);
    assert(rt_audio_sdl2_live_device_count() == 1);
    assert(rt_audio_sdl2_queue_pcm_f64_raw(first + 1, (int64_t)(uintptr_t)pcm, 8, 2, 48000) == 0);
    assert(rt_audio_sdl2_queue_pcm_f64_raw(first, -1, 8, 2, 48000) == 0);
    assert(rt_audio_sdl2_queue_pcm_f64_raw(first, (int64_t)(uintptr_t)pcm, 8, 2, 48000) == 4);
    assert(rt_audio_sdl2_queue_pcm_f64_raw(
        first, (int64_t)(uintptr_t)pcm,
        ((int64_t)UINT32_MAX / (int64_t)sizeof(float)) + 1, 2, 48000
    ) == 0);
    assert(rt_audio_sdl2_submitted_frames(first) == 4);
    assert(rt_audio_sdl2_underrun_count(first) == -1);
    assert(rt_audio_sdl2_close(first) == 1);
    assert(rt_audio_sdl2_close(first) == 0);
    assert(rt_audio_sdl2_live_device_count() == 0);

    int64_t second = rt_audio_sdl2_init();
    assert(second > 0 && second != first);
    assert(rt_audio_sdl2_close(first) == 0);
    assert(rt_audio_sdl2_live_device_count() == 1);
    assert(rt_audio_sdl2_queue_pcm_f64_raw(first, (int64_t)(uintptr_t)pcm, 8, 2, 48000) == 0);
    assert(rt_audio_sdl2_close(second) == 1);
    puts("sdl2-audio-live: PASS");
    return 0;
}
