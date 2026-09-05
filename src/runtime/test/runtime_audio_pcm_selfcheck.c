#include "runtime.h"

#include <stdio.h>

SplValue spl_array_get(SplArray* array, int64_t index) {
    if (!array || index < 0 || index >= array->len) {
        SplValue nil = { .tag = SPL_NIL };
        return nil;
    }
    return array->items[index];
}

double spl_as_float(SplValue value) {
    return value.tag == SPL_FLOAT ? value.as_float : 0.0;
}

int main(void) {
    int64_t engine = rt_audio_init();
    if (!engine) {
        puts("UNAVAILABLE: miniaudio device");
        return 77;
    }
    SplValue values[960];
    SplArray samples = { .items = values, .len = 960, .cap = 960 };
    for (int i = 0; i < 480; ++i) {
        double sample = (i % 32 < 16) ? 0.1 : -0.1;
        values[i * 2].tag = SPL_FLOAT;
        values[i * 2].as_float = sample;
        values[i * 2 + 1].tag = SPL_FLOAT;
        values[i * 2 + 1].as_float = sample;
    }
    int64_t playback = rt_audio_play_pcm_f32(&samples, 2, 48000);
    if (!playback || rt_audio_live_playback_count() < 1) {
        rt_audio_shutdown(engine);
        return 2;
    }
    rt_audio_stop(playback);
    if (rt_audio_live_playback_count() != 0) {
        rt_audio_shutdown(engine);
        return 3;
    }
    rt_audio_shutdown(engine);
    puts("PASS: miniaudio PCM playback handles returned to baseline");
    return 0;
}
