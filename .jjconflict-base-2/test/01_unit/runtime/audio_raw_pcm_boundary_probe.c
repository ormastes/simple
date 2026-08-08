#include "runtime.h"

SplValue spl_array_get(SplArray* array, int64_t index) {
    SplValue value = {0};
    (void)array;
    (void)index;
    return value;
}

double spl_as_float(SplValue value) {
    (void)value;
    return 0.0;
}

int64_t rt_audio_play_pcm_f64_raw(
    int64_t samples_addr,
    int64_t sample_count,
    int64_t channels,
    int64_t sample_rate
);

int main(void) {
    if (rt_audio_play_pcm_f64_raw(0, 2, 2, 48000) != 0) return 1;
    if (rt_audio_play_pcm_f64_raw(1, 0, 2, 48000) != 0) return 2;
    if (rt_audio_play_pcm_f64_raw(1, 2, 1, 48000) != 0) return 3;
    /* Device is deliberately not initialized: valid shape must fail closed
       before the trusted internal address is dereferenced. */
    if (rt_audio_play_pcm_f64_raw(1, 2, 2, 48000) != 0) return 4;
    return 0;
}
