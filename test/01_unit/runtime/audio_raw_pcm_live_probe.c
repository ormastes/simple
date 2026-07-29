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

int64_t rt_audio_init(void);
void rt_audio_shutdown(void);
int64_t rt_audio_play_pcm_f64_raw(
    int64_t samples_addr,
    int64_t sample_count,
    int64_t channels,
    int64_t sample_rate
);
void rt_audio_stop(int64_t playback_handle);
int64_t rt_audio_live_playback_count(void);

int main(void) {
    double samples[960 * 2];
    int64_t frame;
    for (frame = 0; frame < 960; ++frame) {
        double sample = (frame % 54) < 27 ? 0.05 : -0.05;
        samples[frame * 2] = sample;
        samples[frame * 2 + 1] = sample;
    }
    if (rt_audio_init() <= 0) return 1;
    int64_t handle = rt_audio_play_pcm_f64_raw(
        (int64_t)(uintptr_t)samples, 960 * 2, 2, 48000
    );
    if (handle <= 0) {
        rt_audio_shutdown();
        return 2;
    }
    if (rt_audio_live_playback_count() <= 0) {
        rt_audio_shutdown();
        return 3;
    }
    rt_audio_stop(handle);
    if (rt_audio_live_playback_count() != 0) {
        rt_audio_shutdown();
        return 4;
    }
    rt_audio_stop(handle);
    rt_audio_shutdown();
    rt_audio_shutdown();
    return 0;
}
