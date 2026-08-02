#include "runtime.h"
#include <stdio.h>
#include <string.h>

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
int64_t rt_audio_shutdown(int64_t engine_handle);
int64_t rt_audio_play_pcm_f64_raw(
    int64_t samples_addr,
    int64_t sample_count,
    int64_t channels,
    int64_t sample_rate
);
void rt_audio_stop(int64_t playback_handle);
int64_t rt_audio_live_playback_count(void);
int64_t rt_audio_live_device_count(void);
const char* rt_audio_backend_name(void);
int64_t rt_audio_backend_is_real(void);
int64_t rt_audio_live_source_count(void);

int main(int argc, char** argv) {
    double samples[960 * 2];
    int64_t frame;
    for (frame = 0; frame < 960; ++frame) {
        double sample = (frame % 54) < 27 ? 0.05 : -0.05;
        samples[frame * 2] = sample;
        samples[frame * 2 + 1] = sample;
    }
    if (rt_audio_live_device_count() != 0) return 1;
    int64_t first_engine = rt_audio_init();
    int64_t second_engine = rt_audio_init();
    if (first_engine <= 0 || second_engine <= 0 ||
        first_engine == second_engine ||
        rt_audio_live_device_count() != 2) return 1;
    const char* backend = rt_audio_backend_name();
    if (!backend || backend[0] == '\0' || strcmp(backend, "uninitialized") == 0)
        return 1;
    if ((strcmp(backend, "Null") == 0) == (rt_audio_backend_is_real() != 0))
        return 1;
    printf("audio_backend=%s real=%lld\n", backend,
           (long long)rt_audio_backend_is_real());
    if (argc > 1 && strcmp(argv[1], "--require-real") == 0 &&
        rt_audio_backend_is_real() == 0) {
        rt_audio_shutdown(first_engine);
        rt_audio_shutdown(second_engine);
        return 77;
    }
    if (!rt_audio_shutdown(first_engine) ||
        rt_audio_live_device_count() != 1 ||
        rt_audio_shutdown(first_engine)) return 1;
    int64_t handle = rt_audio_play_pcm_f64_raw(
        (int64_t)(uintptr_t)samples, 960 * 2, 2, 48000
    );
    if (handle <= 0) {
        rt_audio_shutdown(second_engine);
        return 2;
    }
    if (rt_audio_live_playback_count() <= 0) {
        rt_audio_shutdown(second_engine);
        return 3;
    }
    rt_audio_stop(handle);
    if (rt_audio_live_playback_count() != 0) {
        rt_audio_shutdown(second_engine);
        return 4;
    }
    rt_audio_stop(handle);
    if (!rt_audio_shutdown(second_engine) ||
        rt_audio_shutdown(second_engine)) return 5;
    if (rt_audio_live_device_count() != 0 ||
        rt_audio_live_playback_count() != 0 ||
        rt_audio_live_source_count() != 0) return 5;
    return 0;
}
