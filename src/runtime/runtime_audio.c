/*
 * Simple Runtime — Audio subsystem (miniaudio backend)
 *
 * Uses the vendored miniaudio.h copy in this directory.
 * See THIRD_PARTY_NOTICES.md for redistribution details.
 * Build: cc -c -fPIC -O2 -std=gnu11 -I. -lpthread -lm runtime_audio.c -o runtime_audio.o
 */

#define MINIAUDIO_IMPLEMENTATION
#if defined(__clang__)
#pragma clang diagnostic push
/* FreeBSD's Clang diagnoses backend helpers disabled by miniaudio's platform
 * selection. Keep vendored-header noise out of the owned-code -Werror gate. */
#pragma clang diagnostic ignored "-Wunused-function"
#endif
#include "miniaudio.h"
#if defined(__clang__)
#pragma clang diagnostic pop
#endif
#include "runtime.h"

#include <math.h>
#include <stdint.h>
#if defined(_WIN32) || defined(_WIN64)
#define RT_AUDIO_WINDOWS_LOCK
#include <windows.h>
#else
#include <pthread.h>
#endif
#include <stdlib.h>
#include <string.h>

/* ================================================================
 * Static engine state
 * ================================================================ */

static ma_engine  g_audio_engine;
static int        g_audio_initialized = 0;

#define RT_AUDIO_SLOT_COUNT 256
#define RT_AUDIO_HANDLE_BASE UINT64_C(4294967296)

typedef struct {
    ma_sound* sound;
    ma_audio_buffer* pcm_buffer;
    float* pcm_data;
    uint32_t generation;
    int live;
    int paused;
} rt_audio_slot;

typedef struct {
    uint32_t generation;
    int live;
} rt_audio_engine_slot;

static rt_audio_engine_slot g_engine_slots[RT_AUDIO_SLOT_COUNT];
static rt_audio_slot g_source_slots[RT_AUDIO_SLOT_COUNT];
static rt_audio_slot g_playback_slots[RT_AUDIO_SLOT_COUNT];

/* Cross-platform lock: MSVC has no <pthread.h> (no POSIX threads on Windows),
 * so this file — unlike most of the runtime, which already carries the same
 * split for runtime_pool.c — used pthread_mutex_t unconditionally and could
 * not build under MSVC at all ("fatal error C1083: Cannot open include file:
 * 'pthread.h'"). CRITICAL_SECTION needs InitializeCriticalSection() before
 * first use (no static initializer exists), so lazy-init it once via
 * InitOnceExecuteOnce, same idiom as runtime_pool.c's g_pool_lock. */
#ifdef RT_AUDIO_WINDOWS_LOCK
static CRITICAL_SECTION g_audio_lock;
static INIT_ONCE g_audio_lock_once = INIT_ONCE_STATIC_INIT;

static BOOL CALLBACK rt_audio_lock_init_once(PINIT_ONCE once, PVOID param, PVOID* context) {
    (void)once;
    (void)param;
    (void)context;
    InitializeCriticalSection(&g_audio_lock);
    return TRUE;
}

static void rt_audio_lock_ensure_init(void) {
    InitOnceExecuteOnce(&g_audio_lock_once, rt_audio_lock_init_once, NULL, NULL);
}

#define RT_AUDIO_LOCK() do { rt_audio_lock_ensure_init(); EnterCriticalSection(&g_audio_lock); } while (0)
#define RT_AUDIO_UNLOCK() LeaveCriticalSection(&g_audio_lock)
#else
static pthread_mutex_t g_audio_lock = PTHREAD_MUTEX_INITIALIZER;
#define RT_AUDIO_LOCK() pthread_mutex_lock(&g_audio_lock)
#define RT_AUDIO_UNLOCK() pthread_mutex_unlock(&g_audio_lock)
#endif

static int64_t audio_handle(size_t index, uint32_t generation) {
    return (int64_t)((uint64_t)generation * RT_AUDIO_HANDLE_BASE + index + 1);
}

static rt_audio_engine_slot* audio_engine_slot(int64_t handle) {
    if (handle <= 0) return NULL;
    uint64_t raw = (uint64_t)handle;
    uint64_t one_based = raw % RT_AUDIO_HANDLE_BASE;
    uint32_t generation = (uint32_t)(raw / RT_AUDIO_HANDLE_BASE);
    if (one_based == 0 || one_based > RT_AUDIO_SLOT_COUNT || generation == 0) {
        return NULL;
    }
    rt_audio_engine_slot* slot = &g_engine_slots[one_based - 1];
    if (!slot->live || slot->generation != generation) return NULL;
    return slot;
}

static int64_t audio_engine_store(void) {
    size_t i;
    for (i = 0; i < RT_AUDIO_SLOT_COUNT; ++i) {
        if (!g_engine_slots[i].live) {
            if (g_engine_slots[i].generation == 0) {
                g_engine_slots[i].generation = 1;
            }
            g_engine_slots[i].live = 1;
            return audio_handle(i, g_engine_slots[i].generation);
        }
    }
    return 0;
}

static int64_t audio_engine_live_count_unlocked(void) {
    int64_t count = 0;
    size_t i;
    for (i = 0; i < RT_AUDIO_SLOT_COUNT; ++i) {
        if (g_engine_slots[i].live) count += 1;
    }
    return count;
}

static rt_audio_slot* audio_slot(
    rt_audio_slot* slots, int64_t handle, size_t* index_out
) {
    if (handle <= 0) return NULL;
    uint64_t raw = (uint64_t)handle;
    uint64_t one_based = raw % RT_AUDIO_HANDLE_BASE;
    uint32_t generation = (uint32_t)(raw / RT_AUDIO_HANDLE_BASE);
    if (one_based == 0 || one_based > RT_AUDIO_SLOT_COUNT || generation == 0) {
        return NULL;
    }
    size_t index = (size_t)(one_based - 1);
    rt_audio_slot* slot = &slots[index];
    if (!slot->live || slot->generation != generation || !slot->sound) {
        return NULL;
    }
    if (index_out) *index_out = index;
    return slot;
}

static int64_t audio_store(
    rt_audio_slot* slots,
    ma_sound* sound,
    ma_audio_buffer* pcm_buffer,
    float* pcm_data
) {
    size_t i;
    for (i = 0; i < RT_AUDIO_SLOT_COUNT; ++i) {
        if (!slots[i].live) {
            if (slots[i].generation == 0) slots[i].generation = 1;
            slots[i].sound = sound;
            slots[i].pcm_buffer = pcm_buffer;
            slots[i].pcm_data = pcm_data;
            slots[i].live = 1;
            slots[i].paused = 0;
            return audio_handle(i, slots[i].generation);
        }
    }
    return 0;
}

static void audio_release_slot(rt_audio_slot* slot) {
    if (!slot || !slot->live) return;
    ma_sound_stop(slot->sound);
    ma_sound_uninit(slot->sound);
    free(slot->sound);
    if (slot->pcm_buffer) {
        ma_audio_buffer_uninit(slot->pcm_buffer);
        free(slot->pcm_buffer);
    }
    free(slot->pcm_data);
    slot->sound = NULL;
    slot->pcm_buffer = NULL;
    slot->pcm_data = NULL;
    slot->live = 0;
    slot->paused = 0;
    slot->generation += 1;
    if (slot->generation == 0) slot->generation = 1;
}

static void audio_reap_finished(void) {
    size_t i;
    for (i = 0; i < RT_AUDIO_SLOT_COUNT; ++i) {
        rt_audio_slot* slot = &g_playback_slots[i];
        if (slot->live && !slot->paused && ma_sound_at_end(slot->sound)) {
            audio_release_slot(slot);
        }
    }
}

/* ================================================================
 * Engine lifecycle
 * ================================================================ */

int64_t rt_audio_init(void) {
    RT_AUDIO_LOCK();
    int initialized_here = 0;
    if (!g_audio_initialized) {
        ma_engine_config config = ma_engine_config_init();
        config.sampleRate = 48000;
        ma_result result = ma_engine_init(&config, &g_audio_engine);
        if (result != MA_SUCCESS) {
            RT_AUDIO_UNLOCK();
            return 0;
        }
        g_audio_initialized = 1;
        initialized_here = 1;
    }

    int64_t handle = audio_engine_store();
    if (handle == 0 && initialized_here) {
        ma_engine_uninit(&g_audio_engine);
        g_audio_initialized = 0;
    }
    RT_AUDIO_UNLOCK();
    return handle;
}

const char* rt_audio_backend_name(void) {
    RT_AUDIO_LOCK();
    const char* name = "uninitialized";
    if (g_audio_initialized) {
        ma_device* device = ma_engine_get_device(&g_audio_engine);
        if (device && device->pContext) {
            name = ma_get_backend_name(device->pContext->backend);
        }
    }
    RT_AUDIO_UNLOCK();
    return name;
}

int64_t rt_audio_backend_is_real(void) {
    RT_AUDIO_LOCK();
    int64_t real = 0;
    if (g_audio_initialized) {
        ma_device* device = ma_engine_get_device(&g_audio_engine);
        real = device && device->pContext &&
            device->pContext->backend != ma_backend_null;
    }
    RT_AUDIO_UNLOCK();
    return real;
}

int64_t rt_audio_shutdown(int64_t engine_handle) {
    RT_AUDIO_LOCK();
    rt_audio_engine_slot* engine_slot = audio_engine_slot(engine_handle);
    if (!engine_slot) {
        RT_AUDIO_UNLOCK();
        return 0;
    }
    engine_slot->live = 0;
    engine_slot->generation += 1;
    if (engine_slot->generation == 0 ||
        engine_slot->generation > 0x7fffffffu) {
        engine_slot->generation = 1;
    }
    if (audio_engine_live_count_unlocked() > 0) {
        RT_AUDIO_UNLOCK();
        return 1;
    }

    size_t i;
    for (i = 0; i < RT_AUDIO_SLOT_COUNT; ++i) {
        audio_release_slot(&g_playback_slots[i]);
        audio_release_slot(&g_source_slots[i]);
    }
    ma_engine_uninit(&g_audio_engine);
    g_audio_initialized = 0;
    RT_AUDIO_UNLOCK();
    return 1;
}

/* ================================================================
 * Sound loading / unloading
 * ================================================================ */

int64_t rt_audio_load_sound(const char* path) {
    if (!path) return 0;
    RT_AUDIO_LOCK();
    if (!g_audio_initialized) {
        RT_AUDIO_UNLOCK();
        return 0;
    }

    ma_sound* sound = (ma_sound*)malloc(sizeof(ma_sound));
    if (!sound) {
        RT_AUDIO_UNLOCK();
        return 0;
    }

    ma_result result = ma_sound_init_from_file(
        &g_audio_engine, path, 0, NULL, NULL, sound);
    if (result != MA_SUCCESS) {
        free(sound);
        RT_AUDIO_UNLOCK();
        return 0;
    }
    int64_t handle = audio_store(g_source_slots, sound, NULL, NULL);
    if (!handle) {
        ma_sound_uninit(sound);
        free(sound);
    }
    RT_AUDIO_UNLOCK();
    return handle;
}

void rt_audio_unload_sound(int64_t handle) {
    RT_AUDIO_LOCK();
    audio_release_slot(audio_slot(g_source_slots, handle, NULL));
    RT_AUDIO_UNLOCK();
}

/* ================================================================
 * Playback
 * ================================================================ */

/*
 * Helper: clone a loaded sound for independent playback.
 * miniaudio allows multiple ma_sound instances from the same data source,
 * but for simplicity we re-init from the same file via ma_sound_init_copy.
 * On older miniaudio versions without _copy, we just start() the original.
 */
static int64_t play_sound_internal(int64_t sound_handle, int looped) {
    RT_AUDIO_LOCK();
    if (!g_audio_initialized) {
        RT_AUDIO_UNLOCK();
        return 0;
    }
    audio_reap_finished();
    rt_audio_slot* source = audio_slot(g_source_slots, sound_handle, NULL);
    if (!source) {
        RT_AUDIO_UNLOCK();
        return 0;
    }

    /* Create an independent copy so multiple plays don't collide */
    ma_sound* playback = (ma_sound*)malloc(sizeof(ma_sound));
    if (!playback) {
        RT_AUDIO_UNLOCK();
        return 0;
    }

    ma_result result = ma_sound_init_copy(
        &g_audio_engine, source->sound, 0, NULL, playback);
    if (result != MA_SUCCESS) {
        free(playback);
        RT_AUDIO_UNLOCK();
        return 0;
    }

    ma_sound_set_looping(playback, looped ? MA_TRUE : MA_FALSE);
    if (ma_sound_start(playback) != MA_SUCCESS) {
        ma_sound_uninit(playback);
        free(playback);
        RT_AUDIO_UNLOCK();
        return 0;
    }
    int64_t handle = audio_store(g_playback_slots, playback, NULL, NULL);
    if (!handle) {
        ma_sound_stop(playback);
        ma_sound_uninit(playback);
        free(playback);
    }
    RT_AUDIO_UNLOCK();
    return handle;
}

int64_t rt_audio_play(int64_t sound_handle) {
    return play_sound_internal(sound_handle, 0);
}

int64_t rt_audio_play_looped(int64_t sound_handle) {
    return play_sound_internal(sound_handle, 1);
}

static int64_t audio_play_pcm_owned_locked(
    float* pcm,
    size_t sample_count,
    int64_t channels
) {
    ma_audio_buffer* buffer =
        (ma_audio_buffer*)malloc(sizeof(ma_audio_buffer));
    ma_sound* playback = (ma_sound*)malloc(sizeof(ma_sound));
    if (!buffer || !playback) {
        free(pcm);
        free(buffer);
        free(playback);
        return 0;
    }

    ma_audio_buffer_config buffer_config = ma_audio_buffer_config_init(
        ma_format_f32,
        (ma_uint32)channels,
        (ma_uint64)(sample_count / (size_t)channels),
        pcm,
        NULL
    );
    if (ma_audio_buffer_init(&buffer_config, buffer) != MA_SUCCESS) {
        free(pcm);
        free(buffer);
        free(playback);
        return 0;
    }
    if (ma_sound_init_from_data_source(
        &g_audio_engine, (ma_data_source*)buffer, 0, NULL, playback
    ) != MA_SUCCESS) {
        ma_audio_buffer_uninit(buffer);
        free(pcm);
        free(buffer);
        free(playback);
        return 0;
    }
    if (ma_sound_start(playback) != MA_SUCCESS) {
        ma_sound_uninit(playback);
        ma_audio_buffer_uninit(buffer);
        free(pcm);
        free(buffer);
        free(playback);
        return 0;
    }
    int64_t handle = audio_store(
        g_playback_slots, playback, buffer, pcm
    );
    if (!handle) {
        ma_sound_stop(playback);
        ma_sound_uninit(playback);
        ma_audio_buffer_uninit(buffer);
        free(pcm);
        free(buffer);
        free(playback);
    }
    return handle;
}

#ifdef SIMPLE_RUNTIME_AUDIO_STUB_SPLARRAY
/*
 * rt_audio_play_pcm_f32 is the one rt_audio_* entry point that touches
 * SplArray (spl_array_get/spl_as_float, both defined in runtime.c). The
 * interpreter/seed crate (src/compiler_rust/runtime/build.rs) does not
 * compile runtime.c -- Rust reimplements that layer natively -- so those two
 * symbols are unavailable there, and linking the real body below fails with
 * "undefined symbol: spl_array_get". The interpreter refuses this one name
 * at the Rust dispatch layer instead of ever calling through (see
 * interpreter_extern/audio.rs: a native SplArray* is not marshallable from
 * that Value representation without a natively-linked ABI bridge, matching
 * the rt_sdl2_present_rgba/rt_glfw_present_argb precedent), so this stub
 * body is never reached from that path -- it exists only to satisfy the
 * linker. build.rs is the only caller that defines this macro; the native
 * product build (runtime_compiler.spl) does not, and keeps the real
 * implementation in the #else branch unchanged.
 */
int64_t rt_audio_play_pcm_f32(
    SplArray* samples,
    int64_t channels,
    int64_t sample_rate
) {
    (void)samples; (void)channels; (void)sample_rate;
    return 0;
}
#else
int64_t rt_audio_play_pcm_f32(
    SplArray* samples,
    int64_t channels,
    int64_t sample_rate
) {
    if (!samples || channels != 2 || sample_rate != 48000 ||
        samples->len <= 0 || samples->len % channels != 0 ||
        samples->len > INT64_C(48000) * 2 * 600) {
        return 0;
    }
    RT_AUDIO_LOCK();
    if (!g_audio_initialized) {
        RT_AUDIO_UNLOCK();
        return 0;
    }
    audio_reap_finished();

    size_t sample_count = (size_t)samples->len;
    float* pcm = (float*)malloc(sample_count * sizeof(float));
    if (!pcm) {
        RT_AUDIO_UNLOCK();
        return 0;
    }
    size_t i;
    for (i = 0; i < sample_count; ++i) {
        double value = spl_as_float(spl_array_get(samples, (int64_t)i));
        if (value > 1.0) value = 1.0;
        if (value < -1.0) value = -1.0;
        pcm[i] = (float)value;
    }
    int64_t handle = audio_play_pcm_owned_locked(
        pcm, sample_count, channels
    );
    RT_AUDIO_UNLOCK();
    return handle;
}
#endif /* SIMPLE_RUNTIME_AUDIO_STUB_SPLARRAY */

int64_t rt_audio_play_pcm_f64_raw(
    int64_t samples_addr,
    int64_t sample_count_i64,
    int64_t channels,
    int64_t sample_rate
) {
    if (samples_addr <= 0 || channels != 2 || sample_rate != 48000 ||
        sample_count_i64 <= 0 || sample_count_i64 % channels != 0 ||
        sample_count_i64 > INT64_C(48000) * 2 * 600) {
        return 0;
    }
    RT_AUDIO_LOCK();
    if (!g_audio_initialized) {
        RT_AUDIO_UNLOCK();
        return 0;
    }
    audio_reap_finished();

    size_t sample_count = (size_t)sample_count_i64;
    const double* samples =
        (const double*)(uintptr_t)samples_addr;
    float* pcm = (float*)malloc(sample_count * sizeof(float));
    if (!pcm) {
        RT_AUDIO_UNLOCK();
        return 0;
    }
    size_t i;
    for (i = 0; i < sample_count; ++i) {
        double value = samples[i];
        if (value > 1.0) value = 1.0;
        if (value < -1.0) value = -1.0;
        pcm[i] = (float)value;
    }
    int64_t handle = audio_play_pcm_owned_locked(
        pcm, sample_count, channels
    );
    RT_AUDIO_UNLOCK();
    return handle;
}

void rt_audio_stop(int64_t playback_handle) {
    RT_AUDIO_LOCK();
    audio_release_slot(audio_slot(g_playback_slots, playback_handle, NULL));
    RT_AUDIO_UNLOCK();
}

void rt_audio_pause(int64_t playback_handle) {
    RT_AUDIO_LOCK();
    rt_audio_slot* slot = audio_slot(g_playback_slots, playback_handle, NULL);
    if (slot) {
        ma_sound_stop(slot->sound);
        slot->paused = 1;
    }
    RT_AUDIO_UNLOCK();
}

void rt_audio_resume(int64_t playback_handle) {
    RT_AUDIO_LOCK();
    rt_audio_slot* slot = audio_slot(g_playback_slots, playback_handle, NULL);
    if (slot && ma_sound_start(slot->sound) == MA_SUCCESS) slot->paused = 0;
    RT_AUDIO_UNLOCK();
}

/* ================================================================
 * Volume
 * ================================================================ */

void rt_audio_set_volume(int64_t playback_handle, double volume) {
    RT_AUDIO_LOCK();
    rt_audio_slot* slot = audio_slot(g_playback_slots, playback_handle, NULL);
    if (slot) ma_sound_set_volume(slot->sound, (float)volume);
    RT_AUDIO_UNLOCK();
}

int64_t rt_audio_set_pitch(int64_t playback_handle, double pitch) {
    if (!isfinite(pitch) || pitch <= 0.0) return 0;

    RT_AUDIO_LOCK();
    rt_audio_slot* slot = audio_slot(g_playback_slots, playback_handle, NULL);
    if (slot) ma_sound_set_pitch(slot->sound, (float)pitch);
    RT_AUDIO_UNLOCK();
    return slot ? 1 : 0;
}

void rt_audio_set_master_volume(double volume) {
    RT_AUDIO_LOCK();
    if (g_audio_initialized) {
        ma_engine_set_volume(&g_audio_engine, (float)volume);
    }
    RT_AUDIO_UNLOCK();
}

double rt_audio_get_master_volume(void) {
    RT_AUDIO_LOCK();
    double volume = g_audio_initialized
        ? (double)ma_engine_get_volume(&g_audio_engine) : 0.0;
    RT_AUDIO_UNLOCK();
    return volume;
}

/* ================================================================
 * Query
 * ================================================================ */

int64_t rt_audio_is_playing(int64_t playback_handle) {
    RT_AUDIO_LOCK();
    rt_audio_slot* slot = audio_slot(g_playback_slots, playback_handle, NULL);
    int64_t playing = slot && ma_sound_is_playing(slot->sound) ? 1 : 0;
    if (slot && !slot->paused && ma_sound_at_end(slot->sound)) {
        audio_release_slot(slot);
        playing = 0;
    }
    RT_AUDIO_UNLOCK();
    return playing;
}

/* ================================================================
 * Spatial audio (3D positioning)
 * ================================================================ */

void rt_audio_set_sound_position(int64_t playback_handle, double x, double y, double z) {
    RT_AUDIO_LOCK();
    rt_audio_slot* slot = audio_slot(g_playback_slots, playback_handle, NULL);
    if (slot) ma_sound_set_position(slot->sound, (float)x, (float)y, (float)z);
    RT_AUDIO_UNLOCK();
}

void rt_audio_set_spatialization_enabled(int64_t playback_handle, int64_t enabled) {
    RT_AUDIO_LOCK();
    rt_audio_slot* slot = audio_slot(g_playback_slots, playback_handle, NULL);
    if (slot) ma_sound_set_spatialization_enabled(
        slot->sound, enabled ? MA_TRUE : MA_FALSE
    );
    RT_AUDIO_UNLOCK();
}

void rt_audio_set_listener_position(double x, double y, double z) {
    RT_AUDIO_LOCK();
    if (g_audio_initialized) {
        ma_engine_listener_set_position(
            &g_audio_engine, 0, (float)x, (float)y, (float)z
        );
    }
    RT_AUDIO_UNLOCK();
}

void rt_audio_set_listener_direction(double x, double y, double z) {
    RT_AUDIO_LOCK();
    if (g_audio_initialized) {
        ma_engine_listener_set_direction(
            &g_audio_engine, 0, (float)x, (float)y, (float)z
        );
    }
    RT_AUDIO_UNLOCK();
}

void rt_audio_set_listener_world_up(double x, double y, double z) {
    RT_AUDIO_LOCK();
    if (g_audio_initialized) {
        ma_engine_listener_set_world_up(
            &g_audio_engine, 0, (float)x, (float)y, (float)z
        );
    }
    RT_AUDIO_UNLOCK();
}

void rt_audio_set_sound_min_distance(int64_t playback_handle, double distance) {
    RT_AUDIO_LOCK();
    rt_audio_slot* slot = audio_slot(g_playback_slots, playback_handle, NULL);
    if (slot) ma_sound_set_min_distance(slot->sound, (float)distance);
    RT_AUDIO_UNLOCK();
}

void rt_audio_set_sound_max_distance(int64_t playback_handle, double distance) {
    RT_AUDIO_LOCK();
    rt_audio_slot* slot = audio_slot(g_playback_slots, playback_handle, NULL);
    if (slot) ma_sound_set_max_distance(slot->sound, (float)distance);
    RT_AUDIO_UNLOCK();
}

int64_t rt_audio_live_source_count(void) {
    RT_AUDIO_LOCK();
    int64_t count = 0;
    size_t i;
    for (i = 0; i < RT_AUDIO_SLOT_COUNT; ++i) {
        if (g_source_slots[i].live) count += 1;
    }
    RT_AUDIO_UNLOCK();
    return count;
}

int64_t rt_audio_live_device_count(void) {
    RT_AUDIO_LOCK();
    int64_t count = audio_engine_live_count_unlocked();
    RT_AUDIO_UNLOCK();
    return count;
}

int64_t rt_audio_live_playback_count(void) {
    RT_AUDIO_LOCK();
    audio_reap_finished();
    int64_t count = 0;
    size_t i;
    for (i = 0; i < RT_AUDIO_SLOT_COUNT; ++i) {
        if (g_playback_slots[i].live) count += 1;
    }
    RT_AUDIO_UNLOCK();
    return count;
}

/* ================================================================
 * Capture (recording) — miniaudio capture device -> WAV file sink
 *
 * Single active capture at a time (one static device+encoder), matching
 * the single static playback engine above. Fail-closed: if no capture
 * device is available (headless CI, no PulseAudio/ALSA capture node),
 * ma_device_init fails and rt_audio_capture_start returns 0 before any
 * file is created — callers must not treat 0 as success.
 * ================================================================ */

static ma_device  g_capture_device;
static ma_encoder g_capture_encoder;
static int        g_capture_active = 0;
static ma_uint64  g_capture_frames = 0;

static void capture_data_callback(ma_device* device, void* output, const void* input, ma_uint32 frame_count) {
    (void)device;
    (void)output;
    if (!g_capture_active || !input) return;
    ma_encoder_write_pcm_frames(&g_capture_encoder, input, frame_count, NULL);
    g_capture_frames += frame_count;
}

int64_t rt_audio_capture_start(const char* path, int64_t sample_rate, int64_t channels) {
    if (!path || g_capture_active || sample_rate <= 0 || channels <= 0) return 0;

    /* Open the capture device first: this is the step that fails when
     * there is no capture hardware/backend (headless CI). Only create the
     * WAV sink file once a device is confirmed available, so the
     * no-device path leaves no stray file behind. */
    ma_device_config dev_config = ma_device_config_init(ma_device_type_capture);
    dev_config.capture.format   = ma_format_s16;
    dev_config.capture.channels = (ma_uint32)channels;
    dev_config.sampleRate       = (ma_uint32)sample_rate;
    dev_config.dataCallback     = capture_data_callback;

    if (ma_device_init(NULL, &dev_config, &g_capture_device) != MA_SUCCESS) {
        return 0;
    }

    ma_encoder_config enc_config = ma_encoder_config_init(
        ma_encoding_format_wav, ma_format_s16, (ma_uint32)channels, (ma_uint32)sample_rate);
    if (ma_encoder_init_file(path, &enc_config, &g_capture_encoder) != MA_SUCCESS) {
        ma_device_uninit(&g_capture_device);
        return 0;
    }

    if (ma_device_start(&g_capture_device) != MA_SUCCESS) {
        ma_encoder_uninit(&g_capture_encoder);
        ma_device_uninit(&g_capture_device);
        return 0;
    }

    g_capture_frames = 0;
    g_capture_active = 1;
    return 1;
}

int64_t rt_audio_capture_is_active(void) {
    return g_capture_active ? 1 : 0;
}

int64_t rt_audio_capture_frame_count(void) {
    return (int64_t)g_capture_frames;
}

int64_t rt_audio_capture_stop(void) {
    if (!g_capture_active) return 0;
    ma_device_uninit(&g_capture_device);
    ma_encoder_uninit(&g_capture_encoder);
    g_capture_active = 0;
    return (int64_t)g_capture_frames;
}
