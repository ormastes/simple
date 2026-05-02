/*
 * Simple Runtime — Audio subsystem (miniaudio backend)
 *
 * Uses the vendored miniaudio.h copy in this directory.
 * See THIRD_PARTY_NOTICES.md for redistribution details.
 * Build: cc -c -fPIC -O2 -std=gnu11 -I. -lpthread -lm runtime_audio.c -o runtime_audio.o
 */

#define MINIAUDIO_IMPLEMENTATION
#include "miniaudio.h"

#include <stdint.h>
#include <stdlib.h>
#include <string.h>

/* ================================================================
 * Static engine state
 * ================================================================ */

static ma_engine  g_audio_engine;
static int        g_audio_initialized = 0;

/* ================================================================
 * Engine lifecycle
 * ================================================================ */

int64_t rt_audio_init(void) {
    if (g_audio_initialized) return 1;

    ma_result result = ma_engine_init(NULL, &g_audio_engine);
    if (result != MA_SUCCESS) return 0;

    g_audio_initialized = 1;
    return 1;
}

void rt_audio_shutdown(void) {
    if (!g_audio_initialized) return;
    ma_engine_uninit(&g_audio_engine);
    g_audio_initialized = 0;
}

/* ================================================================
 * Sound loading / unloading
 * ================================================================ */

int64_t rt_audio_load_sound(const char* path) {
    if (!g_audio_initialized || !path) return 0;

    ma_sound* sound = (ma_sound*)malloc(sizeof(ma_sound));
    if (!sound) return 0;

    ma_result result = ma_sound_init_from_file(
        &g_audio_engine, path, 0, NULL, NULL, sound);
    if (result != MA_SUCCESS) {
        free(sound);
        return 0;
    }

    return (int64_t)(uintptr_t)sound;
}

void rt_audio_unload_sound(int64_t handle) {
    if (!handle) return;
    ma_sound* sound = (ma_sound*)(uintptr_t)handle;
    ma_sound_uninit(sound);
    free(sound);
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
    if (!g_audio_initialized || !sound_handle) return 0;

    ma_sound* src = (ma_sound*)(uintptr_t)sound_handle;

    /* Create an independent copy so multiple plays don't collide */
    ma_sound* playback = (ma_sound*)malloc(sizeof(ma_sound));
    if (!playback) return 0;

    ma_result result = ma_sound_init_copy(
        &g_audio_engine, src, 0, NULL, playback);
    if (result != MA_SUCCESS) {
        free(playback);
        return 0;
    }

    ma_sound_set_looping(playback, looped ? MA_TRUE : MA_FALSE);
    ma_sound_start(playback);

    return (int64_t)(uintptr_t)playback;
}

int64_t rt_audio_play(int64_t sound_handle) {
    return play_sound_internal(sound_handle, 0);
}

int64_t rt_audio_play_looped(int64_t sound_handle) {
    return play_sound_internal(sound_handle, 1);
}

void rt_audio_stop(int64_t playback_handle) {
    if (!playback_handle) return;
    ma_sound* s = (ma_sound*)(uintptr_t)playback_handle;
    ma_sound_stop(s);
    ma_sound_uninit(s);
    free(s);
}

void rt_audio_pause(int64_t playback_handle) {
    if (!playback_handle) return;
    ma_sound* s = (ma_sound*)(uintptr_t)playback_handle;
    ma_sound_stop(s);  /* miniaudio: stop without uninit = pause */
}

void rt_audio_resume(int64_t playback_handle) {
    if (!playback_handle) return;
    ma_sound* s = (ma_sound*)(uintptr_t)playback_handle;
    ma_sound_start(s);
}

/* ================================================================
 * Volume
 * ================================================================ */

void rt_audio_set_volume(int64_t playback_handle, double volume) {
    if (!playback_handle) return;
    ma_sound* s = (ma_sound*)(uintptr_t)playback_handle;
    ma_sound_set_volume(s, (float)volume);
}

void rt_audio_set_master_volume(double volume) {
    if (!g_audio_initialized) return;
    ma_engine_set_volume(&g_audio_engine, (float)volume);
}

double rt_audio_get_master_volume(void) {
    if (!g_audio_initialized) return 0.0;
    return (double)ma_engine_get_volume(&g_audio_engine);
}

/* ================================================================
 * Query
 * ================================================================ */

int64_t rt_audio_is_playing(int64_t playback_handle) {
    if (!playback_handle) return 0;
    ma_sound* s = (ma_sound*)(uintptr_t)playback_handle;
    return ma_sound_is_playing(s) ? 1 : 0;
}

/* ================================================================
 * Spatial audio (3D positioning)
 * ================================================================ */

void rt_audio_set_sound_position(int64_t playback_handle, double x, double y, double z) {
    ma_sound* s = (ma_sound*)(uintptr_t)playback_handle;
    if (!s) return;
    ma_sound_set_position(s, (float)x, (float)y, (float)z);
}

void rt_audio_set_spatialization_enabled(int64_t playback_handle, int64_t enabled) {
    ma_sound* s = (ma_sound*)(uintptr_t)playback_handle;
    if (!s) return;
    ma_sound_set_spatialization_enabled(s, enabled ? MA_TRUE : MA_FALSE);
}

void rt_audio_set_listener_position(double x, double y, double z) {
    ma_engine_listener_set_position(&g_audio_engine, 0, (float)x, (float)y, (float)z);
}

void rt_audio_set_listener_direction(double x, double y, double z) {
    ma_engine_listener_set_direction(&g_audio_engine, 0, (float)x, (float)y, (float)z);
}

void rt_audio_set_listener_world_up(double x, double y, double z) {
    ma_engine_listener_set_world_up(&g_audio_engine, 0, (float)x, (float)y, (float)z);
}

void rt_audio_set_sound_min_distance(int64_t playback_handle, double distance) {
    ma_sound* s = (ma_sound*)(uintptr_t)playback_handle;
    if (!s) return;
    ma_sound_set_min_distance(s, (float)distance);
}

void rt_audio_set_sound_max_distance(int64_t playback_handle, double distance) {
    ma_sound* s = (ma_sound*)(uintptr_t)playback_handle;
    if (!s) return;
    ma_sound_set_max_distance(s, (float)distance);
}
