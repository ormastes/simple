/*
 * Simple Runtime — Audio effects stubs (pitch, filters, reverb, delay)
 *
 * These functions are resolved by the Simple extern declarations in
 * audio_ffi.spl.  When miniaudio node graph support is available,
 * these stubs should be replaced with real implementations.
 *
 * Build: cc -c -fPIC -O2 -std=gnu11 runtime_audio_effects.c -o runtime_audio_effects.o
 */

#include <stdint.h>

/* ================================================================
 * Pitch control — stub
 * Real implementation would call ma_sound_set_pitch(sound, (float)pitch)
 * ================================================================ */

int64_t rt_audio_set_pitch(int64_t sound_handle, double pitch) {
    (void)sound_handle;
    (void)pitch;
    /* TODO: wire to ma_sound_set_pitch(sound, (float)pitch) */
    return 0;
}

/* ================================================================
 * Low-pass filter — stub
 * ================================================================ */

int64_t rt_audio_add_lowpass(int64_t sound_handle, double cutoff_hz) {
    (void)sound_handle;
    (void)cutoff_hz;
    return 0;
}

/* ================================================================
 * High-pass filter — stub
 * ================================================================ */

int64_t rt_audio_add_highpass(int64_t sound_handle, double cutoff_hz) {
    (void)sound_handle;
    (void)cutoff_hz;
    return 0;
}

/* ================================================================
 * Reverb — stub
 * ================================================================ */

int64_t rt_audio_add_reverb(int64_t sound_handle, double decay,
                            double wet_dry) {
    (void)sound_handle;
    (void)decay;
    (void)wet_dry;
    return 0;
}

/* ================================================================
 * Delay — stub
 * ================================================================ */

int64_t rt_audio_add_delay(int64_t sound_handle, double time_ms,
                           double feedback) {
    (void)sound_handle;
    (void)time_ms;
    (void)feedback;
    return 0;
}

/* ================================================================
 * Remove a single effect — stub
 * ================================================================ */

int64_t rt_audio_remove_effect(int64_t sound_handle,
                               int64_t effect_handle) {
    (void)sound_handle;
    (void)effect_handle;
    return 0;
}

/* ================================================================
 * Clear all effects — stub
 * ================================================================ */

int64_t rt_audio_clear_effects(int64_t sound_handle) {
    (void)sound_handle;
    return 0;
}
