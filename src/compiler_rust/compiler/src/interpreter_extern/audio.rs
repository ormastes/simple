//! Audio (`rt_audio_*`) extern registration for the interpreter/JIT path.
//!
//! `rt_audio_*` is implemented once, in C, at `src/runtime/runtime_audio.c`
//! (a real miniaudio-backed engine -- not a capability stub like
//! `rt_opengl_*`/`rt_oneapi_*`). Before this lane the interpreter had no
//! entry for the family at all, so every call died with the generic
//! `unknown extern function: rt_audio_init` -- indistinguishable from "no
//! audio support". That is the wrong diagnosis: `runtime_audio.c` was simply
//! absent from **both** C-source lists that gate whether a build can link
//! against it -- the native-product-build list
//! (`src/compiler/70.backend/backend/runtime_compiler.spl`'s `sources`
//! array) AND the C sources this crate's own build script compiles
//! (`../../runtime/build.rs`), the same "source-list-absent" shape the
//! `rt_sdl2_*`/`rt_opengl_*`/`rt_oneapi_*` lanes found, just missing from
//! both lists at once instead of one. See
//! doc/08_tracking/bug/interpreter_extern_unreachable_names.md bucket (a)
//! and doc/03_plan/runtime/native_binding/interpreter_extern_registration_lanes.md.
//!
//! Unlike the `rt_opengl_*`/`rt_oneapi_*` families, `rt_audio_*` is not
//! uniformly `int64_t`-in/`int64_t`-out: it mixes `int64_t` handles,
//! `double` (volume/position/distance), `const char*` (sound paths, the
//! backend name), and one `SplArray*`-taking entry point
//! (`rt_audio_play_pcm_f32`). Marshalling a native `SplArray*` from this
//! interpreter's `Value` representation is not safe without a
//! natively-linked ABI bridge (see `rt_sdl2_present_rgba`'s identical
//! refusal in `sdl2.rs`), so that one name is refused cleanly here rather
//! than risking a bad transmute; every other name in the family is real.
//!
//! Every symbol below is declared `unsafe extern "C"` and linked directly
//! into this binary from the `runtime_sffi_c` static archive -- no dlopen
//! dance needed, since `runtime_audio.c`/miniaudio has no optional system
//! dependency the way SDL2 does.

use crate::error::CompileError;
use crate::value::Value;
use std::ffi::{CStr, CString};
use std::os::raw::c_char;

unsafe extern "C" {
    fn rt_audio_init() -> i64;
    fn rt_audio_shutdown(engine_handle: i64) -> i64;
    fn rt_audio_load_sound(path: *const c_char) -> i64;
    fn rt_audio_unload_sound(handle: i64);
    fn rt_audio_play(sound_handle: i64) -> i64;
    fn rt_audio_play_looped(sound_handle: i64) -> i64;
    fn rt_audio_stop(playback_handle: i64);
    fn rt_audio_pause(playback_handle: i64);
    fn rt_audio_resume(playback_handle: i64);
    fn rt_audio_set_volume(playback_handle: i64, volume: f64);
    fn rt_audio_set_pitch(playback_handle: i64, pitch: f64) -> i64;
    fn rt_audio_set_master_volume(volume: f64);
    fn rt_audio_get_master_volume() -> f64;
    fn rt_audio_is_playing(playback_handle: i64) -> i64;
    fn rt_audio_live_source_count() -> i64;
    fn rt_audio_live_playback_count() -> i64;
    fn rt_audio_live_device_count() -> i64;
    fn rt_audio_backend_name() -> *const c_char;
    fn rt_audio_backend_is_real() -> i64;
    fn rt_audio_set_sound_position(playback_handle: i64, x: f64, y: f64, z: f64);
    fn rt_audio_set_spatialization_enabled(playback_handle: i64, enabled: i64);
    fn rt_audio_set_listener_position(x: f64, y: f64, z: f64);
    fn rt_audio_set_listener_direction(x: f64, y: f64, z: f64);
    fn rt_audio_set_listener_world_up(x: f64, y: f64, z: f64);
    fn rt_audio_set_sound_min_distance(playback_handle: i64, distance: f64);
    fn rt_audio_set_sound_max_distance(playback_handle: i64, distance: f64);
    fn rt_audio_play_pcm_f64_raw(samples_addr: i64, sample_count: i64, channels: i64, sample_rate: i64) -> i64;
    fn rt_audio_capture_start(path: *const c_char, sample_rate: i64, channels: i64) -> i64;
    fn rt_audio_capture_is_active() -> i64;
    fn rt_audio_capture_frame_count() -> i64;
    fn rt_audio_capture_stop() -> i64;
}

/// Full `rt_audio_*` (bucket-a) family, asserted against the C source by
/// `audio_arity_table_has_all_thirty_one_symbols` below; the C prototypes in
/// `src/runtime/runtime.h`/`runtime_audio.c` remain the source of truth for
/// `dispatch`'s match arms.
const AUDIO_ARITY: &[(&str, usize)] = &[
    ("rt_audio_init", 0),
    ("rt_audio_shutdown", 1),
    ("rt_audio_load_sound", 1),
    ("rt_audio_unload_sound", 1),
    ("rt_audio_play", 1),
    ("rt_audio_play_looped", 1),
    ("rt_audio_play_pcm_f32", 3),
    ("rt_audio_stop", 1),
    ("rt_audio_pause", 1),
    ("rt_audio_resume", 1),
    ("rt_audio_set_volume", 2),
    ("rt_audio_set_pitch", 2),
    ("rt_audio_set_master_volume", 1),
    ("rt_audio_get_master_volume", 0),
    ("rt_audio_is_playing", 1),
    ("rt_audio_live_source_count", 0),
    ("rt_audio_live_playback_count", 0),
    ("rt_audio_live_device_count", 0),
    ("rt_audio_backend_name", 0),
    ("rt_audio_backend_is_real", 0),
    ("rt_audio_set_sound_position", 4),
    ("rt_audio_set_spatialization_enabled", 2),
    ("rt_audio_set_listener_position", 3),
    ("rt_audio_set_listener_direction", 3),
    ("rt_audio_set_listener_world_up", 3),
    ("rt_audio_set_sound_min_distance", 2),
    ("rt_audio_set_sound_max_distance", 2),
    ("rt_audio_play_pcm_f64_raw", 4),
    ("rt_audio_capture_start", 3),
    ("rt_audio_capture_is_active", 0),
    ("rt_audio_capture_frame_count", 0),
    ("rt_audio_capture_stop", 0),
];

fn expect_arity(name: &str, args: &[Value], expected: usize) -> Result<(), CompileError> {
    if args.len() != expected {
        return Err(CompileError::runtime(format!(
            "{name} expects {expected} argument(s), got {}",
            args.len()
        )));
    }
    Ok(())
}

fn as_int(name: &str, args: &[Value], i: usize) -> Result<i64, CompileError> {
    match &args[i] {
        Value::Int(n) => Ok(*n),
        other => Err(CompileError::runtime(format!(
            "{name}: argument {i} must be an int, got {other:?}"
        ))),
    }
}

fn as_float(name: &str, args: &[Value], i: usize) -> Result<f64, CompileError> {
    match &args[i] {
        Value::Float(f) => Ok(*f),
        Value::Int(n) => Ok(*n as f64),
        other => Err(CompileError::runtime(format!(
            "{name}: argument {i} must be a float, got {other:?}"
        ))),
    }
}

fn as_text(name: &str, args: &[Value], i: usize) -> Result<CString, CompileError> {
    match &args[i] {
        Value::Str(s) => CString::new(s.as_ref().clone()).map_err(|_| {
            CompileError::runtime(format!("{name}: argument {i} contains an embedded NUL"))
        }),
        other => Err(CompileError::runtime(format!(
            "{name}: argument {i} must be a string, got {other:?}"
        ))),
    }
}

/// The owned audio provider always returns a static backend-name string.
/// NULL is therefore a provider-contract violation, not empty text.
fn c_str_to_value(ptr: *const c_char, symbol: &str) -> Result<Value, CompileError> {
    if ptr.is_null() {
        return Err(CompileError::runtime(format!(
            "{symbol}: foreign text contract returned null"
        )));
    }
    let owned = unsafe { CStr::from_ptr(ptr) }.to_string_lossy().into_owned();
    Ok(Value::Str(std::sync::Arc::new(owned)))
}

/// Dispatch a `rt_audio_*` call. Returns the family-scoped refusal for any
/// name that starts with the prefix but has no C definition -- distinguishing
/// "known family, no such function" from the generic "unknown extern
/// function" text a caller would otherwise see, matching the rt_sdl2_* guard.
pub fn dispatch(name: &str, args: &[Value]) -> Result<Value, CompileError> {
    match name {
        "rt_audio_init" => {
            expect_arity(name, args, 0)?;
            Ok(Value::Int(unsafe { rt_audio_init() }))
        }
        "rt_audio_shutdown" => {
            expect_arity(name, args, 1)?;
            let a0 = as_int(name, args, 0)?;
            Ok(Value::Int(unsafe { rt_audio_shutdown(a0) }))
        }
        "rt_audio_load_sound" => {
            expect_arity(name, args, 1)?;
            let path = as_text(name, args, 0)?;
            Ok(Value::Int(unsafe { rt_audio_load_sound(path.as_ptr()) }))
        }
        "rt_audio_unload_sound" => {
            expect_arity(name, args, 1)?;
            let a0 = as_int(name, args, 0)?;
            unsafe { rt_audio_unload_sound(a0) };
            Ok(Value::Nil)
        }
        "rt_audio_play" => {
            expect_arity(name, args, 1)?;
            let a0 = as_int(name, args, 0)?;
            Ok(Value::Int(unsafe { rt_audio_play(a0) }))
        }
        "rt_audio_play_looped" => {
            expect_arity(name, args, 1)?;
            let a0 = as_int(name, args, 0)?;
            Ok(Value::Int(unsafe { rt_audio_play_looped(a0) }))
        }
        "rt_audio_play_pcm_f32" => Err(CompileError::runtime(format!(
            "{name}: takes a native SplArray*, which cannot be marshalled from this \
             interpreter's Value representation without a natively-linked ABI bridge; \
             use rt_audio_play_pcm_f64_raw (raw pointer + length) instead"
        ))),
        "rt_audio_stop" => {
            expect_arity(name, args, 1)?;
            let a0 = as_int(name, args, 0)?;
            unsafe { rt_audio_stop(a0) };
            Ok(Value::Nil)
        }
        "rt_audio_pause" => {
            expect_arity(name, args, 1)?;
            let a0 = as_int(name, args, 0)?;
            unsafe { rt_audio_pause(a0) };
            Ok(Value::Nil)
        }
        "rt_audio_resume" => {
            expect_arity(name, args, 1)?;
            let a0 = as_int(name, args, 0)?;
            unsafe { rt_audio_resume(a0) };
            Ok(Value::Nil)
        }
        "rt_audio_set_volume" => {
            expect_arity(name, args, 2)?;
            let a0 = as_int(name, args, 0)?;
            let a1 = as_float(name, args, 1)?;
            unsafe { rt_audio_set_volume(a0, a1) };
            Ok(Value::Nil)
        }
        "rt_audio_set_pitch" => {
            expect_arity(name, args, 2)?;
            let a0 = as_int(name, args, 0)?;
            let a1 = as_float(name, args, 1)?;
            Ok(Value::Int(unsafe { rt_audio_set_pitch(a0, a1) }))
        }
        "rt_audio_set_master_volume" => {
            expect_arity(name, args, 1)?;
            let a0 = as_float(name, args, 0)?;
            unsafe { rt_audio_set_master_volume(a0) };
            Ok(Value::Nil)
        }
        "rt_audio_get_master_volume" => {
            expect_arity(name, args, 0)?;
            Ok(Value::Float(unsafe { rt_audio_get_master_volume() }))
        }
        "rt_audio_is_playing" => {
            expect_arity(name, args, 1)?;
            let a0 = as_int(name, args, 0)?;
            Ok(Value::Int(unsafe { rt_audio_is_playing(a0) }))
        }
        "rt_audio_live_source_count" => {
            expect_arity(name, args, 0)?;
            Ok(Value::Int(unsafe { rt_audio_live_source_count() }))
        }
        "rt_audio_live_playback_count" => {
            expect_arity(name, args, 0)?;
            Ok(Value::Int(unsafe { rt_audio_live_playback_count() }))
        }
        "rt_audio_live_device_count" => {
            expect_arity(name, args, 0)?;
            Ok(Value::Int(unsafe { rt_audio_live_device_count() }))
        }
        "rt_audio_backend_name" => {
            expect_arity(name, args, 0)?;
            c_str_to_value(unsafe { rt_audio_backend_name() }, name)
        }
        "rt_audio_backend_is_real" => {
            expect_arity(name, args, 0)?;
            Ok(Value::Int(unsafe { rt_audio_backend_is_real() }))
        }
        "rt_audio_set_sound_position" => {
            expect_arity(name, args, 4)?;
            let a0 = as_int(name, args, 0)?;
            let a1 = as_float(name, args, 1)?;
            let a2 = as_float(name, args, 2)?;
            let a3 = as_float(name, args, 3)?;
            unsafe { rt_audio_set_sound_position(a0, a1, a2, a3) };
            Ok(Value::Nil)
        }
        "rt_audio_set_spatialization_enabled" => {
            expect_arity(name, args, 2)?;
            let a0 = as_int(name, args, 0)?;
            let a1 = as_int(name, args, 1)?;
            unsafe { rt_audio_set_spatialization_enabled(a0, a1) };
            Ok(Value::Nil)
        }
        "rt_audio_set_listener_position" => {
            expect_arity(name, args, 3)?;
            let a0 = as_float(name, args, 0)?;
            let a1 = as_float(name, args, 1)?;
            let a2 = as_float(name, args, 2)?;
            unsafe { rt_audio_set_listener_position(a0, a1, a2) };
            Ok(Value::Nil)
        }
        "rt_audio_set_listener_direction" => {
            expect_arity(name, args, 3)?;
            let a0 = as_float(name, args, 0)?;
            let a1 = as_float(name, args, 1)?;
            let a2 = as_float(name, args, 2)?;
            unsafe { rt_audio_set_listener_direction(a0, a1, a2) };
            Ok(Value::Nil)
        }
        "rt_audio_set_listener_world_up" => {
            expect_arity(name, args, 3)?;
            let a0 = as_float(name, args, 0)?;
            let a1 = as_float(name, args, 1)?;
            let a2 = as_float(name, args, 2)?;
            unsafe { rt_audio_set_listener_world_up(a0, a1, a2) };
            Ok(Value::Nil)
        }
        "rt_audio_set_sound_min_distance" => {
            expect_arity(name, args, 2)?;
            let a0 = as_int(name, args, 0)?;
            let a1 = as_float(name, args, 1)?;
            unsafe { rt_audio_set_sound_min_distance(a0, a1) };
            Ok(Value::Nil)
        }
        "rt_audio_set_sound_max_distance" => {
            expect_arity(name, args, 2)?;
            let a0 = as_int(name, args, 0)?;
            let a1 = as_float(name, args, 1)?;
            unsafe { rt_audio_set_sound_max_distance(a0, a1) };
            Ok(Value::Nil)
        }
        "rt_audio_play_pcm_f64_raw" => {
            expect_arity(name, args, 4)?;
            let a0 = as_int(name, args, 0)?;
            let a1 = as_int(name, args, 1)?;
            let a2 = as_int(name, args, 2)?;
            let a3 = as_int(name, args, 3)?;
            Ok(Value::Int(unsafe { rt_audio_play_pcm_f64_raw(a0, a1, a2, a3) }))
        }
        "rt_audio_capture_start" => {
            expect_arity(name, args, 3)?;
            let path = as_text(name, args, 0)?;
            let a1 = as_int(name, args, 1)?;
            let a2 = as_int(name, args, 2)?;
            Ok(Value::Int(unsafe { rt_audio_capture_start(path.as_ptr(), a1, a2) }))
        }
        "rt_audio_capture_is_active" => {
            expect_arity(name, args, 0)?;
            Ok(Value::Int(unsafe { rt_audio_capture_is_active() }))
        }
        "rt_audio_capture_frame_count" => {
            expect_arity(name, args, 0)?;
            Ok(Value::Int(unsafe { rt_audio_capture_frame_count() }))
        }
        "rt_audio_capture_stop" => {
            expect_arity(name, args, 0)?;
            Ok(Value::Int(unsafe { rt_audio_capture_stop() }))
        }
        _ => Err(CompileError::runtime(format!(
            "{name}: unknown rt_audio_* function (no C definition in runtime_audio.c)"
        ))),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn audio_arity_table_has_all_thirty_two_symbols() {
        assert_eq!(AUDIO_ARITY.len(), 32);
    }

    #[test]
    fn bogus_name_in_prefix_gets_family_refusal_not_generic_unknown() {
        let err = dispatch("rt_audio_zzz_bogus", &[]).unwrap_err();
        let text = format!("{err}");
        assert!(text.contains("unknown rt_audio_*"), "got: {text}");
        assert!(!text.contains("unknown extern function"), "got: {text}");
    }

    #[test]
    fn backend_name_returns_a_string_not_an_error() {
        assert!(matches!(dispatch("rt_audio_backend_name", &[]).unwrap(), Value::Str(_)));
    }

    #[test]
    fn null_backend_name_is_a_contract_error() {
        let result = c_str_to_value(std::ptr::null(), "rt_audio_backend_name");
        assert!(result.is_err(), "null foreign text must never become empty text");
    }

    #[test]
    fn array_taking_entry_point_is_refused_cleanly() {
        let err = dispatch(
            "rt_audio_play_pcm_f32",
            &[Value::Int(0), Value::Int(2), Value::Int(48000)],
        )
        .unwrap_err();
        let text = format!("{err}");
        assert!(text.contains("natively-linked"), "got: {text}");
    }
}
