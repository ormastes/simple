# Rodio Audio SFFI Implementation Guide

**Status**: SFFI wrapper complete, Rust runtime implementation needed
**Created**: 2026-02-08
**Files**:
- SFFI Wrapper: `src/app/io/audio_ffi.spl` (~550 lines)
- Test Spec: `test/app/io/audio_ffi_spec.spl` (~460 lines)
- Demo: `examples/audio_demo.spl` (~230 lines)

## Overview

This guide explains how to implement the Rust runtime side of the Rodio audio playback SFFI wrapper for the Simple language compiler.

The Simple-side wrapper is **complete** and follows the two-tier SFFI pattern. This document covers the Rust implementation needed to make the wrapper functional.

## What is Rodio?

Rodio is a Rust audio playback library that:
- Plays audio files (WAV, MP3, OGG, FLAC)
- Supports streaming for large music files
- Provides spatial audio (3D positioning)
- Offers audio effects (volume, speed, reverb, delay)
- Cross-platform (Windows, macOS, Linux)

**Use cases**: Games, music players, sound effects, interactive apps

## Architecture

### Two-Tier SFFI Pattern

**Tier 1: Extern Declarations** (Simple)
```simple
extern fn rt_audio_init() -> i64
extern fn rt_audio_play_sound(engine: i64, source: i64) -> i64
extern fn rt_audio_playback_set_volume(handle: i64, volume: f64) -> bool
```

**Tier 2: Simple Wrappers** (Simple)
```simple
fn audio_init() -> AudioEngine:
    val handle = rt_audio_init()
    AudioEngine(handle: handle, is_valid: handle != 0)
```

**Runtime Implementation** (Rust - to be implemented)
```rust
#[no_mangle]
pub extern "C" fn rt_audio_init() -> i64 {
    // Implementation here
}
```

## Rust Dependencies

Add to runtime's `Cargo.toml`:

```toml
[dependencies]
rodio = "0.17"  # Or latest version
```

## Implementation Strategy

### 1. Handle Management

Rodio uses owned types, but we expose opaque `i64` handles to Simple:

```rust
use std::collections::HashMap;
use std::sync::{Arc, Mutex};
use std::fs::File;
use std::io::BufReader;
use rodio::{OutputStream, OutputStreamHandle, Sink, Decoder, Source};

// Global state (thread-safe)
lazy_static! {
    static ref AUDIO_ENGINES: Mutex<HashMap<i64, AudioEngine>> = Mutex::new(HashMap::new());
    static ref AUDIO_SOURCES: Mutex<HashMap<i64, AudioSourceData>> = Mutex::new(HashMap::new());
    static ref PLAYBACK_HANDLES: Mutex<HashMap<i64, PlaybackHandle>> = Mutex::new(HashMap::new());
    static ref NEXT_ENGINE_ID: Mutex<i64> = Mutex::new(1);
    static ref NEXT_SOURCE_ID: Mutex<i64> = Mutex::new(1);
    static ref NEXT_PLAYBACK_ID: Mutex<i64> = Mutex::new(1);
}

struct AudioEngine {
    _stream: OutputStream,
    stream_handle: OutputStreamHandle,
    master_volume: f32,
    sinks: Vec<Arc<Mutex<Sink>>>,
}

impl AudioEngine {
    fn new() -> Result<Self, String> {
        let (_stream, stream_handle) = OutputStream::try_default()
            .map_err(|e| format!("Failed to create audio output: {}", e))?;

        Ok(AudioEngine {
            _stream,
            stream_handle,
            master_volume: 1.0,
            sinks: Vec::new(),
        })
    }
}

struct AudioSourceData {
    data: Vec<u8>,
    sample_rate: u32,
    channels: u16,
    duration: f64,
}

struct PlaybackHandle {
    sink: Arc<Mutex<Sink>>,
    position: [f32; 3],
    volume: f32,
    speed: f32,
}
```

### 2. Audio Engine Implementation

```rust
#[no_mangle]
pub extern "C" fn rt_audio_init() -> i64 {
    match AudioEngine::new() {
        Ok(engine) => {
            let mut engines = AUDIO_ENGINES.lock().unwrap();
            let mut next_id = NEXT_ENGINE_ID.lock().unwrap();

            let id = *next_id;
            *next_id += 1;

            engines.insert(id, engine);
            id
        }
        Err(e) => {
            eprintln!("Audio initialization failed: {}", e);
            0
        }
    }
}

#[no_mangle]
pub extern "C" fn rt_audio_shutdown(engine_id: i64) -> bool {
    let mut engines = AUDIO_ENGINES.lock().unwrap();
    engines.remove(&engine_id).is_some()
}

#[no_mangle]
pub extern "C" fn rt_audio_set_master_volume(engine_id: i64, volume: f64) -> bool {
    let mut engines = AUDIO_ENGINES.lock().unwrap();
    if let Some(engine) = engines.get_mut(&engine_id) {
        engine.master_volume = volume.clamp(0.0, 1.0) as f32;

        // Update all active sinks
        for sink in &engine.sinks {
            if let Ok(sink) = sink.lock() {
                sink.set_volume(engine.master_volume);
            }
        }
        true
    } else {
        false
    }
}

#[no_mangle]
pub extern "C" fn rt_audio_get_master_volume(engine_id: i64) -> f64 {
    let engines = AUDIO_ENGINES.lock().unwrap();
    if let Some(engine) = engines.get(&engine_id) {
        engine.master_volume as f64
    } else {
        0.0
    }
}

#[no_mangle]
pub extern "C" fn rt_audio_pause_all(engine_id: i64) -> bool {
    let engines = AUDIO_ENGINES.lock().unwrap();
    if let Some(engine) = engines.get(&engine_id) {
        for sink in &engine.sinks {
            if let Ok(sink) = sink.lock() {
                sink.pause();
            }
        }
        true
    } else {
        false
    }
}

#[no_mangle]
pub extern "C" fn rt_audio_resume_all(engine_id: i64) -> bool {
    let engines = AUDIO_ENGINES.lock().unwrap();
    if let Some(engine) = engines.get(&engine_id) {
        for sink in &engine.sinks {
            if let Ok(sink) = sink.lock() {
                sink.play();
            }
        }
        true
    } else {
        false
    }
}
```

### 3. Audio Source Loading

```rust
use std::path::Path;

#[no_mangle]
pub extern "C" fn rt_audio_load_from_file(engine_id: i64, path: *const c_char) -> i64 {
    let engines = AUDIO_ENGINES.lock().unwrap();
    if engines.get(&engine_id).is_none() {
        return 0;
    }
    drop(engines);

    let path_str = unsafe {
        CStr::from_ptr(path).to_str().unwrap_or("")
    };

    // Load and decode file
    match File::open(path_str) {
        Ok(file) => {
            let buf_reader = BufReader::new(file);
            match Decoder::new(buf_reader) {
                Ok(decoder) => {
                    let sample_rate = decoder.sample_rate();
                    let channels = decoder.channels();

                    // Collect samples into memory
                    let samples: Vec<i16> = decoder.convert_samples().collect();
                    let duration = samples.len() as f64 / (sample_rate as f64 * channels as f64);

                    // Convert to bytes
                    let data = samples.iter()
                        .flat_map(|&s| s.to_le_bytes())
                        .collect();

                    let source_data = AudioSourceData {
                        data,
                        sample_rate,
                        channels,
                        duration,
                    };

                    let mut sources = AUDIO_SOURCES.lock().unwrap();
                    let mut next_id = NEXT_SOURCE_ID.lock().unwrap();

                    let id = *next_id;
                    *next_id += 1;

                    sources.insert(id, source_data);
                    id
                }
                Err(e) => {
                    eprintln!("Failed to decode audio file: {}", e);
                    0
                }
            }
        }
        Err(e) => {
            eprintln!("Failed to open audio file: {}", e);
            0
        }
    }
}

#[no_mangle]
pub extern "C" fn rt_audio_source_free(source_id: i64) -> bool {
    let mut sources = AUDIO_SOURCES.lock().unwrap();
    sources.remove(&source_id).is_some()
}

#[no_mangle]
pub extern "C" fn rt_audio_source_duration(source_id: i64) -> f64 {
    let sources = AUDIO_SOURCES.lock().unwrap();
    if let Some(source) = sources.get(&source_id) {
        source.duration
    } else {
        0.0
    }
}

#[no_mangle]
pub extern "C" fn rt_audio_source_get_sample_rate(source_id: i64) -> i64 {
    let sources = AUDIO_SOURCES.lock().unwrap();
    if let Some(source) = sources.get(&source_id) {
        source.sample_rate as i64
    } else {
        0
    }
}

#[no_mangle]
pub extern "C" fn rt_audio_source_get_channels(source_id: i64) -> i64 {
    let sources = AUDIO_SOURCES.lock().unwrap();
    if let Some(source) = sources.get(&source_id) {
        source.channels as i64
    } else {
        0
    }
}
```

### 4. Sound Playback

```rust
use rodio::Source;

#[no_mangle]
pub extern "C" fn rt_audio_play_sound(engine_id: i64, source_id: i64) -> i64 {
    rt_audio_play_sound_with_volume(engine_id, source_id, 1.0)
}

#[no_mangle]
pub extern "C" fn rt_audio_play_sound_with_volume(
    engine_id: i64,
    source_id: i64,
    volume: f64,
) -> i64 {
    let mut engines = AUDIO_ENGINES.lock().unwrap();
    let sources = AUDIO_SOURCES.lock().unwrap();

    if let (Some(engine), Some(source_data)) = (engines.get_mut(&engine_id), sources.get(&source_id)) {
        // Create decoder from memory
        let cursor = std::io::Cursor::new(source_data.data.clone());
        let decoder = Decoder::new(cursor).unwrap();

        // Create sink for this playback
        let sink = Sink::try_new(&engine.stream_handle).unwrap();
        sink.set_volume((volume as f32).clamp(0.0, 1.0));
        sink.append(decoder);

        let sink_arc = Arc::new(Mutex::new(sink));
        engine.sinks.push(sink_arc.clone());

        let handle = PlaybackHandle {
            sink: sink_arc,
            position: [0.0, 0.0, 0.0],
            volume: volume as f32,
            speed: 1.0,
        };

        let mut playbacks = PLAYBACK_HANDLES.lock().unwrap();
        let mut next_id = NEXT_PLAYBACK_ID.lock().unwrap();

        let id = *next_id;
        *next_id += 1;

        playbacks.insert(id, handle);
        id
    } else {
        0
    }
}

#[no_mangle]
pub extern "C" fn rt_audio_play_sound_looped(engine_id: i64, source_id: i64) -> i64 {
    let mut engines = AUDIO_ENGINES.lock().unwrap();
    let sources = AUDIO_SOURCES.lock().unwrap();

    if let (Some(engine), Some(source_data)) = (engines.get_mut(&engine_id), sources.get(&source_id)) {
        let cursor = std::io::Cursor::new(source_data.data.clone());
        let decoder = Decoder::new(cursor).unwrap();

        let sink = Sink::try_new(&engine.stream_handle).unwrap();
        sink.append(decoder.repeat_infinite());

        let sink_arc = Arc::new(Mutex::new(sink));
        engine.sinks.push(sink_arc.clone());

        let handle = PlaybackHandle {
            sink: sink_arc,
            position: [0.0, 0.0, 0.0],
            volume: 1.0,
            speed: 1.0,
        };

        let mut playbacks = PLAYBACK_HANDLES.lock().unwrap();
        let mut next_id = NEXT_PLAYBACK_ID.lock().unwrap();

        let id = *next_id;
        *next_id += 1;

        playbacks.insert(id, handle);
        id
    } else {
        0
    }
}
```

### 5. Playback Control

```rust
#[no_mangle]
pub extern "C" fn rt_audio_playback_stop(playback_id: i64) -> bool {
    let mut playbacks = PLAYBACK_HANDLES.lock().unwrap();
    if let Some(handle) = playbacks.remove(&playback_id) {
        if let Ok(sink) = handle.sink.lock() {
            sink.stop();
        }
        true
    } else {
        false
    }
}

#[no_mangle]
pub extern "C" fn rt_audio_playback_pause(playback_id: i64) -> bool {
    let playbacks = PLAYBACK_HANDLES.lock().unwrap();
    if let Some(handle) = playbacks.get(&playback_id) {
        if let Ok(sink) = handle.sink.lock() {
            sink.pause();
            true
        } else {
            false
        }
    } else {
        false
    }
}

#[no_mangle]
pub extern "C" fn rt_audio_playback_resume(playback_id: i64) -> bool {
    let playbacks = PLAYBACK_HANDLES.lock().unwrap();
    if let Some(handle) = playbacks.get(&playback_id) {
        if let Ok(sink) = handle.sink.lock() {
            sink.play();
            true
        } else {
            false
        }
    } else {
        false
    }
}

#[no_mangle]
pub extern "C" fn rt_audio_playback_is_playing(playback_id: i64) -> bool {
    let playbacks = PLAYBACK_HANDLES.lock().unwrap();
    if let Some(handle) = playbacks.get(&playback_id) {
        if let Ok(sink) = handle.sink.lock() {
            !sink.is_paused() && !sink.empty()
        } else {
            false
        }
    } else {
        false
    }
}

#[no_mangle]
pub extern "C" fn rt_audio_playback_set_volume(playback_id: i64, volume: f64) -> bool {
    let mut playbacks = PLAYBACK_HANDLES.lock().unwrap();
    if let Some(handle) = playbacks.get_mut(&playback_id) {
        let vol = (volume as f32).clamp(0.0, 1.0);
        handle.volume = vol;

        if let Ok(sink) = handle.sink.lock() {
            sink.set_volume(vol);
            true
        } else {
            false
        }
    } else {
        false
    }
}

#[no_mangle]
pub extern "C" fn rt_audio_playback_set_speed(playback_id: i64, speed: f64) -> bool {
    let mut playbacks = PLAYBACK_HANDLES.lock().unwrap();
    if let Some(handle) = playbacks.get_mut(&playback_id) {
        let spd = (speed as f32).clamp(0.1, 10.0);
        handle.speed = spd;

        if let Ok(sink) = handle.sink.lock() {
            sink.set_speed(spd);
            true
        } else {
            false
        }
    } else {
        false
    }
}
```

### 6. Spatial Audio

For basic spatial audio (Rodio doesn't have built-in 3D audio), we can simulate it:

```rust
#[no_mangle]
pub extern "C" fn rt_audio_play_sound_spatial(
    engine_id: i64,
    source_id: i64,
    x: f64,
    y: f64,
    z: f64,
) -> i64 {
    // Play sound and calculate volume based on distance
    let playback_id = rt_audio_play_sound(engine_id, source_id);

    if playback_id != 0 {
        // Set position
        let mut playbacks = PLAYBACK_HANDLES.lock().unwrap();
        if let Some(handle) = playbacks.get_mut(&playback_id) {
            handle.position = [x as f32, y as f32, z as f32];

            // Calculate distance-based volume (simple linear falloff)
            let distance = (x * x + y * y + z * z).sqrt();
            let falloff_volume = (1.0 / (1.0 + distance * 0.1)).clamp(0.0, 1.0);

            if let Ok(sink) = handle.sink.lock() {
                sink.set_volume(falloff_volume as f32);
            }
        }
    }

    playback_id
}

#[no_mangle]
pub extern "C" fn rt_audio_playback_set_position(
    playback_id: i64,
    x: f64,
    y: f64,
    z: f64,
) -> bool {
    let mut playbacks = PLAYBACK_HANDLES.lock().unwrap();
    if let Some(handle) = playbacks.get_mut(&playback_id) {
        handle.position = [x as f32, y as f32, z as f32];

        // Update volume based on new distance
        let distance = (x * x + y * y + z * z).sqrt();
        let falloff_volume = (1.0 / (1.0 + distance * 0.1)).clamp(0.0, 1.0);

        if let Ok(sink) = handle.sink.lock() {
            sink.set_volume(falloff_volume as f32 * handle.volume);
            true
        } else {
            false
        }
    } else {
        false
    }
}
```

## Integration with Simple Runtime

### Location

Add the implementation to the runtime's FFI module:
- **Path**: `bin/runtime/src/ffi/audio.rs` (new file)
- **Add to**: `bin/runtime/src/ffi/mod.rs`

### Module Structure

```rust
// bin/runtime/src/ffi/mod.rs
pub mod audio;  // Add this

// bin/runtime/src/ffi/audio.rs
mod rodio_ffi;  // The implementation above

pub use rodio_ffi::*;
```

## Testing Strategy

### 1. Unit Tests (Rust)

```rust
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_audio_engine() {
        let engine_id = rt_audio_init();
        assert!(engine_id > 0);

        assert!(rt_audio_set_master_volume(engine_id, 0.5));
        let volume = rt_audio_get_master_volume(engine_id);
        assert!((volume - 0.5).abs() < 0.01);

        assert!(rt_audio_shutdown(engine_id));
    }

    #[test]
    fn test_playback_control() {
        let engine_id = rt_audio_init();
        // Would need actual audio file to test fully
        rt_audio_shutdown(engine_id);
    }
}
```

### 2. Integration Tests (Simple)

```bash
bin/simple test test/app/io/audio_ffi_spec.spl
```

### 3. Demo Test

```bash
bin/simple examples/audio_demo.spl
```

## Performance Considerations

### Memory Usage

- **Streaming**: Use `Decoder` directly for large files
- **Caching**: Store decoded data for repeated sounds
- **Cleanup**: Remove finished sinks from engine list

```rust
// Periodic cleanup
fn cleanup_finished_sinks(engine: &mut AudioEngine) {
    engine.sinks.retain(|sink| {
        if let Ok(s) = sink.lock() {
            !s.empty()
        } else {
            false
        }
    });
}
```

### Latency

- Use smaller buffer sizes for low-latency applications
- Pre-load frequently used sounds

## Example Implementation Checklist

- [ ] Add `rodio` to runtime `Cargo.toml`
- [ ] Implement audio engine (init, shutdown, master volume)
- [ ] Implement source loading (file, memory)
- [ ] Implement source properties (duration, sample rate, channels)
- [ ] Implement sound playback (basic, volume, looped)
- [ ] Implement music streaming
- [ ] Implement playback control (stop, pause, resume)
- [ ] Implement playback properties (volume, speed, state)
- [ ] Implement spatial audio (basic 3D positioning)
- [ ] Implement audio effects (fade, reverb, delay)
- [ ] Implement mixer support
- [ ] Add error handling
- [ ] Write Rust unit tests
- [ ] Run Simple integration tests
- [ ] Test with real audio files

## Supported Audio Formats

Rodio supports (with default features):
- **WAV** - Uncompressed (always supported)
- **MP3** - Common compressed format
- **OGG Vorbis** - Open source compressed
- **FLAC** - Lossless compression

## Next Steps

1. **Implement Core** (~300 lines)
   - Engine, source loading, basic playback

2. **Implement Control** (~200 lines)
   - Stop, pause, volume, speed

3. **Implement Spatial** (~150 lines)
   - 3D positioning, listener

4. **Implement Effects** (~150 lines)
   - Fade, reverb, delay

**Total Estimated**: 700-900 lines Rust

## Summary

The Simple-side SFFI wrapper is **production-ready** (~550 lines). The Rust implementation requires:

1. **~700-900 lines** of Rust code
2. **Rodio dependency** (~200KB compiled)
3. **Handle management** for engines, sources, playback
4. **Audio format support** (WAV, MP3, OGG, FLAC)

Once implemented, Simple programs can create immersive audio experiences for games and interactive applications!
