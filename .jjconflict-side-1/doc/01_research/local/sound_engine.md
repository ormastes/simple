<!-- codex-research -->
# Sound Engine Local Research

## Scope
Research for `.spipe/sound-engine/state.md`: lightweight cross-platform sound engine for Linux, BSD, macOS, Android, iOS, and Simple OS; Engine2D/Engine3D hooks; pure-Simple codec/DSP; optimization, parallelism, and hardening.

## Existing Implementation
- Runtime backend: `src/runtime/runtime_audio.c` embeds vendored `miniaudio.h` and exposes `rt_audio_*` lifecycle, sound loading, playback, pause/resume, volume, master volume, query, spatial position, listener orientation, distance, and pitch hooks.
- Simple SFFI wrappers: `src/lib/nogc_sync_mut/io/audio_sffi.spl` maps the runtime calls to `AudioEngine`, `AudioSource`, and `AudioPlayback` wrappers, then exports raw and friendly APIs.
- Engine API: `src/lib/nogc_sync_mut/engine/audio/audio_manager.spl` owns `AudioManager`, default buses (`sfx`, `music`, `ui`), clip cache, active-sound tracking, 2D/3D spatial playback, listener state, bus/master volume, stop/pause/resume, and teardown.
- Shared types: `src/lib/nogc_sync_mut/engine/audio/types.spl` defines `AudioClip`, `SoundHandle`, `AudioBus`, `AudioConfig`, and `Listener3D`.
- Effects metadata exists in `src/lib/nogc_sync_mut/engine/audio/effects.spl`; SFFI declarations for effects exist, but runtime implementation evidence was not found in the sampled runtime file.
- Game2D asset wrapper: `src/lib/nogc_sync_mut/game2d/audio/sound.spl` provides `Sound.sfx`, `Sound.music`, `Sound.spatial_sfx`, and volume derivation metadata.
- Runtime-family facades exist under `gc_async_mut`, `nogc_async_mut`, and `gc_sync_mut`, mostly as exports or copied wrappers.

## Existing Tests
- `test/01_unit/lib/engine/audio_spec.spl` uses a pure-Simple mock manager for buses, clip caching, handle generation, mute/unmute, and volume round trips.
- `test/01_unit/lib/engine/audio_spatial_spec.spl` covers active-sound tracking, stop removal, bus volume, default listener values, and listener position update via a mock spatial manager.
- `test/03_system/app/audio_group_spec.spl` and engine/game audio specs exist, but this lane still needs feature-specific SPipe system specs for the requested cross-platform status, codec, no-audio backend, and Engine2D/Engine3D flows.
- Some existing assertions use boolean wrapper forms such as `expect(ok).to_equal(true)` and `expect(handle.is_valid()).to_equal(true)`; new specs should follow the SPipe rule to avoid placeholder/equality-only forms where stronger direct assertions are possible.

## Related Architecture And Docs
- `doc/05_design/ui/graphics/engine_2d.md` already lists an `audio/` area and an `AudioManager` role in the game engine architecture.
- `doc/05_design/language/memory/gc_nogc_module_parity.md` records engine-audio and game2d-audio facade parity expectations.
- SimpleOS driver docs mention audio readiness requiring controller, codec, DMA ring, period/timer, mixer, and CPU audio acceleration, especially in `doc/04_architecture/os/simpleos/platform/simpleos_driver_mdsoc_plus_platform.md`.
- Game compatibility/platform contracts include audio readiness and optional audio APIs under `src/os/game/platform/`.

## Gaps Against The SPipe State
- Platform capability status is not modeled at the sound-engine API boundary as `native`, `portable`, `unsupported`, or `host-unavailable`.
- Device backend selection is currently hidden inside `rt_audio_init()` with a binary success/failure result.
- No explicit no-audio/mock backend appears in the production API, though tests define local mock managers.
- Engine2D and Engine3D integration hooks are partial: game2d has sound metadata and AudioManager has 2D/3D spatial calls, but stable scene-entity attachment and command emission contracts need design.
- Pure-Simple codec support beyond existing replay/SFM/database codecs needs a sound-specific format, streaming boundary, corrupt-input rejection, fixed vectors, and performance evidence.
- Parallel mixing/stream decode/asset preparation is not represented in the sampled audio code.
- Hardening coverage needs invalid state, malformed input, extreme sample rates, channel mismatch, underrun/overflow, teardown during playback, and cleanup-after-failure tests.

## Recommended Next Step
Use these findings to select a scoped requirement option. The most repo-aligned path is to keep miniaudio as the native device bridge, add a Simple capability/no-audio facade above it, and build codec/DSP/parallel/hardening pieces in pure Simple with runtime-backed acceleration only behind explicit contracts.
