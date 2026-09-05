# Research: Sound / Music / Effect Editing Tooling for Games

## 1. Local infra inventory

### Three-tier engine audio (`src/lib/{nogc_sync_mut,nogc_async_mut,gc_async_mut}/engine/audio/`)
The three tiers are near-identical ports (same file set, same APIs) targeted at different
memory/concurrency models. `nogc_sync_mut` is the reference tier; `gc_async_mut` drops
`sound_engine.spl` (uses a facade spec instead — see `engine_audio_facade_spec.spl`).

| File | LOC | What it does | Maturity |
|---|---|---|---|
| `audio_manager.spl` | 283 | Real playback façade wired to `rt_audio_*` (miniaudio via SFFI): load/play/pause/stop, per-bus volume, 2D/3D position, listener orientation, master volume, `stop_all`/`destroy`. | Functional, wired to real backend. |
| `bus.spl` | 215 | `BusGraph` — named dB-domain bus DAG (FMOD/Godot-style): `add_bus`, `route` (cycle-rejecting), `set_volume_db`, `effective_gain` (own Taylor-series `dB→linear`, no libm dependency). | Solid pure-Simple logic, well-commented. |
| `audio_group.spl` | 157 | `AudioGroupTree` — simpler linear-volume parent/child mixing tree (distinct from `BusGraph`; the two overlap in purpose and aren't unified). | Functional. |
| `mixer_snapshot.spl` | 216 | `MixerSnapshot` + `MixerSnapshotManager` — named volume snapshots with lerp transitions (`transition_to`, `update(dt)`). | Functional, pure Simple. |
| `effects.spl` | 94 | `AudioEffect` enum (LowPass/HighPass/Reverb/Delay) + `EffectsChain` (add/remove_at/clear). Pure data/ordering — no DSP math, no rendering. | Data model only; actual filtering happens in `runtime_audio.c`/miniaudio node graph via `rt_audio_add_*`, not in Simple. |
| `hrtf.spl` | 99 | `HRTFData`/`HRIREntry` — azimuth/elevation → per-ear delay+gain table. | Data structure present; no evidence of a shipped HRIR dataset or use of it by `audio_manager`. |
| `doppler.spl` | 93 | Classic Doppler pitch formula, clamped [0.5, 2.0]. | Small, self-contained, testable. |
| `occlusion.spl` | 103 | Raycast-count → volume multiplier. | Small, self-contained. |
| `listener_system.spl` | 87 | ECS-style `AudioListenerComponent`/`AudioSourceComponent`, velocity tracking for Doppler. | Functional glue. |
| `sound_engine.spl` | 63 | **Not a real engine** — a command-log facade (`SoundEngine.play_2d/3d` just appends a `SoundCommand` to a list) used for platform-capability contract testing, not playback. Absent from `gc_async_mut` tier. | Test scaffold, not production playback path. |
| `types.spl` | 106 | `AudioClip`, `SoundHandle`, `AudioBus`, `AudioConfig`, `Listener3D` — plain data. | Stable. |

### Backend (`src/lib/nogc_sync_mut/io/audio_sffi.spl`, 169 lines)
Thin SFFI wrapper over `src/runtime/runtime_audio.c` (198 lines) + `miniaudio.h` (vendored,
excluded from owned-code scope). Exposes:
- **Playback only**: init/shutdown, load-from-file, play/play-looped/stop/pause/resume, volume
  (per-sound + master), spatial position/listener/min-max distance, pitch, and an effects
  node-graph (`rt_audio_add_lowpass/highpass/reverb/delay`, remove/clear).
- `runtime_audio.c` calls `ma_engine_init`, `ma_sound_init_from_file`, `ma_sound_init_copy` —
  **no** `ma_encoder` (WAV write), **no** `ma_decoder` direct use (engine handles decode
  internally via miniaudio's built-in WAV/FLAC/MP3 decoders — Vorbis/OGG not linked in this
  runtime), **no** capture/record API, **no** raw PCM buffer access from Simple.
- Net effect: Simple code can play a sound file and shape it live through a filter/reverb/delay
  node graph, but **cannot decode-to-samples, synthesize, or encode-to-file** from within Simple.

### `src/lib/nogc_sync_mut/game2d/audio/sound.spl` (37 lines)
Trivial `Sound` struct (clip_path/bus_name/volume/looped/spatial) with `sfx()`/`music()`/
`spatial_sfx()` constructors. Delegates all real work to `AudioManager`. No music-sequencing,
no per-note/pattern concept.

### `src/lib/common/engine/audio/sound_contract.spl` (106 lines)
FFI-free pure contracts used by cross-platform capability tests: `SoundBackendCapability`
(per-platform native/portable/unsupported status), `SoundCommand` (2D pan/volume math,
3D distance falloff — deterministic, milli-unit fixed point), `SoundCodecResult` (a **fake**
decode-vector validator keyed on a `"SSND:"` text magic string — not a real codec, just a
test double), `SoundParallelEvidence` (worker-pool vs inline evidence stub). This is
infrastructure for *testing the contract*, not a real codec/format layer.

### Test coverage (43 spec files found, `01_unit`/`03_system` trees duplicated under legacy
`test/unit`/`test/system` paths — likely stale mirrors, not double-counted here)
| Spec | `it` blocks | Covers |
|---|---|---|
| `test/01_unit/lib/engine/audio_bus_spec.spl` | 30 | `BusGraph` DAG, routing, dB math |
| `test/01_unit/lib/engine/audio_spec.spl` | 10 | `AudioManager` logic via a **mock** (no real `rt_audio_*` calls) |
| `test/01_unit/lib/common/audio_effects/audio_effects_spec.spl` | 7 | `EffectsChain` add/remove/clear (data only) |
| `test/03_system/app/audio_group_spec.spl` | 6 | `AudioGroupTree` |
| `test/01_unit/lib/engine/audio_spatial_spec.spl` | 5 | Doppler/occlusion math |
| `test/01_unit/lib/nogc_async_mut/game3d/audio_spec.spl` | 5 | 3D facade |
| `test/01_unit/app/io/audio_ffi_spec.spl` | 1 (568 lines, likely one big `it` with many raw assertions) | SFFI binding smoke |
| `engine_audio_facade_spec.spl` (gc/nogc_async tiers) | 1–2 each | Facade parity |

No spec renders audio to a file and asserts on sample bytes; all playback-path tests are either
pure-Simple math (bus/doppler/occlusion) or mocks. The one real-backend spec
(`audio_ffi_spec.spl`) exercises the SFFI surface but not sample-accurate output (device audio
is inherently non-deterministic to assert on).

### Grep sweep for synthesis/sequencing
`sequencer`, `tracker`, `synthesiz*`, `adsr` — **zero** hits anywhere under `src/lib/**/audio`,
`src/lib/**/game2d|game3d`, or `src/lib/common/engine/audio`. All hits repo-wide are compiler
internals (`monomorphize/tracker.spl`, `capability_tracker.spl`, VHDL backend, etc.) — no
overlap with audio. `wav|ogg|mp3|flac` hits only appear in `types.spl`/`listener_system.spl`
doc-comments (example paths like `"sfx/hit.wav"`) and `window_winit.spl`/`ftp_sffi.spl`
(unrelated substring matches, e.g. "wav" in "wave" or FTP not audio).

**Conclusion: there is no sound-effect synthesis, no ADSR envelope, no music sequencer/tracker,
and no WAV/audio file encoder anywhere in the codebase.** The engine is a real-time
playback+mix+spatialize+filter layer over pre-authored asset files (miniaudio), with a
well-built bus/snapshot/spatial math layer on top. Authoring new sound assets or music
currently requires an external tool; Simple has no format, no CLI, and no encode path.

## 2. Gap analysis vs. a shipped game's needs

| Need | Exists? | Real vs. YAGNI |
|---|---|---|
| Play pre-authored SFX/music files, mix by bus, mute/duck, spatialize | **Yes** — `AudioManager` + `BusGraph`/`AudioGroupTree` + `MixerSnapshotManager` + doppler/occlusion | Already covers most of what a shipped 2D/3D game needs at runtime. |
| Live effect chain on a bus/sound (lowpass/highpass/reverb/delay) | **Yes**, via miniaudio node graph + `EffectsChain` data model | Real, exercised at runtime — not authoring-time. |
| **Sound *authoring*: envelope/ADSR, pitch/layering for one-shot SFX** | **No** | Real gap. Every shipped game needs some way to shape a raw sample (fade in/out at minimum) or layer variations (e.g. footstep with pitch jitter) without hand-editing in a DAW every time. A minimal ADSR-on-render step is cheap and high-value. |
| **Music sequencing (even simple pattern/step form)** | **No** | Real gap only if the platform intends any *procedural* or data-driven music (adaptive loops, layered stems switched by `MixerSnapshotManager`, a simple chiptune-style pattern for placeholder/test content). A full tracker (multi-channel, instruments, effects columns) is almost certainly YAGNI for a first pass — the lazy, adequate version is a flat "sequence of (clip, start_ms, gain)" event list, not a note-based tracker. Full FT2-style tracker: skip until a concrete game asks for it. |
| **Waveform export (render to WAV file, byte-identical)** | **No** | Real gap and the crux one: without it, there is no way to (a) let a human preview a described sound offline, (b) get a deterministic, assertable test oracle. This is the one piece worth building first — everything else (CLI, SDN format) is scaffolding around it. |
| **Effect-chain preview/audition outside a live device** | Partially — `EffectsChain` exists but has no renderer; only `rt_audio_add_*` applies it live on a real audio device | Needed only if the preview path can't just piggyback on WAV-render (render dry, apply the same effect math offline, or reuse the miniaudio node graph in an offline `ma_engine` with a WAV encoder sink — miniaudio supports engine-to-encoder routing). Build after WAV render. |
| **A description format for a sound/music asset (SDN)** | No dedicated format; `sound_contract.spl`'s `"SSND:"` magic is a test fixture, not a real format | Needed to drive CLI render deterministically. Small, additive — not a big new subsystem. |
| **CLI or TUI edit surface** | No `simple sound` subcommand exists (checked `src/app/cli` — no audio-specific command) | Needed as the actual deliverable; a GUI is YAGNI until the CLI/SDN/render loop is proven. |
| **Capture/recording, live mic input** | No | YAGNI for a game platform's SFX/music authoring — this is a live-input feature, not asset authoring. Skip entirely. |
| **HRTF-based binaural spatialization** | Data structures exist (`hrtf.spl`) but disconnected from `AudioManager`/runtime | Not a music/SFX-authoring gap — it's a runtime spatial-audio feature, out of scope for this doc's tooling ask. Leave as-is. |

**Bottom line**: the runtime/mixing side is already solid and disproportionately more complete
than the authoring side, which is empty. The lazy, high-leverage move is: WAV encoder (runtime
extern) → tiny synth/render primitives (envelope, tone/noise generators, or just "play clip
through effects and capture to buffer") → SDN sound/music description → `simple sound` CLI
(validate/render/play) — in that order, each step usable/testable standalone. A tracker-grade
music sequencer and a GUI are explicitly deferred (YAGNI) until a real game asset demands them.
