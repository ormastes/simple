<!-- codex-design -->
# Sound Engine Detail Design

## Modules
- `src/lib/common/engine/audio/sound_contract.spl`: pure status enums, command records, sample format, codec header, stream chunk metadata, and error labels.
- `src/lib/nogc_sync_mut/engine/audio/sound_engine.spl`: public mutable facade.
- `src/lib/nogc_sync_mut/engine/audio/backend_registry.spl`: maps target platform to backend status and adapter.
- `src/lib/nogc_sync_mut/engine/audio/no_audio_backend.spl`: deterministic backend for tests and unavailable hosts.
- `src/lib/nogc_sync_mut/engine/audio/mixer_queue.spl`: ordered command queue and mixer snapshots.
- `src/lib/nogc_sync_mut/engine/audio/simple_sound_codec.spl`: pure-Simple sound asset codec.
- `src/lib/nogc_sync_mut/engine/audio/streaming_decode.spl`: chunk cursor and bounded decode.
- `src/lib/nogc_sync_mut/engine/audio/parallel_jobs.spl`: worker-pool facade with inline fallback evidence.
- `src/lib/nogc_sync_mut/game2d/audio/sound_binding2d.spl`: 2D entity binding.
- `src/lib/nogc_sync_mut/engine/audio/sound_binding3d.spl`: 3D entity/listener binding.

## Core Data
```simple
struct SoundBackendCapability:
    platform: text
    status: text
    backend: text
    reason: text

struct SoundCommand:
    order: i64
    kind: text
    entity_id: text
    clip_id: text
    volume: f64
    pan: f64
    x: f64
    y: f64
    z: f64

struct SoundCodecHeader:
    magic: text
    version: i64
    sample_rate: i64
    channels: i64
    encoding: text
    frame_count: i64
```

Use text status values initially to match existing Simple patterns and avoid enum interop churn across runtime families.

## API Shape
`SoundEngine.create(config)` selects a backend via `backend_registry`, creates default groups, initializes mixer state, and records capability evidence. `SoundEngine.create_no_audio(config)` bypasses native device I/O for CI and deterministic specs.

Playback APIs enqueue `SoundCommand` records first, then submit to the selected backend. Native playback is an effect of draining the queue; no-audio playback records commands and active handles only.

## Codec Algorithm
The first codec is `SimpleSound`:
- header with magic/version/sample rate/channel count/encoding/frame count;
- PCM/lossless reference frames;
- compact delta frames for game assets;
- chunk table for streaming decode.

Decode validates header, channel count, sample rate, frame bounds, and chunk size before allocation. Corrupt input returns structured error text.

## Parallelism
`parallel_jobs` accepts decode/prepare jobs and returns `SoundParallelEvidence`:
- `mode`: `worker-pool` or `inline-fallback`;
- `submitted`;
- `completed`;
- `deterministic_order_hash`.

The mixer consumes completed buffers in command-order sequence, never worker completion order.

## Engine2D Binding
The 2D adapter maps entity world position to pan and volume:
- pan from horizontal listener-relative offset clamped to `[-1.0, 1.0]`;
- volume from distance attenuation and group volume;
- command can be generated without renderer/device state.

## Engine3D Binding
The 3D adapter maps source/listener transforms to:
- distance attenuation;
- Doppler pitch metadata;
- occlusion factor;
- HRTF-ready azimuth/elevation labels.

The first implementation emits metadata and mixer commands; advanced HRTF convolution can be a later backend capability.

## Error Handling
Use structured result records or `Result<T, E>` where available. Hardening errors include `invalid-device-state`, `bad-magic`, `unsupported-version`, `bad-sample-rate`, `bad-channel-count`, `bad-frame-size`, `buffer-underrun`, `buffer-overflow`, and `teardown-during-playback`.

## Verification Mapping
- REQ-001 to REQ-005: backend facade, no-audio backend, and platform status specs.
- REQ-006 to REQ-007: Engine2D/Engine3D binding specs.
- REQ-008 to REQ-009: codec vector and corrupt-input specs.
- REQ-010: parallel evidence and deterministic mixer ordering specs.
- REQ-011: hardening matrix specs.
- REQ-012 to REQ-013: system scenario manuals and docs.
