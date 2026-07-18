<!-- codex-design -->
# Sound Engine Architecture

## Scope
Selected lane: feature option `D` plus NFR option `3`. The sound engine must cover cross-platform device status, no-audio fallback, 2D/3D game hooks, pure-Simple codec/streaming, parallel asset work, hardening, and Simple OS boundaries.

## Existing Base
- Native device bridge: `src/runtime/runtime_audio.c` plus `src/runtime/miniaudio.h`.
- Simple wrappers: `src/lib/nogc_sync_mut/io/audio_sffi.spl`.
- Current manager/types: `src/lib/nogc_sync_mut/engine/audio/`.
- Game2D metadata: `src/lib/nogc_sync_mut/game2d/audio/sound.spl`.
- SimpleOS readiness: `src/os/drivers/audio/`, `src/os/game/platform/`, and driver readiness contracts.

## Pattern Choice
Use an MDSOC-style virtual capsule named `sound_engine`:

```
public Simple API
  -> capability + backend registry capsule
  -> mixer command capsule
  -> codec/stream capsule
  -> Engine2D adapter capsule
  -> Engine3D adapter capsule
  -> native runtime or SimpleOS service boundary
```

The capsule owns cross-cutting status, deterministic command ordering, and hardening evidence. Native miniaudio and SimpleOS drivers stay below the public API as device-I/O adapters.

## Layers
1. `common/engine/audio`: pure status, commands, codec headers, sample buffers, mixer snapshots, and error types.
2. `nogc_sync_mut/engine/audio`: mutable `SoundEngine`, no-audio backend, backend registry, mixer queue, streaming cursor, and worker facade.
3. `nogc_sync_mut/io/audio_sffi`: native runtime bridge only; no platform policy.
4. `nogc_sync_mut/game2d/audio`: 2D scene/entity adapter.
5. `nogc_sync_mut/gpu/engine3d` or `engine/audio`: 3D listener/entity adapter.
6. `os/drivers/audio` and `os/game/platform`: Simple OS capability and driver evidence.

## Backend Status Contract
Every target reports one of:
- `native`: real target backend available and selected.
- `portable`: portable bridge available, usually miniaudio or no-device-safe runtime path.
- `unsupported`: target intentionally lacks playback support.
- `host-unavailable`: current host cannot execute or probe that target.

No boolean init result may be used as the only platform evidence.

## Device Boundary
The native bridge may use miniaudio for Linux, BSD, macOS, Android, and iOS. Simple OS uses the OS audio service/driver contracts. The public Simple layer depends on capability records and backend traits, not direct `rt_audio_*` calls.

## Mixer And Parallelism
Background workers may decode, resample, and prepare buffers. The mixer consumes a deterministic queue:

```
stream/decode jobs -> ready buffer records -> ordered mixer commands -> backend submit
```

The mixer boundary must record whether worker-pool execution ran or inline fallback was used.

## Codec Position
First production lane should implement a Simple-owned sound asset container with:
- lossless or PCM reference frames;
- compact game-asset frames;
- streaming chunks;
- fixed vectors;
- corrupt-input rejection.

Opus/Vorbis compatibility remains a design target, but a full pure-Simple Opus/Vorbis encoder is not required for the first production-ready lane.

## Engine2D And Engine3D Integration
Engine2D adapter reads entity transform and emits pan/volume/mixer commands without requiring a renderer. Engine3D adapter reads entity plus listener/camera state and emits distance, Doppler, occlusion, and HRTF-ready metadata.

## Hardening
Hardening belongs in codec parsers, backend lifecycle, mixer queues, and teardown. Invalid states must produce structured errors or `unsupported`/`host-unavailable` status, never silent success.

## Observability
Required counters:
- selected backend and status;
- no-audio backend selected;
- mixer command count;
- streaming chunks decoded;
- worker jobs scheduled/completed;
- inline fallback count;
- codec corrupt-input rejects;
- teardown cleanup count.

## Architecture Risks
- Runtime effects declarations currently exceed sampled `runtime_audio.c` implementation evidence; implementation must reconcile declarations and C symbols.
- Existing tests use local mock managers; production should centralize the no-audio backend to avoid mock drift.
- Platform evidence for Android, iOS, BSD, macOS, and Simple OS may be `host-unavailable` on Linux CI, but that must be explicit.
