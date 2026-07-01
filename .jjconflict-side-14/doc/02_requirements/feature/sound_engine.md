<!-- codex-research -->
# Sound Engine Feature Requirements

## Selection
User selected feature option `D`: Full Sound Engine Lane.

## Goal
Build the full requested Simple sound engine lane: platform facade, no-audio backend, Engine2D and Engine3D hooks, pure-Simple codec support, streaming, parallel workers, hardening, docs, and SPipe system specs.

## Requirements
- REQ-001: Provide a documented `SoundEngine` Simple API for initialization, capability probing, playback, streaming, pause/resume, stop, volume, pan, spatial position, listener state, mixer groups, effects, and deterministic teardown.
- REQ-002: Preserve the existing miniaudio runtime bridge as an allowed native device-I/O boundary while exposing a Simple-owned platform capability facade above it.
- REQ-003: Report Linux, BSD, macOS, Android, iOS, and Simple OS backend status as one of `native`, `portable`, `unsupported`, or `host-unavailable`; tests must prove status mapping cannot silently pass as native support.
- REQ-004: Provide a no-audio/mock backend usable by unit, integration, and system specs on hosts without audio hardware.
- REQ-005: Keep the public Simple sound layer lightweight by avoiding mandatory heavyweight third-party dependencies outside the runtime bridge and documenting any native dependency boundary.
- REQ-006: Add Engine2D hooks that attach sounds to 2D scene entities, derive pan/volume from 2D transforms, and emit deterministic mixer commands without requiring an active renderer.
- REQ-007: Add Engine3D hooks that attach sounds to 3D scene entities, synchronize listener state with camera/listener transforms, and emit deterministic distance attenuation, Doppler, occlusion, and HRTF-ready metadata.
- REQ-008: Add pure-Simple sound codec support with at least one high-quality uncompressed or lossless reference path and one compact game-asset encoding path.
- REQ-009: Codec support must include streaming decode boundaries, fixed-vector round trips, corrupt-input rejection, bounded allocation behavior, and no placeholder equality-only assertions.
- REQ-010: Mixing, streaming decode, and asset preparation must support safe parallel task distribution when worker-pool support exists, with deterministic mixer ordering and explicit inline fallback evidence otherwise.
- REQ-011: Hardening coverage must include invalid device states, malformed codec data, extreme sample rates, channel-count mismatches, buffer underrun/overflow boundaries, teardown during playback, and cleanup after failures.
- REQ-012: SPipe system specs and generated manuals must demonstrate five primary flows: play a 2D positional sound, play a 3D positional sound, stream decoded audio, run with the no-audio backend, and report platform capability status.
- REQ-013: Documentation must explain architecture, platform support, codec format choices, Engine2D/Engine3D integration points, optimization strategy, Simple OS driver/service boundaries, and the parallel-review handoff checklist.

## Scope Exclusions
Full DAW editing, MIDI sequencing, network voice chat, proprietary codec patent licensing, and guaranteed native-device execution on unavailable CI hosts are out of scope for the first production-ready lane.
