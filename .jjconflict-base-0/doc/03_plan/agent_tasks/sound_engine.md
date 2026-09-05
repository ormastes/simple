<!-- codex-design -->
# Sound Engine Agent Task Breakdown

## Lane Ownership
Feature lane: `.spipe/sound-engine/`.

## Parallel Tasks
- Research reviewer: confirm miniaudio, codec, and platform assumptions against `doc/01_research/*/sound_engine.md`.
- Architecture reviewer: validate `doc/04_architecture/sound_engine.md` against MDSOC layering and SimpleOS boundaries.
- API implementer: add `SoundEngine`, backend registry, no-audio backend, and status contracts.
- Engine integration implementer: add Engine2D and Engine3D sound binding modules.
- Codec implementer: add `SimpleSound` codec, streaming decode, fixed vectors, and corrupt-input rejection.
- Parallelism implementer: add worker facade, inline fallback evidence, and deterministic mixer queue.
- Hardening implementer: add invalid-state, malformed-input, boundary, teardown, and cleanup tests.
- Optimization reviewer: run baseline/optimized checks on codec/DSP hot paths and record blockers.
- Documentation reviewer: refresh guides, generated manuals, and SimpleOS boundary docs.

## Review Checklist
- Requirements REQ-001 through REQ-013 have implementation and tests.
- NFR-001 through NFR-011 have direct evidence.
- Platform support never silently claims native support.
- No-audio backend is production-quality for CI and tests.
- Parallel fallback cannot masquerade as worker-pool execution.
- Codec tests include absolute fixed vectors and malformed input.
- Generated docs contain no executable `.spl` files under `doc/06_spec`.

## Refactoring Alignment (2026-06-12)

Per `doc/03_plan/ui/graphics/engine/game_engine_2d3d_unification_plan_2026-06-12.md`
(P3 audio bus API), main refactoring executed by a separate agent:

- API implementer: `SoundEngine` exposes a named bus-graph API (buses with dB
  volume, sends, effect slots) layered over `engine/audio/audio_group.spl` and
  miniaudio's node graph — FMOD/Godot bus model, no parallel mixing path.
- Engine integration implementer: Engine2D/Engine3D bindings route through the
  bus graph; the 3D spatial chain (`hrtf.spl`, `doppler.spl`, `occlusion.spl`,
  `listener_system.spl`) stays in `engine/audio/` and is engine-agnostic.
- Optional Steam Audio SFFI spatializer is a plugin behind the same listener/
  emitter API, not a fork of it; absence is a typed status, not silent fallback.
