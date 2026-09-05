<!-- codex-design -->
# Sound Engine System Test Plan

## Executable Spec
`test/03_system/app/sound_engine/feature/sound_engine_spec.spl`

## Generated Manual
`doc/06_spec/03_system/app/sound_engine/feature/sound_engine_spec.md`

## Coverage
- REQ-001: public API surface represented by lifecycle/playback/streaming/group/effects command contract.
- REQ-002, REQ-003: platform capability matrix covers Linux, BSD, macOS, Android, iOS, and Simple OS.
- REQ-004, REQ-005: no-audio backend and lightweight dependency boundary.
- REQ-006: 2D positional sound command.
- REQ-007: 3D positional/listener metadata command.
- REQ-008, REQ-009: codec round trip, streaming chunks, malformed input rejection.
- REQ-010: worker vs inline fallback evidence and deterministic mixer order.
- REQ-011: hardening matrix.
- REQ-012, REQ-013: primary scenario manual and documentation links.

## Scenario Groups
1. Platform capability status.
2. No-audio lifecycle and playback.
3. 2D entity sound flow.
4. 3D entity sound flow.
5. Codec streaming and malformed data.
6. Parallel decode/mixer determinism.
7. Hardening matrix and documentation evidence.

## Quality Gates
- No executable specs under `doc/06_spec`.
- No `pass_todo`, empty bodies, or equality-only self-comparisons.
- Host-unavailable platform checks must name the unavailable host condition.
- Generated manual must show the five primary game-development flows without requiring the source spec.
