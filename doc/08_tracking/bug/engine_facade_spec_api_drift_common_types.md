# Engine Facade Specs: API Drift in std.common.engine Types

**Status:** PARTIAL FIX — Bug 1 (Vec3.forward) and Bug 3 (KeyCode.code, MouseButtonId.code) fixed 2026-05-30; Bug 2 (RawHandle refactor) remains OPEN
**Severity:** Moderate — import resolution fixed; spec logic fails due to API drift in common types
**Affected specs:**
- `test/01_unit/lib/gc_async_mut/engine/audio/engine_audio_facade_spec.spl`
- `test/01_unit/lib/gc_async_mut/engine/component/engine_component_facade_spec.spl`
- `test/01_unit/lib/gc_async_mut/engine/input/engine_input_facade_spec.spl`
- `test/01_unit/lib/gc_async_mut/engine/scene/engine_scene_facade_spec.spl`
- `test/01_unit/lib/gc_async_mut/engine/sprite/engine_sprite_facade_spec.spl`
- Same 5 specs under `test/01_unit/lib/nogc_async_mut/engine/` (identical failures)
**Confirmed identical in nogc counterparts:** yes — pre-existing, not caused by gc facade scaffolding.

## Symptoms

### Bug 1: Vec3.forward() missing — audio spec — FIXED 2026-05-30
`semantic: unknown static method forward on class Vec3`
Specs call `Vec3.forward()` but `src/lib/common/engine/math3d.spl` only defines `Vec3.zero()` and `Vec3.one()`.
**Fixed:** Added `static fn forward() -> Vec3: Vec3(x: 0.0, y: 0.0, z: 1.0)` to `Vec3` in `math3d.spl`.
Convention: +Z forward (standard OpenGL/game engine convention).

### Bug 2: RawHandle(index:, generation:) constructor mismatch — component, scene, sprite specs
`semantic: class RawHandle has no field named index`
`semantic: too many arguments for class RawHandle constructor`
Specs call `RawHandle(index: 1, generation: Generation(value: 1))` but `RawHandle` in `ids.spl` only has `value: i64`.
Specs also pass `RawHandle(...)` to `NodeId(raw:)` and `TextureId(raw:)`, but those fields are `raw: i64`.
**Fix required:** Either (a) add `index: i64` and `generation: Generation` fields to `RawHandle` AND change `NodeId.raw`/`TextureId.raw` to `raw: RawHandle`, updating all call sites in `nogc_sync_mut/engine/scene/`, `nogc_sync_mut/engine/sprite/`, etc.; or (b) rewrite spec to use `RawHandle(value: n)` and `NodeId(raw: n)` with plain integers.
This is a significant API refactor — scope it separately.

### Bug 3: KeyCode(code:) field missing — input spec — FIXED 2026-05-30
`semantic: class KeyCode has no field named code`
Specs call `KeyCode(code: 32)` but `KeyCode` in `units.spl` only had `value: i64`.
**Fixed:** Renamed `KeyCode.value` to `KeyCode.code` and `MouseButtonId.value` to `MouseButtonId.code` in `units.spl` to match all real callers (default_bindings.spl, keys.spl, specs).
Both gc_async_mut and nogc_async_mut input specs now pass.

## Context
These failures pre-date the gc_async_mut facade scaffolding (2026-05-30). The gc_async_mut facades
were added in commit `nq ee` to fix module resolution. The 5 runtime failures here are unrelated
to import resolution and exist identically in the nogc_async_mut variants.

## Files to Fix
- `src/lib/common/engine/math3d.spl` — add Vec3.forward()
- `src/lib/common/engine/ids.spl` — RawHandle struct + NodeId/TextureId.raw type
- `src/lib/common/engine/units.spl` — KeyCode.code field
