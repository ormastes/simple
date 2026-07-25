# `RawHandle`/`NodeId`/`TextureId` generational-handle API drift

**Date:** 2026-07-20
**Severity:** medium (test-only impact so far; not confirmed to affect
production callers)
**Status:** open — needs an owner decision, not a mechanical test fix
**Found by:** whole-suite `test/unit/` triage campaign, `lib/engine` +
`lib/nogc_async_mut/engine` clusters

## Symptom

Multiple engine-facade specs construct `RawHandle`/`NodeId`/`TextureId` using
a 2-3-field "generational handle" shape (`index` + `generation`, or a 2-arg
positional `.new(...)`), but the CURRENT class definitions in
`src/lib/common/engine/ids.spl` are single-field opaque wrappers with no
`.new()` static constructor at all:

```simple
# src/lib/common/engine/ids.spl (current)
pub class RawHandle:
    """Opaque integer handle for foreign resources (GPU buffers, OS handles, etc.)."""
    value: i64

    static fn null() -> RawHandle:
        RawHandle(value: 0)

    fn is_null() -> bool:
        self.value == 0

pub class TextureId:
    """Unique identifier for a loaded texture asset."""
    raw: i64          # <- plain i64, NOT a RawHandle
    ...
```

vs. what the specs assume:

```simple
# test/unit/lib/engine/sprite_spec.spl:84
val tex_id = TextureId(raw: RawHandle.new(0, 1))   # RawHandle.new/2 does not exist; TextureId.raw is i64, not RawHandle

# test/unit/lib/nogc_async_mut/engine/component/engine_component_facade_spec.spl:16-17
val node = NodeId(raw: RawHandle(index: 1, generation: Generation(value: 1)))
val tex = TextureId(raw: RawHandle(index: 2, generation: Generation(value: 1)))
# RawHandle has only a `value: i64` field, not `index`/`generation`
```

Errors observed (deployed binary
`bin/release/x86_64-unknown-linux-gnu/simple`, `bin/simple test <spec>
--no-session-daemon`):

- `semantic: unknown static method new on class RawHandle`
- `semantic: class \`RawHandle\` has no field named \`index\``

## Root-cause hypothesis

This is not a rename — it's a genuine shape change. Either:
1. `RawHandle` used to carry `index`/`generation` (a classic ECS
   generational-arena handle) and was collapsed down to a bare `value: i64`
   wrapper (dropping generational safety), and `NodeId`/`TextureId` used to
   wrap `RawHandle` but now wrap plain `i64` directly — and the specs were
   never updated to match, or
2. The specs encode an *intended* future generational-handle design that was
   never implemented in `ids.spl`.

Distinguishing these requires knowing the current intended engine ID
architecture, which is a design call, not a mechanical test-triage fix. Left
unmodified per the "never weaken/rewrite an assertion to force green" rule —
guessing which side is stale risks silently reverting or silently adopting a
design change.

## Affected specs

- `test/unit/lib/engine/sprite_spec.spl` — `describe "SpriteSheet"` block, 3
  examples (`"computes frame rect for first frame"`, `"...second row"`,
  `"returns total frame count"`), all via `RawHandle.new(0, 1)` at lines 84,
  93, 101.
- `test/unit/lib/nogc_async_mut/engine/component/engine_component_facade_spec.spl`
  — `"re-exports 2D registry and helper extensions"` (line 16), via
  `RawHandle(index: 1, generation: Generation(value: 1))`.

(The rest of `sprite_spec.spl`'s failures are unrelated — see
`EngineColor.rgba` unknown-static-method, now fixed by this same triage pass
to a struct literal; and two genuine numeric-precision bugs in
`pack_color`/`unpack_color` and `create_solid_color_texture` that were masked
by the `EngineColor.rgba` compile error and are now newly visible, still
unclassified.)
