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

---

## Resolution 2026-08-17 — NOT test-only: production code was calling `RawHandle.new/2` too

### The record understated this: it is a live production defect

The "test-only impact so far" severity note above is **wrong**. `RawHandle.new`
is called from shipped library code, not just specs:

```
src/lib/nogc_sync_mut/engine/scene/node3d.spl:106:        val raw = RawHandle.new(index, gen_val)
src/lib/nogc_sync_mut/engine/scene/node.spl:127:        val raw = RawHandle.new(index, gen_val)
src/lib/nogc_sync_mut/engine/scene/serializer.spl:87:        val raw = RawHandle.new(si2, 1)
src/lib/nogc_sync_mut/engine/scene/serializer.spl:121:            val parent_raw = RawHandle.new(parent_idx, 1)
```

Every one of those is `Node2DStore.create_node` / `Node3DStore.create_node` /
the scene deserializer — i.e. creating ANY scene node was unreachable code.

### Reproduction (before)

```
$ nice -n 19 timeout 400 bin/simple run /tmp/.../p9.spl
[jit-fallback] unresolved external symbol 'RawHandle_dot_new': whole module dropped to the interpreter
[INFO] JIT compilation failed, falling back to interpreter: Cranelift JIT compile: Module error: unresolved external symbol 'RawHandle_dot_new' would NULL-jump in JIT; deferring to interpreter
error: semantic: unknown static method new on class RawHandle
```

### Which side is authoritative: the PACKED i64, decided by existing source

The record framed this as an open design call. It is not — the decision was
already made and half-landed. `src/lib/nogc_sync_mut/engine/sprite/texture.spl`
carries the migration note in-tree:

```
# TextureId.raw is a plain i64 (common/engine/ids.spl); the generational
# handle packs index into the low 32 bits and generation into the high 32.
# (The previous code constructed TextureId(raw: RawHandle) and read
# id.raw.index — inconsistent with ids.spl and rejected by JIT lowering.)
```

and implements it (`TextureId(raw: idx + (new_gen << 32))`, read back with
`id.raw & 0xFFFFFFFF` / `id.raw >> 32`). So **hypothesis 1 in this record is
correct** — the struct-shaped generational `RawHandle` was deliberately
collapsed to a packed i64 — and `texture.spl` finished the migration while
`ids.spl` and the scene files never did. Generational safety was NOT dropped;
it moved into the bit packing.

### Root cause (in scope)

`src/lib/common/engine/ids.spl`, two defects:

1. **`RawHandle.new(index, generation)` never existed** (`ids.spl:58-63` had
   only `value`, `null()`, `is_null()`), so all four production call sites and
   `test/unit/lib/engine/sprite_spec.spl:84,93,101` failed to resolve.
2. **`NodeId.to_index()` / `TextureId.to_index()` returned the whole packed
   word**, with a docstring that actively asserted the bug: *"Return the arena
   index backing this id (same as `raw`)."* Under the packed layout that is
   `index + (generation << 32)` — for any generation > 0 it is a huge number,
   so `node.spl`'s `if index < 0 or index >= self.nodes.len(): return nil`
   would reject every live handle. A silent-wrong-result defect, latent behind
   defect 1.

### Fix

`src/lib/common/engine/ids.spl`:
- Added `RawHandle.new(index, generation) -> i64` packing
  `(index & 0xFFFFFFFF) + (generation << 32)`, plus `RawHandle.index_of/1` and
  `RawHandle.generation_of/1` unpackers. It returns a plain `i64`, not a
  `RawHandle`, because that is what `NodeId.raw`/`TextureId.raw` are and what
  every call site feeds directly into `NodeId(raw: ...)`.
- `NodeId.to_index()` / `TextureId.to_index()` now mask the low 32 bits, and
  each gained a `generation()` accessor. Docstrings corrected.

`RawHandle` keeps `value`/`null()`/`is_null()` — it is still the opaque
foreign-resource handle its own docstring describes; the packing statics are
additive and break no existing caller.

### Spec side

`test/unit/lib/engine/sprite_spec.spl` needed no change — its
`TextureId(raw: RawHandle.new(0, 1))` is now exactly right.

`test/unit/lib/nogc_async_mut/engine/component/engine_component_facade_spec.spl:16-17`
**was updated, and this is a deliberate spec change, stated explicitly**: it
constructed `RawHandle(index: 1, generation: Generation(value: 1))`, the
struct-shaped design that was deliberately dropped in favour of packing. It now
uses `RawHandle.new(1, 1)`. No assertion was weakened or deleted — only the
construction expression was moved to the authoritative API, with a comment
pointing back at this record.

`Generation` is untouched and still exported; it remains the standalone
generational counter type.

### Verification

New spec `test/01_unit/lib/common/engine/ids_packed_handle_spec.spl` — carries
both the reproducing cases (`RawHandle.new`, `to_index` on a packed handle) and
class-generalizing prevention: an index x generation round-trip matrix across
every packed id type (including generation 0, the case a naive `raw`
passthrough gets right by accident), stale-vs-bumped handle distinctness, and
the `invalid()` sentinels vs. slot 0.

### Status

**FIXED.** Remaining known gap, out of this worker's scope: `node.spl:145,157`
and `node3d.spl` still read `id.raw.generation.value` — field access on an
`i64` — the read-side half of the same half-finished migration. Those files are
under `src/lib/nogc_sync_mut/**` and were not editable here; they should be
changed to `id.generation()` (or `RawHandle.generation_of(id.raw)`), which now
exists for them. Filed as the follow-up to this record.
