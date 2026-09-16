# Engine lib API surface drift vs. spec expectations

**Date:** 2026-07-20
**Category:** GENUINE-BUG (missing/mismatched implementation, not a test-naming issue)
**Command:** `SIMPLE_RUST_SEED_WARNING=0 timeout 90 bin/release/x86_64-unknown-linux-gnu/simple test <spec> --no-session-daemon`

## Symptom

A large family of `test/unit/lib/engine/*_spec.spl` files fail (partially or
completely) because the `src/lib/common/engine/*.spl` and
`src/lib/nogc_sync_mut/engine/**/*.spl` modules they exercise implement only a
narrow subset of the API surface the spec files test against — in several
cases a structurally different design entirely. This is NOT a simple
rename/stale-API issue: the missing pieces are real, non-trivial
functionality (new methods, new classes, redesigned fields), so it is out of
scope for a test-spec-only or one-line-rename fix.

Failure granularity is **per-example, not whole-file**: SSpec evaluates each
`it` block independently, so an example fails only if it references a symbol
that doesn't exist in the imported module. This was confirmed directly via
`test/unit/lib/skia/matrix_spec.spl` (see below) where exactly the 5 examples
calling the one missing method failed, and the other 13 (using only
implemented methods) passed.

## Affected specs and concrete deltas found

- **`test/unit/lib/engine/rect_spec.spl`** (0/10 passing) — `src/lib/common/engine/rect.spl`'s
  `Rect2` has only `zero()`, `right()`, `bottom()`, `contains_point()`,
  `intersects()`, `is_empty()`, `to_string()`. Spec calls `Rect2.new(...)`
  (no static `new`; canonical ctor is `Rect2(x:, y:, width:, height:)`),
  `.from_center()`, `.left()`, `.top()`, `.merge()`, `.expand()` — none exist.
  Every one of the 10 examples touches at least one missing symbol (either
  the missing `.new()` ctor or one of the missing geometry methods).

- **`test/unit/lib/engine/math2d_spec.spl`** (7/16 passing) —
  `src/lib/common/engine/math2d.spl`'s `Vec2` has `zero/one/add/sub/scale/dot/
  length/normalized/to_string`. Spec expects `mul_scalar` (→ real rename of
  `scale`), `normalize` (→ real rename of `normalized`), plus genuinely
  missing `cross`, `length_squared`, `distance_to`, `lerp`. `Transform2D`
  is missing `transform_point()` and `compose()` entirely (only `identity()`
  + `to_string()` exist).

- **`test/unit/lib/engine/ids_spec.spl`** (2/13 passing) —
  `src/lib/common/engine/ids.spl` implements a flat-int-id design
  (`RawHandle{value:i64}`, `NodeId{raw:i64}`, no `.eq()` anywhere, no
  `SpriteId` class at all). Spec expects a generational-handle design
  (`RawHandle{index, generation}` via `.new(index, gen)`/`.invalid()`/
  `.is_valid()`/`.to_index()`/`.eq()`, `NodeId{raw: RawHandle}`, plus a
  `SpriteId` wrapper). This is a different design, not a rename.

- **`test/unit/lib/engine/units_spec.spl`** (17/42 passing) —
  `src/lib/common/engine/units.spl` declares fields + a handful of static
  constructors only. **No** unit class has `to_f64()`, `to_i64()`, `add()`,
  `sub()`, `eq()`, or `Angle.to_radians()`. `GamepadButtonId`, `PixelSize`,
  `FrameIndex`, `RGBA8` classes don't exist at all. (`Volume.mute_vol()` vs.
  existing `Volume.silent()` looks like a rename but is moot — the class is
  missing all the instance methods the spec needs regardless.)

- **`test/unit/lib/engine/color_spec.spl`** (4/9 passing) —
  `src/lib/common/engine/color.spl`'s `EngineColor` has only
  `white/black/red/green/blue/transparent`. Spec needs `.rgba()`, `.rgb()`,
  `.lerp()`, `.to_rgba8()`, `.from_hex()`, `.with_alpha()` — none exist.

- **`test/unit/lib/engine/signal_spec.spl`** (0/8 passing) —
  `src/lib/common/engine/signal/signal.spl`'s `Signal` is missing
  `connect_once()`, and `disconnect()` returns nothing (spec expects a
  `bool`). Worse: `src/lib/common/engine/signal/event_bus.spl` (imported by
  the spec as `std.common.engine.signal.event_bus.{EventBus}`) **does not
  exist as a file**, and no `EventBus` class exists anywhere in the repo
  (verified via `grep -rn "class EventBus" src/`).

- **`test/unit/lib/engine/component_registry_spec.spl`** (0/8 passing) —
  `ComponentRegistry`/`SpriteData`/`CameraData` themselves match the spec,
  but every example constructs a `NodeId`/`TextureId`/`RawHandle` using the
  generational-handle shape (`RawHandle(index:, generation:)`), which fails
  for the same `ids.spl` reason as above.

- **`test/unit/lib/engine/serializer_spec.spl`** (0/4 passing) —
  `src/lib/nogc_sync_mut/engine/scene/{node,serializer}.spl` define
  `create/has_tag/get_node/node_count/get_local_transform` +
  `serialize_scene/deserialize_scene`. Spec calls `.new()`, `add_tag()`,
  `set_parent()`, `set_position()`, `set_z_index()`, `is_valid()` — none of
  these exist on `NodeStore`/node.

- **`test/unit/lib/engine/batch_spec.spl`** (1/5 passing) and
  **`test/unit/lib/engine/command_spec.spl`** (7/12 passing) —
  `src/lib/nogc_sync_mut/engine/render/command.spl` defines
  `create/eq/invalid/len/to_i64` (+ `get_z_order`/`sort_commands_by_z` in
  `batch.spl`). Spec calls `.new()`, `push()`, `clear()` on
  `RenderCommandBuffer` — not defined.

## Root-cause hypothesis

These `src/lib/common/engine/*.spl` and `src/lib/nogc_sync_mut/engine/**`
modules read like early/partial scaffolding (field declarations + a couple
of static factory constructors) that the corresponding `test/unit/lib/engine/
*_spec.spl` files were written ahead of — i.e., spec-first stubs whose
implementation was never finished, OR the implementation was later
simplified/reverted without the specs being pruned to match. `ids.spl` in
particular looks like a genuinely different (simpler) design than what
`component_registry_spec.spl`/`serializer_spec.spl`/`ids_spec.spl` assume,
suggesting a design pivot that didn't propagate to the source.

## Why this isn't fixed here

- Spec-side fix is impossible without weakening/deleting assertions for the
  missing behavior (prohibited).
- Source-side fix requires implementing real new methods/classes across at
  least 6 files (`rect.spl`, `math2d.spl`, `ids.spl`, `units.spl`,
  `color.spl`, `signal/{signal,event_bus}.spl`) — well beyond the "one-line
  import/rename" allowance for this cluster-fix pass.

## Suggested next step

Treat as a scoped implementation task: pick one module at a time (`ids.spl`
is highest-leverage since 3 specs depend on it), decide whether to update the
source to the generational-handle design the specs assume or prune the specs
down to the current design, and implement/port method-by-method with the
specs as the acceptance criteria.
