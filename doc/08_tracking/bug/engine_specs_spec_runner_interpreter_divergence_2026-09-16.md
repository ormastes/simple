# Engine lib specs: spec-runner interpreter diverges from `run` (JIT) path

**Status:** OPEN 2026-09-16.
**Severity:** Blocking for 8 engine spec files (~33 failing examples).
**Spec files:** `test/01_unit/lib/engine/{scene_node,serializer,scene_manager,prefab,engine3d,physics3d,renderer3d,renderer3d_bugfix}_spec.spl`
**Lib files:** `src/lib/nogc_sync_mut/engine/scene/node.spl`, `src/lib/nogc_sync_mut/engine/scene/node3d.spl`, `src/lib/nogc_sync_mut/engine/physics/backend.spl`, `src/lib/nogc_sync_mut/engine/physics/config.spl`, `src/lib/nogc_sync_mut/engine/render/renderer3d.spl`
**Path:** `bug` track.

## Observed

Four distinct failure shapes, all reproducible GREEN under `bin/simple run` and RED under `bin/simple test` on the same code:

1. **Struct field access on Option-unwrapped payloads reported as Dict.**
   `store.get_node(nid)` returns `Node2D?`; `if val Some(node) = ...: node.name`
   fails with `semantic: undefined field: unknown property, key, or method 'name' on Dict`.
   Minimal repro (`/tmp/nodetest.spl`-equivalent) prints `player` under `run`.
   Hits: scene_node (9), serializer (4), scene_manager (2), prefab (1).
2. **Enum returns violate the non-optional contract.**
   `select_backend(PhysicsBackend.Auto)` (returns `PhysicsBackend`, never nil)
   fails with `semantic: nil is forbidden by the non-optional return contract of
   'select_backend'`. Under `run` it prints the enum. Hits: engine3d (2),
   physics3d (10).
3. **Module-local type shadowing across modules.**
   `node3d.spl` imports `Vec3` from `std.common.engine.math3d` (which has
   `static fn one()`), but the runner resolves the local `struct Vec3` in
   `physics/config.spl` (only `zero()`): `semantic: unknown static method one
   on class Vec3`. Hits: engine3d (3).
4. **Array indexing with str inside Dict iteration.**
   `render_scene` fails with `semantic: cannot index array with type 'str'`
   around `components.entries[key]` / `nodes.nodes[key]`. Under `run` the same
   scene renders. Hits: renderer3d (1), renderer3d_bugfix (1).

## Impact

8 spec files stay RED with failures that do not exist on the JIT path, masking
real regressions and blocking the lane's clean-exit criteria.

## Expectation

The spec-runner interpreter and the `run` JIT must agree on: enum return
marshalling, Option payload typing, cross-module name resolution for imported
types vs module-local structs, and Dict/array index typing. Each of the four
shapes above should fail (or pass) identically under both entry points.

## Unblock condition

Reproduce each shape with a minimal `.spl` fixture under both `bin/simple run`
and the test-runner path, fix the interpreter divergences in the runner
(`src/app/test_runner_new/` / interpreter core), then re-run the 8 spec files
listed above — all must reach `outcome=OK` without spec-side weakening.
