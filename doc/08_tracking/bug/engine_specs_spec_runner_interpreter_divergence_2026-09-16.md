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

## 2026-11-07 — shape 3 root cause and fix (round 15, PR "interp: module-qualified type registry")

Shape 3 (`unknown static method one on class Vec3`) is a seed-interpreter
registry defect, not a runner one: the class/struct registry consulted by
static-path calls, `Value::Constructor` calls and instance dispatch was the
flat bare-name map (last registration wins), and the per-module table that
`owner_module_class` reads (`MODULE_CLASSES_CACHE`) was itself overwritten by
bare name every time any module's `impl Name:` block was evaluated
(`evaluation_helpers.rs`, "Update MODULE_CLASSES_CACHE with the enriched
class definition" loop), so module A's cached `Vec3` became module B's.

Fix (`src/compiler_rust/compiler/src/module_cache.rs`):
`resolve_class_in_scope` — executing module's own definition, then its
`use m.{Name}` / `use m.*` binding, then the unique owned definition, else an
"ambiguous type" error; `resolve_class_for_instance` — the definition whose
fields are exactly the instance's; `refresh_cached_class` — enrichment moves
only the slot holding the pre-enrichment allocation; entry-declared classes
are recorded under `<entry>`. Static-path dispatch resolves the class BEFORE
the bare-name `GLOBAL_IMPL_METHODS` merge.

Repro: `test/01_unit/compiler/95.interp/interpreter/module_qualified_type_registry_spec.spl`
(fixtures `test/helpers/modqual/`), RED on the pre-fix seed with exactly
`unknown static method zero on class Vec3` and `class Config has no field named backend`.
Prevention: `..._prevention_spec.spl` (same dir). Shapes 1, 2 and 4 are
separate defects and are not addressed by this change.
