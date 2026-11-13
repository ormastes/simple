# Engine lib specs: spec-runner interpreter diverges from `run` (JIT) path

**Status:** fix-implemented-verification-pending (2026-11-07, #7498): shape 3 (same-name type picked last-wins) fixed; engine3d 0/5 -> 2/5. Residuals: spec-side factory mismatch and missing `Transform3D.up()` (see dated note below).
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

Residuals measured on the fixed seed (`engine3d_spec` 0/5 -> 2/5), neither a
registry pick: (a) `class PhysicsConfig3D has no field named backend` x2 —
the spec imports `default_physics_config_3d` from
`physics.simple.types3d` (a 3-field `PhysicsConfig3D`) and hands it to
`physics.world3d.PhysicsWorld3D.create`, whose `config.spl` struct carries
`backend`; the interpreter now reports that mismatch faithfully (owner
decision: which factory the spec/engine should use); (b) `method up not found
on type object (receiver Transform3D)` — `component/camera3d.spl:57` calls
`transform.up()` but `math3d.Transform3D` defines only `forward()`; no
`Transform3D.up` exists in `src/lib` (lib gap, previously masked by the
`Vec3.one()` failure).

## 2026-11-10 triage (lane p3-runner3, row 15): LIVE — fix surface out of lane

Re-checked `test/01_unit/lib/engine/engine3d_spec.spl` with the worktree
seed-smoke binary (bin/simple.exe, v1.0.0-rc.1, `--mode=interpreter`): 0/5,
with shape 2 (`nil is forbidden by the non-optional return contract of
'select_backend'`) x2 and shape 3 (`unknown static method one on class Vec3`)
x3 — i.e. the 2026-11-07 #7498 registry fix (present in this tree's
`src/compiler_rust/.../module_cache.rs`) is NOT effective in this deployed
seed-smoke binary, and shape 2 was never addressed. The doc's residual notes
(factory mismatch, `Transform3D.up()`) are not even reached on this binary.

Fix surface, all out of this lane's scope:
- seed interpreter (`src/compiler_rust/**`, seed-fix lane active): rebuild the
  deployed seed from current source and re-verify shape 3; implement shape 2
  (enum non-optional return marshalling on the spec-runner path).
- `Transform3D.up()` lib gap (`src/lib/common/engine/math3d.spl` — only
  `forward()` exists; `component/camera3d.spl:57` calls `transform.up()`).
- Owner decision: which `PhysicsConfig3D` factory the engine3d spec and
  `PhysicsWorld3D.create` should standardise on (`physics.simple.types3d`
  3-field vs `physics/config.spl` with `backend`).

Per the unblock condition, no spec-side weakening was done.

## 2026-11-13 — P3 runner priority lane (work/p3-runner-lane-20261113, base 80a8116e5e2): lib/spec standardisation landed; shapes 1/2 residuals closed; shape 4 root-caused with minimal repro (seed lane)

Windows seed-smoke binary (`bin/simple.exe`, `Simple v1.0.0-rc.1`,
`--mode=interpreter` route). Shape 3 stays fixed (#7498 effective in this
binary). Landed in this lane (all bounded lib/spec changes, no spec-side
weakening — assertions unchanged):

1. **`Transform3D.up()` lib gap closed** —
   `src/lib/common/engine/math3d.spl`: instance `fn up() -> Vec3` alongside
   `forward()` (`rotation.rotate_vector(Vec3.up()).normalize()`), matching
   the existing call in `component/camera3d.spl:57 view_matrix`.
2. **PhysicsConfig3D factory/world standardisation** — the record's
   "owner decision" resolved to the repo's own convention (see
   `game.rollball/game.spl` and `physics/__init__.spl`): pair the factory
   with the world implementation you import. `physics.world3d` (full) needs
   `physics.config.default_physics_config_3d`; `physics.simple.world3d`
   needs `physics.simple.types3d.default_physics_config_3d`.
   - `test/01_unit/lib/engine/engine3d_spec.spl` and
     `test/01_unit/lib/engine/physics3d_spec.spl` use the simple-world API
     (`step(Seconds)`, 4-arg `add_dynamic_body`) — their
     `PhysicsWorld3D` import now comes from `physics.simple.world3d`
     (was `physics.world3d`, whose `create` reads `config.backend`).
   - `src/lib/nogc_sync_mut/engine/core/engine3d.spl` (Engine3D facade) had
     the same latent mix (full world + simple factory, so `Engine3D.create`
     would die in `PhysicsWorld3D.create`) — its factory import now comes
     from `physics.config`. No external `create_with_config` callers exist.
3. **Serializer text→number parse repaired** —
   `src/lib/nogc_sync_mut/engine/scene/serializer.spl` `_parse_f64`/
   `_parse_i64` relied on `val result: i64 = s` (text→int annotation
   coercion), which the spec-runner interpreter does not honour (see shape-4
   root cause below). Rewritten to the canonical
   `std.common.text.parse_i64` / `s.trim().parse_f64() ?? 0.0`, which also
   actually implements the documented "returns -1/0.0 on invalid" contract.
4. **Impossible render fixtures repaired** — three specs built a scene with
   the camera at z=5/10 in identity rotation (looking along +Z) and the
   mesh at the origin, i.e. BEHIND the camera, then asserted
   `draw_calls > 0`. Proven unsatisfiable under `bin/simple run` too
   (identical program: DRAW_CALLS=0; with the mesh at z=10: DRAW_CALLS=1).
   Mesh placed in front of the camera in `engine3d_spec`,
   `renderer3d_spec`, `renderer3d_bugfix_spec` (assertions unchanged).

**Per-file before → after (this lane, same binary):**

| spec | before | after |
|---|---|---|
| scene_node | shape 1, 9 failing | 12/12 OK |
| serializer | shape 1, 4 failing | 4/4 OK |
| scene_manager | shape 1, 2 failing | 11/11 OK |
| prefab | shape 1, 1 failing | 11/11 OK |
| physics3d | shape 2, ~10 failing | 10/10 OK |
| engine3d | 0/5 | 4/5 |
| renderer3d | 1 failing | 15/16 |
| renderer3d_bugfix | 1 failing | 2/3 |

**Shape 4 root cause — minimal repro (seed lane owns the fix).** The
spec-runner interpreter ignores explicit local type annotations; the RHS
type wins:

```simple
describe "Annot":
    it "annotated local from f64 literal":
        var arr: [i64] = [10, 20, 30]
        var i: i64 = 0.0
        expect(arr[i]).to_equal(10)
```

- `bin/simple test` → `semantic: cannot index array with type 'f64'` (both
  `var i: i64 = 0.0` and `val j: i64 = w - 3.0` mistype as f64).
- `bin/simple run` (same code as a `fn main`) → prints fine; annotation is
  honoured and converts.

This is the same defect that kills the renderer rasterizer
(`renderer3d.spl _rasterize_triangle_3d`, `val idx = py * self.width + px`
→ `self.depth[idx]` at fused :269:21): `py/px` derive from
`var ix0: i64 = min_x` (f64 RHS), so the interpreter types the index f64.
A lib-side `val idx: i64 = ...` pin was tried and rejected by the same
semantic pass (still f64) — the fix belongs in the seed interpreter's
local binding typing, not in renderer hot-loop workarounds. The three
remaining RED examples (engine3d render, renderer3d, renderer3d_bugfix)
all bottom out here; they previously failed EARLIER (behind-camera
assertion) which masked the semantic defect until the fixture was repaired.

Verification: canary `test/02_integration/app/context_log_modes_spec.spl`
4/4 after the changes. Non-record engine-dir rows untouched by this lane
(`signal_spec` unresolved-module and `units_spec` Seconds-method gaps are
pre-existing, separate subjects).
