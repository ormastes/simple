# 2D/3D Collision + Physics Engine — Production Readiness Audit

Scope: `src/lib/nogc_sync_mut/engine/physics/` (canonical) and
`physics2/` (candidate duplicate). Method: module inventory, TODO/stub
grep, live spec runs (`bin/simple test`), cross-reference against the two
shipping games (`src/app/game.rollball`, `src/app/game.breakout`).

## 1. Inventory

`engine/physics/` is one tree with **two generations of implementation
living side by side**, both wired into the same `__init__.spl`:

- **Generation 2 (current, multi-backend)** — top-level `world2d.spl`,
  `world3d.spl` + subdirs `data/` (6 files), `narrowphase/` (3),
  `broadphase/` (2), `graph/` (3: graph_coloring, island_manager,
  sleeping), `solver/` (2: tgs_solver, xpbd_solver), `backend_cpu/` (3:
  scalar/simd solver, simd_broadphase), `backend_gpu/` (2), `integration/`
  (render_sync, ecs_system), `query/` (raycast2d, overlap). Real SoA/AoSoA
  data layout, CPU SIMD + GPU backend selection (`backend.spl`).
- **Generation 1 (legacy, single-backend)** — duplicated in two places:
  `physics/simple/*.spl` (19 files, 3,904 lines) **and** a second, almost
  byte-identical copy of the same 19 files at `physics/` top level
  (`body2d.spl`, `body3d.spl`, `shapes2d.spl`, `shapes3d.spl` are byte-for-
  byte `cmp -s` identical to their `simple/` twins; `collision2d.spl`,
  `contact2d/3d.spl`, `query.spl`, `query3d.spl`, `types.spl`, `types3d.spl`
  differ by 1-2 lines only — a stray `#![allow(...)]` pragma or an FFI→SFFI
  comment edit). `joints.spl` (473 vs `simple/joints.spl` 209) and
  `world3d.spl` (322 vs `simple/world3d.spl` 546) diverge substantially —
  the top-level pair is Gen-2, `simple/`'s is Gen-1's own `PhysicsWorld3D`.

**Consequence:** `physics/__init__.spl` does `export world2d.*`,
`export world3d.*` (Gen-2) **and** `export simple.*` (Gen-1, which itself
re-exports `world.*` / `world3d.*`). That is **two different classes named
`PhysicsWorld2D`** (`world.spl:78` legacy, `world2d.spl:41` Gen-2) and
**two different `PhysicsWorld3D`** (`world3d.spl:38` Gen-2,
`simple/world3d.spl:76` legacy) exported from the same wildcard namespace.
Nobody currently does `use ...physics.*` (all call sites import a specific
submodule), so it isn't tripping today, but it is a live name-collision
landmine in the public surface.

**Both generations are actively used, by different consumers**:
`src/lib/nogc_sync_mut/engine/core/engine3d.spl` (the generic `Engine3D`
used by every game) wires `physics.world3d.{PhysicsWorld3D}` (Gen-2 class)
but imports its config type from `physics.simple.types3d.{PhysicsConfig3D}`
(Gen-1 struct) — two structurally-different `PhysicsConfig3D` definitions
(`physics/config.spl:48` vs `physics/simple/types3d.spl:19`) are used
together at `engine3d.spl:94`. Not confirmed broken (didn't execute), but
worth a targeted spec before relying on `Engine3D`'s built-in physics.
`src/lib/nogc_async_mut/engine/physics/` (59 `.spl` files) is a **third**
copy of the Gen-1 tree, in the async-mutable bucket — out of scope here,
same fold-or-delete question applies there.

**physics2/ verdict — orphaned/broken, not a real duplicate to reconcile.**
`src/lib/nogc_sync_mut/engine/physics2/` has only 3 files
(`__init__.spl`, `joints.spl` 473 lines, `world3d.spl` 304 lines).
`__init__.spl` re-exports ~40 submodules (`config.*`, `backend.*`,
`data.solver_body2d.*`, `narrowphase.collision2d.*`, `broadphase.bvh2d.*`,
`graph.graph_coloring.*`, `solver.tgs_solver.*`, …) **none of which exist
as files inside `physics2/`** — `find` confirms no `config.spl`, no
`data/`, `narrowphase/`, `broadphase/`, `graph/`, `solver/` subdirs.
`world3d.spl:8-12` imports `std.nogc_sync_mut.engine.physics2.config`,
`...physics2.data.solver_body3d`, etc. — none resolve. `grep` across
`src/`, `test/`, `doc/` finds **zero references to `engine.physics2`
anywhere outside the `physics2/` directory itself** — no game, no spec, no
other lib module imports it. `jj`/`git log` shows it was live as recently
as commit `a6a92c7481 fix(physics2): inline TGS solver in PhysicsWorld3D`,
so this is an abandoned rewrite-in-place of Gen-2's `world3d.spl`/
`joints.spl`, left half-migrated (its own files moved/renamed into
`physics/` proper) with dangling imports and no callers. **Recommendation:
delete `physics2/` outright — it is dead weight, not a fork to reconcile.**

## 2. Stub/TODO scan

Whole-tree grep for `TODO|FIXME|pass_dn|unimplemented|not implemented`
across `physics/` (all subdirs) returns exactly **3 hits**, all real and
scoped:

- `backend_gpu/gpu_solver.spl:57,61,65,73,79` — 5 `# TODO: Phase 5` markers,
  CUDA malloc/upload/kernel-launch/download all unimplemented; `pass_dn`
  at line 80. GPU backend is a **stub end to end** — `backend.spl`'s
  `select_backend` presumably never picks it for real work yet.
- `world3d.spl:313` and `world2d.spl:369` — one `pass_dn` each, isolated
  (need line-level read before calling these true gaps; low count either
  way).

No `assert(false)` or empty-body stubs found elsewhere. `character_controller.spl`,
`vehicle.spl` (129/10 fns), `ragdoll.spl` (98/9), `cloth.spl` (137/9),
`destruction.spl` (106/9), `trigger.spl` (274/12), `joints.spl` (473/12, 5
joint types: Distance/Revolute/Prismatic/Spring/Weld) all have real
bodies, no stub markers — but see §5 for a 2D-only gap in
`character_controller.spl`.

## 3. Existing specs — inventory vs live status

14 system specs at `test/03_system/engine/physics_*.spl`. Ran all in
interpreter mode (`bin/simple test <file>`, each <10s except cloth ~10s).

**5 of 14 fail** (`physics_stacking`, `physics_3d_smoke`,
`physics_asteroids`, `physics_pool`, `physics_breakout` — marked `*`
above), all with the identical semantic error: `too many arguments for
class RawHandle constructor`, from a shared test-helper idiom
`NodeId(raw: RawHandle.new(idx, 1))` — `RawHandle.new()` is a deprecated
constructor form no longer accepted; the fix is `RawHandle(...)`. This is
a **test-harness regression, not a physics bug**:
`doc/03_plan/ui/production_readiness_master_plan_2026-07-02.md:223`
records these same specs already fixed ("repaired 4 stale specs: RawHandle
ctor") — they have since regressed, almost certainly via the mass
revert/restore chain visible in `jj log` (`369a3725bb revert: restore
13,174 files mass-deleted by e3e22d19da torn-working-copy commit`, `0c6b4f4679
restore: recover 1245 conflict-deleted source files`). **This blocks
validating stacking stability, asteroids/pool restitution, and the
engine-driven breakout scenario until the 5 files are patched** — cheap,
mechanical, ~1 line each.

The 9 passing specs cover: 3D narrowphase (sphere-sphere, sphere-box,
box-box — exact analytic penetration values), joints (8 examples),
collision layers (5), sleeping (5), XPBD solver (4), contact cache (4),
perf (4), cloth (5, ~10s). `doc/08_tracking/bug/physics_world3d_sphere_collision_not_detected_2026-07-02.md`
documents a real Gen-2 bug (Sphere-Box narrowphase never dispatched,
ball fell through boxes) fixed same-day — already resolved, cited here
only as evidence the Gen-2 engine gets real bug-fix attention.

Directory also has stale mirrors: `test/system/` / `test/unit/` duplicate
`test/03_system/` / `test/01_unit/` — flagged, not investigated further.

## 4. Games vs the physics library — the real finding

**`game.rollball` (`src/app/game.rollball/game.spl`) dogfoods Gen-2
directly**: imports `physics.config.{default_physics_config_3d}` and
`physics.world3d.{PhysicsWorld3D}` (line 38-39), creates
`PhysicsWorld3D.create(config)` (line 311), uses `add_static_body`,
`add_box_collider`, `add_dynamic_body`, `add_sphere_collider`, `step()`,
`get_position()`. **But it also reaches past the public API into raw SoA
internals** — `world.bodies.vel_x[bi]`, `vel_z[bi]`, `pos_z` (lines
235-273) — because `PhysicsWorld3D` has no `set_velocity`/`apply_impulse`/
`apply_force` accessor. That's a real API-surface gap, not a design
choice: the only way to nudge a body's velocity from game code today is to
mutate the solver's internal arrays directly.

**`game.breakout` (`src/app/game.breakout/game.spl`) uses no physics
module at all** — zero `use std.nogc_sync_mut.engine.physics.*` imports
anywhere in `game.spl` or `main.spl`. Ball/paddle/brick collision is 100%
hand-rolled AABB overlap tests: `_update_ball_walls` (line 156),
`_update_ball_paddle` (line 167, manual AABB-vs-AABB with an inline
offset-based bounce angle), `_update_ball_bricks` (line 180, linear scan +
manual AABB overlap). No restitution material, no CCD (ball at ~220 px/s,
7px radius, 16ms step ≈ 3.5px/step — currently safe, but any speed-up
pass would tunnel through bricks with zero CCD), no broadphase (linear
scan over all bricks every frame — fine at 32 bricks, a smell at scale).
**This is the headline finding: the flagship 2D game does not use the 2D
physics library it ships next to.** The engine has CCD (`ccd.spl`, real
`sweep_circle_vs_circle`/`sweep_circle_vs_line` implementations, 301
lines), collision layers, and triggers — none of it reachable from
breakout's code path.

## 5. Gap analysis vs Box2D/Rapier-class expectations

| Capability | Status |
|---|---|
| Stable stacking (N boxes at rest) | Implemented (island/sleeping/BVH) but **untested right now** — spec broken by RawHandle regression (§3) |
| Restitution/friction | Config fields exist; asteroids/pool specs (restitution-shaped) currently broken (§3) |
| CCD for fast bodies | `ccd.spl` fully implemented (sweep circle-circle, circle-line, TOI) — **never called from `world2d.spl`/`world3d.spl` step** — implemented-but-unwired |
| Deterministic fixed-step | Proven — rollball's `fixed_update`/`run_session`; breakout's own hand-rolled loop is separately replay-hash-tested |
| Raycast/shapecast queries | `query3d.spl` real (exact `t`/normal); `query/raycast2d.spl` + `overlap.spl` for Gen-2 2D |
| Trigger events | `trigger.spl` (274/12 fns) implemented; no game consumes it |
| Joint stability | 5 joint types (`joints.spl`); passing spec (8 examples) |
| Character controller ground/slope | **2D-only** (`GroundInfo.ground_normal_x/y`, no `z`) — no 3D variant |
| GPU backend | Stub (§2), 5 explicit TODOs; CPU SIMD/scalar are the only working backends |

## 6. What games actually need (the 20%)

Breakout needs AABB-vs-AABB, circle-vs-AABB, wall bounce, brick removal,
paddle english — **all already exist** in `world2d.spl`/`collision2d.spl`.
Rollball needs dynamic sphere vs static box, gravity, velocity nudge,
ground reset — **exists in Gen-2**, minus the velocity-accessor gap (§4).
Neither needs joints/cloth/ragdoll/vehicle/GPU — that 80% is correctly
optional, not correctly *validated-by-nothing*: trigger/CCD/character_controller
also have zero callers under `src/app/`, so they're unexercised by any
real game today.
