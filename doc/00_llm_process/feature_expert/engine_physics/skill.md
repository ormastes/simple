# Engine Physics (2D/3D) Feature Expert

## Role

Own feature-specific process knowledge for the active physics engine:
`PhysicsWorld2D` (broadphase BVH + bruteforce, collision filtering, sensor
triggers) and `PhysicsWorld3D` (full 3-axis contact-constraint solving,
buffered Begin/Stay/End contact events). Part of the unified 2D/3D engine
hardening — physics items in the phased plan below.

## Pipeline Links

- Plan: [doc/03_plan/ui/unified_2d_engine/web_wm_gpu_3d_review_2026-07-20.md](../../../../doc/03_plan/ui/unified_2d_engine/web_wm_gpu_3d_review_2026-07-20.md)
  (phases 0-7, 10-item slice — item covering [C29] and the CollisionMatrix
  wiring)
- [verify skill](../../../../.claude/skills/verify/SKILL.md)

## Feature Links

- 2D world (`4c9697fa5d4`):
  [src/lib/nogc_sync_mut/engine/physics/world2d.spl](../../../../src/lib/nogc_sync_mut/engine/physics/world2d.spl)
  (`PhysicsWorld2D`) — new `collision_matrix: CollisionMatrix` field
  (defaults `CollisionMatrix.all_collide()`, from
  `collision_layers.spl`, pre-existing), new API
  `set_collider_filter(node_id, filter)`, `set_trigger(node_id, is_trigger)`,
  `contact_count()`, `get_trigger_events() -> [TriggerContactEvent]`.
  `detect_contacts_bvh`/`detect_contacts_bruteforce` both reject a pair via
  `collision_matrix.should_collide(ca.filter, cb.filter)` BEFORE
  narrowphase, and route `is_sensor` pairs to `trigger_events` instead of
  the constraint solver.
- `Collider2D` (narrowphase/shapes2d.spl) gained a `filter: CollisionFilter`
  field — both static constructors (`circle`, `box_shape`) default it to
  `CollisionFilter.all()`.
- Spec: `test/01_unit/lib/engine/physics/physics2/world2d_filter_trigger_spec.spl`
  (4/4) + probe `probe_world2d_filter_trigger.spl` (13/13).
- 3D world (`fd8e2e4b02a`):
  [src/lib/nogc_sync_mut/engine/physics/world3d.spl](../../../../src/lib/nogc_sync_mut/engine/physics/world3d.spl)
  (`PhysicsWorld3D`) — full 3-axis impulse solver: `vec3_cross`,
  `contact_velocity_3d(idx, rx, ry, rz)`, `angular_term_3d(idx, r, d)`,
  `solve_tangent_3d(...)` applied for BOTH tangent directions, 3-axis
  angular impulses on all 3 body axes, `events() -> [ContactEvent3D]`.
- [src/lib/nogc_sync_mut/engine/physics/data/constraint3d.spl](../../../../src/lib/nogc_sync_mut/engine/physics/data/constraint3d.spl)
  (new) — `ContactConstraint3DSoA`: xyz normal/point + auto-derived
  orthonormal tangent1/tangent2 basis + 3 accumulated clamped lambdas
  (normal, tangent1, tangent2), structure-of-arrays.
- [src/lib/nogc_sync_mut/engine/physics/events3d.spl](../../../../src/lib/nogc_sync_mut/engine/physics/events3d.spl)
  (new) — `ContactPairTracker3D.diff(body_a, body_b, n) ->
  [ContactEvent3D]`: `CONTACT_PHASE_BEGIN/STAY/END`, pair-identity keyed
  (`pair_key`, lo/hi normalized), set-diffed once per fixed step against
  the previous step's pair set.
- Spec: `test/01_unit/lib/engine/physics/physics2/world3d_contact3d_spec.spl`
  (4/4) + probe `probe_world3d_contact3d.spl` (13/13).

## Gotchas

- **STALE Gen-1 code exists in parallel — do not edit it by mistake.**
  [src/lib/nogc_sync_mut/engine/physics/simple/](../../../../src/lib/nogc_sync_mut/engine/physics/simple/)
  (`world.spl`, `world3d.spl`, `body2d.spl`, `body3d.spl`, `collision2d.spl`,
  `collision3d.spl`, etc.) is an OLDER, separate physics stack, not the
  active one. The maintained world is the TOP-LEVEL
  `src/lib/nogc_sync_mut/engine/physics/world2d.spl` /
  `world3d.spl` (SoA data, BVH broadphase, `CollisionMatrix`). Confirm the
  path before touching anything under `physics/simple/`.
- **`[C29]` fixed by `fd8e2e4b02a`**: before this change, `PhysicsWorld3D`'s
  solver only read/wrote `ang_vel_z`/`inv_inertia_z` — a 2D-shaped solver
  bolted onto 3D data — so z-axis linear/angular impulses were silently
  dropped for any contact not axis-aligned in the XY plane (the world was
  "3D" in name only). Any future edit to the 3D solver must verify all
  three axes (x/y/z) are threaded through impulse application end to end,
  not just present in the struct fields.
- **Default behavior is byte-identical.** `CollisionMatrix.all_collide()` +
  `CollisionFilter.all()` were chosen so this landing is additive/
  non-breaking for every existing physics2d caller — a regression here
  would show up as EVERY existing caller's contact set changing, which is
  the fast way to notice a `should_collide` wiring mistake.
- **Sensor/trigger contacts never reach the constraint solver.** The
  `ca.is_sensor or cb.is_sensor` check happens BEFORE `self.constraints.add`
  in both the BVH and bruteforce paths — a sensor pair only ever produces a
  `TriggerContactEvent` (2D) / is excluded from the impulse solve. A
  collider being a sensor says nothing about the other collider's
  mass/kinematic-ness — that's an orthogonal check (already present,
  `inv_mass == 0.0` on both sides skips the pair entirely).
- **3D contact events are step-buffered, never mid-solve callbacks.**
  `ContactPairTracker3D.diff` runs once per fixed step, after
  `detect_contacts()`, comparing the current step's deduped pair set
  against the previous step's — consume via `world.events()` after
  `step()` returns.
- **`ContactConstraint3DSoA` has no persistent-manifold/warm-start yet**
  (explicitly ponytail-flagged in-file) — cleared every substep by
  `detect_contacts()`. `feature_id_a`/`feature_id_b` are carried through so
  a later tranche can add cross-step contact matching without a layout
  change.

## Open Bugs

None filed by either commit (`4c9697fa5d4`, `fd8e2e4b02a`) — both landed
with green specs/probes and no new `doc/08_tracking/bug/` entries. The
solver's 2D-shaped-3D-data class of bug ([C29]) is the one this feature
FIXED, not one it introduced.

## Update Rule

After research, requirements, architecture, design, implementation,
verification, or release work changes this feature area, add or refresh
links here BEFORE committing, so the next agent starts from the current
project state.

Template: `.spipe/spipe/doc/00_llm_process/template/feature_skill.md`
