# 2D/3D Collision + Physics Engine — Production Plan

Source: `doc/01_research/app/game_engine/collision_physics_audit.md`.
Goal: make `engine/physics/` (Gen-2) the one path every game routes
through, close the correctness gaps a real game would hit, delete dead
weight. No new architecture — everything below wires or fixes code that
already exists.

## P0 — Unblock validation (do first, cheap)

1. **Fix the RawHandle regression in 5 specs** — `test/03_system/engine/{physics_stacking,physics_3d_smoke,physics_asteroids,physics_pool,physics_breakout}_spec.spl`
   all call `RawHandle.new(idx, 1)`; replace with the current `RawHandle(...)`
   constructor (match the working pattern already used in
   `physics_3d_collision_spec.spl` and the 9 passing specs). Mechanical,
   ~1 line per file. Re-run each with `bin/simple test <file>` and confirm
   green before touching anything else — these are the only oracle for
   stacking stability and restitution today.
2. **Delete `src/lib/nogc_sync_mut/engine/physics2/`** — 3 files, zero
   external callers, dangling imports to non-existent submodules
   (confirmed by grep across `src/`, `test/`, `doc/`). Nothing depends on
   it; this is deletion, not a merge.
3. **Resolve the `PhysicsWorld2D`/`PhysicsWorld3D` name collision** in
   `physics/__init__.spl` — decide Gen-2 (`world2d.*`/`world3d.*`) is
   canonical, stop `export simple.*` from re-exporting a second
   `PhysicsWorld2D`/`3D`/`PhysicsConfig3D` under the same wildcard. Two
   options, pick the cheaper once `engine3d.spl`'s actual dependency is
   confirmed: (a) rename Gen-1's exports (`LegacyPhysicsWorld2D`) if
   `engine/core/engine.spl`/`engine3d.spl` still need Gen-1 at runtime, or
   (b) migrate `engine.spl`/`engine3d.spl` onto Gen-2 and delete
   `physics/simple/` + its top-level byte-duplicate files
   (`body2d.spl`, `body3d.spl`, `shapes2d.spl`, `shapes3d.spl` are
   `cmp`-identical dupes already — safe to delete outright regardless of
   (a)/(b), they aren't diverging Gen-1 sources, they're literal copies).

## P1 — Dogfood the games onto the engine

4. **Wire `game.breakout` onto `engine/physics/world2d.spl`** — replace
   `_update_ball_walls`/`_update_ball_paddle`/`_update_ball_bricks`
   (`src/app/game.breakout/game.spl:156-199`) with
   `PhysicsWorld2D.add_dynamic_body`/`add_box_collider` for ball/paddle/
   bricks, `collision_layers.spl` to separate brick/paddle/wall layers,
   and `trigger.spl` for brick-destroy-on-contact instead of the manual
   overlap scan. This is the actual "library eats its own game" goal —
   today it's the reverse. Keep the existing golden/replay specs
   (`breakout_event_animation_spec.spl` etc.) as the regression oracle:
   ball trajectory, brick-clear order, and score must stay byte-identical
   after the swap (same fixed-step, same initial velocity/config).
5. **Close rollball's velocity-accessor gap** — add
   `PhysicsWorld3D.set_velocity(node_id, vx, vy, vz)` /
   `.apply_impulse(...)` next to the existing `get_position`/
   `get_velocity`, so `src/app/game.rollball/game.spl:235-273` stops
   reaching into `world.bodies.vel_x[bi]` directly. Small, additive,
   unblocks encapsulation without touching rollball's tuning constants.
6. **Wire CCD into `world2d.spl`/`world3d.spl`'s step loop** — `ccd.spl`'s
   `sweep_circle_vs_circle`/`sweep_circle_vs_line` are implemented but no
   `step()` calls them. Gate it behind `needs_ccd(vx, vy, radius, config)`
   (already exists) so slow bodies pay zero cost. This is the concrete
   fix for "breakout's ball could tunnel through bricks at higher speed" —
   currently safe only because ball speed happens to stay under one
   radius per step.

## P2 — Everything else, lower priority

7. Verify (don't yet fix) the `engine3d.spl:94` `PhysicsConfig3D` type
   mismatch (Gen-2 `PhysicsWorld3D.create()` called with a value typed as
   Gen-1's `physics.simple.types3d.PhysicsConfig3D`) — write one spec that
   constructs `Engine3D` and steps physics; if it's silently structural-
   typed and fine, close as non-issue; if it errors, folds into P0.3(b).
8. GPU backend (`backend_gpu/gpu_solver.spl`, 5 TODOs) — leave stubbed,
   no game needs it; file as a standing TODO, don't implement speculatively.
9. 3D character controller — `character_controller.spl` is 2D-only
   (`GroundInfo` has no `z`); add only if/when a 3D platformer game is
   scoped. Not needed by rollball or breakout today (YAGNI).
10. Fold or delete the third physics-lib copy at
    `src/lib/nogc_async_mut/engine/physics/` (59 files, same Gen-1 shape)
    — separate audit, flagged here, not sized.

## BDD oracles (SSpec, `describe`/`it`, absolute expected values)

Add to `test/03_system/engine/physics_stacking_spec.spl` (once P0.1 lands)
and a new `physics_ccd_spec.spl`:

```
describe "Two-body elastic collision (analytic)":
  it "equal masses, head-on: velocities exchange exactly":
    # m1=m2=1, v1=(2,0), v2=(0,0), e=1.0 -> v1'=(0,0), v2'=(2,0)
    expect(after.v1).to_equal((0.0, 0.0))
    expect(after.v2).to_equal((2.0, 0.0))

describe "Restitution ratio":
  it "e=0.5 drop from h=1.0 rebounds to h=0.25 (v_out/v_in = e)":
    expect(math_abs(v_out / v_in - 0.5) < 1e-6).to_equal(true)

describe "Stack of N boxes at rest":
  it "10 boxes settle with zero drift after 300 steps":
    step_n(world, 300)
    expect(max_position_delta_over_last_50_steps < 1e-4).to_equal(true)

describe "Raycast exact hit points":
  it "ray from origin along +x hits sphere at (r, 0, 0) with normal (1,0,0)":
    val hit = physics_raycast_3d(world, Vec3(0,0,0), Vec3(1,0,0), 100.0)
    expect(hit.point).to_equal(Vec3(x: 1.0, y: 0.0, z: 0.0))

describe "Same-seed determinism":
  it "two independently-stepped worlds with identical config+seed hash identically":
    expect(hash(world_a.snapshot())).to_equal(hash(world_b.snapshot()))

describe "CCD prevents tunneling":
  it "ball at 50x normal breakout speed still bounces off a 1px-thick brick":
    expect(ball.x_after_step).to_be_less_than(brick.right_edge)
```
