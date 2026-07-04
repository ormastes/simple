# Collision/Physics Plan — TLDR

```
P0 fix-the-oracle   → RawHandle.new() → RawHandle() in 5 specs (1-liner each)
                    → delete physics2/ (dead, 0 callers)
                    → un-collide PhysicsWorld2D/3D name clash in __init__.spl
P1 dogfood          → breakout: hand-rolled AABB → world2d.spl + triggers
                    → rollball: add set_velocity/apply_impulse (kill raw SoA poke)
                    → wire ccd.spl into step() (implemented, never called)
P2 later/optional   → verify engine3d.spl config-type mismatch
                    → GPU backend stays stubbed (no caller needs it)
                    → 3D character controller only if a 3D platformer ships
                    → nogc_async_mut/engine/physics/ dup — separate audit
```

Top 3, in order: (1) fix 5 specs + delete `physics2/` — restores the only
oracle for stacking/restitution and removes dead orphaned code in one
pass; (2) wire `game.breakout` onto `engine/physics` — the audit's
headline finding is that the flagship game bypasses the library entirely;
(3) wire `ccd.spl` into the step loop — implemented but dormant, and it's
the concrete fix for ball-tunnels-through-brick at higher speeds.

BDD oracles specified with exact numbers: two-body elastic exchange,
restitution ratio = e, N-box stack zero-drift after 300 steps, raycast
hit point exact, same-seed hash-identical determinism, CCD no-tunnel at
50x speed.

Full doc: `doc/03_plan/app/game_engine/collision_physics_plan.md`
