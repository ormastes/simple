# Collision/Physics Audit — TLDR

`engine/physics/` = two generations wired into one `__init__.spl` (name
collision on `PhysicsWorld2D`/`3D`). `physics2/` = orphaned, imports 40
modules that don't exist inside it, zero external callers — **delete**.

```
physics/__init__.spl
 ├─ export world2d.*/world3d.*  Gen-2 SIMD/GPU/TGS/XPBD → rollball, Engine3D
 └─ export simple.*             Gen-1 legacy, ALSO byte-dup'd at top level
physics2/  ─╳─  imports physics2.config/data/... (never existed) — 0 callers
```

Headline: **breakout uses zero physics-engine code** — hand-rolled AABB in
`game.spl` (lines 156-199). Rollball dogfoods Gen-2 but pokes raw SoA
(`world.bodies.vel_x[bi]`) — no `set_velocity`/`apply_force` accessor.

5 of 14 physics specs currently **fail** (stacking/3d_smoke/asteroids/
pool/breakout) — all same cause: deprecated `RawHandle.new(idx,1)` ctor, a
regression (fixed once per master_plan:223, reverted by the torn-working-
copy restore). One-line fix each, unblocks stacking/CCD-adjacent coverage.

CCD (`ccd.spl`) is fully implemented but **never called** from `step()`.
Character controller is 2D-only. GPU backend is a 5-TODO stub.
Raycast3D/joints/triggers are real and unused by any game.

Full doc: `doc/01_research/app/game_engine/collision_physics_audit.md`
