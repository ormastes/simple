# PhysicsWorld3D sphere collision not detected (world3d_spec)

Date: 2026-07-02
Status: fixed 2026-07-02 (was pre-existing; NOT caused by the mut-capability sweep)
Severity: P3
Related: doc/03_plan/ui/production_readiness_master_plan_2026-07-02.md (P4 / G4)

## Symptom

`test/unit/lib/engine/physics/physics2/world3d_spec.spl` — "sphere collision
detected" fails (`expected false to equal true`); two spheres placed to
overlap report no contact.

## Provenance

Verified 2026-07-02: the same test fails with the pre-sweep
`physics/simple/contact3d.spl` restored from commit e44293ca, so the
failure predates the mut-capability changes. This is the only remaining
red test in `test/unit/lib/engine/physics/physics2/` (36 pass / 1 fail).

## Root cause + fix

`PhysicsWorld3D.collide_3d` only dispatched Sphere-Sphere and Box-Box; the
Sphere-Box pairing fell through to `has_contact: false`, so spheres fell
through box floors. The narrowphase helper `collide_sphere_aabb_3d` already
existed in `narrowphase/collision3d.spl` but was never called. Fix: wire
both orderings in `collide_3d` (normal flipped for Sphere-then-Box so it
stays a->b for the solver). `physics2` suite now 37/37.
