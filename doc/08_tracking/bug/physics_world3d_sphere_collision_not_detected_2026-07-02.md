# PhysicsWorld3D sphere collision not detected (world3d_spec)

Date: 2026-07-02
Status: open (pre-existing; verified NOT caused by the 2026-07-02 mut-capability sweep)
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

Blocks G4 (3D game lane) — sphere-sphere narrowphase in the 3D world needs
a fix before a playable 3D game gate can pass.
