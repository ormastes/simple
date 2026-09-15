# Vec3.transform_direction method dispatch fails at runtime

Date: 2026-09-15
Discovered by: test-wave agent B (spec triage)

## Affected specs (left RED)
- test/01_unit/lib/nogc_sync_mut/gpu_mesh3d_spec.spl
- test/01_unit/lib/nogc_sync_mut/graph_ir3d_spec.spl

## Observed
src/lib/nogc_sync_mut/gpu/renderer3d.spl:185-187 calls
`model_mat.transform_direction(...)`; runtime raises `method
transform_direction not found on type Vec3` although the method is defined
at src/lib/common/engine/math3d.spl:272.

## Unblock condition
Fix method dispatch for transform_direction on Vec3 (or the receiver typing
in renderer3d), then re-run both specs.
