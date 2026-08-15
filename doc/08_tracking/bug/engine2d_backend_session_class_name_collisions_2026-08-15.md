# engine2d/session cross-module class-name collisions (2026-08-15)

## Summary
The interpreter resolves class members by NAME across co-compiled modules, so
same-named classes in different modules execute one definition's method bodies
against the other's instances — surfacing as `cannot assign field on non-object
value` / `unknown static method` in engine2d specs (e.g.
`test/02_integration/gpu/engine2d_backend_matrix_spec.spl`).

Three parallel definitions of the BackendSession* family existed:
- `src/lib/gc_async_mut/gpu/engine2d/backend_session.spl` (enum Mode/Kind, ComputeError) — LIVE, kept as-is
- `src/lib/nogc_sync_mut/gpu/engine2d/backend_session.spl` (class-style Mode/Kind)
- `src/lib/gc_async_mut/gpu/session/session_types.spl` (+ session_api/perf/frame)

## Fixed (renamed, this change)
- nogc tree: `BackendSessionMode/Kind` → `ComputeSessionMode/Kind`
  (backend_session.spl, cpu_simd_session.spl, cpu_simd_session_contract_spec.spl + mirror)
- gpu/session tree: `BackendSessionHandle/Policy/Error` → `GpuSessionHandle/Policy/Error`;
  `BackendFrame/BackendFrameStats` → `GpuSessionFrame/GpuSessionFrameStats`
  (session_types.spl, session_api.spl, session_perf.spl, session_frame.spl,
  session_frame_contract_spec.spl)

## Still open (not renamed — actively edited by concurrent work)
- `src/lib/gc_async_mut/gpu/engine2d/engine2d_api.spl` defines local
  `enum BackendSessionMode` / `BackendSessionKind` duplicating
  `gc_async_mut/gpu/engine2d/backend_session.spl`'s enums.
- `src/lib/gc_async_mut/gpu/engine2d/web_render_session.spl:23` defines a local
  `enum BackendSessionMode` (third copy).
- `src/lib/nogc_sync_mut/gpu/engine2d/backend_session.spl:224` still defines
  `class BackendSessionError` (internal-only; collides with spec-local mocks in
  `test/*/gpu/graphics_3d_session_managed_backend_spec.spl`).

## Verification (queued behind the Stage-4 bootstrap resource lock)
```
SIMPLE_TIMEOUT_SECONDS=600 bin/simple test test/01_unit/lib/gpu/engine2d/cpu_simd_session_contract_spec.spl
SIMPLE_TIMEOUT_SECONDS=600 bin/simple test test/01_unit/lib/gc_async_mut/gpu/session/session_frame_contract_spec.spl
SIMPLE_TIMEOUT_SECONDS=600 bin/simple test test/02_integration/gpu/engine2d_backend_matrix_spec.spl
```
Status: VERIFIED 2026-08-15 — all three queued specs pass (3/3, 3/3, 4/4; matrix 16/16).
