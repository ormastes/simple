# Bug: BackendSessionKind CPU SIMD API Drift

Date: 2026-06-01
Status: open (triaged 2026-06-11)

## Summary

The Engine2D backend-session API has incompatible `BackendSessionKind`
representations across runtime families. The `gc_async_mut` path models it as
an enum with `BackendSessionKind.CpuSimd`, while the `nogc_sync_mut` path models
it as a class with constructor helpers such as `BackendSessionKind.cpu_simd()`.

This surfaced while hardening backend screenshot comparison: importing the
current Engine2D backend stack from a focused comparison spec exposed a compiler
failure instead of producing backend evidence.

## Evidence

- `src/lib/gc_async_mut/gpu/engine2d/backend_session.spl` defines
  `enum BackendSessionKind` with `CpuSimd`.
- `src/lib/gc_async_mut/gpu/engine2d/engine2d_api.spl` references
  `BackendSessionKind.CpuSimd` in `resolve_kind` and `resolved_kind_name`.
- `src/lib/nogc_sync_mut/gpu/engine2d/backend_session.spl` defines
  `class BackendSessionKind` with helper `static fn cpu_simd()`.
- `src/lib/nogc_sync_mut/gpu/engine2d/cpu_simd_session.spl` returns
  `BackendSessionKind.cpu_simd()`.
- Attempting to compile the backend screenshot comparison spec while importing
  the current Engine2D backend stack produced:
  `struct BackendSessionKind has no field named CpuSimd`.

## Impact

- Blocks clean backend-qualified evidence paths for CPU SIMD through Engine2D.
- Risks inconsistent Metal/Vulkan/CUDA/SIMD backend session handling when specs
  or tools import multiple runtime-family layers.
- Makes screenshot comparison specs vulnerable to backend API drift before they
  can verify comparison behavior.

## Expected Fix

- Define one canonical backend-session kind representation for Engine2D backend
  evidence APIs, or add explicit family-local adapters at the MDSOC boundary.
- Ensure `cpu_simd` maps consistently in string parsing, diagnostic names,
  session creation, and backend evidence reports.
- Add a focused spec that proves `cpu_simd` can be resolved without importing a
  conflicting runtime-family representation.

## Verification Targets

- A focused CPU SIMD backend-session spec passes under the current test runner.
- Engine2D backend evidence code can import CPU SIMD session APIs without
  `BackendSessionKind.CpuSimd` field errors.
- Backend screenshot comparison remains decoupled from hardware session drift
  unless running a backend-qualified evidence lane.

## Current-State Recheck: 2026-06-01

The original field-error symptom is not reproducible in the current dirty
worktree under clean targeted checks:

- `SIMPLE_LIB=src src/compiler_rust/target/debug/simple test test/01_unit/lib/gpu/engine2d/backend_session_contract_spec.spl --mode=interpreter --clean`: 3 passed, 0 failed.
- `SIMPLE_LIB=src src/compiler_rust/target/debug/simple test test/01_unit/lib/gpu/engine2d/cpu_simd_session_contract_spec.spl --mode=interpreter --clean`: 3 passed, 0 failed.
- `SIMPLE_LIB=src src/compiler_rust/target/debug/simple check src/lib/gc_async_mut/gpu/engine2d/backend_session.spl`: passed.
- `SIMPLE_LIB=src src/compiler_rust/target/debug/simple check src/lib/nogc_sync_mut/gpu/engine2d/backend_session.spl`: passed.
- `SIMPLE_LIB=src src/compiler_rust/target/debug/simple check src/lib/gc_async_mut/gpu/engine2d/engine2d_api.spl`: passed.

The two runtime-family representations still differ by design shape
(`BackendSessionKind.CpuSimd` enum variant vs `BackendSessionKind.cpu_simd()`
class constructor), so the architecture/design step should still define the
boundary contract. Current implementation work should treat this bug as
monitored rather than actively reproducing.
