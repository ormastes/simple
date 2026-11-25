# Engine2D BackendProbeResult missing is_hardware/strict_failure_without_fallback (present on 3D counterpart)
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

## Symptom

`test/01_unit/lib/gpu/engine2d/backend_probe_strict_spec.spl` fails all 8
examples:

```
semantic: method `strict_failure_without_fallback` not found on type `BackendProbeResult`
semantic: method `is_hardware` not found on type `BackendProbeResult`
semantic: method 'probe_all_summary' not found on value of type object in nested call context
```

## Root cause

`class BackendProbeResult` is defined at
`src/lib/gc_async_mut/gpu/engine2d/backend_probe.spl:36`, but has neither an
`is_hardware` nor a `strict_failure_without_fallback` method anywhere in that
file (confirmed via grep for `fn is_hardware`/`fn strict_failure_without_fallback`
scoped to the file — no hits).

Repo-wide, both methods **do** exist, but only on the 3D backend-probe
counterpart: `src/lib/gc_async_mut/gpu/engine3d/backend_probe3d.spl` defines
`fn is_hardware` and `fn strict_failure_without_fallback` (presumably on
`BackendProbeResult3D` or a related type there). This strongly suggests the 2D
`BackendProbeResult` was meant to get the same "strict/hardened" API surface as
its 3D sibling (the spec's own name, `backend_probe_strict_spec.spl`, and its
description `"Engine2D strict backend probe diagnostics"`, match the hardening
theme) but the methods were never ported over to the 2D type, or the 2D probe
module was refactored without carrying them along.

The third failure, `method 'probe_all_summary' not found on value of type
object in nested call context`, is a related but distinct symptom (different
error shape — "on value of type object" rather than naming
`BackendProbeResult` directly) for the `"probe summary includes all hardened
backend names"` example; likely the same missing-hardening-API root cause but
not independently confirmed against a specific function definition site in
this triage pass.

## Repro

```
SIMPLE_RUST_SEED_WARNING=0 timeout 25 \
  bin/release/x86_64-unknown-linux-gnu/simple test \
  test/01_unit/lib/gpu/engine2d/backend_probe_strict_spec.spl --no-session-daemon
```

## Fix hypothesis (not attempted — src/** GPU-probe API work, out of test-shard scope)

Port `is_hardware`, `strict_failure_without_fallback`, and whatever backs
`probe_all_summary` from the 3D backend-probe module
(`src/lib/gc_async_mut/gpu/engine3d/backend_probe3d.spl`) onto the 2D
`BackendProbeResult` in `src/lib/gc_async_mut/gpu/engine2d/backend_probe.spl`,
or confirm with the GPU/engine2d owner whether the 2D probe intentionally
diverges from 3D and the spec needs to target a different/newer type instead.

## Affected specs

- `test/01_unit/lib/gpu/engine2d/backend_probe_strict_spec.spl` (8/8 examples
  fail; this is the contested gpu/engine2d area so was left unedited per this
  campaign's ENV-skip guidance, but the root cause above is a genuine,
  well-defined API gap, not an environment/hardware-availability issue)


## Resolution 2026-11-25 — FIXED

### Root cause

Confirmed live on `release/1.0.0` (worktree `C:\wt-p3-probe`, branch
`work/p3-probe-20261125`). The bug had grown beyond the three missing methods
named above: `class BackendProbeResult` in
`src/lib/gc_async_mut/gpu/engine2d/backend_probe.spl` was missing
`is_hardware()`, `summary()`, a `probe_all_summary()` on `BackendProber`, and
a `memory_mb` field, **and** the strict probe emitted un-hardened generic
diagnostics (`<name>_runtime` feature gates, backend-name api strings,
`has_compute=false` on every unavailable probe, no OptiX branch at all), so
the spec's hardened 2D contracts (e.g. `rocm_hip_runtime`,
`opencl_icd_platform`, `optix_2d_raster_unsupported`, `cpu-simd-x86` api
names) could not be met. `strict_failure_without_fallback()` had already been
ported earlier and was passing.

### What was ported / changed (all in `src/lib/gc_async_mut/gpu/engine2d/backend_probe.spl`)

- `BackendProbeResult.is_hardware()` — delegates to the existing
  `helpers_availability.backend_is_hardware()`; cpu/software/cpu_simd lanes
  report false, GPU device backends true.
- `BackendProbeResult.summary()` — `diagnostic_text()` plus
  `;executed=<bool>;memory_mb=<n>`, mirroring the 3D `summary()` pattern and
  the `CpuSimdRuntimeEvidence` `executed=` convention.
- New fields `executed: bool = true` and `memory_mb: i64 = 0` (defaulted, so
  the direct `BackendProbeResult(...)` constructions in `ffi_dispatch.spl`,
  `sffi_dispatch.spl`, and `backend_vulkan_spirv.spl` keep compiling).
- `BackendProber.probe_all_summary()` — mirrors
  `Engine3DBackendProber.probe_all_summary()`: `runtime_evidence selected=…`
  rollup of all 12 hardened backends' summaries plus
  `metal_status=/vulkan_status=/cuda_status=/opencl_status=/opencl_gate=/
  opencl_reason=/cpu_simd_*_status=` fields.
- Hardened per-backend strict diagnostics in `_strict_probe_backend()` with
  2D-specific names (not blind 3D copies): rocm gate `rocm_hip_runtime`;
  cpu_simd api `cpu-simd`, gate `runtime_cpu_features`; arch SIMD lanes
  `cpu-simd-x86`/`-arm`/`-riscv` with gates `x86_sse42_avx2_avx512`/
  `arm_neon_sve`/`riscv_vector_extension`; opencl gate `opencl_icd_platform`
  with an "OpenCL ICD platform evidence" reason; new optix branch reporting
  `optix_2d_raster_unsupported` (ptx, compute-only, no raster/present).
  Unavailable-but-compute-capable APIs (rocm/opencl/optix) now report
  `has_compute=true` with `has_graphics/has_present=false`; the generic
  cuda/vulkan/metal/webgpu path is unchanged.

### Verification evidence

Runtime: pure-Simple self-hosted binary (Simple v1.0.0-rc.1, build-commit
`3cf0911a5873a7a189682d34337043d140c79dd0`), `SIMPLE_LIB=src`, `--mode=interpreter`.

Before (unmodified source): `9 examples, 7 failures` —
`semantic: method 'is_hardware' not found on type 'object'`,
`semantic: method 'probe_all_summary' not found on value of type object in
nested call context`, plus gate/name mismatches
(`expected rocm_runtime to equal rocm_hip_runtime`,
`expected optix_runtime to equal optix_2d_raster_unsupported`,
`expected opencl_runtime to equal opencl_icd_platform`).

After: `test/01_unit/lib/gpu/engine2d/backend_probe_strict_spec.spl` —
`SPEC FILE VERDICT: … outcome=OK declared>=9 executed=9 passed=9 failed=0`
(9 examples, 0 failures; assertions unchanged).

Regression sweep on dependents of the changed class:
`test/01_unit/lib/gpu/engine2d/ffi_dispatch_spec.spl` — 7/7 pass.
`test/01_unit/lib/gpu/engine2d/compute_dispatch_spec.spl` — 5/6 pass; the one
failure (`routes explicit backend requests through strict factory probe
results`: unknown backend returns status `Unavailable`, spec expects
`Failed`) reproduces identically with the unmodified `backend_probe.spl`
(verified via `git stash`), i.e. it is a pre-existing, separate bug and was
not introduced or worsened by this fix.
