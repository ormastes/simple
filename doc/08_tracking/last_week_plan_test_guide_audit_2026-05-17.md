# Last Week Plan/Test/Guide Audit

Date: 2026-05-17

## Scope

Audit target: commits on `main` from the last week, with emphasis on the dense 2026-05-17 work stream:

- Scheduler process isolation.
- SIMD auto-application.
- SimpleOS driver and game-platform work.
- GPU/graphics backend sessions, 2D/3D rendering, Metal/CUDA/Vulkan/WebGPU, and ARM/RISC-V JIT integration.
- Runtime Rust-to-C migration slices.

## Summary

Most large jobs have at least one of plan, design, test, or guide coverage. The weak point is consistency: several jobs have implementation and tests, but no single doc that tells a maintainer which plan applies, which tests are authoritative, and which guide/API surface should be used.

This document is the bridge index for those jobs until each area gets fully integrated into its own canonical guide.

## Coverage Matrix

| Job cluster | Plan/design coverage | Test coverage | Guide/API coverage | Status |
| --- | --- | --- | --- | --- |
| Scheduler process isolation | `doc/05_design/scheduler_process_isolation.md`, `doc/03_plan/sys_test/scheduler_process_isolation.md`, `doc/03_plan/agent_tasks/scheduler_process_isolation.md`, duplication audit | `test/01_unit/os/scheduler_isolation_spec.spl` | Missing canonical user/developer guide | Needs guide + runner-discovery cleanup |
| SIMD auto-application | `doc/03_plan/sys_test/simd_auto_application.md`, `doc/05_design/simd_rollout_plan.md`, SIMD tracking docs | SIMD/runtime/compiler tests exist across `test/runtime`, `test/02_integration/rendering`, compiler tests | Missing concise auto-application guide for optimizer authors | Needs guide |
| SimpleOS driver platform | `doc/03_plan/sys_test/x86_64_desktop_driver_completion.md`, driver feature requests, hardware safety docs | `test/03_system/simpleos/driver_acceleration_perf_spec.spl`, display DMA and driver specs | Driver API docs are fragmented | Needs guide index |
| SimpleOS game compatibility platform | Covered by SimpleOS production and compatibility plans, scattered tests | Wine/process/session/kernel compatibility tests exist | Missing operator guide for platform capabilities and known limits | Needs guide |
| GPU backend sessions and graphics | `doc/04_architecture/compiler/graphics/graphics_3d_session_managed_backend.md`, `doc/05_design/graphics_3d_session_managed_backend.md`, GPU design docs, perf tracking | `test/01_unit/gpu`, `test/05_perf/graphics_2d`, WebGPU/Vulkan/Metal/CUDA smoke/perf tests | `doc/07_guide/api/gpu_api.md` exists | Mostly documented; needs one test-command table |
| ARM/RISC-V JIT and 32/64 GPU targets | ARM/Metal constraint doc, graphics/JIT design notes | JIT hotspot and graphics perf tests exist | Missing architecture compatibility guide for target matrix | Needs guide |
| Runtime Rust-to-C migration | Many small refactor commits, C runtime sources and smoke checks | Mostly covered by existing runtime/compiler checks | Missing migration progress index | Needs tracking index |

## Problems Found

### 1. Scheduler tests are not yet trustworthy enough as a release gate

The scheduler process-isolation test file compiles, and prior commit text says 20 tests passed. However, one recent direct runner invocation reported `0` discovered examples. That means maintainers can mistake a successful runner exit for real coverage.

Required improvement:

- Convert manual `test_*` functions into the repository's discovered spec form, or add a wrapper that makes the existing functions visible to the runner.
- Keep `bin/simple check test/01_unit/os/scheduler_isolation_spec.spl` as syntax coverage only, not behavior coverage.

Canonical commands:

```bash
bin/simple check src/os/kernel/ipc/syscall_scheduler.spl src/os/kernel/scheduler/process_isolation.spl src/os/kernel/scheduler/sched_class_queue.spl src/os/kernel/scheduler/sched_policy_engine.spl test/01_unit/os/scheduler_isolation_spec.spl
bin/simple test test/01_unit/os/scheduler_isolation_spec.spl --mode=interpreter --clean
```

### 2. GPU/graphics work has strong docs, but test entrypoints are scattered

The graphics session work has architecture, design, API docs, unit tests, perf tests, and smoke tests. The gap is discoverability: a maintainer has to know which tests correspond to backend sessions, Qualcomm/ARM target profiles, 2D perf, and 3D session APIs.

Required improvement:

- Add a test-command table to `doc/07_guide/api/gpu_api.md` or a dedicated graphics test guide.
- Separate "hardware required" tests from CPU-only/smoke tests.

Canonical commands:

```bash
bin/simple check src/lib/gc_async_mut/gpu/session src/lib/gc_async_mut/gpu/engine2d src/lib/nogc_sync_mut/jit/jit_arm_mixed.spl
bin/simple test test/01_unit/gpu/graphics_session_spec.spl --mode=interpreter
bin/simple test test/01_unit/gpu/qualcomm_vulkan_target_profile_spec.spl --mode=interpreter --clean
SIMPLE_NO_STUB_FALLBACK=1 bin/simple test test/01_unit/jit/jit_arm_hotspot_opt_spec.spl --mode=interpreter --clean
```

### 3. SIMD auto-application lacks a maintainer-facing guide

SIMD planning and tests exist, but the optimizer author path is not obvious. The missing guide should explain:

- Which patterns are safe for auto-application.
- How scalar fallback is selected.
- How duplication between manual SIMD intrinsics and auto rewrites is prevented.
- Which tests prove semantic parity.

Required improvement:

- Add `doc/07_guide/optimization/simd_auto_application.md`.
- Link it from the SIMD rollout plan.

### 4. Driver and SimpleOS platform docs are fragmented

Driver and OS platform work has many plans and tests, but no single guide index that maps:

- driver class,
- hardware boundary,
- test file,
- performance check,
- known unsupported path.

Required improvement:

- Add a driver/platform guide index under `doc/07_guide/simpleos/`.
- Keep implementation-specific details in design docs; use the guide as the entrypoint.

### 5. Runtime Rust-to-C migration lacks a current tracking index

The Rust-to-C migration was split across many commits. That is good for review, but bad for later audit unless the migration inventory is updated.

Required improvement:

- Update `doc/08_tracking/simpleos/c_to_simple_inventory.md` or add a runtime-C migration index with:
  - migrated symbol groups,
  - remaining Rust-backed externs,
  - required smoke checks.

## Immediate Fixes Added By This Audit

- Created this bridge audit so last-week work has one plan/test/guide coverage map.
- Recorded scheduler duplication/overlap separately in `doc/05_design/scheduler_process_isolation_duplication_analysis.md`.
- Identified scheduler test discovery as the highest-priority documentation/test mismatch.

## Follow-Up Backlog

1. Convert scheduler isolation tests into discovered examples.
2. Add graphics backend test-command table to the GPU API guide.
3. Add SIMD auto-application maintainer guide.
4. Add SimpleOS driver/platform guide index.
5. Update runtime C migration inventory.

## Rule Going Forward

For each feature commit that claims tests passed, the related doc must name:

- the plan/design doc,
- the authoritative test command,
- whether tests are hardware-dependent or CPU-only,
- the user/developer guide entrypoint,
- and any known duplication or integration risk.
