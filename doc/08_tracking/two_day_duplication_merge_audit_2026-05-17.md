# Two-Day Duplication Merge Audit

Date: 2026-05-17

## Scope

Audited work on `main` from the last two days plus the current working-copy WIP.

Main clusters:

- GPU/graphics backend sessions, 2D/3D rendering, Metal/CUDA/Vulkan/WebGPU.
- ARM/RISC-V JIT and 32/64 target-profile work.
- Scheduler process isolation and syscall scheduling.
- SIMD auto-application.
- SimpleOS driver/game compatibility platform.
- Runtime Rust-to-C migration slices.
- Current WIP: custom primitive SFFI public API and custom primitive bitfield support.

## Highest-Priority Merge Targets

### 1. GPU Backend Adapter Boilerplate

Files:

- `src/lib/gc_async_mut/gpu/session/backend_cpu_adapter.spl`
- `src/lib/gc_async_mut/gpu/session/backend_cuda_adapter.spl`
- `src/lib/gc_async_mut/gpu/session/backend_metal_adapter.spl`
- `src/lib/gc_async_mut/gpu/session/backend_vulkan_adapter.spl`
- `src/lib/gc_async_mut/gpu/session/backend_webgpu_adapter.spl`

Repeated logic:

- `handle`, `initialized`, `session_mode` state.
- `initialized == false` guards.
- `supports_compute`, `supports_graphics`, `supports_present`.
- `device_info` string assembly.
- command-count validation and init/cleanup shape.

Merge direction:

- Add shared adapter metadata helpers in the session module.
- Keep backend-specific extern calls in each adapter.
- Move common device-info formatting and initialized/command validation into one helper module.

Risk if not merged:

- Backend behavior drifts. CUDA/WebGPU already required consistency fixes after rebase.

### 2. Scheduler Policy Logic Duplicated In Test Harness

Files:

- `src/os/kernel/scheduler/process_isolation.spl`
- `src/os/kernel/scheduler/sched_class_queue.spl`
- `src/os/kernel/scheduler/sched_policy_engine.spl`
- `src/os/kernel/ipc/syscall_scheduler.spl`
- `test/unit/os/scheduler_isolation_spec.spl`

Repeated logic:

- class validation,
- priority bounds,
- preemption ordering,
- starvation threshold/boost,
- CPU affinity routing,
- schedctl op decoding,
- isolation escalation rules.

Merge direction:

- Tests should import production helpers where possible.
- Keep independent scalar/oracle helpers only where the test intentionally validates production logic by comparison.
- Convert the current manual test harness into runner-discovered examples.

Risk if not merged:

- The test can pass against its own duplicated model while production scheduler behavior diverges.

### 3. Custom Primitive Type Metadata

Current WIP files:

- `src/compiler/35.semantics/lint/sffi_custom_primitive.spl`
- `src/compiler/50.mir/custom_primitive_bitfield.spl`

Repeated logic:

- primitive type lists,
- unsigned integer checks,
- bit-width mapping,
- ABI name mapping,
- validity rules for bool/int/float/text.

Merge direction:

- Create one canonical custom-primitive metadata helper for:
  - known primitive check,
  - bit width,
  - signed/unsigned/integer/float/bool/text classification,
  - C/Rust/LLVM ABI names.
- Use that helper from both SFFI validation and bitfield layout.

Risk if not merged:

- SFFI and bitfield rules disagree for the same custom primitive wrapper.

### 4. Fixed-Slot Registry/Field Storage Patterns

Files:

- `src/compiler/35.semantics/lint/sffi_custom_primitive.spl`
- `src/compiler/50.mir/custom_primitive_bitfield.spl`

Repeated logic:

- 16-slot migration registry with explicit `m0..m15`.
- 8-field bitfield layout with explicit `f0..f7`.
- large if/elif setter and getter ladders.

Merge direction:

- If the language/runtime allows arrays/lists for these contexts, replace fixed-slot ladders with indexed storage.
- If fixed slots are required for compiler bootstrap constraints, extract slot get/set helpers and document the bootstrap limitation.

Risk if not merged:

- Any slot-count increase repeats error-prone boilerplate across modules.

### 5. SIMD Scalar Fallback/Oracle Duplication

Files:

- `doc/07_guide/compiler_simd_auto_application.md`
- `test/runtime/simd_text_test.spl`
- `test/runtime/simd_text_fuzz_test.spl`
- rendering SIMD parity tests and perf specs.

Repeated logic:

- scalar fallback behavior,
- feature-gated vector path selection,
- scalar-oracle test implementations.

Merge direction:

- Keep scalar production helpers as the source of truth.
- Allow test-local scalar oracles only when they are intentionally independent.
- Mark those tests as oracle tests in names/comments.

Risk if not merged:

- Manual SIMD intrinsics and auto-vectorized rewrites can grow different semantics.

## Lower-Priority Merge Targets

### Runtime Rust-to-C Migration

The runtime migration is split across many small commits. That is good for review, but the tracking index should merge repeated migration status logic into one inventory:

- migrated symbol group,
- C source file,
- old Rust owner,
- smoke command,
- remaining external dependency.

### SimpleOS Driver/Game Platform

Driver and game-platform docs are currently routed through a new guide index. Remaining duplication risk is mostly in constants and capability policy between:

- kernel driver mechanisms,
- user-space services,
- game/Wine compatibility glue.

## Recommended Merge Order

1. Custom primitive metadata helper, before the WIP grows more SFFI/bitfield rules.
2. Scheduler test harness to production-helper imports and discovered examples.
3. GPU backend adapter shared metadata/validation helpers.
4. SIMD oracle naming and shared scalar helper audit.
5. Runtime migration inventory consolidation.

## Non-Merge Exceptions

Do not merge logic when duplication is intentional for verification:

- independent scalar oracle used to test SIMD/vector code,
- C reference benchmark used to compare Simple runtime behavior,
- hardware smoke tests that intentionally duplicate a minimal call path.

Those cases must be named as `oracle`, `reference`, or `smoke` in the test/doc so they are not mistaken for production duplication.
