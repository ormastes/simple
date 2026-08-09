# Metal GPU lane: device verification pending — no Metal host in this repo

- **Status:** OPEN (blocked on hardware, not on code)
- **Filed:** 2026-08-09
- **Area:** `src/lib/gc_async_mut/gpu_lane/` (Metal lane), SVM-G / GMB-1
- **Design:** `doc/05_design/app/tools/metal_gpu_lane_and_vulkan_jit_notebook_architecture_2026-08-09.md`
  §5, §9, §11; parent `doc/05_design/runtime/gpu_remote_interpreter_architecture.md`

## What this tracks

Every Metal-lane artifact in this repo is **structurally complete and
host-aware-skip-clean, and UNVERIFIED on real hardware**. This document exists
so that status stays explicit rather than being quietly inferred from green
test runs.

The repo's development and CI hosts are Linux. The Rust runtime's Metal
implementation (`src/compiler_rust/runtime/src/metal_graphics_runtime.rs`, ~35
`rt_metal_*` entry points wrapped through
`src/compiler_rust/compiler/src/interpreter_extern/gpu.rs`) is gated on
`#[cfg(target_os = "macos")]`, so `rt_metal_is_available()` **hard-returns
false** here. This is an OS-build-time property, not a runtime `dlopen` probe
like CUDA's or Vulkan's — there is no "install a driver and it works" fix. A
Metal device path **cannot** execute on this host by construction.

## Affected artifacts

| Artifact | Verified on Linux | Unverified until a Mac runs it |
|---|---|---|
| `src/lib/gc_async_mut/gpu_lane/metal_lane_session.spl` (N2) | probe returns `skip:metal-unavailable-not-macos`; skip-clean | every FFI call sequence: device/queue/buffer/shader/pipeline/encoder lifecycle, timeout + completion-unknown quarantine, shutdown release ordering |
| `src/lib/gc_async_mut/gpu_lane/metal_vm_executor.spl` (N3) | all pure host functions: `build_svmg_arena`, `build_svmg_arena_persisting_data` (both code-length directions), `read_sentinel`, `read_log`, `read_records`, `debug_break_of`; fail-closed `run_source` before `init` | upload → dispatch → wait → readback round trip; that a real readback is `ARENA_TOTAL_SIZE`; that `last_dispatch_sentinel` behaves as the timeout contract assumes |
| `src/lib/gc_async_mut/gpu_lane/svmg_metal_kernel.metal` (N3) | **nothing.** It has never been compiled by any Metal compiler, on any machine. | ALL of it: that it compiles at all under `rt_metal_compile_shader`; every one of the 50 opcodes; DBG-1 save/restore; trap/sentinel values; LOG/RECORD ring writes |

## Specifically NOT claimed

- **Not claimed:** "Metal SVM-G conformance verified." It is not, and cannot be
  here. `test/03_system/gpu_lane/metal_vm_executor_conformance_spec.spl` is
  green on Linux **entirely via its SKIP branch**; its `DEVICE-RAN` branch has
  never executed.
- **Not claimed:** that `svmg_metal_kernel.metal` compiles. There is no
  offline `metal`/`metallib` toolchain on a non-macOS host, which is also why
  the kernel is checked in as MSL **source** rather than a compiled artifact
  (unlike the `.ptx`/`.spv` siblings). A syntax error in it would be invisible
  to every test in this repo. **This is the single highest-risk unknown.**
- **Not claimed:** that the single-buffer code/data co-residency divergence
  (`mem_store_load_byte`, filed as
  `svmg_device_arena_code_coresidency_diverges_from_ref_vm_2026-08-07.md`)
  reproduces on Metal. The conformance spec *predicts* the value 13107201 by
  the same arithmetic that was **observed** on CUDA and Vulkan. If a real Mac
  reports a different value, that is a genuine new Metal finding and must be
  filed — not assimilated into the existing bug.

## How to tell which branch a spec took

The Metal conformance spec is deliberately self-describing, because a spec
that passes either by skipping **or** by matching proves nothing on its own —
its green tick is uninformative. Grep spec output:

```
[metal_vm_executor_conformance] SKIPPED: skip:metal-unavailable-not-macos ...
[metal_vm_executor_conformance] DEVICE-RAN: ...
```

This uses `print`, not `step(...)`: **step text is swallowed on a passing
run**, so a step-only marker is invisible precisely on the green run you are
trying to interpret.

Two further guards keep neither branch vacuous:

- The SKIP branch asserts the **specific** reason string, so a Mac skipping
  for a *different* reason (no device, bad ordinal) does not look identical to
  this host. Proven by sabotage: changing the expected reason yields
  `assert_equal failed: expected skip:SABOTAGE-wrong-reason, got
  skip:metal-unavailable-not-macos` (3 failures).
- The DEVICE-RAN branch asserts a **launch-count floor** (`expect(launches)
  .to_be_greater_than(20)`), so a "device run" that dispatched nothing cannot
  pass. Same technique that caught a fake Vulkan run on P6b.

## Closing this bug

Requires a macOS host with a Metal-capable GPU. On that host:

1. `bin/simple test test/03_system/gpu_lane/metal_vm_executor_conformance_spec.spl`
2. Confirm the output line reads `DEVICE-RAN:`, **not** `SKIPPED:` — a green
   run alone is not evidence.
3. Record the device name (`rt_metal_device_name`), the launch count, and the
   full `Results:` line in this document.
4. Expect the first run to surface MSL **compile** errors
   (`metal-lane-shader-compile-failed` from `MetalLaneSession.init`) before any
   semantic result. Fix those in `svmg_metal_kernel.metal` and re-run.
5. Only then may any Metal conformance claim be made, and it must name the
   machine it was made on.

Until all five steps are done, any statement that the Metal lane "works" is
unsupported.
