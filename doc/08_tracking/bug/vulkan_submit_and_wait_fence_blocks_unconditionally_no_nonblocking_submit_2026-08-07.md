# No non-blocking Vulkan compute submit exists — `rt_vulkan_submit_and_wait_fence` always blocks on `u64::MAX`, so a host-side fence timeout can never fire

**Status:** RESOLVED (2026-08-20) — verified on a live NVIDIA RTX A6000, see
"Resolution" at the end of this file. Not committed/pushed by the fixing
session; the changes are in the working tree.
**Found:** 2026-08-07
**Component:** `src/compiler_rust/runtime/src/vulkan/device.rs:1047`
(`Device::submit_compute_command_with_fence`) and its `.spl` caller chain
`rt_vulkan_submit_and_wait_fence` → `vulkan_sffi_submit_and_wait_fence`
(`src/lib/nogc_sync_mut/gpu/engine2d/sffi_vulkan.spl:65,450`).
**Attribution:** measured on the Rust bootstrap seed (`bin/simple` prints the
seed banner), live NVIDIA TITAN RTX / RTX A6000 Vulkan 1.4 hosts.
**Discovered while implementing:** Task C1,
`src/lib/gc_async_mut/gpu_lane/vulkan_lane_session.spl`
(`VulkanLaneSession.dispatch_once`), design doc
`doc/05_design/runtime/gpu_remote_interpreter_architecture.md` section 6.1
step 5 ("One `vkCmdDispatch` per test; fence with `GPU_LANE_TIMEOUT_MS`; on
timeout or `VK_ERROR_DEVICE_LOST` force sentinel `0xDEAD0000`").

## What was found

The Vulkan SFFI surface exposed to Simple code has exactly two compute
submission primitives: `rt_vulkan_submit_and_wait` and
`rt_vulkan_submit_and_wait_fence`. Both names are accurate: neither is a
"submit only, return immediately with a pending fence" primitive.
`rt_vulkan_submit_and_wait_fence`'s Rust implementation
(`vulkan_graphics_runtime_compute.rs:631` →
`Device::submit_compute_command_with_fence`, `vulkan/device.rs:1047-1077`)
does:

```rust
let submit_result = unsafe { self.handle().queue_submit(*queue, &[submit_info], fence.handle()) };
...
if let Err(e) = fence.wait(u64::MAX) {   // <-- blocks here, unconditionally
    return Err(FencedSubmitError::CompletionUnknown(e));
}
...
Ok(())
```

`Fence::wait` (`vulkan/sync.rs:44`) calls `vkWaitForFences(..., true,
timeout_ns)` with `timeout_ns = u64::MAX` — i.e. wait forever. So by the time
`rt_vulkan_submit_and_wait_fence` returns a fence handle to Simple code at
all, the GPU work is **already complete**. A subsequent, separate
`rt_vulkan_wait_fence(fence, timeout_ns)` call from `.spl` (which does honor
its `timeout_ns` argument correctly, via a plain `vkWaitForFences`) is
therefore always polling an **already-signaled** fence — it can never
observe a timeout, no matter how small the caller's `timeout_ns` or how long
the dispatched shader genuinely runs.

## How this was diagnosed (not guessed)

Built `VulkanLaneSession.dispatch_once` (design doc §6.1 step 5 pattern:
submit, get a fence handle, then wait on it with the caller's own budget) and
a test that submits a genuinely long-running, non-optimizable single-thread
shader under an intentionally tiny host timeout budget:

1. First attempt: a compile-time-constant arithmetic-series accumulator loop
   (500,000,000 iterations) with `timeout_ms = 0`. Failed to trigger a
   timeout — turned out to be a **different**, more mundane problem (the
   loop is closed-form-reducible by the shader compiler, so it likely
   executed in native time regardless of the stated iteration count) —
   filed as a test-design mistake, not this bug, and fixed by switching to a
   genuinely non-foldable workload.
2. Second attempt: `test/fixtures/gpu_lane/vulkan_bounded_long_loop.spv`, a
   hand-assembled (`spirv-as`/`spirv-val`-clean) single-thread **xorshift**
   loop whose seed AND iteration count are both read from the arena buffer
   at shader **runtime** (not compile-time constants), so the SPIR-V
   compiler cannot constant-fold, strength-reduce, or unroll it away — a
   strictly serial RAW dependency chain. Ran it with 5,000,000 iterations
   (estimated ~24 cycles/iteration dependency latency × 5M ≈ well over 50ms
   of real GPU time on either device) under `timeout_ms = 1`.
3. Still returned success (`dispatch_result == ""`, no timeout) —
   confirming the delay is not in the shader's actual execution time but in
   `submit_and_wait_fence` having already fully waited before the
   `.spl`-level timeout logic even runs.
4. Read `Device::submit_compute_command_with_fence` and found the
   `fence.wait(u64::MAX)` call directly in the submit path, confirming the
   mechanism.

## Impact

The GMB-1 Vulkan lane's host watchdog contract (design doc §3.3 / §6.1 step
5 / §7 `GPU_LANE_TIMEOUT_MS`) — "fence with `GPU_LANE_TIMEOUT_MS`; on timeout
or `VK_ERROR_DEVICE_LOST` force sentinel `0xDEAD0000`" — **cannot currently
be implemented against the exposed Vulkan SFFI surface**, in pure Simple or
otherwise, because there is no way to obtain a pending (not-yet-complete)
fence from Simple code at all. Every available submit path blocks
unconditionally inside the Rust runtime first. This blocks the "real"
timeout half of Task C1 (a device-lost/hang test lane can never be bounded
by a host watchdog through this surface) and will block the corresponding
CUDA-side host watchdog behavior if the CUDA SFFI surface has the same
shape (not checked here — separate task).

`VulkanLaneSession.dispatch_once`'s non-completion branch (force
`VULKAN_LANE_TIMEOUT_SENTINEL`, quarantine dependencies, set
`completion_unknown`/`release_pending`) is implemented correctly per design
and is reachable in principle (it only depends on
`vulkan_sffi_wait_fence` returning false), but is **structurally
unreachable in practice** through `dispatch_once`'s current submit call,
since that call already fully waited by the time the branch's condition is
evaluated.

## Suggested fix (not implemented — needs a Rust change, out of scope for the pure-Simple C1 task)

Add a genuinely non-blocking submit primitive, e.g.
`rt_vulkan_submit_no_wait(cmd) -> fence_handle` that calls
`self.handle().queue_submit(...)` and returns the fence handle immediately
(no `fence.wait(...)` call at all), leaving the existing
`rt_vulkan_wait_fence(fence, timeout_ns)` as the sole place a timeout is
ever applied. `VulkanLaneSession.dispatch_once` would then call the new
non-blocking submit instead of `vulkan_sffi_submit_and_wait_fence`, and the
existing timeout-branch code needs no other change.

## Reproduce

```
SIMPLE_TIMEOUT_SECONDS=0 SIMPLE_RUST_SEED_WARNING=0 bin/simple test \
  test/02_integration/gpu_lane/vulkan_lane_session_spec.spl --no-cache --no-cover-check
```

Second example ("should force the GMB-1 timeout sentinel under a genuinely
tight fence timeout, without hanging") fails:
```
expected 'vulkan-lane-fence-timeout' to equal ''  # (or matcher-specific rendering)
```
i.e. `dispatch_once` legitimately returns `""` (no timeout observed) even
under `timeout_ms = 1` against a shader that provably takes tens of
milliseconds of real GPU time.

## Resolution (2026-08-20) — fixed and verified on real hardware

Fixed essentially as suggested above, plus three defects found only by running
on a device.

**What existed already, and why it never worked.** A committed
`rt_vulkan_submit_no_wait` and `Device::submit_compute_command_no_wait` were
already in the tree — but the extern was **registered nowhere**, so it was
unreachable from Simple code, and its runtime body allocated a fence handle,
moved the `Fence` into the quarantine, then ran a no-op placeholder and
returned the handle. Since `rt_vulkan_wait_fence` only looked in
`state.fences`, that handle could never be resolved. The `Fence` cannot simply
also live in `state.fences`: it owns its `vk::Fence` and destroys it on drop,
so two owning copies would double-destroy.

**Changes**
- `runtime/src/vulkan_graphics_runtime_core.rs` — `QuarantinedComputeSubmission.wait_handle`;
  `State::fence_by_handle()` (resolves plain fences *and* pending quarantined
  ones) and `release_quarantined_wait_handle()`.
- `runtime/src/vulkan_graphics_runtime_compute.rs` — the no-wait success path
  now records `wait_handle`; placeholder removed.
- `runtime/src/vulkan_graphics_runtime_sync.rs` — `wait_fence` resolves via
  `fence_by_handle`; `destroy_fence` revokes a quarantined handle instead of
  destroying a fence the GPU may still be signalling.
- Registered the extern in all four tables (`common/src/runtime_symbols.rs`,
  `codegen/runtime_sffi.rs`, `interpreter_extern/vulkan.rs`,
  `interpreter_extern/mod.rs`) and implemented the interpreter-path
  `rt_vulkan_submit_no_wait_fn` in `interpreter_extern/gpu.rs`.
- `src/lib/nogc_sync_mut/gpu/engine2d/sffi_vulkan.spl` — extern +
  `vulkan_sffi_submit_no_wait`.
- `src/lib/gc_async_mut/gpu_lane/vulkan_lane_session.spl` —
  `dispatch_once` submits non-blocking; all downstream branches unchanged.

The blocking `submit_and_wait_fence` path is untouched and remains the default
for every other caller.

**Defect found only on hardware (would not have surfaced by inspection).**
The first device run got as far as `vulkan-lane-fence-timeout` correctly, then
failed at teardown with `vulkan-lane-quarantine-fence-release-pending` and an
unshutdownable session. Cause: `vulkan_sffi_reap_dependency_quarantine()` calls
`rt_vulkan_wait_idle`, which drains the quarantine and destroys the fence; the
session's subsequent `destroy_fence(pending_fence)` then found nothing and
reported failure, which the session reads as "still pending" — permanently.
Fence release is now **idempotent**: a handle already released by a
device-idle reap reports success (`retired_fence_handles` in the runtime,
`retired_fences` in the interpreter path). Both backends had this bug.

**Two pre-existing blockers cleared** (the `vulkan` feature did not compile at
all, so none of this was buildable): four E0252 duplicate-import errors from
stray unconditional `use` lines in `vulkan_graphics_runtime_{compute,shader}.rs`,
and an E0004 non-exhaustive match in `codegen/vulkan/spirv_instructions.rs`
missing `MirInst::AggregateCopy` (now a clean codegen error, matching the
sibling arms, not a `todo!()`).

**Evidence — NVIDIA RTX A6000, Vulkan 1.4.312, driver NVIDIA:**
```
DISPATCH: 'vulkan-lane-fence-timeout'
  sentinel=3735879680            # 0xDEAD0000
  completion_unknown=true  release_pending=true
RETRY:    'vulkan-lane-quarantine-retry-complete'
  completion_unknown=false release_pending=false pending_fence=0
SHUTDOWN: ''
```
`test/02_integration/gpu_lane/vulkan_lane_session_spec.spl` — **2/2 passed, 4
consecutive runs** (both the arena round-trip and this timeout example).
Device-free contract spec `test/01_unit/gpu/vulkan_submit_no_wait_backed_spec.spl`
2/2. `cargo check --release --bin simple` clean with and without
`--features vulkan`. `check-unbacked-extern-ratchet.shs`: `PASS — 1466 …, 0 new,
0 stale`.

**Caveat — investigated, and it was NOT a Vulkan problem.** `simple run`
reports `skip:vulkan-physical-device-required` on this host while `simple test`
drives both GPUs. Root cause: the `run` path corrupts extern-returned `text`
(`device_type` genuinely returns `"discrete"`, but the consumer observes
`len() == -1`), so the final `device_type != "discrete"` check in `probe()`
wrongly fires. Loader, ICD, enumeration (3 devices), and device selection all
succeed on that path. Because the established spec idiom asserts
`assert_true(probe_result.starts_with("skip:"))`, that false skip is recorded
as a PASS with `skipped=0`. Filed separately as
`doc/08_tracking/bug/run_path_extern_text_corruption_causes_false_gpu_skip_2026-08-20.md`.
All evidence in this record is from the `test` path, which is unaffected.
