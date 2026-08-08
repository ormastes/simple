# No non-blocking Vulkan compute submit exists — `rt_vulkan_submit_and_wait_fence` always blocks on `u64::MAX`, so a host-side fence timeout can never fire

**Status:** OPEN
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
