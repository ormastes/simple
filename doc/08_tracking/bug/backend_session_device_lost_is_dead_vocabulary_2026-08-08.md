# `BackendSessionError.device_lost` is dead vocabulary (engine2d GPU lane)

**Date:** 2026-08-08
**Status:** OPEN — filed, not fixed (deliberately: there is nothing to hook)
**Severity:** low correctness / medium honesty
**Area:** `src/lib/nogc_sync_mut/gpu/engine2d/`

## Claim

`BackendSessionError` advertises a `device_lost` error class. Nothing in the
tree ever constructs it, and `is_recoverable()` hardcodes `false` for it — so
the vocabulary implies a device-loss recovery story the engine2d layer does not
have.

## Evidence (file:line)

- `src/lib/nogc_sync_mut/gpu/engine2d/backend_session.spl:233-234` — the only
  definition:
  ```
  static fn device_lost(msg: text, sid: i64) -> BackendSessionError:
      BackendSessionError(code: "device_lost", message: msg, session_id: sid)
  ```
- `src/lib/nogc_sync_mut/gpu/engine2d/backend_session.spl:245-255` —
  `is_recoverable()` enumerates `mode_conflict`, `unavailable`,
  `policy_violation` as recoverable and falls through to `false` for everything
  else, including `device_lost`. Every other `BackendSessionError` constructor
  in the class (`mode_conflict:230`, `unavailable:236`, `invalid_handle:239`,
  `policy_violation:242`) has real call sites; `device_lost` has none.
- Repo-wide sweep for a construction site:
  `grep -rn 'BackendSessionError.device_lost\|device_lost(' --include=*.spl src/lib/nogc_sync_mut/ test/`
  returns **only line 233 above**. Every other `device_lost` hit in the tree
  belongs to unrelated subsystems that carry their own independent state —
  `src/lib/gc_async_mut/gpu/browser_engine/webgpu_context.spl:43` (a `bool`
  field on the browser WebGPU context) and
  `src/lib/common/engine/audio/simple_audio_device.spl:84` — neither of which
  routes through `BackendSessionError`.

## Why it is not wired here (the blocking gap)

There is no device-loss *signal* available to hook at this layer. The
session-level externs in this directory return success/failure booleans and
handles with no loss status:

- `rt_vk_queue_submit(queue, cmd) -> bool`, `rt_vk_present(queue, cmd) -> bool`
  (`vulkan_session.spl:40,42`) — a lost `VkDevice` surfaces as
  `VK_ERROR_DEVICE_LOST` from the driver, but the extern collapses every
  non-success to a bare `false`, indistinguishable from a validation error.
- `rt_wgpu_submit(queue, cmd_count) -> text` (`webgpu_session.spl:30`) — returns
  a message string, but no runtime path ever produces a device-lost message,
  and WebGPU's `device.lost` promise is not plumbed to the session at all.
- `rt_cuda_kernel_launch(...) -> text` (`cuda_session.spl:25`) — same shape;
  CUDA's sticky-context-error state (`CUDA_ERROR_CONTEXT_IS_DESTROYED` /
  `CUDA_ERROR_ILLEGAL_ADDRESS`) is not surfaced.

So a genuine construction site would require first widening one of these
runtime boundaries to report loss distinctly. That is a real change to the
native runtime, out of scope for a library-layer hardening pass.

## Explicitly NOT done

No stub or fabricated construction site was added to make the variant look
wired. Per `.claude/rules/code-style.md` ("implement or delete, never a
cover-up") the honest states are (a) wire it to a real signal or (b) record it
as dead vocabulary. This doc is (b).

## Unblock condition

Either of:

1. **Implement.** Widen one runtime boundary to report device loss distinctly
   (e.g. `rt_vk_queue_submit` returning a status code rather than `bool`, so
   `VK_ERROR_DEVICE_LOST` is separable from a validation failure), have the
   session map that to `BackendSessionError.device_lost(...)`, and decide
   `is_recoverable()` deliberately — device loss IS recoverable in Vulkan and
   WebGPU by recreating the device, so the current hardcoded `false` is likely
   wrong once a real path exists.
2. **Delete.** Remove `device_lost` from `BackendSessionError` if the engine2d
   session layer is not going to own device-loss recovery, and let the
   browser-engine `webgpu_context.spl` device-loss state remain the single
   owner.

Related: `doc/08_tracking/bug/chrome_vs_simple_gpu_offload_comparison_2026-08-08.md`
(the sibling-backend-drift audit this was found in).
