# Engine2D Vulkan framebuffer cannot reach the real swapchain registry

Date: 2026-08-11
Status: PARTIAL — CANONICAL BUFFER-TO-SWAPCHAIN PRIMITIVE IMPLEMENTED; ENGINE2D MIGRATION AND LIVE PROOF OPEN

## Defect

Engine2D's production Vulkan backend allocates and dispatches its storage
framebuffer through the legacy `rt_vulkan_*` runtime state in
`vulkan_graphics_runtime_core.rs`. Real window, presentation-device, and
swapchain lifecycle is implemented separately by the canonical `rt_vk_*`
SFFI under `value/gpu_vulkan/vulkan_sffi`, using `DEVICE_REGISTRY`,
`WINDOW_SURFACES`, and `SWAPCHAIN_REGISTRY`.

No API transfers Engine2D's device buffer into a canonical acquired swapchain
image. Calling either existing present function cannot fix this: the legacy
swapchain registry has no surface creation caller, while canonical
`rt_vk_swapchain_present` would present an image that Engine2D never wrote.
Host-cache refresh or SDL pixel upload requires device-to-host readback and is
not GPU device presentation.

## 2026-08-11 implementation update

The canonical registry now exposes
`rt_vk_swapchain_copy_buffer_and_present`. It validates that the buffer and
swapchain share a device, checks the packed ARGB byte extent and BGRA-compatible
surface format, transitions an acquired image to `TRANSFER_DST_OPTIMAL`, copies
the device buffer, transitions to `PRESENT_SRC_KHR`, and queue-presents without
host readback. Swapchain images now request `TRANSFER_DST` usage and track
initialization across presentations. Semaphore-free acquisition uses a real
fence and waits for known completion instead of passing both synchronization
handles as null.

The guarded `rt_vk_engine2d_adopt_device` bridge now makes the legacy Engine2D
registry borrow the canonical presentation-capable device before any legacy
resources exist. `rt_vk_swapchain_copy_engine2d_buffer_and_present` then borrows
the live Engine2D buffer directly and invokes the device-local presentation
primitive. Adoption fails closed once any legacy device resource exists.

`VulkanEngine2dPresenter` now owns create/adopt/acquire/copy/present/destroy as
one lifecycle, and the Vulkan showcase host creates it before Engine2D and
presents the exact `backend_handle` returned by strict DrawIR execution. The
structural bridge contract passes 4/4.

This is still not throughput evidence: no Xvfb/physical-surface live
presentation has passed. The current showcase verification path also performs
an explicit correctness readback before presentation, so it must not be used as
a zero-readback timed-frame result. A timed presenter lane must render without
that strict readback and verify its checksum outside the measured frames.

## Required implementation

1. Use one presentation-capable Vulkan device/registry for Engine2D compute,
   window surface, and swapchain resources.
2. Acquire with a real semaphore/fence and known completion.
3. Transition the acquired image to transfer-destination or render-target
   layout, copy/compose the Engine2D framebuffer entirely on-device, transition
   to `PRESENT_SRC_KHR`, and queue-present with the matching wait semaphore.
4. Track initialization per swapchain image. Partial damage is legal only
   after that image has retained valid prior content; otherwise seed it fully.
5. Publish `present_mode=swapchain` and `device_present=true` only after the
   native present succeeds. Record exact transfer/dispatch/submission/fence
   counts and prove zero device-to-host bytes when readback was not requested.

## Acceptance

- Xvfb or a physical display live test creates window + surface +
  presentation-compatible device + swapchain and shows a deterministic frame.
- Exact checksum is established by an explicit verification readback outside
  timed frames; timed frames require zero readback.
- Idle retained switching reports zero raster/transfer work except an honestly
  measured reacquire/re-present operation.
- 7680x4320 dynamic and retained rows report p50/p95, RSS/device memory,
  fallback=false, completion known, and exact presentation receipts.

## Triage addendum (2026-11-11, lane ne7)

**Status: PARTIAL — remains OPEN; live presentation proof still outstanding
(matches 2026-10-27 v3 lane02 freeze: keep_open, no admission without live
checksum evidence).**

Current tip state (branch work/p3-ne7-20261111):

- The presentation ownership moved again: the engine now exposes
  `present_window_device()` (`src/lib/gc_async_mut/gpu/engine2d/engine.spl:3603`),
  forwarding to the strict-submission Vulkan owner
  (`src/lib/gc_async_mut/gpu/engine2d/backend_vulkan.spl`), with
  compositor-side fail-closed scalar gates in
  `src/os/compositor/vulkan_present_damage_gate.spl` (rect validation,
  overlap rejection, receipt byte accounting).
- The symbols this bug's 2026-08-11 update named
  (`VulkanEngine2dPresenter`, `rt_vk_swapchain_copy_engine2d_buffer_and_present`)
  no longer exist in `src/` — `VulkanEngine2dPresenter` survives only in a
  comment in `vulkan_present_damage_gate.spl:3`.
- No live presentation evidence exists on disk: no presentation receipts,
  timed-frame checksums, or 8K p50/p95 rows anywhere under `build/`, `var/`,
  or `doc/08_tracking/` newer than this bug. The sibling bug
  `engine2d_vulkan_window_8k_gate_is_device_present_proxy_2026-08-31`
  (v3 freeze) records that the 8K window gate passes via an Xvfb
  device-present PROXY, not real window rendering — consistent with live
  proof still being open.

Not attempted here: the acceptance criteria (Xvfb/physical surface live
presentation, verification readback outside timed frames, zero-readback
timed frames, 7680x4320 p50/p95 + RSS + presentation receipts) require a
Linux display environment and are out of scope for a Windows P3 lane.

## 2026-11-12 source trace (vulkan-mac lane, work/fix-vulkan-mac-20261112)

Re-traced the presentation path at `7a06b4aafd5` to establish what is and is
not still disconnected:

- `Engine2D.present_window_device()` (`engine.spl:3603`) forwards to the
  strict-submission Vulkan owner and records the backend write-back.
- `VulkanBackend._present_device` (`backend_vulkan.spl:1989`) refuses
  fail-closed without a live `presentation_swapchain`/device framebuffer,
  flushes pending compute, then copies the Engine2D device framebuffer into
  the acquired swapchain image on-device via
  `vulkan_sffi_present_buffer{,_regions}` — no host readback
  (`present_readback_bytes = 0` is recorded before the call).
- The SFFI surface (`src/lib/nogc_sync_mut/gpu/engine2d/sffi_vulkan.spl:1349`)
  delegates to `rt_vulkan_present_buffer{,_regions}` plus byte/rect receipts
  (`rt_vulkan_last_present_copy_bytes/rects`), i.e. the one device/swapchain
  owner allocated by `rt_vulkan_init_window_present`.
- Compositor-side gates exist on both ends: `vulkan_present_damage_gate.spl`
  (rect validation, overlap rejection, receipt byte accounting) and
  `host_compositor_core.spl` validates `latest_vulkan_frame_receipt()`
  freshness/content (`exact-vulkan-present-receipt`,
  `stale-vulkan-present-receipt` refusal).

Conclusion: at the Simple-source layer the buffer-to-swapchain transfer is a
single-registry, device-local path with receipt accounting; the disconnect
named in the 2026-08-11 defect (no API transfers the buffer into a canonical
acquired image) is not present in this tree's source. What remains open is
exactly what the 2026-11-11 triage recorded: live presentation proof (Xvfb or
physical surface, verification readback outside timed frames, zero-readback
timed frames, 7680x4320 p50/p95 + receipts), which needs a display
environment and an admitted compiler — neither available to this lane. No
source change was made; status remains open (PARTIAL).


---

## 2026-11-13 addendum — P3 gpu lane p3-gpu-20261113 (work/p3-gpu-20261113, base 6f4cb189867)

**Verdict: PARTIAL, unchanged from the 2026-11-11 ne7 triage — live
presentation proof still outstanding; not producible on a Windows P3 lane.**
Presentation ownership remains at `present_window_device()`
(`src/lib/gc_async_mut/gpu/engine2d/engine.spl`) with the strict-submission
Vulkan owner and the compositor fail-closed gates; the acceptance criteria
(Xvfb/physical surface live presentation, verification readback outside timed
frames, zero-readback timed frames, 7680x4320 p50/p95 + RSS + presentation
receipts) require a Linux display environment. No live presentation evidence
was searched for or claimed here; per the v3 freeze this row stays OPEN with
no admission without live checksum evidence.
