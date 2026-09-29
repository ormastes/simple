<!-- codex-architecture -->
# Simple 2D Multiplatform Vulkan Hardening Architecture

Status: accepted interface freeze and evidence boundary, 2026-08-08. This is
an implementation handoff, not a claim of a live Vulkan DrawIR frame. It
supersedes no existing renderer, Venus, or QEMU document; it joins their
interfaces for the Linux, SimpleOS ARM64/QEMU, macOS, and UNO Q acceptance
lanes.

## Decision

All UI producers use one semantic and rendering path:

```text
input/event + audio completion
  -> semantic WM/UI state -> DrawIrComposition
  -> Engine2D Vulkan-first executor -> fence -> device readback -> receipt
                                     \-> explicit CPU/SIMD fallback receipt

SimpleOS guest: VirtioGpuDiscoveryProvider -> Venus protocol/queue (future)
                 -> same executor contract, never a second renderer
```

`DrawIrComposition` is the sole boundary between Web, GUI, WM, and Simple 2D
producers and an executor. `FontRenderer`/`FontRenderBatch` is transient
executor material; atlas pixels, Vulkan objects, native handles, and caches do
not enter DrawIR. `SimpleOsHostGpuSession` remains the bounded QEMU ivshmem
capsule, not a second graphics API.

## Frozen public-to-next-layer interfaces

| Layer | Frozen contract and owner | Rule |
|---|---|---|
| Common capability | `GpuAccelerationProvider`, `GpuProviderCapabilityReceipt`, `GpuExecutionReceipt` in planned `src/lib/common/gpu/acceleration_provider.spl` | The interface is intentionally not implemented until its provider and receipt tests exist. It exposes capability/admission and immutable execution evidence, never PCI/Venus/private handles. |
| VirtIO discovery | `VirtioGpuDiscoveryProvider`, `VirtioGpuDiscoveryReceipt`, `VirtioGpuPciCapability`, `VirtioGpuDeviceConfig`, `VirtioGpuSharedMemoryRegion` in `src/os/drivers/virtio/virtio_gpu_discovery.spl` | Existing discovery is bounded and cacheable for one device lifetime. `VenusDiscovered` is discovery only; its `vulkan_executed` and `device_readback` remain false. Reset clears the cached receipt. |
| Venus private subtree | `VenusProtocolProbe`, `VenusSession`, `VenusCommandQueue`, `VenusFenceReceipt`, `VenusDeviceReadbackReceipt` under `src/os/drivers/virtio/_Venus/` | Protocol classification, blobs, rings, queue, fences, and readback remain sibling-private. A compositor consumes only a common execution receipt. |
| Runtime lifetime | `VulkanRuntimeLifecycle` in `src/compiler_rust/runtime/src/vulkan_graphics_runtime_core.rs`; `VulkanSession.runtime_lease_held` in `src/lib/gc_async_mut/gpu/engine2d/vulkan_session.spl` | Every discovery, render target, and ProcessingIR execution owner holds its own lease. A non-final release cannot tear down the process device; final release waits idle, clears/quarantines resources, then shuts down exactly once. |
| ARM IO join | planned `Arm64WmIoReceiptOwner` and immutable `Arm64WmIoFrameReceipt` in `src/os/compositor/arm64_virtio_io_receipt.spl` | It joins an accepted normalized input event, WM mutation, frame, and optional VirtIO-SND completion atomically. It owns no input parser, audio driver, or renderer. |
| Compiler dispatch | native compiler canonical qualified-layout/nominal-dispatch invariant | A native virtual call is permitted only when the resolved receiver has nominal class/trait implementation evidence and an initialized vtable. Structural/duck-shaped values, including a mixin-only render target, must use a concrete/explicit adapter or fail compile-time admission; they must not synthesize a vtable call. |

The planned common and ARM receipt files are names reserved by this design; an
absent file is an unresolved implementation item, not an invitation to add a
parallel contract. Existing `HostWmInputReceipt`, `VirtioInputPollReceipt`,
`VirtioSndServiceReceipt`, `VirtioSndCaptureReceipt`, and `WmFsFrameReceipt`
remain their domain owners until the atomic join is implemented.

## Vulkan lifetime and admission

There are two deliberately different admission levels.

1. A bounded HELLO may use cached physical-device discovery. At
   `origin/sync-gh` `e5f8d170`, Linux `SimpleOsGpuHostAllPlatform` keeps a
   discovery lease and HELLO performs no shader work, submission, fence, or
   teardown within its negotiation budget. A HELLO receipt has no render
   handle, identity, pixels, or provenance and is never a render PASS.
2. A DRAW_IR/RENDER/ProcessingIR request creates or retains an execution
   lease, revalidates the selected physical device, submits, obtains the
   matching fence, and returns same-generation device-origin bytes. Its
   receipt must have a positive backend handle and device identity, positive
   checksum/pixel count, `readback_source=device_readback`, no skipped DrawIR
   command, matching run/frame/generation, and exact CPU oracle parity.

If init acquires a lease then any later session setup fails, that owner releases
its lease after releasing its own created resources. Daemon shutdown releases
the discovery lease only after request work has completed. Device reset,
protocol change, device loss, or selected-device change invalidates every
capability/session/execution receipt before reuse.

Linux host policy is Vulkan-first: the all-platform Linux host refuses a
non-Vulkan render engine. A requested Vulkan path must fail closed; it may not
quietly satisfy a Vulkan request with CPU, Metal, DirectX, a cache, a scanout,
or a synthetic handle. A separately selected CPU/SIMD fallback is allowed only
with explicit `fallback` status and non-device provenance.

## DrawIR execution matrix and hot-path rules

| Semantic command family | DrawIR/Engine2D owner | Vulkan requirement | Failure rule |
|---|---|---|---|
| clear, filled/outlined rect, rounded rect | canonical DrawIR composition and Vulkan dispatch | clipping, opacity, ordered blend and full output coverage | unsupported/unchecked dispatch rejects the frame; it cannot be silently skipped |
| line, circle, triangle, gradient | canonical DrawIR composition | backend algorithm must match the CPU oracle for the selected command class | an approximation needs a named compatible lowering and parity proof |
| text/glyph run | semantic text in DrawIR; `FontRenderer` lowers through `draw_text` | font identity, glyph positions, atlas upload/batch, and frame readback correlate | stale/missing atlas or incomplete glyph receipt prevents Vulkan promotion |
| image/resource | bounded image-resource wire table and DrawIR image command | resolved ARGB resource, clipping, native src-over, checksum and output coverage | unresolved/invalid resource is an explicit reject, never a placeholder pixel |
| animation and event-driven damage | semantic state/epoch owner -> next composition | frame sequence is monotonic and correlated to the accepted event | a timer/capture alone does not prove rendering |

The healthy path holds a persistent daemon/runtime session, pipeline cache,
descriptor/command ownership, and revision-keyed image/font material across
frames. It does not rescan PCI/capsets, re-enumerate devices, spawn a daemon,
recompile pipelines, allocate an unbounded atlas, or read back a full frame for
an unchanged scene. Cache invalidation is only by device/session reset, font or
image revision change, composition/resource revision change, or terminal
shutdown. The performance receipt records 20 post-oracle warm samples,
nearest-rank p95, daemon/QEMU/combined max RSS, selected backend/device, and
the exact executable/argv/profile. No numeric performance PASS exists without
that same-profile baseline and budget.

## ARM event/audio atomic receipt

`Arm64WmIoReceiptOwner.publish(...)` is the frozen future seam. It accepts
only: (a) one ordered `VirtioInputEvent` normalized by the existing ARM input
backend including left/right Ctrl and Alt, pointer button/motion/wheel state;
(b) the resulting WM semantic target, mutation/state epoch, and frame sequence;
and (c) a validated playback or capture completion when the scenario requests
audio. It emits one immutable receipt containing schema/version, boot/session
generation, event sequence, modifier bitmap, target/action/reason, WM epoch,
frame/generation correlation, audio stream/direction/session/generation,
period frames/sample hash/status, and terminal status.

The owner publishes only after all present components validate against the same
session generation. Missing audio is represented as `audio=not_requested`; a
partial, stale, replayed, out-of-order, or cross-session component is rejected
and cannot be joined later by a shell parser. The input backend owns decoding;
VirtIO-SND owns DMA/PCM/fence semantics; the WM owns mutation; Engine2D owns
pixels. This prevents duplicate ARM keyboard/mouse/audio routing.

## Environment profiles and current evidence

| Profile | What is presently defensible | Promotion blocker |
|---|---|---|
| Linux Vulkan host | e5f8d170 retains runtime leases and uses bounded cached physical HELLO admission; source/contract surfaces exist | a full DrawIR submission/fence/device-readback receipt through the current native compiler and daemon must pass; no HELLO-only promotion |
| SimpleOS ARM64 QEMU | guest boot, BAR mapping, physical Vulkan HELLO, shared ARM input/audio contracts are useful narrow evidence | native nominal-dispatch defect reaches the first render-request path; no accepted DrawIR execution/readback, event-to-frame/audio join, or showcase capture yet |
| macOS | implementation, emulator/contract, and test preparation can proceed | this Linux host cannot claim macOS-native Vulkan/Metal or HVF execution; require an approved macOS host and real receipt/capture |
| UNO Q | board wrapper reports explicit blocked reasons | no attached board/runner and no accepted native GPU lifecycle (firmware, MMU/cache, queue, fence, readback, display) |

TCG, source scans, screenshots, QEMU flags, scanout, synthetic handles, CPU
mirrors, cached historical rows, and a physical-device HELLO retain their
narrow evidence class. They never promote a device-executed row.

## Exact remaining blockers

1. Integrate and freshly compile/test the corrected native nominal class
   dispatch path; the qualified-layout fix alone is not proof that the first
   DrawIR request is safe.
2. Replay one bounded first DrawIR request after HELLO and retain daemon exit,
   request/completion generation, selected device, fence, and readback evidence.
3. Complete the queued Venus execution chain only after discovery: protocol
   classification, blob/ring, queue, fence, and device readback.
4. Implement the atomic ARM event/audio receipt owner, then run mouse,
   pointer/drag/wheel, keyboard, both Ctrl/Alt sides, playback, and capture
   through a correlated rendered frame.
5. Capture the animated DrawIR showcase with text/font evidence and record the
   warm p95/RSS profile on an accelerated QEMU run.
6. Obtain a macOS host and an attached UNO Q before their rows can become
   runnable; retain fail-closed `unsupported`/`blocked` evidence until then.

## References

- `doc/04_architecture/simpleos_qemu_host_gpu_2d.md`
- `doc/04_architecture/simpleos_venus_gpu_stack.md`
- `doc/04_architecture/gpu_web_differential_oracle.md`
- `doc/04_architecture/simple2d_primitive_lane.md`
- `doc/05_design/simple_2d_multiplatform_vulkan_hardening.md`
- `doc/03_plan/agent_tasks/simple_2d_multiplatform_vulkan_hardening.md`
