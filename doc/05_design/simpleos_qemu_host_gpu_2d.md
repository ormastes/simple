<!-- codex-design -->
# SimpleOS QEMU Host-GPU 2D Detail Design

## Shared Contract

`SimpleOsHostGpuHello` carries protocol version, maximum payload/batch sizes,
render and processing backend sets, readback support, and readiness.

`SimpleOsHostGpuRequest` carries protocol version, run ID, frame ID, kind
(`draw_ir` or `processing_ir`), bounded dimensions/counts, payload bytes, and
input checksum.

`SimpleOsHostGpuReceipt` carries the same IDs, status, stable reason, selected
backend, native device identity and positive handle, output bytes/checksum,
elapsed time, and host-service RSS.

All numeric wire fields use fixed-width little-endian encoding. The decoder
checks the fixed header and declared length before reading the body. One
outstanding request map rejects duplicate or stale receipts.

## Flow

1. The guest maps the QEMU `ivshmem-plain` BAR2 region and negotiates bounded
   capabilities through its control header.
2. Canonical RECT/TEXT/IMAGE Draw IR semantics and ProcessingIR `FillU32` use the payload area.
   Production WM frames first form one `DrawIrComposition`; the local fallback
   resolves checksum-valid top-level `WmContentFrame` pixels as IMAGE resources.
   The guest encodes unique referenced top-level IMAGE pixels as bounded,
   checksummed little-endian records in the negotiated readback arena and
   publishes their count, byte length, and checksum with the request. Clipped
   nested resources remain open.
3. The daemon validates, dispatches to its private host adapter, reads output
   back in the same completion, and emits a correlated receipt. It snapshots
   resource bytes before rendering and rechecks request generation immediately
   before overwriting the shared arena with result pixels.
4. The guest validates provenance and exact CPU-oracle parity.
5. Any unavailable service/backend or invalid receipt returns a stable reason
   and selects the existing software/CPU path without preventing boot.

`FramebufferDriver.present_argb32_from_mmio` is the bounded presentation
primitive for a later production executor-wiring slice. It rejects invalid or
unaligned source addresses, mismatched dimensions/byte counts, non-ARGB32 or
undersized-pitch destinations, overflow, direct-MMIO source/destination
overlap, insufficient host-buffer capacity, and non-positive or mismatched
checksums. It scans the complete source before any destination write, then
copies exact rows using the destination pitch and presents only after the copy
finishes. It allocates no staging buffer. `Engine2dWmFrameExecutor` remains the
frame owner; this helper is not a session API and does not authorize a
producer-side full-frame shortcut.

The local `Engine2dWmFrameExecutor` rejects duplicate or unreferenced content
frames, stale revisions, bad checksums, unresolved IMAGE commands, and nested
GROUP metadata. The wire accepts the same top-level IMAGE resource set, but
production host-offload selection remains open until session wiring and fresh
QEMU evidence. The host-only fresh-device executor may bypass the software
offscreen surface for one exact opaque IMAGE covering the full target;
all other IMAGE shapes preserve the existing offscreen/fallback behavior.

Local production composition calls
`engine2d_draw_ir_adv_composition_present_with_images`. The shared internal
executor takes independent `present_frame` and `readback_frame` controls:
regular composition is `(true, true)`, fresh-device execution is
`(false, true)`, and the production present-only path is `(true, false)`. When
readback is disabled, both preflight rejection and successful rendering return
`engine2d_readback([], "not_requested")`; neither branch calls the Engine2D
readback API. Rendering, presentation, and accounting remain otherwise
identical, so the WM avoids allocating a discarded full-frame pixel snapshot.

## Bounds and Failure Policy

Use negotiated maxima for payload bytes, commands, dimensions, queue depth,
and outstanding batches. Reject before allocation. Unknown versions,
out-of-range references, stale IDs, duplicate completions, missing readback,
zero handles, checksum mismatch, or missing device identity are `fail`, not
fallback passes. Missing host capability is `unsupported`; missing prepared
environment is `blocked`.

The 8 MiB wire provides 8,318,976 readback bytes. The selected 1280x720 fixture
fits, while the current 3840x2160 production desktop does not. Production 4K
must retain local rendering until the wire capacity is deliberately expanded
with updated bounds and evidence; downscale and crop are not fallback options.

## Checked Vulkan Dispatch

`vulkan_dispatch_framebuffer_compute_checked(framebuffer, pipeline, push,
gx, gy, gz) -> i64` reuses the checked IMAGE dispatch lifecycle with one bound
framebuffer and no owned source buffer:

1. reject invalid handles, empty push data, zero workgroups, or missing fenced
   submission with `0`;
2. build and validate descriptor and command state, discarding a partial
   command on known setup failure;
3. submit with a fence and return `-1` when completion or dependent command/
   descriptor release remains unknown;
4. return `1` only when completion and cleanup evidence are complete;
5. otherwise return `0` without receipt eligibility or CPU replay; a completed
   mutation may exist when only cleanup evidence failed.

`VulkanBackend._dispatch_framebuffer_checked(...) -> i64` is the sole state
mapper. `1` sets `dirty`; `0` sets the existing sticky conservative provenance
flag and marks a valid initialized framebuffer dirty for conservative device
refresh; `-1` sets that flag plus `completion_unknown` and remains unreadable.
CLEAR, RECT outline/filled, filled
CIRCLE, filled TRIANGLE, and vertical GRADIENT route through it. Emulated
line/circle/rounded shapes inherit the checked RECT-filled path. No new runtime
alias, dispatcher class, or backend API is introduced.

`vulkan_dispatch_image_composite_checked(...) -> i64` retains the same fenced
source-buffer lifecycle for both modes of the existing blit pipeline. Mode 0 is
exact copy. Mode 1 applies framebuffer bounds, the active half-open clip, and
integer straight-ARGB src-over with `opacity_milli`. A real Vulkan readback must
match `SoftwareBackend` exactly and report `device_readback` with neither CPU
fallback nor unknown completion. Status `2` distinguishes a completed mutation
with ineligible cleanup evidence from status `0` (no submission), preventing a
non-idempotent src-over CPU replay.

This slice hardens the existing raw host-daemon CLEAR/RECT fixture only. The
production WM minimum remains solid RECT plus canonical `draw_text` using
the Draw IR `font-identity`, exact-size IMAGE, clip, and embedded src-over/
opacity. Font selection continues through `FontRenderer` and transient
`FontRenderBatch`; font bytes and atlas/cache state do not enter Draw IR. The
host rejects any command that falls back to CPU or lacks checked completion
before emitting a device receipt. Checked image src-over is now available, but
the production WM remains excluded until its offscreen surface is device-rendered
before group opacity and representative p95 evidence are proven.

## Observability and NFRs

Each row records host OS, guest ISA, QEMU version/arguments, protocol/backend,
device identity, IDs, timing, max RSS, and checksums. Native-ISA rows require
negotiation within 500 ms, render/readback p95 at most 16.7 ms, incremental RSS
at most 256 MiB, and processing speedup at least 1.5x to become preferred.

## Minimal Implementation Order

1. Pure Simple codec/validator and CPU oracle tests.
2. x86_64 Linux/Vulkan rendering plus CUDA-preferred, Vulkan-fallback ProcessingIR guest-daemon vertical slice.
3. AArch64 and RISC-V transport adapters using the identical protocol.
4. macOS Metal and Windows DirectX adapters only on prepared native hosts.
5. Wire canonical row output into the hardening matrix without changing its
   existing 26-row pass contract.
