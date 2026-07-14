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

`simpleos_host_gpu_wire_correlation_valid` is the single numeric correlation
owner. Non-HELLO requests require `run_id_hash > 0` and `frame_id > 0` before
guest publication and daemon execution; completion parsing and device receipt
admission compare the exact values, with device admission also requiring the
positive expected pair. HELLO remains exempt because its control exchange
intentionally carries zero IDs.

`qemu_argv_evidence_valid` validates the existing per-argument hex encoding
without decoding variable paths. It requires the exact x86_64, AArch64, or
RISC-V token count/order, derives the kernel basename from `kernel_for_isa`,
and accepts a variable nonempty shared-memory path only inside the canonical
`memory-backend-file,id=hostgpu,share=on,...,size=8M` object. Both live row
admission and cached promotion use this owner.

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

`FramebufferDriver.present_argb32_from_mmio` is the bounded production
presentation primitive. It rejects invalid or
unaligned source addresses, mismatched dimensions/byte counts, non-ARGB32 or
undersized-pitch destinations, overflow, direct-MMIO source/destination
overlap, insufficient host-buffer capacity, and non-positive or mismatched
checksums. It scans the complete source before any destination write, then
copies exact rows using the destination pitch and presents only after the copy
finishes. It allocates no staging buffer. `Engine2dWmFrameExecutor` remains the
frame owner; this helper is not a session API and does not authorize a
producer-side full-frame shortcut.

The production `Engine2dWmFrameExecutor` rejects duplicate or unreferenced content
frames, stale revisions, bad checksums, unresolved IMAGE commands, and nested
GROUP metadata. The wire accepts the same top-level IMAGE resource set, but
maps BAR2 into the active x86 VMM, derives generations only from an idle wire
slot, and selects host offload only after bounded negotiation. Fresh QEMU
evidence remains open. The host-only fresh-device executor preflights the
whole composition before mutation. It admits full-target batches plus bounded
named embedded surfaces at opacity `(0, 1000]`, containing opaque RECTs plus a
nonzero-alpha first RECT that initializes a transparent child, canonical WM
metadata-only styles, exact unscaled IMAGEs, and resolved TEXT
whose selected font and every transient atlas quad preflight within a
framebuffer-area glyph-pixel work budget;
the first command must be an opaque full-target RECT or IMAGE so newly allocated
Vulkan memory is never read before initialization. Direct IMAGE commands and
canonical TEXT glyph quads use checked src-over. Font bytes are loaded by the
existing SFFI font owner, never by Engine2D; family resolution preserves native
dylib priority and then uses the validated pure-Simple selected-byte fallback.
Effect-styled or later translucent RECT, scaling, unnamed/unbounded surfaces,
and GROUP remain rejected. A Vulkan child must return checked device readback and
is composited through the checked parent src-over path before its retained
session is released.

One `DRAW_IR_BACKEND_AUTO` production composition feeds both routes. A validated
host receipt presents through the framebuffer MMIO owner; any host failure falls
through to `engine2d_draw_ir_adv_composition_present_with_images` without a
second producer or composition. Local production composition calls
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

This slice hardens the existing raw host-daemon CLEAR/RECT fixture and the
fresh production Draw IR subset. The production WM minimum remains RECT
plus canonical `draw_text` using
the Draw IR `font-identity`, exact-size IMAGE, clip, and embedded src-over/
opacity. Font selection continues through `FontRenderer` and transient
`FontRenderBatch`; font bytes and atlas/cache state do not enter Draw IR. The
host rejects any command that falls back to CPU or lacks checked completion
before emitting a device receipt. Checked image src-over now carries IMAGE
pixels, preflighted glyph quads, and shared-session child frames at canonical WM
opacity. Production guest submission and representative p95 evidence remain
open.

## Checked Metal Draw IR source

`Engine2D.create_requested_backend(..., "metal")` is strict native selection;
the explicit `metal-on-vulkan` key owns compatibility. A new Metal surface must
complete a transparent device clear before any Draw IR mutation can qualify.
Embedded WM surfaces retain the parent's `MetalSession`, return exact checked
device readback, and composite through `draw_metal_image_blend_checked` using
the shared MSL src-over/opacity pipeline. Clear, 2D primitive, image blit, and
composite helpers require encode, dispatch, end, commit, and wait success.
Unknown commit completion poisons the surface and retains command dependencies
rather than replaying on CPU. Known completion and uncommitted failure remove
the runtime's encoder/command registry handles through the Metal facade. The host
receipt hashes the default Metal device name and total memory. Raw CLEAR/RECT
uses the same strict Engine2D factory as Draw IR and is receipt-eligible only
with exact native Metal selection, checked device completion, device readback,
a positive framebuffer handle, and the same stable identity. ProcessingIR and
all three QEMU ISA rows still need prepared macOS receipts before they can be
marked verified.

## Checked DirectX D3D11 source

On Windows, `DirectXBackend` keeps the CPU mirror for fallback semantics but
queues only the receipt-eligible CLEAR, bounded FILL_RECT, and opaque IMAGE
subset; an IMAGE may initialize the target only when full-sized, while a prior
CLEAR permits bounded partial images. One canonical no-GC facade owns the two raw runtime hooks;
the hardware-only D3D11 owner validates the complete bounded stream, executes
once, performs blocking staging readback, and returns both a positive target
handle and the executing adapter identity. The backend caches that result and
poisons native eligibility after an unsupported or post-execution mutation.
`Engine2DReadback` carries the validated identity through Draw IR, and the
wrapper rejects raw/Draw IR identity disagreement.
Non-Windows DirectX remains explicitly named software emulation. The guest,
daemon, and wrapper now negotiate DirectX rendering independently from
CUDA-preferred/Vulkan-fallback ProcessingIR. Live Windows QEMU receipts remain
open while TODO 548 blocks Simple compiler execution.

CUDA device provenance comes from preferred `cuDeviceGetUuid_v2` with legacy
symbol fallback behind the canonical CUDA runtime facade. The runtime rejects
the all-zero sentinel and otherwise returns a stable nonzero 63-bit UUID hash.
The ProcessingIR executor and daemon both reject zero identity; the native
readback gate checks the shared fixed hash vector, repeatability, and pairwise
distinction when multiple devices are present. Aggregate PASS also requires a
positive identity and a nonempty backend report.

## Observability and NFRs

### Native Metal ProcessingIR

`processing_ir_execute_metal` owns a dedicated MSL FillU32 kernel and does not
reuse Engine2D clear or `MetalSession`. It validates the common ProcessingIR,
uses the synchronous checked Metal compute owner, performs pointer-based device
readback through the canonical Metal I/O facade, and returns a positive
historical resource handle plus stable device metadata identity only after
exact output recovery. The shared runtime accepts completion only when the
command reaches `MTLCommandBufferStatus::Completed` with no error. A separate
CPU oracle remains the daemon's final parity gate.

Each row records host OS, guest ISA, QEMU version/arguments, protocol/backend,
device identity, IDs, timing, max RSS, and checksums. Native-ISA rows require
negotiation within 500 ms, render/readback p95 at most 16.7 ms, incremental RSS
at most 256 MiB, and processing speedup at least 1.5x to become preferred.

## Minimal Implementation Order

1. Pure Simple codec/validator and CPU oracle tests.
2. x86_64 Linux/Vulkan rendering plus CUDA-preferred, Vulkan-fallback ProcessingIR guest-daemon vertical slice.
3. AArch64 production RAMFB/Engine2D desktop using the identical protocol;
   RISC-V follows after its dynamic scanout/present owner replaces fixed C anchors.
4. macOS Metal and Windows DirectX adapters only on prepared native hosts.
5. Wire canonical row output into the hardening matrix without changing its
   existing 26-row pass contract.
