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
