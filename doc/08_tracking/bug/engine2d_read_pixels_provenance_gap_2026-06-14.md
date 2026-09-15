# Engine2D Read Pixels Provenance Gap

## Closed 2026-09-13 — Fixed: readback provenance is typed at the Engine2D backend boundary

- **measured** (grep of current source): the "Minimal Fix" landed, under the name `Engine2DReadback` rather than `Engine2DReadbackResult`. `fn read_pixels_with_source() -> Engine2DReadback` is declared on the backend trait (`src/lib/gc_async_mut/gpu/engine2d/backend.spl:104`) and implemented across backends — baremetal, directx, intel, cpu, cuda, among others.
- **measured**: the exact source taxonomy the entry specified is present — `backend.spl:44-56` maps `device_readback` / `cpu_mirror` and admits `host_cache_after_device_present`, `host_cache_after_device_copy`, `swapchain_present`, `cpu_fallback`. `backend_cpu.spl:73` returns `engine2d_readback(..., "cpu_mirror")`; `backend_cuda.spl:1051` returns `"device_readback"` only on a successful device-to-host copy, exactly as specified.
- **measured**: `read_pixels()` survives as the compatibility wrapper (`engine.spl:16,286`), and provenance is consumed by the viability probe (`engine.spl:1150,1169` — "viable: device provenance + fill/clip/blit pixel round-trip") and by the Simple Web presenter (`simple_web_engine2d_renderer.spl` via `SimpleWebLayoutEngine2DReadbackResult`).
- **inferred**: the fail-closed production-wrapper requirement is satisfiable now that the type exists; GPU hardware lanes were not exercised on this Windows host.

Date: 2026-06-14

## Status

CLOSED 2026-09-13 — fixed; provenance typed as `Engine2DReadback` + `read_pixels_with_source()`.

## Problem

`BrowserBackend` can now carry host/GPU queue packet evidence and a same-frame
Engine2D pixel readback checksum, but it cannot yet prove whether
`Engine2D.read_pixels()` came from a direct device readback, a host cache
refreshed by device present, or a CPU mirror fallback.

The production wrapper must fail closed until this provenance is typed at the
Engine2D boundary.

## Minimal Fix

- Add `Engine2DReadbackResult` with `pixels`, `backend`, `source`,
  `pixel_count`, `checksum`, and `reason`.
- Add `Engine2D.read_pixels_with_provenance()`.
- Keep `Engine2D.read_pixels()` as the compatibility wrapper returning
  `.pixels`.
- Implement backend sources:
  - CUDA/OpenCL: `device_readback` only when device-to-host copy succeeds.
  - Metal: `device_readback` only when `gpu_frame_complete` and GPU-only
    readback returns a full frame.
  - Vulkan: `host_cache_after_device_present` after `present()` refreshes the
    host buffer.
  - WebGPU/software/CPU: `cpu_mirror` or host buffer as appropriate.
- Consume the typed result in the Simple Web Engine2D presenter and WebRender
  artifact receipt before allowing
  `same_frame_gpu_backend_readback_status=pass`.
