# Host/GPU Event Path System Test Plan

## Scope
- Prove host events can produce queue submit and receipt evidence without GPU hardware.
- Prove unresolved or stale target-cache events stay on the host.
- Prove coarse Draw IR batches can route to the GPU lane while host semantic mutation remains host-owned.

## Evidence
- `test/03_system/feature/language/host_gpu_event_path_spec.spl`
- `doc/06_spec/03_system/feature/language/host_gpu_event_path_spec.md`
- `test/01_unit/lib/gc_async_mut/gpu/engine2d/draw_ir_runtime_queue_spec.spl`
- `doc/06_spec/01_unit/lib/gc_async_mut/gpu/engine2d/draw_ir_runtime_queue_spec.md`
- `test/01_unit/app/ui/web_render_backend_api_spec.spl` covers the shared
  artifact queue metadata helper and BrowserBackend frame propagation through
  generated widget HTML.
- `test/01_unit/lib/gc_async_mut/ui/web_render_pixel_backend_queue_spec.spl`
  proves GPU-selected web pixel artifacts carry submitted/drained runtime queue
  metadata while software artifacts stay queue-neutral.

## Backend Notes
- Linux local verification now covers adapter evidence, runtime queue
  submit/drain evidence, forced-native lane queue evidence, and a GPU-selected
  Draw IR batch bridge into the runtime queue.
- Web-render artifacts now have queue submit/drain fields and BrowserBackend has
  matching `last_artifact_queue_*` diagnostics, but GUI/web production evidence
  still needs a completed frame run with one runtime packet and one drain
  receipt.
- Generated widget HTML now routes through a deterministic widget raster path
  before the full CSS/layout renderer, so `BrowserBackend.render_frame` no
  longer stalls on the shared pixel artifact path.
- Vulkan readback passed locally through
  `scripts/check/check-vulkan-engine2d-readback.shs`.
- CUDA generated 2D readback passed locally through
  `scripts/check/check-cuda-generated-2d-readback.shs`.
- Metal readback requires macOS and is planned as native macOS evidence, not
  Linux fallback evidence; Linux reports typed unavailable.
- ROCm/HIP requires `hipcc`/`rocminfo` and supported AMD hardware; this Linux
  host reports typed unavailable because the primary ROCm probe tool is absent.
