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

## macOS Metal host lane

The existing Metal contract tests are sufficient; this lane adds no duplicate
tests. A prepared macOS host must run the canonical checks below and retain the
resulting receipts. Linux may run the source/contract checks, but must not mark
this lane complete or substitute CPU/Vulkan output.

| Check | Canonical command | Required receipt |
|---|---|---|
| Generated Metal 2D readback | `scripts/check/check-metal-generated-2d-readback.shs` | `status=pass`, module verification, submit and wait, host upload/download, `readback_available=true`, and exact nonzero fill/copy/alpha/scroll checksums |
| Metal MSL diagnostic | `scripts/check/check-macos-metal-msl-library-micro-diagnostic.shs` | native MSL compile/library validation, positive device/command handles, submit-wait completion, device readback, and exact checksum |
| Production Metal 2D live evidence | `scripts/check/check-macos-metal-2d-live-evidence.shs` | `source=device_readback`, positive backend/device handles, changed interaction checksum, and exact Draw IR readback checksum |
| Vulkan/Metal parity | `scripts/check/check-macos-vulkan-metal-2d-parity-evidence.shs build/macos_vulkan_2d_live/evidence.env build/macos_metal_2d_live/evidence.env` | both lanes use device readback; equal scene/event/font/Draw IR evidence; zero accepted pixel/channel delta |

Archive each Mac result under `build/macos_metal_2d_live/`,
`build/macos_metal_msl_library_micro_diagnostic/`, and
`build/metal_generated_2d_readback/`, including each `evidence.env`, bounded
logs, device identity, OS/architecture, and source/repository revision. The
required host rows are macOS x86_64 and macOS AArch64, each with a fresh
receipt. A missing device, timeout, CPU mirror, Vulkan fallback, or absent
submit-wait/readback/checksum field is unavailable/fail, never a pass.
