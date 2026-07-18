<!-- codex-research -->
# Local Research: SimpleOS QEMU Host-GPU 2D

## Finding

SimpleOS currently CPU-rasterizes Engine2D commands into guest DMA memory and uses VirtIO-GPU only for 2D scanout transfer. `virtio_gpu_init.spl` creates and attaches a 2D resource; `virtio_gpu_ops.spl` presents it with `TRANSFER_TO_HOST_2D` plus `RESOURCE_FLUSH`; `backend_virtio_gpu.spl` performs the pixel work on the guest CPU.

No current SimpleOS/QEMU path negotiates 3D contexts, capsets, blobs, virgl, Venus, rutabaga, or gfxstream. The existing `device_readback` label means a direct read from guest device-backing memory, not proof that a host GPU rendered the pixels.

## Existing paths to reuse

- Backend/reason contract: `src/lib/gc_async_mut/gpu/engine2d/backend_probe.spl`
- Drawing/processing split: `src/lib/gc_async_mut/gpu/engine2d/backend_lane.spl`
- Guest scanout fallback: `src/os/drivers/virtio/virtio_gpu*.spl`
- Exact framebuffer capture/comparison: `src/os/compositor/qemu_capture.spl`, `src/os/compositor/screenshot_compare.spl`
- Host GPU backends and strict probes: `src/lib/gc_async_mut/gpu/engine2d/`
- Portable processing architecture: `doc/04_architecture/compiler/backend/processing_backend.md`
- Aggregate gate: `scripts/check/check-simpleos-hardening-evidence-matrix.shs`

## Architecture gaps

| Guest | Current display evidence | Host-GPU gap |
|---|---|---|
| x86_64 | Plain VirtIO-GPU 2D scenario | No host execution transport or receipt |
| AArch64 | RAM framebuffer target | No accelerated GPU scenario |
| RISC-V64 | VirtIO-GPU QMP framebuffer smoke | Display proves pixels, not acceleration |

`ProcessingIR` is documented but its proposed implementation roots are not present. The selected implementation must add only the minimum shared processing contract needed by the parity fixture and reuse existing generated-kernel/backend facilities.

## Collision warning

VirtIO-GPU driver and Engine2D files are concurrently dirty. This lane must preserve those changes and first add its protocol at a separate owner boundary, integrating into shared files only after reviewing the live diff.

