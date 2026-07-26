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

## Cross-host and physical-board extension (2026-07-26)

The reusable repository seam is already present:

`DrawIrComposition -> Engine2dWmFrameExecutor -> Engine2D backend lane ->
SimpleOsHostGpuSession/native surface -> correlated readback`.

The shared QEMU offload contract lives in
`src/lib/common/gpu/simpleos_host_gpu_protocol.spl` and the guest mapping path
in `src/os/lib/gpu_bridge/host_gpu_ivshmem*.spl`. It is distinct from
`src/os/drivers/virtio/virtio_gpu*.spl`, which remains a 2D scanout transport.
Linux, macOS, and Windows host execution should therefore share this session
and evidence schema while isolating native resource interop in host adapters.

The Simple 2D public boundary must remain unchanged:

- `src/lib/common/ui/draw_ir.spl` owns `DrawIrComposition`;
- `src/lib/gc_async_mut/gpu/engine2d/backend.spl` owns `RenderBackend` and
  `Engine2DReadback`;
- `src/lib/gc_async_mut/gpu/engine2d/backend_lane.spl` owns drawing versus
  processing selection;
- `backend_metal.spl`, `backend_vulkan.spl`, and `backend_software.spl` remain
  private backend implementations;
- event routing remains host input -> Simple dispatcher -> state/dirty Draw IR
  -> Engine2D. GPU transport never owns event policy.

No native-board GPU owner exists for the named targets. UNO Q repository
coverage currently concerns the STM32U585 MCU lane, not QRB2210/Adreno. No
VisionFive 2 BXE or UP Squared N4200 i915/ANV driver, boot matrix, readback
wrapper, or physical-board artifact is present. These must be new platform
adapters below the same Engine2D/evidence contract, not new Simple 2D APIs.

Current host Metal/Vulkan evidence and dirty live wrappers are host-only. They
must be retained as regression prerequisites but cannot prove a SimpleOS guest
or physical-board GPU row.
