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

## Completion refresh (2026-07-27)

Current `main` now contains the dependency-inversion slice that the earlier
audit identified:

- `DrawIrRenderTarget` is the internal Draw IR execution boundary.
- Normal applications continue through `Engine2D`.
- `MetalDrawIrRenderTarget` reuses `MetalBackend`, `FontRenderer`,
  `Engine2DReadback`, and strict positive device identity.
- `main_macos.spl` composes the shared daemon runner with
  `SimpleOsGpuHostMacPlatform`; its measured closure excludes `engine.spl` and
  non-Metal providers.

The remaining critical path is no longer renderer decomposition:

1. admit a current pure-Simple compiler;
2. build the Metal-only daemon with no stub fallback;
3. build fresh ARM64 probe and desktop guest ELFs;
4. boot through the canonical HVF/file-backed-RAM wrapper;
5. accept only completed Metal device readback with positive native handles;
6. compare packed pixels and serialized bytes exactly with the CPU/SIMD oracle;
7. collect the required warm samples and RSS evidence.

The deployed macOS compiler candidates fail the wrapper's mandatory CLI/env ABI
admission probe. The repository bootstrap report identifies the supported
recovery: rebuild the Rust seed from current Rust source in a private target
directory, use it only to create a current pure-Simple stage, then admit and
use that pure-Simple artifact for normal build/test work.

No current ARM64 probe or desktop guest ELF is available. Cached guests remain
inadmissible. The wrapper also lacks a verified ARM64-only selector, so a
bounded `SIMPLEOS_HOST_GPU_GUEST_ISAS=aarch64` contract is required to avoid
unrelated x86/RISC-V construction in the macOS completion lane.

Metal font dispatch has a real device framebuffer/readback path and real
persistent atlas material, but `MetalDrawIrRenderTarget` returns `nil` font
evidence. Honest promotion requires recording successful atlas upload facts and
proving exact post-dispatch device pixels against a canonical software replay
seeded from the actual pre-dispatch device readback.
