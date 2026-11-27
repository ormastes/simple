# Metal gpu_only composites blends on the CPU mirror but labels the readback device

- Status: fix-implemented-verification-pending (P2, `waiting-for: macOS Metal verification`). Found by review on 2026-11-26; fixed on 2026-11-27 (W5-3) with Windows interpreter host unit verification.
- File: `src/lib/gc_async_mut/gpu/engine2d/backend_metal.spl`

In `gpu_only` mode `draw_rect_blend`, `draw_gradient_rect_h` and
`draw_radial_gradient` (around lines 2280-2325) call
`_begin_gpu_only_cpu_composite` (download the device framebuffer into the
mirror), rasterize on `self.mirror`, then `_commit_gpu_only_cpu_composite`
(line ~1377, re-upload) and set `gpu_frame_complete = true`.
`read_pixels_with_source` (~line 842) then labels that frame
`ReadbackSource.DeviceReadback`. Pixels are correct, but provenance is not:
evidence that requires a device composite accepts a CPU composite.

Fix direction: either composite these on the device, or carry a distinct
source (e.g. a cpu-mirror-upload label) when any span of the frame went
through the CPU composite, so device-only gates reject it.

Repro needs a macOS Metal host: a gpu_only frame with one translucent
`draw_rect_blend`, then assert `read_pixels_with_source().source` is not
`device_readback`.

## 2026-11-27 W5-3 Fix (`fix-implemented-verification-pending`)

- **Source (`src/lib/gc_async_mut/gpu/engine2d/backend_metal.spl`)**:
  - Added `cpu_composite_reason: text` field on `MetalBackend` (reset in `make_metal_backend()`, `init()`, `init_with_session()`, `shutdown()`, and `clear()`; set in `draw_rect_filled()` mask emulation, `_begin_gpu_only_cpu_composite()`, and `_commit_gpu_only_cpu_composite()`).
  - Extracted `metal_resolve_gpu_only_readback_source(cpu_composite_reason: text) -> text` and `MetalBackend.cpu_composite_reason_in_frame() -> text`.
  - Updated `read_pixels_with_source()` so any completed `gpu_only` frame mutated via CPU-mirror compositing returns `ReadbackSource.CpuMirror` (`"cpu_mirror"`, `backend_handle: 0`, `device_identity: 0`) instead of `ReadbackSource.DeviceReadback`. Pure-GPU frames keep `device_readback` with retained handle/device identity.
- **Specs**:
  - Updated `test/02_integration/rendering/metal_engine2d_readback_spec.spl` (masked and clipped CPU-composited `draw_rect_blend` cases expect `"cpu_mirror"` and reject `"device_readback"`).
  - Added `test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_metal_readback_provenance_and_glass_spec.spl`.
- **Host verification (`SIMPLE_LIB=src`, `--mode=interpreter` on Windows)**:
  - `backend_metal_readback_provenance_and_glass_spec.spl`: 4/4 PASS.
  - `metal_engine2d_readback_spec.spl`: 13/13 PASS (macOS native branches skipped on non-macOS host).
  - `backend_metal_hardening_spec.spl`: 36/36 PASS; `backend_metal_device_free_contract_spec.spl`: 7/7 PASS; `backend_readback_handle_contract_spec.spl`: 1/1 PASS.
- **Pending**: live macOS Metal hardware run (`waiting-for: macOS Metal verification`).
