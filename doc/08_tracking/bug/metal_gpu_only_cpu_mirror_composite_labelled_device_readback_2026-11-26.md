# Metal gpu_only composites blends on the CPU mirror but labels the readback device

- Status: open (P2). Found by review on 2026-11-26; source-read only, this
  Linux aarch64 host has no Metal device, so it is not reproduced here.
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
