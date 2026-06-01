<!-- codex-research -->
# GUI Lib macOS + SimpleOS QEMU ARM64 Perf Domain Research

## Sources

- QEMU virtio-gpu documentation: https://www.qemu.org/docs/master/system/devices/virtio-gpu.html
- QEMU system-emulation introduction: https://www.qemu.org/docs/master/system/introduction.html
- QEMU QMP reference for `screendump`: https://qemu.readthedocs.io/en/v7.2.19/interop/qemu-qmp-ref.html
- Apple Metal drawable best practices: https://developer.apple.com/library/archive/documentation/3DDrawing/Conceptual/MTLBestPracticesGuide/Drawables.html
- Apple Metal command-buffer best practices: https://developer.apple.com/library/archive/documentation/3DDrawing/Conceptual/MTLBestPracticesGuide/CommandBuffers.html
- Apple Metal CPU/GPU synchronization sample: https://developer.apple.com/documentation/metal/synchronizing-cpu-and-gpu-work
- Playwright visual comparisons: https://playwright.dev/docs/test-snapshots

## Findings

- QEMU supports `hvf` on macOS for x86 and Arm hosts. A macOS ARM64 host must explicitly select HVF for hardware virtualization; otherwise TCG emulation is the fallback and is not a valid performance baseline.
- QEMU virtio-gpu has a 2D backend and accelerated `virglrenderer` and `rutabaga_gfx` backends. The repo should treat acceleration as a probed capability, not an assumed invariant, because backend availability depends on the installed QEMU build and guest driver path.
- QMP `screendump` captures the primary display by default and can write `ppm` or `png` on supported QEMU versions. This matches the repo's QMP capture scripts and should remain the authoritative VM screenshot primitive.
- Apple recommends holding Metal drawables briefly, acquiring them late, releasing them promptly, and registering drawable presentation on the command buffer before commit. Waiting for GPU completion before presentation creates CPU stalls.
- Apple recommends submitting the fewest command buffers per frame that keep the GPU busy, with one or two per frame typical for many apps. More command buffers can hide starvation but also introduce CPU-GPU synchronization stalls.
- Visual comparison should use stable baselines, explicit viewport/capture size, thresholds, and masking or style normalization for volatile content. Pixel-level checks are useful for deterministic VM framebuffers; perceptual or thresholded checks are better for host UI paths with font/subpixel variation.

## Implications For This Repo

- The macOS host perf lane must record QEMU accelerator, CPU, display backend, Metal availability, Simple runtime mode, and whether results came from native, interpreter, or JIT execution.
- The QEMU ARM64 lane must fail strict verification if HVF or a live QMP capture socket is required but absent; non-strict local planning may record unavailable evidence with exact prerequisites.
- Capture comparison should produce raw capture, normalized dimensions/format, mismatch count, first mismatch coordinate, checksum/hash, and a human-readable markdown report.
- Pure-Simple optimization must be measured against the existing `test/perf/graphics_2d` and WM perf harnesses before and after changes.
