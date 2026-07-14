# Native GPU Font Readback

**Status:** release-blocking and currently unavailable
**Traceability:** REQ-010, REQ-012, REQ-013, REQ-014; NFR-002, NFR-004, NFR-005, NFR-006, NFR-008
**Executable:** `test/03_system/app/simple_2d/feature/native_gpu_font_readback_spec.spl`

This scenario has four independent live evidence rows. CUDA Engine2D executes
the checker-produced font artifact on its native compute backend/device;
Vulkan Engine3D separately renders HUD and world text on its graphics
backend/device; SimpleOS supplies a pinned-font guest framebuffer oracle; and
the warm performance/resource budgets pass. The CUDA and Vulkan rows neither
require nor imply the same device or backend. CPU rendering, source emission,
upload-only evidence, and environment claims are not substitutes.

## Operator flow

### Prove native submission and device readback

Treat the first unavailable rung as failure: compiled program, native resource
creation, submission, completed fence, and device-origin readback are required
before any backend is promoted.

For CUDA, the retained toolchain record must identify the Simple invocation and
resolved native compiler binaries with exact SHA-256, the current emitter
source/version hashes, the exact retained generated `.cu` source/hash, a
verified PTX artifact/hash, and the versioned font entry. The scenario installs
that artifact through `Engine2D.install_cuda_font_artifact`, dispatches one
canonical `FontRenderBatch`, and requires the pinned module identity, CUDA
execution target, nonzero backend handle, device-origin readback, and exact CPU
pixels. This Engine2D compute row is independent of the Vulkan Engine3D row.

### Render Engine3D HUD and world text on the promoted backend

The checker `expect_engine3d_font_readback` requires nonzero native device,
pipeline, texture, sampler, and fence handles; HUD and world draws; verified
HUD placement and world transform/depth behavior; a completed and destroyed
fence; device-origin nonblank readback; and CPU-oracle parity.

Current expected result is an explicit failure until native execution is
retained. Source now owns dedicated HUD/world pipelines, combined sampler
binding, depth test+write, zero-coverage fragment discard, fenced device-image
readback, and exact public-pixel comparison. The depth oracle uses a translated
perspective camera and four native frames (near-only, far-only, and both draw
orders); every fully opaque overlap pixel must keep the near color.
The independent HUD-only frame derives the expected nonzero pixel count and
bounds directly from the shared batch atlas at `(4,4)` and requires an exact
device-readback match. Reported pipeline and texture identities are resolved
from their logical handles rather than resource-array positions.

### Capture SimpleOS pinned-font pixels

The checker `expect_simpleos_font_pixel_oracle` requires the pinned Noto Sans
Mono asset SHA-256, the fixed 18×23 RGB region SHA-256, exactly 1,242 region
bytes, and `qemu-pmemsave` device origin. The guest now loads registry-validated
bytes from the canonical image path or the shared extensionless FAT alias
`/SYS/FONTS/NOTOSANS`. The pure-Simple reader uses a
32 MiB ceiling and the C compatibility reader uses 4 MiB; both admit this
pinned 1,708,408-byte payload without truncation. It paints
the fixed `A`/32 px witness and emits a marker only after hashing live MMIO. The
fullscreen wrapper independently hashes a dynamic-scanout
`pmemsave` crop and retains serial, raw/PPM, capture output, and region digest.
A disposable host-built FAT32 image contains the fallback at the exact pinned
length and SHA-256, but no successful QEMU artifact is retained yet; missing
any durable guest artifact is `unavailable` and fails this promotion gate.

### Measure warm font rendering and resource bounds

The checker `expect_font_perf_budget` requires at least 95% warm cache hits;
1,024-glyph p95 at most 4 ms at 1080p and 8 ms at 4K; 4,096-glyph native p95 at
least 1.25× faster than the CPU oracle; no unchanged full-atlas upload; at most
10% RSS growth; and a nonzero GPU high-water mark at most 128 MiB.

The performance SSpec is the sole collector and overwrites the strict
source/font/device-pinned durable record. This system scenario only loads that
record; missing, stale, partial, or non-passing evidence fails closed.

## Evidence artifacts

- Engine3D evidence: native device identity, resource/fence handles, draw counts,
  readback bytes/source, absolute pixels, and CPU diff.
- SimpleOS evidence: guest serial log plus QEMU `pmemsave` PPM and fixed-region
  digest.
- Performance evidence: raw samples and stage counters for shaping, material,
  upload, queue, sync, readback, RSS, and GPU resource high-water.

The executable spec is the authority. Regenerate this manual after its four
scenarios pass and require SPipe docgen to report zero stubs.
