# Native GPU Font Readback

**Status:** release-blocking and currently unavailable
**Traceability:** REQ-011, REQ-012, REQ-013, REQ-014; NFR-002, NFR-004, NFR-005, NFR-006, NFR-007, NFR-008
**Executable:** `test/03_system/app/simple_2d/feature/native_gpu_font_readback_spec.spl`

> Hand-maintained mirror pending canonical `spipe-docgen`; no generated-manual
> PASS is claimed.

This scenario has three SimpleOS provenance rejection rows, two fail-closed
classification rows, and three independent live evidence rows. Vulkan Engine2D
and
the Engine3D font adapter render on a consistent device name/type/driver tuple;
SimpleOS supplies a
pinned-font guest framebuffer oracle; and the warm performance/resource
budgets pass. CUDA Engine2D generated-artifact evidence is owned by the
separate `cuda_generated_font_handoff_spec.spl` pair. That CUDA row and this
Vulkan row neither require nor imply the same device or backend. The Vulkan
tuple check is not a device UUID or retained execution proof. CPU rendering,
upload-only evidence, and environment claims are not substitutes.

## Operator flow

### Reject noncanonical SimpleOS artifact evidence

Reject missing or copied wrapper provenance, malformed or ambiguous SHA-256
fields, and copied metadata whose canonical retained files do not match. These
three fail-closed rows do not claim QEMU execution or retained pixel evidence.

### Classify unavailable hardware

The shared promotion classifier returns `unavailable` when controlled
Engine2D and Engine3D records both report missing native graphics hardware.
Unavailable is never pass.

### Reject forged native proof

The same classifier returns `rejected` for an Engine2D record whose pixels
came from `cpu_fallback` and an Engine3D record whose claimed readback does
not match its device evidence. These rows do not require hardware and cannot
promote a backend.

### Prove native submission and device readback

Treat the first unavailable rung as failure: compiled program, native resource
creation, submission, completed fence, and device-origin readback are required
before any backend is promoted.

### Render Engine2D plus Engine3D HUD/world text on Vulkan

Engine2D requires a native pipeline, atlas buffer, submitted command, completed
fence, concrete device-readback handle and device identity, nonblank pixels,
and exact packed-ARGB CPU pixel equality.

The checker `expect_engine3d_font_readback` requires nonzero native device,
distinct HUD/world pipelines, texture, sampler, and fence handles; HUD and world draws; verified
HUD placement and world transform/depth behavior; a completed and destroyed
fence; device-origin nonblank readback; and CPU-oracle parity.

Current expected result is an explicit failure until native execution is
retained. Source now owns dedicated HUD/world pipelines, combined sampler
binding, depth test+write, zero-coverage fragment discard, fenced device-image
readback, exact atlas owner/generation/payload hash, and public-pixel comparison.
The public selector reports the honest hybrid identity `vulkan-font`; repeated
installation must retain the same HUD/world pipelines and sampler. The depth oracle uses a translated
perspective camera and four native frames (near-only, far-only, and both draw
orders); every fully opaque overlap pixel must keep the near color.
The independent HUD-only frame derives the expected nonzero pixel count and
bounds directly from the shared batch atlas at `(4,4)` and requires an exact
device-readback match. Reported pipeline and texture identities are resolved
from their logical handles rather than resource-array positions.

### Capture SimpleOS pinned-font pixels

The checker `expect_simpleos_font_pixel_oracle` requires the pinned Noto Sans
Mono asset SHA-256, the canonical taskbar-clock 56×48 RGB region SHA-256,
exactly 8,064 region bytes, and `qemu-pmemsave` device origin. The guest loads registry-validated
bytes from the canonical image path or the shared extensionless FAT alias
`/SYS/FONTS/NOTOSANS`. The pure-Simple reader uses a
32 MiB ceiling and the C compatibility reader uses 4 MiB; both admit this
pinned 1,708,408-byte payload without truncation. The existing 12 px
`taskbar-clock` command is emitted by the canonical WM DrawIR frame; no private
post-frame font draw remains. The fullscreen wrapper independently hashes the
dynamic rightmost 56×48 `pmemsave` crop and retains serial, raw/PPM, capture
output, and region digest. The expected canonical hash is intentionally unset
until a trusted retained capture establishes it; promotion stays fail-closed
until the value is pinned and reproduced.
A disposable host-built FAT32 image contains the fallback at the exact pinned
length and SHA-256, but no successful QEMU artifact is retained yet; missing
any durable guest artifact is `unavailable` and fails this promotion gate.

### Measure warm font rendering and resource bounds

The checker `expect_font_perf_budget` requires at least 95% warm cache hits;
1,024-glyph p95 at most 4 ms at 1080p and 8 ms at 4K; 4,096-glyph native p95 at
least 1.25× faster than the CPU oracle; no unchanged full-atlas upload; at most
10% RSS growth; a nonzero GPU high-water mark at most 128 MiB; controlled
Vulkan-poison CPU fallback; unchanged prepared-batch identity; and eleven
post-loss CPU samples whose recomputed p95 does not exceed baseline.

The performance SSpec is the sole collector and overwrites the strict v5
run/host/source/font/device-pinned durable record. This system scenario only loads that
record; missing, stale, partial, or non-passing evidence fails closed.

## Evidence artifacts

- Engine2D/Engine3D evidence: consistent device tuple, native resource/fence handles, draw counts,
  readback bytes/source, absolute pixels, and CPU diff.
- SimpleOS evidence: guest serial log plus QEMU `pmemsave` PPM and fixed-region
  digest.
- Performance evidence: five budget/recovery arrays, seven stage arrays,
  recovery identity, upload/RSS, GPU resource high-water, compiled artifact and
  batch/payload identities, observed handles/fence, changed device pixels, and
  exact CPU parity. NFR-008 source/schema coverage is present; the retained
  native v5 record remains pending.

The executable spec is the authority. Regenerate this manual after all eight
scenarios pass and require SPipe docgen to report zero stubs.
