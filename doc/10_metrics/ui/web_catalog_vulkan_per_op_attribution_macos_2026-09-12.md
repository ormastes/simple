# Vulkan lane per-op attribution, css-layout.html (macOS M4, 2026-09-12)

Binary bracketed identical before and after every run:
`/Users/ormastes/simple/build/cargo-r2/release/simple`, `stat -f '%z %m'` =
`39368072 1789171430`. Mode: `SIMPLE_2D_BACKEND=vulkan
SIMPLE_VK_READBACK=native SIMPLE_2D_BACKEND_STRICT=1 SIMPLE_VK_TIMING=1
SIMPLE_EXECUTION_MODE=interpreter SIMPLE_TIMEOUT_SECONDS=0`, one run at a time.
Page `examples/06_io/ui/web_catalog/css-layout.html`, 40,960 bytes.
Harness and raw logs: `build/perf/vk_attr_2026-09-12/` (gitignored).

## What the frame is actually made of (300x253, BEFORE)

Frame 47,143 ms. Table from `vulkan_timing_table()`, ms:

| bucket | n | total | max |
|---|---|---|---|
| **font_composite** | **5** | **27,317** | **5,514** |
| rect (all dispatches) | 187 | 145 | 2 |
| image_blend | 76 | 103 | 2 |
| image_composite (1x1) | 76 | 99 | 2 |
| enqueue (funnel) | 112 | 20 | 0 |
| flush | 8 | 20 | 13 |
| sffi bind+push+dispatch | 112 each | 5 total | 0 |
| sffi_submit_and_wait | 5 | 15 | 9 |

**This refutes the standing attribution.** `web_catalog_vulkan_lane_raster_term_2026-09-12.md`
put ~0.6 s on each 1x1 alpha blend; measured directly, 76 of them cost **99 ms
total (1.3 ms each)** and all 187 rect dispatches cost 145 ms. The whole SFFI
bind/push/dispatch chain is 5 ms. The earlier figure came from a run that moved
two variables at once, and no per-op cost was ever measured.

## Where font_composite goes (300x253, sub-steps)

| sub-step | n | total ms |
|---|---|---|
| **font_atlas_pack_u32_to_u8** | **5** | **19,012** |
| **font_atlas_payload_sha256** | **5** | **8,234** |
| font_atlas_sffi_upload | 5 | 44 |
| font_packed_params | 5 | 4 |
| font_quad_validate | 5 | 1 |
| font_owner_identity | 5 | 0 |

The two O(atlas) interpreted walks are 27.2 s of the 27.3 s. The GPU upload
they feed is 44 ms. The atlas is a fixed **1024x1024 (1,048,576 px / 4 MB)**
regardless of glyph count, so each walk is ~1M interpreted iterations.

Miss reason: `composites=5 gen_changed=5 identity_changed=2 dims_changed=1
generations=[2 3 4 6 7]`. The generations ASCEND, so the atlas was genuinely
dirty every time (new glyphs rasterized per batch) — the cache was not falsely
missing. The waste was rebuilding all 4 MB for a few new glyph cells.

## After: repack only `batch.dirty_rects`

| metric | before | after |
|---|---|---|
| frame, 300x253 | 47,646 ms | **36,066 ms (-24.3%)** |
| font_atlas_pack | 19,012 ms | **7,823 ms** |
| font_composite | 27,348 ms | 16,208 ms |
| pack_full / pack_incremental | 5 / 0 | **2 / 3** |
| frame checksum | 325932497106919 | unchanged |
| PPM | — | **byte-identical (`cmp`)** |

cpu_simd control, same page/size/binary: **25,xxx ms** (see below). Vulkan went
from 2.7x that to 1.44x.

## Control and the honest gap

`cpu_simd` at 300x253 measured **25 s** (start 1789181280, end 1789181305).
Of the 36.1 s Vulkan frame, only ~16.5 s is inside the Vulkan backend; the
remaining ~19.6 s is layout/style, shared with cpu_simd. So the lane-specific
cost is ~16.5 s against roughly 6 s of cpu_simd painting.

**Target missed.** Reaching parity needs the two remaining O(atlas) walks gone:
`font_atlas_payload_sha256` 8.3 s and the 2 surviving full repacks 7.8 s.
Concrete next steps, neither taken here:
1. **Digest:** make it incremental over the same dirty cells (per-row
   fingerprint table, SHA-256 over the table). It changes digest VALUES, and
   ~10 spec files read this token, so it needs those specs run — not possible
   from this session's binary. Not attempted rather than attempted blind.
2. **Full repack:** `vulkan_sffi_copy_to_buffer_u32` uploads `[u32]` with no
   pack at all, but is opt-in because an older deployed binary aborts on the
   unknown extern (`typed_vulkan_upload_no_fallback_on_old_binary_2026-09-11.md`).

## Counter trustworthiness

The pooled-slot census (`dispatches_frame=1 submits=0 font_atlas_cpu_builds=0`
against 111 drawn rects) reads a backend instance that did not draw. Use the
module-global `vulkan_timing_*` / `vulkan_font_pack_*` counters instead.
