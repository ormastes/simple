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
| PPM | — | **byte-identical (`cmp`)** at 300x253 ONLY |

**Pixel equality holds at 300x253 and NOT at 900x760.** Do not read the row
above as a general claim. At 900x760 the frame checksum moves off the
no-mirror baseline `2936851417192293`, and three code variants gave two values
NON-monotonically with identical `pack_full=8 pack_incremental=13` throughout:

| variant | 900x760 checksum |
|---|---|
| no mirror (baseline) | 2936851417192293 |
| mirror, invalidate inside dirty branch | 2936851411469080 |
| + invalidate at function entry | 2936851404759230 |
| + require generation continuity (strictly stricter) | 2936851411469080 |

A strictly stricter variant returning to a looser variant's value, with the
pack counts never moving, is not explicable by the guard conditions. A repeat
run of one variant WAS byte-identical, so the render is deterministic for at
least that variant. The cause is under diagnosis with a mirror self-check
(`SIMPLE_VK_FONT_SELFCHECK=1`) that compares the mirror against a full pack of
the same atlas after every incremental repack and reports whether any
mismatching pixel lies inside a reported dirty rect.

cpu_simd control, same page/size/binary: **25,xxx ms** (see below). Vulkan went
from 2.7x that to 1.44x.

## 900x760: the dominant term is a DIFFERENT one

True before/after pair on this tree, same binary, one run at a time (the
"before" was produced by checking the two font files back to the
instrumentation-only commit, so the instrumentation is identical on both sides):

| bucket | before | after |
|---|---|---|
| frame | 863,307 ms | **789,177 ms (-8.6%)** |
| font_composite (23 calls) | 113,668 ms | **61,463 ms (-45.9%)** |
| font_atlas_pack | — | 29,095 ms (`pack_full=8 pack_incremental=13`) |
| **image_composite (264 calls)** | 568,149 ms | **544,646 ms** |
| rect (550) | 286,068 | 270,139 |
| image_blend (262) | 285,770 | 269,842 |

The font fix does what it does at both sizes (-46% of the font term), but at
900x760 **the font term was never the dominant one**: `_draw_image_composite_native`
is **544 s of a 789 s frame (69%)**, with a **max of 179,403 ms for a SINGLE
call**. Its SFFI upload is 237 ms across all 264 calls, so the cost is interpreted
host work inside the composite, not the GPU.

Nesting note for reading the table: `rect` ⊃ `image_blend` ⊃ `image_composite`.
`rect - image_blend` is 297 ms, so the alpha-rect `[color; w*h]` allocation is
NOT the term; and `image_composite - image_blend` is ~275 s, i.e. more than half
the composite time comes from callers other than the alpha-rect path.

**Not diagnosed further here, and deliberately not fixed.** One call doing 179 s
of work is ~70x a full-surface (684,000 px) interpreted pack at the rate the
atlas pack measures (3.7 us/px), so `_prepare_image_upload` alone does not
explain it. The untimed candidate that would is task suspect (d): a
`_draw_image_composite_native` early `return 0` falling back to
`emu_draw_image_blend` (`backend_emu_adv.spl:66`), which does a full
`core.read_pixels()` plus an interpreted per-pixel blend **without calling
`mark_cpu_fallback`** — which is why `cpu_fallback_reason` is empty and every
existing counter reads clean. Three probes would settle it in one run: wall time
+ `pixel_count` on `_prepare_image_upload`, a reason counter on every `return 0`
exit of `_draw_image_composite_native_impl`, and a timer on
`read_pixels_with_source()` itself (the `readback` bucket wraps only
`read_pixels()`, n=2, and would miss a core-level call).

## Control and the honest gap

`cpu_simd` at 300x253 measured **25 s** (start 1789181280, end 1789181305).
Of the 36.1 s Vulkan frame, only ~16.5 s is inside the Vulkan backend; the
remaining ~19.6 s is layout/style, shared with cpu_simd. So the lane-specific
cost is ~16.5 s against roughly 6 s of cpu_simd painting.

**Target missed, and the arithmetic says no incremental scheme reaches it.**
cpu_simd's 25 s is ~19.6 s shared layout/style plus ~5.4 s of its own painting.
Vulkan after is 19.6 s shared plus 16.5 s backend, so parity requires the Vulkan
backend to fit in ~5.4 s — i.e. never touching 1M atlas pixels at all. Only the
typed `[u32]` upload or a producer-supplied used-extent gets there; caching
does not.

Reaching parity needs the two remaining O(atlas) walks gone:
`font_atlas_payload_sha256` 8.3 s and the 2 surviving full repacks 7.8 s.
Concrete next steps, neither taken here:
1. **Digest:** make it incremental over the same dirty cells (per-row
   fingerprint table, SHA-256 over the table). It changes digest VALUES, and
   ~10 spec files read this token, so it needs those specs run — not possible
   from this session's binary. Not attempted rather than attempted blind.
2. **Full repack:** `vulkan_sffi_copy_to_buffer_u32` uploads `[u32]` with no
   pack at all, but is opt-in because an older deployed binary aborts on the
   unknown extern (`typed_vulkan_upload_no_fallback_on_old_binary_2026-09-11.md`).

## The unconditional style traces are already gone

F14 reported `[rfm]` / `[font-*-trace]` printing hundreds of lines per render
(815 `[rfm]` lines in 4,354). On `origin/main` @ `51ae2a9c4e3` they are all
level-gated already (`_WM_TRACE` in `text_layout/font_renderer.spl:2611+`,
`_font_style_trace_on` in `simple_web_html_layout_renderer_core.spl:2865`).
Measured on a full 300x253 Vulkan render here: `[rfm]` 0 lines,
`font-inherit-trace` 0, `font-style-trace` 0, whole log **401 lines**. Only
`[web-style-producer]` still prints unconditionally, at 5 lines per render —
not worth a gate. **No print-gating change was made**; the gap closed upstream.

## Counter trustworthiness

The pooled-slot census (`dispatches_frame=1 submits=0 font_atlas_cpu_builds=0`
against 111 drawn rects) reads a backend instance that did not draw. Use the
module-global `vulkan_timing_*` / `vulkan_font_pack_*` counters instead.
