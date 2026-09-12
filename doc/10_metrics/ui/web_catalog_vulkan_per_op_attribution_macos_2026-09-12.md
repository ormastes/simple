# Vulkan lane per-op attribution, css-layout.html (macOS M4, 2026-09-12)

Binary bracketed identical every run: `build/cargo-r2/release/simple`,
`stat -f '%z %m'` = `39368072 1789171430`. `SIMPLE_2D_BACKEND=vulkan
SIMPLE_VK_READBACK=native SIMPLE_2D_BACKEND_STRICT=1 SIMPLE_VK_TIMING=1
SIMPLE_EXECUTION_MODE=interpreter`, one at a time. Page `css-layout.html`;
logs `build/perf/vk_attr_2026-09-12/` (gitignored).

## 300x253 — where the frame goes (ms)
| bucket | n | before | after |
|---|---|---|---|
| **font_atlas_pack_u32_to_u8** | 5 | **19,012** | **7,433** |
| font_atlas_payload_sha256 | 5 | 8,234 | 8,308 |
| font_composite (total) | 5 | 27,348 | 15,669 |
| rect (all 187 dispatches) / image_composite (76 1x1) | | 244 | 242 |
| enqueue + whole SFFI bind/push/dispatch chain | 112 | 25 | 25 |
| **frame** | | **47,646** | **35,389 (-25.7%)** |

The atlas is a fixed **1024x1024 (4 MB)** whatever the glyph count, so each
pack/digest is ~1M interpreted iterations; it was genuinely dirty every time
(generations `2 3 4 6 7` ascend), so the waste was rebuilding 4 MB for a few new
cells, not a falsely-missing cache. Fix: host byte mirror repacked only over
`batch.dirty_rects` (`pack_full=2 pack_incremental=3`); PPM **byte-identical**,
checksum `325932497106919` unchanged. `font_atlas_sffi_upload` is 44 ms total.

## 900x760 — a DIFFERENT dominant term

True pair on this tree (before = font files checked back to the
instrumentation-only commit, so instrumentation matches both sides):

| bucket | n | before | after |
|---|---|---|---|
| frame | | 863,307 | **789,177 (-8.6%)** |
| font_composite | 23 | 113,668 | **61,463 (-45.9%)** |
| **image_composite** | 264 | 568,149 | **544,646** |
| rect / image_blend | 550/262 | 286,068 | 270,139 |

`image_composite` is **69% of the frame**; its SFFI upload is 237 ms across all
264 calls, so the cost is interpreted host work. It splits in two, needing
different fixes: **~443 s in 3 full-surface composites** (max single call
179,403 ms; `image_composite - image_blend` = 274,804 ms over 2 calls, plus one
168 s alpha rect) — **sub-step UNMEASURED**; and **~102 s across the other 261
small composites (~0.2-0.4 s each)**, the population F14 targeted, real here.

Three probes settle the first half in one run: wall + `pixel_count` on
`_prepare_image_upload` (its `self.image_upload_scratch[...]` class-field writes
are the unverified suspect); a reason counter on each `return 0` of
`_draw_image_composite_native_impl`; a timer on `read_pixels_with_source()` —
the `readback` bucket wraps only `read_pixels()` (n=2) and misses the
`emu_draw_image_blend` fallback, which does a full `core.read_pixels()`
**without `mark_cpu_fallback`**, so every existing counter reads clean.

## Correctness oracle, and the target
Pixel safety comes from `SIMPLE_VK_FONT_SELFCHECK=1`, comparing the mirror to a
full pack of the same atlas after every incremental repack: `checks=13
bad_calls=0 bad_bytes=0` at 900x760. **Do not use the 900x760 frame checksum** —
the page renders non-deterministically there (see
`web_catalog_900x760_frame_checksum_nondeterministic_2026-09-12.md`).

**Target missed at both sizes.** cpu_simd at 300x253 is 25 s = ~19.6 s shared
layout + ~5.4 s painting; Vulkan after is 19.6 + 16.5 s backend, so parity needs
the backend under 5.4 s — never walking 1M atlas pixels. Only the typed `[u32]`
upload (`vulkan_sffi_copy_to_buffer_u32`, opt-in since older binaries abort on
the extern) or a producer-supplied used-extent reaches that; caching does not.
Remaining O(atlas) walks: digest 8.3 s, 2 full repacks 7.4 s.

Pooled-slot counters (`dispatches_frame=1 submits=0` vs 111 drawn rects) read a
backend that did not draw — use the module-global `vulkan_timing_*` /
`vulkan_font_pack_*`. F14's `[rfm]`/`[font-*-trace]` noise is already level-gated
on `origin/main` (0 lines; whole log 401); no gate change made.
