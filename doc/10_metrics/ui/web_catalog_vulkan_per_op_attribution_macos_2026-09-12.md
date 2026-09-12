# Vulkan lane per-op attribution, css-layout.html (macOS M4, 2026-09-12)

Binary bracketed identical every run: `build/cargo-r2/release/simple`,
`stat -f '%z %m'` = `39368072 1789171430`. `SIMPLE_2D_BACKEND=vulkan
SIMPLE_VK_READBACK=native SIMPLE_2D_BACKEND_STRICT=1 SIMPLE_VK_TIMING=1
SIMPLE_EXECUTION_MODE=interpreter`, one at a time (serial: concurrent runs
contend for the same GPU). Page `css-layout.html`; logs gitignored.

## 300x253 — where the frame goes (ms)
| bucket | n | before | after |
|---|---|---|---|
| **font_atlas_pack_u32_to_u8** | 5 | **19,012** | **7,433** |
| font_atlas_payload_sha256 | 5 | 8,234 | 8,308 |
| font_composite (total) | 5 | 27,348 | 15,669 |
| **frame** | | **47,646** | **35,389 (-25.7%)** |

The atlas is a fixed **1024x1024 (4 MB)** whatever the glyph count, so each
pack/digest is ~1M interpreted iterations, and it was genuinely dirty every time
(generations `2 3 4 6 7` ascend) — the waste was rebuilding 4 MB for a few new
cells, not a falsely-missing cache. Fix: mirror repacked only over
`batch.dirty_rects` (`pack_full=2 pack_incremental=3`); PPM byte-identical.

## 900x760 — a DIFFERENT dominant term

| bucket | n | before | after |
|---|---|---|---|
| frame | | 863,307 | **789,177 (-8.6%)** |
| font_composite | 23 | 113,668 | **61,463 (-45.9%)** |
| **image_composite** | 264 | 568,149 | **544,646** |
| rect / image_blend | 550/262 | 286,068 | 270,139 |

`image_composite` is **69% of the frame** and its SFFI upload is 237 ms across
all 264 calls, so the cost is interpreted host work.

Those probes were built and run (2026-09-12, same binary). **The sub-step is no
longer unmeasured, and the fallback hypothesis is excluded:** `reasons: ok=264`
— every composite took the device path, none fell to `emu_draw_image_*`. The
cost is host packing, and it is paid **twice** per composite: 391,259 ms in
`image_pack_u32_to_u8` plus 180,995 ms in `image_exact_size_byte_fallback`,
which fires 262 of 264 times because `vulkan_sffi_copy_to_buffer_prefix`
(`sffi_vulkan.spl:1279`) admits a prefix on the interpreter ABI only when
`byte_count == data.len()`, and the scratch is never shrunk. Device work is
1.3 s total (alloc 315, dispatch 94, upload 907). `max_px=12,874,224` — the
largest source is 18.8x the surface.

Routing the upload through `vulkan_sffi_copy_to_buffer_u32`
(`SIMPLE_VK_IMAGE_UPLOAD=u32`, opt-in) skips both packs, since `pixels` is
already `[u32]`:

| bucket | n | before | after |
|---|---|---|---|
| **frame 900x760** | | **830,186** | **259,523 (-68.7%)** |
| image_composite | 264 | 573,780 | **940** |
| both pack buckets | 264/262 | 572,254 | **0 (never fire)** |
| font_composite | 23 | 68,745 | 70,708 |

**Target MET: 259,523 ms vs the 263,636 ms cpu_simd bar.** PPM **byte-identical**
at BOTH sizes (`cmp` clean; 300x253 is the deterministic oracle, the 900x760
pair also matched but F16 means a future difference there is noise, not
evidence). `upload_reason=typed-requested` confirms the typed lane ran — the two
lanes write identical bytes, so no pixel can witness it. 300x253 is unchanged
(30,861 -> 33,403 ms, noise): all 76 composites there are 1x1, nothing to pack.
Origin: `simple_web_html_engine2d_presenter.spl:597` uploads a host-rasterized
full layout surface and reads it straight back (NOT an eliminable identity
blit) — but that only explains the 684k-px class; the 12.87M-px source is a
scaled/synthesized draw at `draw_ir_adv.spl:2263/2289/2291`, not pinned further.
`font_composite` is now the dominant term. No upload cache: no O(1) array
identity or producer generation exists, and an interpreted digest is the same
O(n) class as the pack (`font_atlas_payload_sha256` = 8.3 s). Detail:
`doc/08_tracking/bug/vulkan_image_composite_interpreted_pack_2026-09-12.md`.

## Correctness oracle
`SIMPLE_VK_FONT_SELFCHECK=1` compares the mirror to a full pack after every
incremental repack: `checks=13 bad_calls=0 bad_bytes=0` at 900x760. **Do not
rely on the 900x760 frame checksum** — F16 records the page as
non-deterministic there; use 300x253 for a byte oracle.

**Target: MET at 900x760, still missed at 300x253.** The typed `[u32]` upload
was the predicted fix and it landed; caching, as predicted, was not needed and
is not implemented. At 300x253 the backend is font-bound (~16.5 s vs the ~5.4 s
parity budget), and the remaining O(atlas) walks — digest 8.3 s, 2 full repacks
7.4 s — are unchanged by this work.

Pooled-slot counters (`dispatches_frame=1 submits=0` vs 111 drawn rects) read a
backend that did not draw — use the module-global `vulkan_timing_*` /
`vulkan_font_pack_*`.
