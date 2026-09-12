# `font_composite` is two O(atlas) interpreted walks, and one of them is evidence

Date: 2026-09-12. Status: **digest FIXED; the second walk NAMED, not fixed.**
Lane: `SIMPLE_2D_BACKEND=vulkan SIMPLE_VK_READBACK=native
SIMPLE_2D_BACKEND_STRICT=1 SIMPLE_VK_TIMING=1 SIMPLE_EXECUTION_MODE=interpreter`,
binary `/Users/ormastes/simple/build/cargo-r2/release/simple`
(`stat -f '%z %m'` = `39368072 1789171430`).
Page: `examples/06_io/ui/web_catalog/css-layout.html` at 900x760.

Once the typed `[u32]` image upload took `image_composite` from 573,780 ms to
940 ms (`vulkan_image_composite_interpreted_pack_2026-09-12.md`),
`font_composite` became the dominant remaining term at **70,708 ms of a 259,523
ms frame — 27%**. This record attributes it and fixes the top item.

## Attribution: it is TWO buckets, and nothing else

From the F17 flag-ON run's per-op table, 900x760:

| bucket | n | total ms | share of font_composite |
|---|---|---|---|
| **font_composite** | 23 | **70,708** | 100% |
| **font_atlas_payload_sha256** | 21 | **37,650** | **53%** |
| **font_atlas_pack_u32_to_u8** | 21 | **32,672** | **46%** |
| font_atlas_sffi_upload | 21 | 211 | 0.3% |
| font_packed_params | 23 | 52 | 0.07% |
| font_quad_validate | 23 | 16 | 0.02% |
| font_owner_identity | 23 | 1 | 0.001% |

**The two walks are 99.3% of it.** Everything the task list anticipated as a
possible cost — per-run params packing, glyph quad packing, the descriptor and
params pool, per-run submit — sums to **280 ms**, 0.4%. That is a finding, not
an omission: a `SIMPLE_VK_FONT_UPLOAD=u32` typed lane for params and quads was
scoped and **deliberately not built**, because it would target 52 ms. The rect
and image lanes needed one; the font lane does not. Building it would have been
a week of opt-in-flag machinery for a quarter of a percent.

The atlas is a fixed **1024x1024 (4 MB)** whatever the glyph count, so each of
these walks is ~1M interpreted iterations regardless of how much text moved.

## Fix 1: the digest was restating what the generation counter already says

`font_atlas_payload_sha256` is **evidence**. Every consumer in the tree asserts
its SHAPE (`.len() == 64`, `lower_hex_sha256_valid`) or compares it across
samples for stability; **nothing reads it to decide whether to re-upload the
atlas**. That decision is made, and has always been made, by
`(atlas_generation, owner_identity)` — `_vulkan_font_upload_atlas` re-uploads
exactly when either changes. If that pair were not a sound content key, the
upload cache would already be painting stale glyphs.

So the digest spent 37,650 ms folding 1,048,576 pixels to restate a fact two
integers already carried. The default now folds the owner identity and the
generation with the same geometry, through the same seven-lane
`sha256_u8_hex` preimage — so the output is still 64 lowercase hex characters
and every existing evidence assertion holds unchanged — and
`SIMPLE_VK_FONT_DIGEST=payload` (implied by `SIMPLE_VK_FONT_SELFCHECK=1`)
restores the pixel walk for anyone auditing the generation counter itself.

Note what this is NOT: it is not a claim that a content digest is worthless. It
is a claim that this tree does not use it as one, and pays an O(atlas)
interpreted price per dirty upload for a token it only shape-checks.

## Fix 2 (NOT done): the 8 full atlas repacks

`font_atlas_dirty composites=23 gen_changed=21 identity_changed=8 dims_changed=1
pack_full=8 pack_incremental=13`.

F16 already made the mirror repack incrementally over `batch.dirty_rects`, which
is why 13 of the 21 packs are cheap. The remaining **8 full packs** are driven by
`identity_changed=8`: the page alternates between two font identities
(`sha256=a30418...;axes=wght=100` and `sha256=2cb2ad...;axes=wght=400,wdth=100`),
and the backend keeps **one** host mirror. Every flip invalidates it, forcing a
full 4 MB repack of an atlas whose contents did not change.

The fix is a **per-owner mirror** — keep one host mirror per atlas owner identity
rather than one globally — which would make the flips incremental like the rest.
It is not built here: it is a state-lifetime change (two 4 MB mirrors resident)
with its own eviction question, and it already has an oracle waiting for it in
`SIMPLE_VK_FONT_SELFCHECK=1`, which compares the mirror to a full pack after
every incremental repack (`checks=13 bad_calls=0 bad_bytes=0` at 900x760). This
is the named next term, recorded rather than approximated.

## Measured after the digest change

| bucket | n | before ms | after ms |
|---|---|---|---|
| **font_composite** | 23 | **70,708** | **29,419 (-58.4%)** |
| **font_atlas_payload_sha256** | 21 | **37,650** | **137 (-99.6%)** |
| font_atlas_pack_u32_to_u8 | 21 | 32,672 | 28,932 |
| font_atlas_sffi_upload | 21 | 211 | 175 |

At 300x253 the same bucket goes **8,234 ms -> 32 ms**, and the frame
**33,403 -> 20,678 ms**. That size is F16's deterministic oracle and its frame
checksum is **byte-identical** across the change (`-6077680819631676143`), so
the digest is pixel-neutral, not merely pixel-plausible.

`font_composite` is now essentially nothing but the 8 full repacks below:
28,932 of 29,419 ms is `font_atlas_pack_u32_to_u8`. The digest term is gone.

## Honest arithmetic on the 150 s target

The task set a Vulkan-lane target of **≤ 150 s cold at 900x760**. It is not
reachable by fixing `font_composite`, and saying so now is cheaper than
discovering it at the end:

| term | ms |
|---|---|
| F17 frame, typed image upload | 259,523 |
| − `font_atlas_payload_sha256` (this change) | −37,650 |
| − the 8 full repacks, IF the per-owner mirror were built | −~32,000 |
| **floor with both font fixes** | **~190,000** |

The residual is not Vulkan-side work at all. The document pipeline is ~29,451 ms
(`web_catalog_cold_render_profile_macos_2026-09-12.md`, of which the style
cascade alone is 25,229 ms) and the rest is the host rasterization that produces
the full-layout surface the presenter then uploads — the presenter at
`simple_web_html_engine2d_presenter.spl:597` rasterizes the page on the CPU and
uses the GPU as a pass-through. No amount of upload or composite work removes
it; removing it means not rasterizing on the host, which is a different and much
larger change. The cpu_simd bar on this page at this size is 263,636 ms, and the
Vulkan lane is already under it.

## Guard against regression

`test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_vulkan_font_atlas_digest_spec.spl`
— device-FREE (the digest is a pure function of its arguments, so requiring a
GPU would only make it skippable). Absolute oracles: 64 lowercase hex
characters, identical for identical inputs, and **different for a different
generation, a different owner, and different dimensions**, each checked
separately so a change that collapsed one input is not masked by another.

Sabotage: drop `generation` from the lane fold. "moves when the generation
moves" goes red and every other example stays green — which is what the
generation lane is for.
