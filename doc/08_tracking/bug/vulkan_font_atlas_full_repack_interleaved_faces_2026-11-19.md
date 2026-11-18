# Vulkan font atlas is fully repacked on every run when two faces interleave

Status: RESOLVED 2026-11-19 on the producer side (see "Resolution" below). Found by
the Vulkan LCD batching lane; the producer lives in `text_layout/font_renderer.spl`.

## Measured (2026-11-19, lavapipe, seed `cargo-target-webrender-blend`)

900x760 page, 36 paragraphs alternating sans / serif (regular, bold, italic) /
monospace, one cold render, `SIMPLE_VK_TIMING=1`:

| lane | wall | `font_atlas_pack_u32_to_u8` | pack_full / incremental |
|---|---|---|---|
| cpu_simd | 29.9 s | - | - |
| Vulkan, default byte upload | 308.2 s | 286.6 s (60 calls, ~5 s each) | 60 / 0 |
| Vulkan, `SIMPLE_VK_FONT_UPLOAD=u32` | 24.2 s | 0 | 0 / 0 |

All three frames are byte-equal. Vulkan with the default upload is 10x slower
than the CPU backend, and all of it is the interpreted 1,048,576-pixel
`_vulkan_font_pixels_to_bytes` loop.

## Cause

`vulkan_font_mirror_continuity` (`backend_vulkan_helpers.spl`) allows the
incremental repack only when `batch.atlas_owner_sequence == host + 1`. With
`SIMPLE_VK_ORDER_TRACE=1` on a two-face page (sans and serif paragraphs
alternating, 3 each):

```
owner=Sans-Regular  slot_seq=6  host_seq_before=6  batch_seq=8  continuity=0 dirty=2
owner=Serif-Regular slot_seq=10 host_seq_before=10 batch_seq=12 continuity=0 dirty=2
owner=Sans-Regular  slot_seq=8  host_seq_before=8  batch_seq=10 continuity=0 dirty=2
```

The per-owner sequence moves by 2 between two batches of the same owner as soon
as another face draws in between, so the rule never holds and every run takes
`VK_FONT_MIRROR_FULL` (`pack_full=6 pack_incremental=0`). A one-face page moves
by 1 and repacks incrementally (`continuity=1`). Raising
`VULKAN_FONT_ATLAS_MIRROR_MAX` 4 -> 8 changes nothing (tried: 308.6 s, 60 / 0).

## Fix directions (not done)

1. Find what bumps `atlas_owner_sequence` a second time when faces interleave
   (producer side), so one dirty batch is one step again.
2. Or make the typed upload (`SIMPLE_VK_FONT_UPLOAD=u32`) the default where
   `vulkan_sffi_copy_to_buffer_u32_admitted()` holds; it has no host pack at all.

Do not relax the `+1` rule on the consumer side: a gap can also mean a dirty
batch that never reached the backend, whose cells the mirror would be missing.

## Resolution (2026-11-19)

Two producer defects, both in `text_layout/font_renderer.spl`. Neither needed
faces to interleave in the way the title says; the `+1` rule on the consumer is
unchanged.

1. **One staged batch stepped the owner sequence more than once.** An LCD run
   publishes dirty cells from up to three passes: the staging pass, the phase
   cells of `_lcd_apply_pen_phases` and the phase-0 cells of
   `_lcd_resolve_deferred_cells`. `_lcd_publish_cells` stepped
   `atlas_owner_sequence` on each call, so a run that added both a phased and a
   phase-0 cell read `host + 2` (the `slot_seq=6 batch_seq=8` of the trace
   above) and was repacked in full. This happens on a one-face page too: twelve
   sizes of Liberation Sans took 12 full packs. `_lcd_publish_cells` now steps
   only when the staged batch has not taken its step yet; later passes add
   their rects to the same step.
2. **The park list held 4 atlases.** With the active one that is five owners.
   A page that cycles through more faces evicted an owner before its turn came
   round, so each return was a wipe: a re-seeded sequence, every glyph inserted
   again, and a full pack. `FONT_ATLAS_PARK_MAX` is 11 (12 owners: three
   generic families in four styles), and `VULKAN_FONT_ATLAS_MIRROR_MAX`
   follows it, because an owner the consumer dropped repacks in full as well.

Measured on lavapipe, seed `cargo-target-webrender-blend`, interpreter lane, one
cold render, base = `30746014ea2`. Wall, then `pack_full / pack_incremental`,
then seconds in `font_atlas_pack_u32_to_u8`:

| page | cpu_simd | Vulkan base | Vulkan head |
|---|---|---|---|
| 12 sizes, one face, 520x340 | 11.5 s | 71.8 s, 12 / 0, 62.1 s | 15.1 s, 1 / 11, 5.1 s |
| 27 paragraphs, nine faces, new glyphs each round, 900x600 | 18.2 s | 152.2 s, 27 / 0, 132.3 s | 66.2 s, 9 / 18, 47.8 s |
| 36 paragraphs, nine faces, 900x760 | 38.5 s | 211.0 s, 36 / 0, 176.6 s | 83.4 s, 9 / 27, 52.6 s |
| catalog `html`, 900x760 | 44.9 s | 108.1 s, 17 / 7, 89.2 s | 42.9 s, 4 / 20, 23.4 s |
| two faces, 3 paragraphs each, 520x200 | 6.0 s | 14.4 s, 2 / 4, 10.7 s | 14.7 s, 2 / 4, 10.9 s |

Vulkan base and Vulkan head are byte-equal on all five pages, and equal to
cpu_simd on the four text pages. Catalog `html` differs between cpu_simd and
Vulkan in the same way on base and head.

## Still open

The first batch of every owner is a full pack of 1,048,576 pixels, about 5 s
in the interpreted `_vulkan_font_pixels_to_bytes` loop: 9 of them are about 44 s of
the 83 s nine-face render. The atlas is all zero outside that batch's dirty
cells, but the consumer has no published fact to rest that on. Either the
producer publishes "fresh atlas, these are all of its cells" or the typed
upload (`SIMPLE_VK_FONT_UPLOAD=u32`, no host pack) becomes the default.
