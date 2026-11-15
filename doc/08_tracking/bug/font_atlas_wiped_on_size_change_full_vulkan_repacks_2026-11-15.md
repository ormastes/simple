# Font atlas wiped on every text-size change -> full Vulkan atlas repacks

Status: FIXED 2026-11-15 on `work/engine2d-parity-3-20261115`.

## Symptom

900x760 `forms-media` catalog page on the Vulkan lane (llvmpipe): 12 full
1,048,576-pixel host atlas repacks (`font_atlas_pack_u32_to_u8`) for only 3
font owners (Liberation Sans 16/13, Liberation Sans Bold 24, DejaVu Sans Mono).

## Root cause (two halves)

1. Producer: `FontRenderer._activate_render_config` reset the whole glyph atlas
   whenever the render-config identity changed, and that identity carries
   `size=`. Atlas cells are already keyed by size (`_font_atlas_entry_index`),
   so a 16 px -> 13 px -> 16 px sequence threw away and re-rasterised every
   glyph. The wipe also re-keyed the active owner, so its parked atlas
   (`_switch_font_atlas`) was stored under a key the next switch never looked
   up: `SIMPLE_FONT_ATLAS_TRACE=1` showed `reset` where `restore` was due.
2. Consumer: `font_render_batch_atlas_owner_identity` embedded the full config
   identity (with `size=`), so the Vulkan per-owner mirror treated Regular 16 and
   Regular 13 as two owners of what is one atlas. Their shared owner sequence
   then always looked non-contiguous (`host_seq=6 batch_seq=8`) -> full repack.

## Fix

`font_render_config_identity_sizeless` (font_types.spl) masks `|size=N|`; the
atlas wipe decision and the atlas owner identity both use it. Any other config
change (face, hinting, antialiasing, atlas policy, ...) still wipes. The owner
identity keeps its length-prefixed form over the sizeless text
(`|config=<len>:<sizeless>`).

## Capacity (no size wipe means one atlas holds every size)

Overflow is already handled: each prepare loop (`while attempt < 2` in
`font_renderer.spl`) calls `_reset_font_atlas` on a failed insert and re-inserts
the whole run into the empty atlas. The reset re-seeds `atlas_owner_sequence`
from the global counter, so the Vulkan mirror sees a gap and takes a full
upload. Pinned by:

- `font_atlas_size_switch_retention_spec` overflow row: 16 px run, cursor parked
  at the bottom edge, 13 px run -> atlas holds 2 cells from (0,0), sequence not
  contiguous, owner unchanged; the 16 px cells come back with a contiguous +1;
  every cell's coverage equals a fresh renderer's.
- `vulkan_font_atlas_overflow_parity_spec` (llvmpipe): 0 mismatches vs the
  software lane across the rebuild, in separate flushes and inside one flush.
  Mutation check: with the reset NOT re-seeding the sequence, the one-flush row
  fails with 69 mismatched pixels (the earlier recorded run reads the rebuilt
  cell).
- Parking the cursor stands in for real fill: driving 1M atlas pixels with
  300-512 px glyphs hit the 900 s spec budget in the interpreter.

## Evidence

- Spec `test/01_unit/lib/nogc_sync_mut/text_layout/font_atlas_size_switch_retention_spec.spl`:
  red at base (returning to 16 px re-inserted 2 cells, owner sequence jumped
  `6 != 4`; with only the producer half, the owner identities differed by
  `size=13` vs `size=16`), 4/4 green with the overflow row.
- forms-media 900x760 vulkan, same seed (59635056 B, mtime 1794616340), 3 runs
  each, load 13-15: `pack_full` 12 -> 3 (one per owner), incremental 9 -> 17,
  pixel sum `2697697746427296` identical, maxrss 2.56-2.59 GB -> 2.10-2.12 GB.
  Interleaved A,B x3 under the seed lock, load 4.2-4.9: A 13.03/12.65/12.61 s,
  B 10.96/11.24/11.39 s (median 12.65 -> 11.24 s); `font_composite`
  2.9-3.3 s -> 1.6-2.1 s, `font_atlas_pack_u32_to_u8` 1.2-1.5 s -> 0.16-0.33 s.
  The earlier non-interleaved 22.4/16.7/19.4 s was host-load noise (load 13-15).
- Unchanged pre-existing reds on the same base: `shared_font_surfaces_spec`
  4/6 (`method identity not found on FontRenderConfig`,
  `cache_identity_snapshot not found on FontRasterizer`), `font_renderer_spec`
  hits the 900 s worker budget.
