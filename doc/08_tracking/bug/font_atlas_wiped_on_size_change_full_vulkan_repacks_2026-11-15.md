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
change (face, hinting, antialiasing, atlas policy, ...) still wipes.

## Evidence

- Spec `test/01_unit/lib/nogc_sync_mut/text_layout/font_atlas_size_switch_retention_spec.spl`:
  red at base (returning to 16 px re-inserted 2 cells, owner sequence jumped
  `6 != 4`; with only the producer half, the owner identities differed by
  `size=13` vs `size=16`), 3/3 green.
- forms-media 900x760 vulkan, same seed (59635056 B, mtime 1794616340), 3 runs
  each, load 13-15: `pack_full` 12 -> 3 (one per owner), incremental 9 -> 17,
  pixel sum `2697697746427296` identical, maxrss 2.56-2.59 GB -> 2.10-2.12 GB.
  Wall 15.0/15.9/17.7 s -> 22.4/16.7/19.4 s: inside the host-load noise, no
  wall claim.
- Unchanged pre-existing reds on the same base: `shared_font_surfaces_spec`
  4/6 (`method identity not found on FontRenderConfig`,
  `cache_identity_snapshot not found on FontRasterizer`), `font_renderer_spec`
  hits the 900 s worker budget.
