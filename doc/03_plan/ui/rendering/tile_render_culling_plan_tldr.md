# Tile Render Culling Plan — TLDR

```
T1 tile core     → 256px document-space grid; bin DrawIrCommands per tile
                 → drop hidden/zero-area ops at bin time; FNV checksum/tile
                 → new paint_tiles.spl (pure fns, shared by both lanes)
T2 cpu lane      → paint_tiled(): raster only live tiles (viewport+512px
                   margin), clip = tile ∩ ancestor ClipRect
                 → scroll = row memmove + raster newly exposed tiles only
                 → flag SIMPLE_WEB_TILE_PAINT (default off, byte-identical)
T3 occlusion     → later full-tile-covering opaque op culls all earlier
                   ops in that tile (conservative; region-union = follow-up)
T4 gpu lane      → per-tile active_clip loop around
                   _engine2d_draw_ir_render_commands (draw_ir_adv.spl:1232)
                 → Vulkan scissor via clip state; skip culled tiles entirely
                 → tile texture cache keyed (tile, checksum); PaintOnly
                   damage routed to tile dirty marks (today dropped)
T5 perf gate     → fixture: K× viewport-height doc, 80/95% offscreen,
                   0/30/70% occluded, 60-step scroll sweep
                 → measure ops-painted / bytes-rastered / wall time
                 → DECISION RULE: GPU tiled ≤ ½ CPU tiled wall time on
                   K=20 ⇒ GPU tiled becomes the DEFAULT lane (CPU =
                   fallback + oracle); else CPU default, GPU opt-in
```

Gates: pixel-identical visible region vs non-tiled (blocking); flag-off
byte-identical until promotion (webrender_gpu_offload_plan convention);
K=20/M=70 fixture must hit ops ≤30% / bytes ≤25% of baseline; fully
visible page overhead ≤110%; tile core ≥95% coverage.

Insertion points: op producer `paint_layout.spl:1440`
(`_html_draw_ir_command`); CPU sibling of `paint()` `paint_layout.spl:629`;
GPU loop `draw_ir_adv.spl:1232` (`active_clip`); Vulkan scissor
`backend_vulkan.spl:205`; damage feed `gpu_web/layout/invalidation.spl:53`
(`StyleDifference.PaintOnly` no-op). Existing 64×64 SoftwareBackend dirty
tiles (present-copy) stay separate from the 256px document grid.

Open: fixed/sticky content = unbinned always-repaint class; document-space
ops need the pre-scroll boxes; glyphs crossing tile edges rely on
clip-correct text raster; DrawIR v3 schema untouched until promotion.
