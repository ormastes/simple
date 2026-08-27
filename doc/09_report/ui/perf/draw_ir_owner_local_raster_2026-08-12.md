# DrawIR owner-local raster evidence — 2026-08-12

Status: **CORRECTNESS PASS / STRUCTURAL SPEEDUP / 8K80 NOT PROVEN**

The standalone paint-chunk rasterizer previously built a fresh dirty-index
array in one full chunk scan, then called `paint_chunks_raster` for a second
full scan. That delegated gate also compared every chunk against a scene-wide
paint revision sum, so one owner's paint mutation rebuilt the whole scene.

`paint_chunk_rasterizer_run` now decides staleness, updates retained keys,
records receipts, and paints in one pass with no dirty-index allocation.
Paint/clip/resource mutations use the same per-owner `RenderRevisions` flags as
canonical DrawIR delta. Property-tree, component, theme, scale, viewport and
capability keys remain global where the existing data model requires it.

Focused coverage passed: a one-owner paint mutation repainted exactly one
100-pixel chunk, skipped two, changed exactly its pixel band, and preserved the
other bands byte-for-byte. After clearing frame dirty flags, the settled frame
rastered zero chunks and zero bytes. Initial-frame and newly-added-chunk parity
coverage also remained green.

O3 analysis completed with 31 further opportunities. This proves single-pass,
damage-proportional behavior for the standalone rasterizer, not an end-to-end
7680x4320 timing row; no 8K/80 claim is made.
