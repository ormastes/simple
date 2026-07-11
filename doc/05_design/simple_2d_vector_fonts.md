<!-- codex-design -->
# Simple 2D Vector Fonts Detail Design

No TUI/GUI control design is needed; this changes raster output behind the existing drawing API.

## Surface and State

Public: `Engine2D.load_font(path) -> bool`, `unload_font()`, existing `draw_text`, `font_cache_stats() -> FontCacheStats`. `FontCacheStats` reports entries, bytes, native generation, hits, misses, rasterizations, and evictions. Each engine owns a lazy optional renderer/cache; the native `spl_fonts` face remains process-global until per-face handles exist.

## Algorithms

Load rejects empty paths, marshals local paths as owned UTF-8 bytes, tries existing dylib candidates, and replaces state only after success. Successful native initialization increments generation; wrapper replacement closes the prior handle and invalidates entries/bytes without counting invalidation as eviction.

Glyph lookup validates input, synchronizes native generation, checks cache, then queries glyph presence only on a miss. A miss rasterizes once into an owned native snapshot, bulk-copies alpha bytes, and frees the snapshot. Cache evicts oldest until both 512 entries and 32 MiB fit.

Text layout rejects sizes outside 1..512 before native work, scans positioned ink bounds once, allocates one transparent payload, and composites cached grayscale coverage into straight-alpha ARGB. Engine2D blends once through `RenderBackend`; SoftwareBackend mutates its framebuffer directly while GPU emulation lanes may still read a full frame. Empty text is a valid empty result; owner/layout failure falls back to bitmap. Unload and shutdown clear the glyph cache, close the selected wrapper, and restore the nil bitmap fast path.

The selected design intentionally retains one process-global face/layout slot.
It supports serialized selection and drawing, not concurrent distinct faces;
owned native face/layout handles are deferred until that capability is selected.

## Fixtures and Evidence

Two tracked 400-byte dual MIT/Apache-2.0 derivative TTF byte fixtures provide distinct ASCII and Latin-1 cmap lanes without host fonts. Tests materialize them via the file facade.

Use 31 paired public `Engine2D` cold/warm samples, excluding load/clear/readback/RSS from timing. Require 100% warm glyph hits, zero warm rerasterization, and warm p50 <=75% cold p50; record p95/framebuffer checksum/backend/RSS. Run the unchanged bitmap-only probe in detached pre-feature and current trees on the same pinned host; require identical checksum and <=5% p50 regression.

## Requirement Traceability

- Load/lifecycle/UTF-8 path and interpreter boundary: REQ-001, REQ-005, REQ-007, REQ-009; NFR-006, NFR-009.
- Layout/raster/fallback/manual oracles: REQ-002 through REQ-004, REQ-010; NFR-007, NFR-008.
- Cache and retained performance evidence: REQ-006, REQ-008; NFR-001 through NFR-005.
