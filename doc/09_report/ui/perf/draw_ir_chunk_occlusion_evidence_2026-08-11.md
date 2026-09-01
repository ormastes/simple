# DrawIR chunk occlusion evidence — 2026-08-11

Status: MECHANISM AND WEB TILE CONSUMER VERIFIED; 8K PERF OPEN.

The shared `common.ui.render_opt` lane now provides conservative paint-chunk
occlusion without changing DrawIR or introducing WebIR/GuiIR. The optimizer
scans chunks in reverse paint order and proves full coverage by exact bounded
rectangle subtraction against later same-surface chunks carrying an explicit
`CHUNK_OPAQUE_EXACT_RECT` proof.

Unknown opacity, different render surfaces, partial coverage, and workspace
exhaustion never cull content. Fixed preallocated flat arrays bound memory and
capacity exhaustion records an overflow receipt, fails the candidate open, and
disables further earlier culls for that preparation pass. Hidden, zero-area,
and off-viewport chunks are rejected independently.

Focused interpreter evidence:

- spec: `test/01_unit/lib/common/ui/render_opt/chunk_occlusion_spec.spl`
- result: 4 examples, 0 failures
- exact union coverage: lower 4x4 chunk removed by two later 2x4 opaque chunks
- parity: optimized replay equals complete uncullled replay pixel-for-pixel
- sabotage: uncertain alpha and cross-surface coverage cull nothing
- overflow: one-rectangle workspace records overflow and retains both chunks

The in-repo optimizer reported 43 opportunities (33 bounds-check elimination,
4 strength reduction, 3 dead-code elimination, and 3 loop-invariant motion).
The source already uses a reusable caller-owned workspace and performs no
steady-state array allocation.

## Production tiled DrawIR consumer

The production Web tile lane calls `engine2d_draw_ir_render_tiled`. That
executor now scans each tile's paint-order bin backward for a later unstyled,
fully opaque solid rectangle whose command bounds and optional command clip
cover the complete active tile. It starts replay at that exact barrier and
reports the omitted prefix as `ops_occluded`. Translucent, styled, partially
clipped, invalid, and unknown commands remain fail-open.

The integration exposed and fixed a ragged-edge adapter defect: the Web GPU
tile owner passed nominal 256x256 rectangles even when the grid's right or
bottom edge was smaller. It now clips tile width/height to the document bounds,
so a true 8K full-viewport fill can cover the final 256x224 tile.

Focused evidence:

- tiled executor spec: 6 examples, 0 failures;
- Web software/Vulkan-requested lane spec: 1 example, 0 failures;
- both lanes report one occluded command and one rendered command;
- complete 128x128 pixel buffers match exactly.

The tiled executor no longer allocates and fills a temporary
`[DrawIrCommand]` for every live tile. It replays each tile's existing
counting-sort index span directly against the canonical command array. A
preflight validates geometry column lengths, monotonic start offsets, exact
item coverage, positive live-tile extents, and every command index before any
raster or submission. New two-tile parity evidence renders 2 optimized
operations versus 4 for the uncullled oracle with identical complete pixels;
malformed indices fail closed with zero raster.

The pre-change broad paint-chunk spec did not execute because dependency
compilation hit the repository's 60-second CPU guard. No 7680x4320 p50/p95,
RSS, device provenance/fallback, or checksum row was produced. Therefore this
evidence does not prove DrawIR, WebRenderer, GUI, or WM at 8K/80.

## 8K software benchmark attempt

`bench_draw_ir_tiled_occlusion_8k.spl` compares identical 7680x4320 scenes in
the same production executor, changing only the opaque-barrier enable bit. It
uses 510 exact tiles (including the 256x224 ragged bottom row), complete host
readback, operation receipts, RSS, and full-buffer checksum parity.

Five-frame, three-frame, and one-frame attempts each exceeded the 180-second
watchdog before emitting a row. The mandatory three-cycle cap is exhausted.
This is a concrete failure to prove 8K/80, not a pass or a measured percentile.
The blocker and split-process acceptance criteria are recorded in
`doc/08_tracking/bug/draw_ir_tiled_8k_software_timeout_2026-08-11.md`.
The benchmark was not rerun after indexed replay landed because that
three-cycle cap remains binding; a fresh scoped evidence session must produce
the next timing row.
