# Blink `StyledLayout` → `PaintChunkRects` paint step — execution plan

Date: 2026-08-10
Source research: `doc/01_research/lib/blink/paint_pipeline_wiring_2026-08-10.md`
(commit `0f5b02e5e503`). Read it in full first — it carries the paint-type
census, exact struct shapes, and the reasons behind every scope cut below.

## Decision (from research, do not relitigate)

Target family 1b — `src/lib/common/ui/render_opt/paint_chunk_rasterizer.spl`'s
`PaintChunkRects` (flat `rect_x/rect_y/rect_w/rect_h: [i64]` + packed ARGB
`colour: [i64]`, `add_rect(x,y,w,h,argb) -> i64`), which already has a proven,
alias-safe consumer (`paint_chunk_rasterizer_run` → `ChunkRasterBuffer`,
spec-proven by `test/01_unit/lib/common/ui/render_opt/paint_chunk_rasterizer_spec.spl`).
Do NOT target `src/lib/blink/entity/paint_chunk.spl` / `paint_artifact.spl`
(family 1a) — zero consumers; it needs a `[DisplayItem]` list and property-tree
ids nothing in the cascade/layout lane produces.

Colour packing already lines up: `ComputedStyle.background_color: SkColor4f`
has `to_sk_color() -> i64` at `src/lib/skia/entity/color.spl:62-67`.

## Scope

IN: new `src/lib/blink/paint/style_paint.spl` with
`pub fn paint_chunks_from_styled_layout(layout: StyledLayout) -> PaintChunkRects`,
background-color rects only, index-parallel walk over
`layout.node_ids`/`layout.styles` with `layout.rect_for(node_id)` geometry
(`i` is an index, NOT a node id — never subscript by `node_ids[i]`). Plus its
spec. No pixels required for acceptance.

OUT (explicitly deferred, do not implement): borders; text/glyph rendering (no
font metrics in this lane); transparent-background skip-optimization (alpha=0
rects ARE emitted); z-order/stacking sort (flat document order); the
`PaintChunks`/`RenderRevisions` staleness wiring from `property_trees.spl`
(orthogonal damage-tracking layer — wire only when a caller needs incremental
re-paint); rects → actual pixels (research §5 names the path:
`ChunkRasterBuffer` sized to viewport, `paint_rect` per rect or an always-dirty
revision triple; the OPEN question there — whether engine2d's compositor can
import an externally-owned `[u32]` buffer — is NOT resolved; grep for a
buffer-import/blit-from entry point before assuming either way).

`ComputedStyle` resolves EXACTLY: `color`, `background_color`,
`margin_left/right/top/bottom`, `padding_left/top` (NOT right/bottom —
`style_bridge.spl:29`), `width`, `height`. Do not invent values for anything
else.

## Ordered steps (each with acceptance)

1. Read in full: `src/lib/blink/layout/style_bridge.spl`,
   `test/01_unit/lib/blink/render_lane_pipeline_spec.spl` (reuse its exact
   HTML/CSS-string→`StyledLayout` entry pattern),
   `src/lib/common/ui/render_opt/paint_chunk_rasterizer.spl` (re-verify
   `PaintChunkRects.add_rect` signature and the exact `use` import string —
   the research doc is a snapshot), `src/lib/skia/entity/color.spl`
   (`to_sk_color`, `sk_color_argb` signatures). Acceptance: signatures match
   research §1b/§3; if `add_rect` differs, STOP and file a bug — do not modify
   the shared rasterizer to fit.
2. Create `src/lib/blink/paint/style_paint.spl` (new dir, sibling of
   `layout/`/`style/`/`entity/`) per research §4 pseudocode. Handle `f64→i64`
   casts explicitly (`.to_i64()`); check whether block_flow can yield negative
   coordinates (should not, but confirm — see
   `doc/08_tracking/bug/paint_rect_negative_x_row_bleed_2026-08-07.md` for the
   historical bug class). Acceptance: lint clean
   (`sh scripts/check/lint-cached.shs`, ONE file at a time — lint is
   superlinear per function).
3. Create `test/01_unit/lib/blink/paint/style_paint_spec.spl` with research
   §4's assertions: (a) one `<div>` `background-color: red; width:100px;
   height:50px; margin:10px` → `rect_count == 1`, `rect_x/rect_y` equal
   `rect_for`'s laid-out left/top (reuse the numbers
   `render_lane_pipeline_spec.spl` already proves — do not recompute margins),
   `rect_w == 100`, `rect_h == 50`, `colour[0] == sk_color_argb(255,255,0,0)`
   (helper as oracle, not a hand-packed literal); (b) `display:none` child
   contributes NO rect; (c) unset background (default transparent
   `sk_color4f(0,0,0,0)`) still emits a rect with `colour == 0`. Oracle-quality
   rule: no substring/tautology oracles; assert on the actual array contents.
4. Run `bin/simple test test/01_unit/lib/blink/paint/style_paint_spec.spl` —
   RELATIVE path (an absolute path runs nothing and exits 0 — known trap).
   No build step needed: `src/lib/**` is read as source every run.
   Acceptance: spec green; `render_lane_pipeline_spec.spl` still 7/7.
5. Land via the plumbing protocol (vcs.md), scoped to exactly the two new
   files. Blob-verify at the fetched tip.

## Dependencies / parallelism

This lane is INDEPENDENT of the SimpleOS WM rung-(d) minimum path: that path's
chrome-only degraded first frame bypasses content painting entirely (empty
`[WmContentFrame]`), so neither track blocks the other. This lane only feeds
the LATER "real fix + content frames" work (Track W2 in
`doc/03_plan/sys_test/simpleos_qemu_wm_real_screen.md` § 2026-08-10) and the
future rects→pixels step (§5 of the research doc).

## Traps carried forward

- `simple test` with an absolute path runs nothing, exit 0.
- Do not batch files into one lint invocation.
- `grep` on PATH is wrapped ugrep honouring .gitignore; control-check zeros
  with `/usr/bin/grep`.
- Do NOT touch `paint_chunk_rasterizer.spl` / `property_trees.spl` /
  `revisions.spl` — they are the input contract.
