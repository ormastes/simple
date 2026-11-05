# Simple Web Text Decoration Geometry Clip Blocker

## Verified + repaired 2026-11-05 (worktree work/libbug-w6-textdecor-20261105)

Behavioral verification on the Linux/aarch64 evidence lane
(`build/phase_snapshots/phase1_1793422538/simple`, interpreter mode):

- `text_decoration_geometry_clip_spec.spl` failed 1/5 before the fix:
  "moves independent underline ink for positive and negative offsets"
  (`expected 36 to equal 28`) — `text-underline-offset:-4px` moved the
  underline 4px *down* instead of up.
- Root cause: `apply_declarations` resolved the property with
  `parse_int(text_underline_offset_norm)`
  (`simple_web_html_layout_renderer_decl_apply.spl`), and the renderer's
  `parse_int` drops a leading `-` (it only accumulates digits), so every
  negative offset silently became positive. Paint geometry, tile ink
  bounds, and ancestor clipping were all correct once the resolved value
  had the right sign.
- Fix: parse with the existing `parse_signed_nth_int(value, 0)`
  (same helper as text-shadow/box-shadow offsets); non-numeric values
  (e.g. `from-font`) fall back to 0 as before.
- After the fix: `text_decoration_geometry_clip_spec.spl` 5/5 PASS.
- Regression baselines (identical before and after the fix, pre-existing
  failures unrelated to this change):
  `browser_renderer_spec.spl` 112/130 (18 pre-existing failures),
  `text_decoration_paint_parity_spec.spl` 2/4 (2 pre-existing failures).

## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

## Triage note 2026-09-13 — not verifiable on this host; left OPEN, not stale
- **inferred**: this entry cites no backticked product paths, so a path-existence stale test does not apply; nothing indicates the code it describes was removed.
- **inferred**: reproduction needs a Linux host with a GPU, RenderDoc, and/or Electron/Chrome Vulkan backing. This triage host is Windows with no such lane, and `bin/simple` here is the Rust seed (v1.0.0-rc.1), not the self-hosted binary these evidence gates are written against.
- **inferred**: "does not run on Windows" is not evidence of a fix, so no closure is claimed. The gate remains blocked until re-run on the Linux evidence lane.

Date: 2026-06-25

## Status

Open.

## Repair candidate 2026-11-03 — behavioral verification blocked

Current source already parses both properties and emits independent decoration
rectangles. Ancestor clips come from `build_ancestor_clip_cache`; they are not
glyph ink clips and must remain intact for `overflow:hidden`.

The candidate repairs two concrete current geometry defects in
`simple_web_html_layout_renderer_paint_raster.spl`: normal raster multiplied
resolved CSS pixel thickness by bitmap glyph scale, and tile text bounds
omitted decoration thickness (including the second stroke of `double`). The
candidate uses CSS pixel thickness directly and includes decoration ink in
conservative tile bounds, without expanding ancestor clips.

`text_decoration_geometry_clip_spec.spl` adds five examples for exact thickness,
positive/negative offsets, default geometry, ancestor clipping, and a thick
double underline reaching a live tile while its glyph node is outside the
viewport and tile margin. These are real raster calls and color/row witnesses,
not screenshots or fabricated DOM output.

Verification: `git diff --check` passed. Behavioral tests, compiler/library
checks and the required runtime smoke gates are **TEST_BLOCKED**: this Windows
checkout has no qualified self-hosted CLI. The tracked `bin/simple.exe` Rust
seed was not used. Zero behavioral examples executed; do not mark this bug
fixed or move support inventory based on this candidate.

## Summary

`text-decoration-thickness` and `text-underline-offset` cannot be safely marked
implemented yet. A scoped attempt to add both properties to the Simple Web HTML
layout renderer made the renderer SSpec fail even after switching from an 8px
fixture to a 16px fixture with larger line-height.

## Evidence

- `bin/simple check src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl` passed after adding the geometry fields.
- `bin/simple test test/01_unit/lib/gc_async_mut/gpu/browser_engine/browser_renderer_spec.spl --mode=interpreter --clean` failed with the new geometry examples.
- Failure shape: the existing underline color behavior remained stable, but
  thickness/offset pixel witnesses did not prove changed visible geometry under
  the current text paint clip/line box behavior.

## Suspected Cause

Underline paint geometry is tied to text ink position and the current paint
clip. Larger thickness or positive offset can be clipped or collapse to the
same visible pixels, so simply changing the underline rectangle height/y
coordinate is not sufficient.

## Required Fix

Before claiming support for `text-decoration-thickness` or
`text-underline-offset`:

- Define underline decoration ink bounds separately from glyph ink bounds.
- Ensure the paint clip includes decoration overflow when CSS line-height permits it.
- Add pixel SSpecs that prove:
  - default underline remains unchanged;
  - thicker underline increases visible decoration pixels;
  - underline offset moves the decoration without clipping it away.
- Then move both properties from unsupported inventory to implemented inventory.

## Non-Solution

Do not add the properties to `CSS_SUPPORTED` as no-ops. That would make
traceability report support that the renderer cannot prove.

