# Drawing Stack — Known Bugs & Workarounds

**Last updated:** 2026-04-15
**Scope:** Chromium-parity renderer (Skia/Blink/viz/cc).
See `doc/04_architecture/drawing_stack.md` for architecture.

Each entry: **symptom** — _workaround / expected fix_.

## Tooling & Workflow

1. **Write-tool silent drops (4 incidents).** Write call returns success,
   file on disk is empty or truncated; Read can return phantom content in
   that state. Affected this session: `tone_map.spl`, `icc_profile.spl`,
   `ot_parser.spl` (gvar decoders), `textblob_v2.spl`.
   _Workaround:_ after every Write, run `wc -l` + `md5sum` + `grep` for a
   known-unique token via Bash; retry Write on mismatch. Documented at
   `memory/feedback_write_tool_silent_drops.md`.

2. **Rewrite-regression pattern (2 incidents).** A sub-agent asked to
   “extend” an entity instead rewrote the types, breaking external
   callers — `cc/entity/property_tree.spl` broke
   `viz/feature/aggregator_compose.spl`; `cc/entity/tile.spl` broke
   `picture_layer_impl` and `tile_manager`.
   _Workaround:_ restored via backward-compat thin wrappers
   (TransformTree/ClipTree/EffectTree/ScrollTree and TileKey/NowBin).
   _Expected fix:_ for future rewrites prefer `layer_base.spl` pattern
   (new type alongside existing, no rename).

3. **Misleading commit history on `632e781aff`.** The message says
   “renderer work”, but the diff is dashboard + virtio. No data loss; the
   renderer work landed in later commits. _Workaround:_ ignore the subject
   line of that commit and grep the diff.

## Skia

4. **CpuBackend matrix not applied.** `cpu/backend.spl` save/restore
   correctly stacks `CanvasState` including `Matrix3x3`, but
   `render_picture` does not transform draw primitives by the current
   matrix — state is tracked, not enforced.
   _Expected fix:_ multiply primitive coords by `state.matrix` before
   rasterisation.

5. **SkCanvas matrix encoding lossy.** `canvas.concat` and
   `canvas.set_matrix` pack the affine into `[tx, ty, sx, sy]` (SkRect
   encoding on the recorder op), dropping any rotation / skew. Rotate()
   recorded ops are also affected when composed through concat.
   _Expected fix:_ widen the recorder op payload to carry all 6 affine
   terms (or store Matrix3x3 directly).

6. **COLRv1 PaintGlyph placeholder mask.** `colrv1.spl` PaintGlyph emits a
   circular coverage mask instead of sampling the referenced glyph's
   outline.
   _Expected fix:_ read glyph id → glyf/CFF2 → flatten outline → rasterise
   into coverage buffer.

7. **gvar shared-tuples stubbed.** `ot_parser.apply_gvar_deltas_to_points`
   contains a `pass_todo` for the shared-tuples peak lookup; only
   `EMBEDDED_PEAK` tuples apply deltas today.
   _Workaround:_ fonts authored with embedded peaks work; fonts relying on
   shared tuples render at default weight.

8. **Path boolean ops not topologically chained.**
   `path_op/boolean.spl` uses a rect fast-path + polygon-subdivision
   fallback. `contains()` queries and simple shapes are correct; **stroke
   expansion** of a boolean result is not reliable because edges are not
   chained into closed contours.
   _Expected fix:_ implement segment-chaining post-clip (Vatti or
   equivalent).

9. **stroke/expand conic flattening weight=1.** `stroke/expand.spl`
   treats conics as quadratic Béziers (weight=1) instead of rational
   flattening. At large stroke widths with `StrokeJoin::Round`, faceting
   is visible on curved joins.
   _Expected fix:_ rational de Casteljau subdivision with weight.

## Blink / Layout

(No known bugs in currently-wired code — most gaps are
feature-incomplete, tracked in `drawing_stack_remains.md`.)

## Test Harness

10. **Interpreter-mode test runner does not execute `it` bodies.** Specs
    load and report green, but assertion statements inside `it { … }`
    blocks are not evaluated in interpreter mode.
    _Workaround:_ run through compiled mode for real verification; see
    `memory/feedback_interpreter_test_limits.md`.
