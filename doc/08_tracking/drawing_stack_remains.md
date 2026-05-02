# Drawing Stack — Remaining Work

**Last updated:** 2026-04-15
**Scope:** Chromium-parity renderer (Skia/Blink/viz/cc) as described in
`doc/04_architecture/drawing_stack.md`.

Complexity markers: **S** (≤ 1 day), **M** (2–5 days), **L** (1–2 weeks),
**XL** (month+).

## Paint & Compositing Integration

- **[L] Paint pass integration.** Walk the Blink LayoutBox tree and emit
  SkCanvas draws into an SkPicture recorder per PaintChunk. Today the
  LayoutBox tree exists and PaintChunk/PropertyTreeState exist, but no code
  connects them.
- **[L] Surface aggregator dispatch.** The viz Aggregator is shell-only
  (`aggregator_walker`, `aggregator_compose`); needs full per-surface walk
  semantics, quad list merging, and damage propagation to siblings.
- **[XL] Display compositor.** Merges surface frames to the physical screen,
  handles vsync, partial swap, overlays. Currently absent.
- **[M] GPU path submission.** `vulkan/backend.spl` has a PipelineKey cache
  and triangulator, but no real GPU draw — needs command buffer recording +
  submission + fence wait.

## Input & Navigation

- **[M] Hit testing.** Given an InputEvent (x,y), walk LayoutBoxes and
  property-tree transforms, return the DomNode target. Inputs exist,
  layout exists, but there is no hit-test pass.
- **[M] Navigation controller.** URL history, back/forward, session
  restoration. `url_parser` exists; no history stack.
- **[M] Scroll manager.** ScrollTree exists in cc, but no scrollbar,
  wheel-event dispatch, or scroll-chaining logic.

## HTML / CSS Completeness

- **[L] HTML error recovery.** The tree_builder handles 7 insertion modes;
  full HTML5 error-recovery state machine (adoption agency, foster
  parenting, template content, fragment parsing) is missing.
- **[M] CSS @media queries.** Parser must branch on media condition;
  evaluator against viewport/capabilities.
- **[M] CSS pseudo-classes.** `:hover`, `:focus`, `:active`, `:nth-child`,
  `:not()` — selector matcher is compound-class only.
- **[M] CSS calc/var/em resolution.** Length resolution is px-only; no
  custom-property cascade, no calc tree.
- **[S] CSS shorthand expansion.** `margin`, `padding`, `border`, `font`
  shorthands must fan out to longhands before cascade.

## Layout Completeness

- **[L] Flex layout.** Missing entirely.
- **[XL] Grid layout.** Missing entirely.
- **[M] Margin collapse.** block_flow currently sums margins naively; needs
  collapsing per CSS 2.1 §8.3.1.
- **[L] Floats.** No float placement or line-box avoidance.
- **[L] Tables.** No table layout (shrink-to-fit, col/row span, caption).

## Text

- **[M] Real font measurement.** `text/line_break.spl` uses a 6px/char
  stub; must call `font_metrics` + glyph advances from the shaped run.
- **[M] Real PaintGlyph outline.** COLRv1 PaintGlyph currently uses a
  placeholder circular mask; need glyf/CFF2 outline sampling to build the
  actual coverage mask.
- **[L] Bidi.** No L/R reordering; shaper classifies scripts but layout
  does not reorder runs.
- **[M] Justify.** Line-breaker is greedy left-align; no inter-word or
  inter-char stretch.
- **[M] Real OS font enumeration.** `font_loader/registry` is a static
  table; needs FontConfig (Linux), DWrite (Win), CoreText (macOS) hooks.

## Skia / SkSL

- **[L] Full SkSL compiler.** Parser produces an AST (uniforms, functions,
  expressions, left-chain binary ops). Missing: operator precedence, type
  checker, IR lowering, bytecode generation.
- **[S] gvar shared-tuples peak lookup.** `apply_gvar_deltas_to_points` has
  a `pass_todo` for shared tuples; EMBEDDED_PEAK tuples work today.
- **[M] Topologically-chained path booleans.** Current impl is rect
  fast-path + polygon-subdivision fallback; `contains()` works but stroke
  expansion of the result would not.
- **[S] Rational conic flattening in stroke/expand.** Conics flattened
  with weight=1; Round joins at large widths show faceting.
- **[S] SkCanvas rotation-preserving matrix encoding.** `concat` and
  `set_matrix` currently encode to `[tx, ty, sx, sy]` and drop the
  rotation component; widen recorder op payload.
- **[S] CpuBackend applies CanvasState matrix.** Matrix3x3 is stored on
  save()/restore() but not applied to draw calls; wire into
  `render_picture`.

## Test Harness

- **[M] Compiled-mode test runner.** Interpreter-mode runner only verifies
  file loading; `it` block bodies do not execute real assertions. Route
  specs through the compiled path so assertions run.
