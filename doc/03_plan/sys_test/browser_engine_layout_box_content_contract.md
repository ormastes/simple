# Browser engine layout box content contract test plan

## Scope

Covers the `BeLayoutBox` contract that the 2026-08-16 layout/paint recovery
settled: the content rectangle is **derived on every call** from the stored
border-box geometry plus the box model, and a layout box refers to its source
element through the integer `node_id` field only.

This is the contract the deleted `_paint_box` helper violated. It read
`box.node` as a field and `content_x` / `content_width` as fields rather than
methods, so it could never execute and was removed rather than ported
(`doc/08_tracking/bug/layout_paint_paint_box_dead_code_wrong_belayoutbox_shape_2026-08-15.md`).
Before this plan there was unit coverage of the paint colour helper but no
system-tier statement of the box contract itself, so the shape that caused the
dead code was unguarded.

Out of scope, deliberately:

- `layout_paint._apply_opacity` — already exhaustively covered at unit tier by
  `test/01_unit/browser_engine/layout_paint_coverage_closure_spec.spl` (all four
  branches). `StyleProps` carries no `opacity` property and the function has no
  product caller, so there is no CSS-to-paint producer to integrate against.
  Adding a system-tier assertion would duplicate unit coverage while implying a
  pipeline the engine does not have.
- The HTML/Draw IR render path, which is covered by
  `test/03_system/gui/web_css/web_css_box_model_spec.spl`.

## Scenario and evidence

Executable: `test/03_system/browser_engine/layout_box_content_contract_spec.spl`
Mirror: `doc/06_spec/03_system/browser_engine/layout_box_content_contract_spec.md`

Runs in-process and headless — no display server, renderer, or network. CSS
arrives as real declaration text through `BeDomNode.set_style`, the engine's own
longhand/shorthand expander, so the padding and border values under test are
produced by the product's CSS path rather than written into the struct by the
test.

The absolute oracle is arithmetic, computed independently in the spec:

    content_x      == x + padding_left + border_width
    content_y      == y + padding_top  + border_width
    content_width  == width  - padding_left - padding_right  - border_width * 2
    content_height == height - padding_top  - padding_bottom - border_width * 2

| # | Scenario | Class | What would fail |
|---|----------|-------|-----------------|
| 1 | 200x100 block at (40,20), 10px padding, 2px border | positive | content rect not inset by padding+border; border box rewritten by the derivation |
| 2 | 50x30 block, zero padding and border | edge (identity) | content rect diverging from the border box when there is nothing to inset |
| 3 | Padding widened after construction | discriminating | `content_x()` returning a stored value instead of recomputing — the exact defect shape of `_paint_box` |
| 4 | 20x20 block with 15px padding per side | error / degenerate | silent clamping of an over-constrained box, hiding the overflow from callers |
| 5 | Element with pinned `node_id` 4242 | positive | box identifying its element by an embedded node object rather than an integer id |
| 6 | Text box built from a padded element | edge | a text box inheriting a box model it must not have |

Scenario 3 is the load-bearing one: it is the only assertion that can tell a
*derived* content rectangle apart from a *stored* one, and a stored one is what
`_paint_box` assumed.

## Traceability

| REQ | Covered by |
|-----|-----------|
| REQ-WEB-BROWSER-004 (web layout/paint geometry) | scenarios 1, 2, 3, 4 |
| REQ-WEB-BROWSER-007 (live node identity preserved) | scenarios 5, 6 |
| REQ-WEB-BROWSER-021 (executable SSpec + mirrored manual traceability) | whole spec + mirror |

## Pass criteria

- All six scenarios pass on an admitted pure-Simple self-hosted CLI.
- No `skip()`, no `pending()`, no placeholder assertion: every expectation is an
  exact value comparison, so an unavailable module fails the run rather than
  quietly reporting green.
- The mirrored manual regenerates with `0 stubs` via
  `bin/simple spipe-docgen test/03_system/browser_engine/layout_box_content_contract_spec.spl --output doc/06_spec --no-index`.
- `find doc/06_spec -name '*_spec.spl' | wc -l` stays `0`.

## Status

**TEST_BLOCKED as of 2026-08-16 — not yet executed.** No admitted pure-Simple
CLI exists in this tree: the deployed self-hosted binary SIGSEGVs on `simple
test --help`, re-bootstrap is gated on that same binary's bounded test ABI
probe, and `bootstrap/stage3/simple native-build` of a spec fails HIR lowering.
See `doc/08_tracking/bug/deployed_selfhost_test_subcommand_segv_blocks_bootstrap_2026-08-16.md`.

The spec is written fail-closed so that it verifies automatically once a
qualified CLI is available; it has never been run and must not be reported as
passing. The mirrored manual is hand-authored in generated shape pending a
docgen run.
