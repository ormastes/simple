# Browser Engine Layout Box Content Contract Specification

> A browser-engine layout box derives its content rectangle from padding and
> border on every call, keeps its stored border-box geometry untouched, and
> identifies its source element by integer node id rather than by an embedded
> node object.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|---------|
| 6 | 6 | 0 | 0 |

**Status: not yet executed (TEST_BLOCKED 2026-08-16).** No admitted pure-Simple
CLI exists in this tree, so the counts above are the spec's declared scenarios,
not observed results. This manual is hand-authored in generated shape pending a
`spipe-docgen` run. See
`doc/08_tracking/bug/deployed_selfhost_test_subcommand_segv_blocks_bootstrap_2026-08-16.md`
and the plan at
`doc/03_plan/sys_test/browser_engine_layout_box_content_contract.md`.

<details><summary>Full Scenario Manual</summary>

# Browser Engine Layout Box Content Contract

Executable source:
`test/03_system/browser_engine/layout_box_content_contract_spec.spl`

Runs entirely in-process and headless — no display server, renderer, or
network. CSS arrives as real declaration text through `BeDomNode.set_style`,
the engine's own longhand/shorthand expander, so the padding and border values
under test are produced by the product's CSS path rather than written into the
struct by the test.

The absolute oracle is arithmetic, computed independently in the spec:

    content_x      == x + padding_left + border_width
    content_y      == y + padding_top  + border_width
    content_width  == width  - padding_left - padding_right  - border_width * 2
    content_height == height - padding_top  - padding_bottom - border_width * 2

## Scenarios

### Content box geometry

#### derives the content rectangle from padding and border

- Author a 200x100 block at (40, 20) with 10px padding and a 2px border
- Read the content origin, which insets the border box by padding and border
- Expected: `content_x() == 52.0`, `content_y() == 32.0`
- Read the content size, which subtracts both paddings and both borders
- Expected: `content_width() == 176.0`, `content_height() == 76.0`
- Confirm the stored border-box geometry was not rewritten by the derivation
- Expected: `x == 40.0`, `y == 20.0`, `width == 200.0`, `height == 100.0`

#### collapses the content box onto the border box when there is no padding or border

- Author a 50x30 block at (5, 7) with zero padding and zero border
- With nothing to inset, the content rectangle equals the border box exactly
- Expected: `content_x() == 5.0`, `content_y() == 7.0`,
  `content_width() == 50.0`, `content_height() == 30.0`

#### recomputes the content rectangle after the box model changes

- Author a 100x100 block at the origin with 10px padding and no border
- Read the content origin produced by the initial padding
- Expected: `content_x() == 10.0`, `content_width() == 80.0`
- Widen the left padding on the box itself
- The content rectangle follows the new padding, proving it is derived per call
  and never stored
- Expected: `content_x() == 30.0`, `content_width() == 60.0`

> This is the load-bearing scenario. It is the only assertion that can tell a
> *derived* content rectangle apart from a *stored* one, and a stored one is
> exactly what the deleted `_paint_box` helper assumed.

### Edge and degenerate boxes

#### reports a negative content width when padding and border overflow the box

- Author a 20x20 block whose 15px padding on each side exceeds its own width
- The engine does not clamp an over-constrained box, so the content width goes
  negative
- Expected: `content_width() == -10.0`, `content_height() == -10.0`
- The stored border box is still the authored size, so the overflow is visible
  to callers
- Expected: `width == 20.0`

### Source element identity

#### carries the source element node id and tag onto its block box

- Author an element whose node id is pinned to a known value
- The box refers to its element by integer node id, not by an embedded node
  object
- Expected: `node_id == 4242`
- The element's tag travels with the box for paint-time lookups
- Expected: `tag_name == "div"`

#### zeroes the box model of a text box even when its element is padded

- Author a padded element and build a text box from it
- A text box carries no box model, so its content rectangle equals its border
  box
- Expected: `content_x() == 3.0`, `content_y() == 4.0`,
  `content_width() == 30.0`, `content_height() == 19.0`
- The text box keeps its payload, the text tag, and its source element id
- Expected: `text_content == "hello"`, `tag_name == "#text"`, `node_id == 77`

## Coverage boundary

`layout_paint._apply_opacity` is deliberately **not** covered here. It is
already exhaustively covered at unit tier by
`test/01_unit/browser_engine/layout_paint_coverage_closure_spec.spl` (all four
branches), `StyleProps` carries no `opacity` property, and the function has no
product caller — so no CSS-to-paint producer exists to integrate against.
Asserting it again at system tier would duplicate unit coverage while implying
a pipeline the engine does not have.

## Traceability

| REQ | Covered by |
|-----|-----------|
| REQ-WEB-BROWSER-004 | content box geometry scenarios |
| REQ-WEB-BROWSER-007 | source element identity scenarios |
| REQ-WEB-BROWSER-021 | executable spec plus this mirrored manual |

</details>
