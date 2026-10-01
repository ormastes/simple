# Browser Engine Layout Box Content Contract System Test

> A reader wants to know whether the browser engine's `BeLayoutBox` really honours

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Browser Engine Layout Box Content Contract System Test

A reader wants to know whether the browser engine's `BeLayoutBox` really honours

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Plan | doc/03_plan/sys_test/browser_engine_layout_box_content_contract.md |
| Source | `test/03_system/browser_engine/layout_box_content_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and Audience

A reader wants to know whether the browser engine's `BeLayoutBox` really honours
the contract that the 2026-08-16 layout/paint recovery settled on: the content
box is **derived on every call** from the stored border-box geometry plus the
box model, and a box refers to its source element by the integer `node_id` only.

That contract is not academic. The deleted `_paint_box` helper was written
against a different, nonexistent shape of the same class — it read `box.node` as
a field and `content_x` / `content_width` as *fields* rather than methods — so it
could never execute. This manual section is the executable statement of the real
shape, so the next author who reaches for a `node` field or a stored `content_*`
value finds a failing test instead of latent dead code.

## Scope and Preconditions

Runs entirely in-process and headless; no display server, no renderer, no
network. CSS arrives as real declaration text through `BeDomNode.set_style`,
which is the engine's own longhand/shorthand expander, so the padding and border
values under test are produced by the product's CSS path rather than poked into
the struct by the test.

## Primary Workflow

Author a small styled element, build its layout box through
`BeLayoutBox.block_for` / `BeLayoutBox.text_box`, and assert exact computed
geometry against an absolute arithmetic oracle:

    content_x      == x + padding_left + border_width
    content_y      == y + padding_top  + border_width
    content_width  == width  - padding_left - padding_right  - border_width * 2
    content_height == height - padding_top  - padding_bottom - border_width * 2

Every expectation is an exact value computed independently in this file, never a
comparison of the implementation against itself and never a "did not crash"
check.

## Evidence and Provenance

Source of truth: `src/lib/gc_async_mut/gpu/browser_engine/layout_box.spl`
(`BeLayoutBox`, `content_x`/`content_y`/`content_width`/`content_height`).
Contract history and the reason `_paint_box` was deleted rather than ported:
`doc/08_tracking/bug/layout_paint_paint_box_dead_code_wrong_belayoutbox_shape_2026-08-15.md`.

Deliberately out of scope: `layout_paint._apply_opacity`. It is already covered
exhaustively at unit tier by
`test/01_unit/browser_engine/layout_paint_coverage_closure_spec.spl` (all four
branches), and `StyleProps` carries no `opacity` property, so no CSS-to-paint
producer exists to integrate against. Asserting it again here would duplicate
unit coverage while inventing a pipeline the engine does not have.

## Scenarios

### Browser engine layout box content contract

#### derives the content rectangle from padding and border

**Manual warnings:**
- invalid manual visibility metadata: # @manual_section "Content box geometry" (expected show, folded, detail, or skip)


- derives the content rectangle from padding and border
- Author a 200x100 block at (40, 20) with 10px padding and a 2px border
- Read the content origin, which insets the border box by padding and border
   - Expected: box_.content_x() equals `52.0`
   - Expected: box_.content_y() equals `32.0`
- Read the content size, which subtracts both paddings and both borders
   - Expected: box_.content_width() equals `176.0`
   - Expected: box_.content_height() equals `76.0`
- Confirm the stored border-box geometry was not rewritten by the derivation
   - Expected: box_.x equals `40.0`
   - Expected: box_.y equals `20.0`
   - Expected: box_.width equals `200.0`
   - Expected: box_.height equals `100.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("derives the content rectangle from padding and border")
step("Author a 200x100 block at (40, 20) with 10px padding and a 2px border")
val box_ = _styled_block(1, "10px", "2px", 40.0, 20.0, 200.0, 100.0)

step("Read the content origin, which insets the border box by padding and border")
expect(box_.content_x()).to_equal(52.0)
expect(box_.content_y()).to_equal(32.0)

step("Read the content size, which subtracts both paddings and both borders")
expect(box_.content_width()).to_equal(176.0)
expect(box_.content_height()).to_equal(76.0)

step("Confirm the stored border-box geometry was not rewritten by the derivation")
expect(box_.x).to_equal(40.0)
expect(box_.y).to_equal(20.0)
expect(box_.width).to_equal(200.0)
expect(box_.height).to_equal(100.0)
```

</details>

#### collapses the content box onto the border box when there is no padding or border

- collapses the content box onto the border box when there is no padding or border
- Author a 50x30 block at (5, 7) with zero padding and zero border
- With nothing to inset, the content rectangle equals the border box exactly
   - Expected: box_.content_x() equals `5.0`
   - Expected: box_.content_y() equals `7.0`
   - Expected: box_.content_width() equals `50.0`
   - Expected: box_.content_height() equals `30.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("collapses the content box onto the border box when there is no padding or border")
step("Author a 50x30 block at (5, 7) with zero padding and zero border")
val box_ = _styled_block(2, "0", "0", 5.0, 7.0, 50.0, 30.0)

step("With nothing to inset, the content rectangle equals the border box exactly")
expect(box_.content_x()).to_equal(5.0)
expect(box_.content_y()).to_equal(7.0)
expect(box_.content_width()).to_equal(50.0)
expect(box_.content_height()).to_equal(30.0)
```

</details>

#### recomputes the content rectangle after the box model changes

- recomputes the content rectangle after the box model changes
- Author a 100x100 block at the origin with 10px padding and no border
- Read the content origin produced by the initial padding
   - Expected: box_.content_x() equals `10.0`
   - Expected: box_.content_width() equals `80.0`
- Widen the left padding on the box itself
- The content rectangle follows the new padding, proving it is derived per call and never stored
   - Expected: box_.content_x() equals `30.0`
   - Expected: box_.content_width() equals `60.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("recomputes the content rectangle after the box model changes")
step("Author a 100x100 block at the origin with 10px padding and no border")
var box_ = _styled_block(3, "10px", "0", 0.0, 0.0, 100.0, 100.0)

step("Read the content origin produced by the initial padding")
expect(box_.content_x()).to_equal(10.0)
expect(box_.content_width()).to_equal(80.0)

step("Widen the left padding on the box itself")
box_.padding_left = 30.0

step("The content rectangle follows the new padding, proving it is derived per call and never stored")
expect(box_.content_x()).to_equal(30.0)
expect(box_.content_width()).to_equal(60.0)
```

</details>

<details>
<summary>Advanced: reports a negative content width when padding and border overflow the box</summary>

#### reports a negative content width when padding and border overflow the box

- reports a negative content width when padding and border overflow the box
- Author a 20x20 block whose 15px padding on each side exceeds its own width
- The engine does not clamp an over-constrained box, so the content width goes negative
   - Expected: box_.content_width() equals `-10.0`
   - Expected: box_.content_height() equals `-10.0`
- The stored border box is still the authored size, so the overflow is visible to callers
   - Expected: box_.width equals `20.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reports a negative content width when padding and border overflow the box")
step("Author a 20x20 block whose 15px padding on each side exceeds its own width")
val box_ = _styled_block(4, "15px", "0", 0.0, 0.0, 20.0, 20.0)

step("The engine does not clamp an over-constrained box, so the content width goes negative")
expect(box_.content_width()).to_equal(-10.0)
expect(box_.content_height()).to_equal(-10.0)

step("The stored border box is still the authored size, so the overflow is visible to callers")
expect(box_.width).to_equal(20.0)
```

</details>


</details>

#### carries the source element node id and tag onto its block box

**Manual warnings:**
- invalid manual visibility metadata: # @manual_section "Source element identity" (expected show, folded, detail, or skip)


- carries the source element node id and tag onto its block box
- Author an element whose node id is pinned to a known value
- The box refers to its element by integer node id, not by an embedded node object
   - Expected: box_.node_id equals `4242`
- The element's tag travels with the box for paint-time lookups
   - Expected: box_.tag_name equals `div`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("carries the source element node id and tag onto its block box")
step("Author an element whose node id is pinned to a known value")
val box_ = _styled_block(4242, "0", "0", 0.0, 0.0, 10.0, 10.0)

step("The box refers to its element by integer node id, not by an embedded node object")
expect(box_.node_id).to_equal(4242)

step("The element's tag travels with the box for paint-time lookups")
expect(box_.tag_name).to_equal("div")
```

</details>

#### zeroes the box model of a text box even when its element is padded

- zeroes the box model of a text box even when its element is padded
- Author a padded element and build a text box from it
- A text box carries no box model, so its content rectangle equals its border box
   - Expected: text_box_.content_x() equals `3.0`
   - Expected: text_box_.content_y() equals `4.0`
   - Expected: text_box_.content_width() equals `30.0`
   - Expected: text_box_.content_height() equals `19.0`
- The text box keeps its payload, the text tag, and its source element id
   - Expected: text_box_.text_content equals `hello`
   - Expected: text_box_.tag_name equals `#text`
   - Expected: text_box_.node_id equals `77`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("zeroes the box model of a text box even when its element is padded")
step("Author a padded element and build a text box from it")
var node = BeDomNode.element_with_id(77, "p")
node.set_style("padding", "12px")
val text_box_ = BeLayoutBox.text_box(node, "hello", 3.0, 4.0, 30.0, 19.0)

step("A text box carries no box model, so its content rectangle equals its border box")
expect(text_box_.content_x()).to_equal(3.0)
expect(text_box_.content_y()).to_equal(4.0)
expect(text_box_.content_width()).to_equal(30.0)
expect(text_box_.content_height()).to_equal(19.0)

step("The text box keeps its payload, the text tag, and its source element id")
expect(text_box_.text_content).to_equal("hello")
expect(text_box_.tag_name).to_equal("#text")
expect(text_box_.node_id).to_equal(77)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** `doc/03_plan/sys_test/browser_engine_layout_box_content_contract.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-WEB-BROWSER-004`
- `REQ-WEB-BROWSER-007`
- `REQ-WEB-BROWSER-021`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `0706c08033b57bcd8d5244f0e35e9b67079277efdbd5a81029d12326db0573f0`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0706c08033b57bcd8d5244f0e35e9b67079277efdbd5a81029d12326db0573f0`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0706c08033b57bcd8d5244f0e35e9b67079277efdbd5a81029d12326db0573f0`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **80/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/browser_engine/layout_box_content_contract_spec.spl
mirror: doc/06_spec/03_system/browser_engine/layout_box_content_contract_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=80; blocker cap makes effective=49
doc/06_spec/03_system/browser_engine/layout_box_content_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/browser_engine/layout_box_content_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: unsupported/limitations
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/browser_engine/layout_box_content_contract_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 25 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/browser_engine/layout_box_content_contract_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 3 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/03_system/browser_engine/layout_box_content_contract_spec.spl:93:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'derives the content rectangle from padding and border' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/browser_engine/layout_box_content_contract_spec.spl:113:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'collapses the content box onto the border box when there is no padding or border' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/browser_engine/layout_box_content_contract_spec.spl:125:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'recomputes the content rectangle after the box model changes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
