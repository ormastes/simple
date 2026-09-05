# Render Lane Pipeline Specification

> I want to hand the browser a page and a stylesheet and get back boxes that are in the right place with the right colours — the thing every other blink spec so far has only proved one link of.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Render Lane Pipeline Specification

I want to hand the browser a page and a stylesheet and get back boxes that are in the right place with the right colours — the thing every other blink spec so far has only proved one link of.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Browser / Blink |
| Status | Active |
| Source | `test/01_unit/lib/blink/render_lane_pipeline_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

I want to hand the browser a page and a stylesheet and get back boxes that are
in the right place with the right colours — the thing every other blink spec so
far has only proved one link of.

Up to now the render lane was a row of parts that each worked alone: the DOM
built trees, the selector engine matched rules, the cascade resolved
declarations into a `ComputedStyle`, and block-flow layout stacked boxes whose
geometry a test typed in by hand. Nothing carried a value from one end to the
other, so "the renderer works" was never actually tested.

These examples run the whole style→layout half of the lane on real input: an
HTML token stream becomes a DOM, a CSS source string is tokenized and parsed
into a stylesheet, every element is cascaded against it, and the resolved
widths, heights and margins drive the block-flow pass. The assertions are on the
far end — the pixel rectangle a box landed on and the background colour it will
paint with — so a break anywhere in the chain shows up as a wrong number here.

Deliberately out of scope: painting. This proves layout boxes carry correct
computed values; turning them into pixels is a separate lane.

@manual_section Browser Rendering

## Scenarios

### geometry_from_style

#### carries px lengths through to the layout geometry unchanged

- carries px lengths through to the layout geometry unchanged
- resolve a stylesheet that sets width, height and a margin on body
- read back the style the cascade produced for body
   - Expected: _near(geo.width, 300.0) is true
   - Expected: _near(geo.height, 40.0) is true
   - Expected: _near(geo.spacing.margin_left, 12.0) is true
   - Expected: "body generated a box" equals `it did not`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("carries px lengths through to the layout geometry unchanged")
step("resolve a stylesheet that sets width, height and a margin on body")
val layout = build_styled_layout(
    _page_tree(),
    _sheet("body { width: 300px; height: 40px; margin-left: 12px; }"),
    800.0, 600.0
)

step("read back the style the cascade produced for body")
match layout.style_for(1):
    Some(s):
        val geo = geometry_from_style(s)
        expect(_near(geo.width, 300.0)).to_equal(true)
        expect(_near(geo.height, 40.0)).to_equal(true)
        expect(_near(geo.spacing.margin_left, 12.0)).to_equal(true)
    None:
        expect("body generated a box").to_equal("it did not")
```

</details>

#### drops a non-px length to zero rather than inventing a pixel value

- drops a non-px length to zero rather than inventing a pixel value
- author a width in em, which this lane cannot resolve
- expect zero, not 10
   - Expected: _near(geometry_from_style(s).width, 0.0) is true
   - Expected: "body generated a box" equals `it did not`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("drops a non-px length to zero rather than inventing a pixel value")
step("author a width in em, which this lane cannot resolve")
val layout = build_styled_layout(
    _page_tree(), _sheet("body { width: 10em; }"), 800.0, 600.0)

step("expect zero, not 10")
match layout.style_for(1):
    Some(s):
        expect(_near(geometry_from_style(s).width, 0.0)).to_equal(true)
    None:
        expect("body generated a box").to_equal("it did not")
```

</details>

### HTML plus CSS through to laid-out boxes

#### places two sibling divs stacked vertically at their cascaded heights

- places two sibling divs stacked vertically at their cascaded heights
- give both divs a width and height, and the second a top margin
- the first div sits at the origin and is 20px tall
   - Expected: _near(r.0, 0.0) is true
   - Expected: _near(r.1, 0.0) is true
   - Expected: _near(r.2, 100.0) is true
   - Expected: _near(r.3, 20.0) is true
   - Expected: "first div laid out" equals `it did not`
- the second div starts below it, offset by its own 5px top margin
   - Expected: _near(r.1, 25.0) is true
   - Expected: _near(r.3, 45.0) is true
   - Expected: "second div laid out" equals `it did not`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("places two sibling divs stacked vertically at their cascaded heights")
step("give both divs a width and height, and the second a top margin")
val css = "div { width: 100px; height: 20px; } .b { margin-top: 5px; }"
val layout = build_styled_layout(_page_tree(), _sheet(css), 800.0, 600.0)

step("the first div sits at the origin and is 20px tall")
match layout.rect_for(2):
    Some(r):
        expect(_near(r.0, 0.0)).to_equal(true)
        expect(_near(r.1, 0.0)).to_equal(true)
        expect(_near(r.2, 100.0)).to_equal(true)
        expect(_near(r.3, 20.0)).to_equal(true)
    None:
        expect("first div laid out").to_equal("it did not")

step("the second div starts below it, offset by its own 5px top margin")
match layout.rect_for(3):
    Some(r):
        expect(_near(r.1, 25.0)).to_equal(true)
        expect(_near(r.3, 45.0)).to_equal(true)
    None:
        expect("second div laid out").to_equal("it did not")
```

</details>

#### offsets children by the parent's padding read from the stylesheet

- offsets children by the parent's padding read from the stylesheet
- pad the body and size the children
- the first child starts inside the parent's padding box
   - Expected: _near(r.0, 10.0) is true
   - Expected: _near(r.1, 8.0) is true
   - Expected: "first div laid out" equals `it did not`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("offsets children by the parent's padding read from the stylesheet")
step("pad the body and size the children")
val css = "body { width: 400px; height: 200px; padding-left: 10px; padding-top: 8px; } div { width: 50px; height: 10px; }"
val layout = build_styled_layout(_page_tree(), _sheet(css), 800.0, 600.0)

step("the first child starts inside the parent's padding box")
match layout.rect_for(2):
    Some(r):
        expect(_near(r.0, 10.0)).to_equal(true)
        expect(_near(r.1, 8.0)).to_equal(true)
    None:
        expect("first div laid out").to_equal("it did not")
```

</details>

#### lets the more specific rule win on the colour the box will paint with

- lets the more specific rule win on the colour the box will paint with
- a type rule paints every div green, a class rule repaints .b red
- the unclassed div keeps green
   - Expected: s.background_color.g > 0.2 is true
   - Expected: s.background_color.r < 0.2 is true
   - Expected: "first div styled" equals `it did not`
- the .b div is repainted red by the higher-specificity rule
   - Expected: s.background_color.r > 0.99 is true
   - Expected: s.background_color.g < 0.2 is true
   - Expected: "second div styled" equals `it did not`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("lets the more specific rule win on the colour the box will paint with")
step("a type rule paints every div green, a class rule repaints .b red")
val css = "div { background-color: green; } .b { background-color: red; }"
val layout = build_styled_layout(_page_tree(), _sheet(css), 800.0, 600.0)

step("the unclassed div keeps green")
match layout.style_for(2):
    Some(s):
        expect(s.background_color.g > 0.2).to_equal(true)
        expect(s.background_color.r < 0.2).to_equal(true)
    None:
        expect("first div styled").to_equal("it did not")

step("the .b div is repainted red by the higher-specificity rule")
match layout.style_for(3):
    Some(s):
        expect(s.background_color.r > 0.99).to_equal(true)
        expect(s.background_color.g < 0.2).to_equal(true)
    None:
        expect("second div styled").to_equal("it did not")
```

</details>

#### generates no box at all for a display:none element

- generates no box at all for a display:none element
- hide the second div through the stylesheet
- the hidden div has no style entry and no rect
   - Expected: "hidden div generated a box" equals `it should not`
   - Expected: true is true
   - Expected: "hidden div was laid out" equals `it should not`
   - Expected: true is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("generates no box at all for a display:none element")
step("hide the second div through the stylesheet")
val css = "div { width: 100px; height: 20px; } .b { display: none; }"
val layout = build_styled_layout(_page_tree(), _sheet(css), 800.0, 600.0)

step("the hidden div has no style entry and no rect")
match layout.style_for(3):
    Some(s):
        expect("hidden div generated a box").to_equal("it should not")
    None:
        expect(true).to_equal(true)
match layout.rect_for(3):
    Some(r):
        expect("hidden div was laid out").to_equal("it should not")
    None:
        expect(true).to_equal(true)
```

</details>

#### gives a text node its own box, sized from the parent's font-size

- gives a text node its own box, sized from the parent's font-size
- build <body><p>hello</p></body> directly on the DOM arena
- size the body and set a font-size on the paragraph
- the text node laid out a box wider and taller than zero
   - Expected: _near(r.3 - r.1, 24.0) is true
   - Expected: _near(r.2 - r.0, 100.0) is true
   - Expected: "text node laid out" equals `it did not`


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("gives a text node its own box, sized from the parent's font-size")
step("build <body><p>hello</p></body> directly on the DOM arena")
var tree = dom_tree_new()
val body_id = tree.create_element("body")
tree.append_child(tree.root_id, body_id)
val p_id = tree.create_element("p")
tree.append_child(body_id, p_id)
val text_id = tree.create_text("hello")
tree.append_child(p_id, text_id)

step("size the body and set a font-size on the paragraph")
val css = "body { width: 200px; } p { width: 100px; font-size: 20px; }"
val layout = build_styled_layout(tree, _sheet(css), 800.0, 600.0)

step("the text node laid out a box wider and taller than zero")
match layout.rect_for(text_id):
    Some(r):
        expect(r.2 - r.0).to_be_greater_than(0.0)
        expect(r.3 - r.1).to_be_greater_than(0.0)
        # height = font-size(20px) * the 1.2 line-height multiplier = 24px
        expect(_near(r.3 - r.1, 24.0)).to_equal(true)
        # width = the containing block's (p's) content width = 100px
        expect(_near(r.2 - r.0, 100.0)).to_equal(true)
    None:
        expect("text node laid out").to_equal("it did not")
```

</details>

#### a block containing text is taller than an equivalent empty block

- a block containing text is taller than an equivalent empty block
- build two parallel <div> subtrees, one with a text child, one empty
- give both divs a width but no declared height (auto)
- the text-bearing div's own box is taller than the empty div's
   - Expected: _near(empty_h, 0.0) is true
   - Expected: "empty div laid out" equals `it did not`
   - Expected: "text-bearing div laid out" equals `it did not`


<details>
<summary>Executable SSpec</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("a block containing text is taller than an equivalent empty block")
step("build two parallel <div> subtrees, one with a text child, one empty")
var tree = dom_tree_new()
val body_id = tree.create_element("body")
tree.append_child(tree.root_id, body_id)
val with_text_id = tree.create_element("div")
tree.set_attribute(with_text_id, "class", "with-text")
tree.append_child(body_id, with_text_id)
val text_id = tree.create_text("hello")
tree.append_child(with_text_id, text_id)
val empty_id = tree.create_element("div")
tree.set_attribute(empty_id, "class", "empty")
tree.append_child(body_id, empty_id)

step("give both divs a width but no declared height (auto)")
val css = "body { width: 200px; } div { width: 100px; }"
val layout = build_styled_layout(tree, _sheet(css), 800.0, 600.0)

step("the text-bearing div's own box is taller than the empty div's")
match layout.rect_for(with_text_id):
    Some(with_text_r):
        match layout.rect_for(empty_id):
            Some(empty_r):
                val with_text_h = with_text_r.3 - with_text_r.1
                val empty_h = empty_r.3 - empty_r.1
                expect(_near(empty_h, 0.0)).to_equal(true)
                expect(with_text_h).to_be_greater_than(empty_h)
            None:
                expect("empty div laid out").to_equal("it did not")
    None:
        expect("text-bearing div laid out").to_equal("it did not")
```

</details>

#### leaves every box at the origin when the stylesheet declares nothing

- leaves every box at the origin when the stylesheet declares nothing
- lay the same page out against an empty stylesheet
- initial values give zero-sized boxes, not missing ones
   - Expected: _near(r.2 - r.0, 0.0) is true
   - Expected: _near(r.3 - r.1, 0.0) is true
   - Expected: "first div laid out" equals `it did not`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("leaves every box at the origin when the stylesheet declares nothing")
step("lay the same page out against an empty stylesheet")
val layout = build_styled_layout(_page_tree(), _sheet(""), 800.0, 600.0)

step("initial values give zero-sized boxes, not missing ones")
match layout.rect_for(2):
    Some(r):
        expect(_near(r.2 - r.0, 0.0)).to_equal(true)
        expect(_near(r.3 - r.1, 0.0)).to_equal(true)
    None:
        expect("first div laid out").to_equal("it did not")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-BLINK-RENDER-LANE-001`
- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a7eb7fd91516d22a67fedc059575fa3533b957429022c8bb453a04686853f386`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a7eb7fd91516d22a67fedc059575fa3533b957429022c8bb453a04686853f386`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a7eb7fd91516d22a67fedc059575fa3533b957429022c8bb453a04686853f386`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/lib/blink/render_lane_pipeline_spec.spl
mirror: doc/06_spec/01_unit/lib/blink/render_lane_pipeline_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=86; blocker cap makes effective=49
doc/06_spec/01_unit/lib/blink/render_lane_pipeline_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/blink/render_lane_pipeline_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/blink/render_lane_pipeline_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/lib/blink/render_lane_pipeline_spec.spl:85:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'carries px lengths through to the layout geometry unchanged' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/blink/render_lane_pipeline_spec.spl:105:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'drops a non-px length to zero rather than inventing a pixel value' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/blink/render_lane_pipeline_spec.spl:120:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'places two sibling divs stacked vertically at their cascaded heights' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
