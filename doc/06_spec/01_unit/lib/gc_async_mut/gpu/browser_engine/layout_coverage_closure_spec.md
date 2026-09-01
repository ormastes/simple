# Layout Coverage Closure Specification

> Tests covering Browser engine layout_to_scene + paint_box command emission, Browser engine layout_get_* accessors, Browser engine hit_test / hit_test_anchor / first_anchor_box, Browser engine layout_flex / layout_text passthrough stubs.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Layout Coverage Closure Specification

## Scenarios

### Browser engine layout_to_scene + paint_box command emission

#### emits a background fill command for a styled root with a background color

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- emits a background fill command for a styled root with a background color


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits a background fill command for a styled root with a background color")
val root = _root([_text(2, "hi")])
val scene = layout_to_scene(root, CssPx(value: 200.0), CssPx(value: 100.0))

var found_fill = false
var i = 0
while i < scene.commands.len():
    if scene.commands[i].starts_with("fill_rect"):
        found_fill = true
    i = i + 1
assert_true(found_fill, "expected a fill_rect command for the background-colored root box")
```

</details>

#### emits a stroke command when the root has a border width and color

- emits a stroke command when the root has a border width and color


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits a stroke command when the root has a border width and color")
val root = _bordered_root([_text(2, "hi")])
val scene = layout_to_scene(root, CssPx(value: 200.0), CssPx(value: 100.0))

var found_stroke = false
var i = 0
while i < scene.commands.len():
    if scene.commands[i].starts_with("stroke_rect"):
        found_stroke = true
    i = i + 1
assert_true(found_stroke, "expected a stroke_rect command for the bordered root box")
```

</details>

#### emits draw_text commands for each text child, in source order

- emits draw_text commands for each text child, in source order


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits draw_text commands for each text child, in source order")
val root = _root([_text(2, "hello"), _text(3, "world")])
val scene = layout_to_scene(root, CssPx(value: 200.0), CssPx(value: 100.0))

var draw_count = 0
var i = 0
while i < scene.commands.len():
    if scene.commands[i].starts_with("draw_text"):
        draw_count = draw_count + 1
    i = i + 1
assert_equal(draw_count, 2)
```

</details>

#### does not emit a fill_rect for a root with no background color set

- does not emit a fill_rect for a root with no background color set


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not emit a fill_rect for a root with no background color set")
val root = BeDomNode(
    node_id: 1,
    tag_name: "main",
    data: "",
    attributes: {},
    style: StyleProps.empty(),
    children: [_text(2, "plain")],
    parent_id: -1)
val scene = layout_to_scene(root, CssPx(value: 100.0), CssPx(value: 50.0))

var found_fill = false
var i = 0
while i < scene.commands.len():
    if scene.commands[i].starts_with("fill_rect"):
        found_fill = true
    i = i + 1
assert_false(found_fill, "no background_color set, so no fill_rect should be emitted")
```

</details>

### Browser engine layout_get_* accessors

#### reports x, y, width, and node id for the layout root box

- reports x, y, width, and node id for the layout root box


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports x, y, width, and node id for the layout root box")
val root = _root([_text(2, "hello")])
val layout = layout_tree(root, 200.0, 100.0)

assert_equal(layout_get_x(layout), 0.0)
assert_equal(layout_get_y(layout), 0.0)
assert_equal(layout_get_width(layout), 200.0)
assert_equal(layout_get_node(layout), 1)
```

</details>

### Browser engine hit_test / hit_test_anchor / first_anchor_box

#### hit_test finds the deepest node containing the point

- hit_test finds the deepest node containing the point


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("hit_test finds the deepest node containing the point")
val root = _root([_text(2, "hello"), _text(3, "world")])
val layout = layout_tree(root, 200.0, 100.0)
val children = layout_get_children(layout)
# first text child occupies the top rows starting at y=0
val hit = hit_test(layout, root, children[0].x + 1.0, children[0].y + 1.0)
assert_true(hit.?, "expected a hit inside the first text child's box")
```

</details>

#### hit_test returns nil when the point falls outside every box

- hit_test returns nil when the point falls outside every box


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("hit_test returns nil when the point falls outside every box")
val root = _root([_text(2, "hello")])
val layout = layout_tree(root, 200.0, 100.0)
val miss = hit_test(layout, root, -50.0, -50.0)
assert_false(miss.?, "point outside the root box should miss")
```

</details>

#### hit_test_anchor finds the innermost enclosing anchor for a point inside it

- hit_test_anchor finds the innermost enclosing anchor for a point inside it


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("hit_test_anchor finds the innermost enclosing anchor for a point inside it")
val anchor_child = _text(3, "link text")
val anchor = _anchor(2, [anchor_child])
val root = _root([anchor])
val layout = layout_tree(root, 200.0, 100.0)
val anchor_box = layout_get_children(layout)[0]
val found = hit_test_anchor(layout, root, anchor_box.x + 1.0, anchor_box.y + 1.0)
assert_true(found.?, "expected the point to resolve inside the anchor subtree")
```

</details>

#### hit_test_anchor returns nil when the hit target has no enclosing anchor

- hit_test_anchor returns nil when the hit target has no enclosing anchor


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("hit_test_anchor returns nil when the hit target has no enclosing anchor")
val root = _root([_text(2, "plain text, no anchor")])
val layout = layout_tree(root, 200.0, 100.0)
val child_box = layout_get_children(layout)[0]
val found = hit_test_anchor(layout, root, child_box.x + 1.0, child_box.y + 1.0)
assert_false(found.?, "no <a> ancestor exists, so hit_test_anchor should return nil")
```

</details>

#### first_anchor_box returns the box of the first anchor element in document order

- first_anchor_box returns the box of the first anchor element in document order


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("first_anchor_box returns the box of the first anchor element in document order")
val anchor = _anchor(2, [_text(3, "link")])
val root = _root([anchor, _text(4, "trailing text")])
val layout = layout_tree(root, 200.0, 100.0)
val found = first_anchor_box(layout, root)
assert_true(found.?, "expected to find the anchor box")
```

</details>

#### first_anchor_box returns nil when the tree has no anchor elements

- first_anchor_box returns nil when the tree has no anchor elements


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("first_anchor_box returns nil when the tree has no anchor elements")
val root = _root([_text(2, "no anchors here")])
val layout = layout_tree(root, 200.0, 100.0)
val found = first_anchor_box(layout, root)
assert_false(found.?, "no <a> elements present, so first_anchor_box should be nil")
```

</details>

### Browser engine layout_flex / layout_text passthrough stubs

#### layout_flex returns the container box unchanged

- layout_flex returns the container box unchanged


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("layout_flex returns the container box unchanged")
val root = _root([_text(2, "hello")])
val layout = layout_tree(root, 200.0, 100.0)
val style = StyleProps.empty()
val result = layout_flex(root, layout, style, nil)
assert_equal(layout_get_width(result), layout_get_width(layout))
```

</details>

#### layout_text returns the container box unchanged

- layout_text returns the container box unchanged


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("layout_text returns the container box unchanged")
val root = _root([_text(2, "hello")])
val layout = layout_tree(root, 200.0, 100.0)
val style = StyleProps.empty()
val result = layout_text(root, layout, style)
assert_equal(layout_get_height(result), layout_get_height(layout))
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/browser_engine/layout_coverage_closure_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Browser engine layout_to_scene + paint_box command emission, Browser engine layout_get_* accessors, Browser engine hit_test / hit_test_anchor / first_anchor_box, Browser engine layout_flex / layout_text passthrough stubs.
- Browser engine layout_to_scene + paint_box command emission
- Browser engine layout_get_* accessors
- Browser engine hit_test / hit_test_anchor / first_anchor_box
- Browser engine layout_flex / layout_text passthrough stubs

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `d09132668a48a7dbaeb8511259727b286d7694fb0ff9d71cd7f78e4e7806b4a0`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d09132668a48a7dbaeb8511259727b286d7694fb0ff9d71cd7f78e4e7806b4a0`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d09132668a48a7dbaeb8511259727b286d7694fb0ff9d71cd7f78e4e7806b4a0`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/gc_async_mut/gpu/browser_engine/layout_coverage_closure_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/layout_coverage_closure_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/layout_coverage_closure_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/layout_coverage_closure_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/layout_coverage_closure_spec.spl:77:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'emits a background fill command for a styled root with a background color' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/layout_coverage_closure_spec.spl:91:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'emits a stroke command when the root has a border width and color' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/layout_coverage_closure_spec.spl:105:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'emits draw_text commands for each text child, in source order' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
