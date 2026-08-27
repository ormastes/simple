# style_longhand_cascade_spec

> Computed-style coverage for the CSS properties the cascade actually keeps.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# style_longhand_cascade_spec

Computed-style coverage for the CSS properties the cascade actually keeps.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/browser_engine/style_longhand_cascade_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Computed-style coverage for the CSS properties the cascade actually keeps.

A reader of this manual wants to know which declarations survive the trip from
a `<style>` block to a node's computed `StyleProps`, and which values a child
picks up from its parent without declaring them.

`BeDomNode.set_style` used to recognise only nine property names -- every other
declaration reaching it was silently dropped, so `font-size`, the box
shorthands and all inheritance computed as if never written. These scenarios
pin the widened property set and the inheritance pass so that regression
cannot return unnoticed.

## Scenarios

### browser engine computed style: longhands, shorthands and inheritance

#### keeps a font-size declaration instead of discarding it

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps a font-size declaration instead of discarding it
- Style a node with an explicit font-size
- Read the computed font-size back off the node
   - Expected: a.style.font_size equals `99.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps a font-size declaration instead of discarding it")
"""font-size is the property whose loss was first reported: a declared
99px stayed at the 16px default because set_style had no branch for it."""
step("Style a node with an explicit font-size")
val root = styled(page("#a { font-size: 99px; }", "<div id='a'>a</div>"))
step("Read the computed font-size back off the node")
val maybe_a = find_by_id(root, "a")
if val a = maybe_a:
    expect(a.style.font_size).to_equal(99.0)  # oracle: declared 99px, not the 16px default

else:
    assert_true(false)  # oracle: the fixture element must exist
```

</details>

#### computes the nine originally-supported properties alongside the new ones

- computes the nine originally-supported properties alongside the new ones
- Declare one legacy property and one newly-supported property together
- The legacy text-valued properties still compute
   - Expected: a.style.color equals `teal`
   - Expected: a.style.overflow equals `hidden`
   - Expected: a.style.position equals `absolute`
- The newly-routed length property computes too
   - Expected: a.style.width equals `250.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("computes the nine originally-supported properties alongside the new ones")
"""The widened property set must not cost the properties that already
worked, so this scenario asserts an old and a new one on one node."""
step("Declare one legacy property and one newly-supported property together")
val root = styled(page(
    "#a { color: teal; overflow: hidden; position: absolute; width: 250px; }",
    "<div id='a'>a</div>"))
val maybe_a = find_by_id(root, "a")
if val a = maybe_a:
    step("The legacy text-valued properties still compute")
    expect(a.style.color).to_equal("teal")  # oracle: pre-existing branch
    expect(a.style.overflow).to_equal("hidden")  # oracle: pre-existing branch
    expect(a.style.position).to_equal("absolute")  # oracle: pre-existing branch
    step("The newly-routed length property computes too")
    expect(a.style.width).to_equal(250.0)  # oracle: 250px parsed to px

else:
    assert_true(false)  # oracle: the fixture element must exist
```

</details>

#### expands the one-value and four-value box shorthands

- expands the one-value and four-value box shorthands
- Declare a one-value margin and a four-value padding
- Every margin side takes the single value
   - Expected: a.style.margin_top equals `10.0`
   - Expected: a.style.margin_right equals `10.0`
   - Expected: a.style.margin_bottom equals `10.0`
   - Expected: a.style.margin_left equals `10.0`
- The padding sides follow CSS top/right/bottom/left order
   - Expected: a.style.padding_top equals `1.0`
   - Expected: a.style.padding_right equals `2.0`
   - Expected: a.style.padding_bottom equals `3.0`
   - Expected: a.style.padding_left equals `4.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("expands the one-value and four-value box shorthands")
"""`margin: 10px` sets all four sides; `padding: 1px 2px 3px 4px` walks
top, right, bottom, left. Both previously computed zero."""
step("Declare a one-value margin and a four-value padding")
val root = styled(page(
    "#a { margin: 10px; padding: 1px 2px 3px 4px; }", "<div id='a'>a</div>"))
val maybe_a = find_by_id(root, "a")
if val a = maybe_a:
    step("Every margin side takes the single value")
    expect(a.style.margin_top).to_equal(10.0)  # oracle: 1-value form fills all sides
    expect(a.style.margin_right).to_equal(10.0)  # oracle: 1-value form fills all sides
    expect(a.style.margin_bottom).to_equal(10.0)  # oracle: 1-value form fills all sides
    expect(a.style.margin_left).to_equal(10.0)  # oracle: 1-value form fills all sides
    step("The padding sides follow CSS top/right/bottom/left order")
    expect(a.style.padding_top).to_equal(1.0)  # oracle: 4-value form, first token is top
    expect(a.style.padding_right).to_equal(2.0)  # oracle: 4-value form, second token is right
    expect(a.style.padding_bottom).to_equal(3.0)  # oracle: 4-value form, third token is bottom
    expect(a.style.padding_left).to_equal(4.0)  # oracle: 4-value form, fourth token is left

else:
    assert_true(false)  # oracle: the fixture element must exist
```

</details>

#### expands the two-value box shorthand into a vertical/horizontal pair

- expands the two-value box shorthand into a vertical/horizontal pair
- Declare a two-value margin
   - Expected: b.style.margin_top equals `5.0`
   - Expected: b.style.margin_bottom equals `5.0`
   - Expected: b.style.margin_left equals `15.0`
   - Expected: b.style.margin_right equals `15.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("expands the two-value box shorthand into a vertical/horizontal pair")
step("Declare a two-value margin")
val root = styled(page("#b { margin: 5px 15px; }", "<div id='b'>b</div>"))
val maybe_b = find_by_id(root, "b")
if val b = maybe_b:
    expect(b.style.margin_top).to_equal(5.0)  # oracle: first token is the vertical pair
    expect(b.style.margin_bottom).to_equal(5.0)  # oracle: first token is the vertical pair
    expect(b.style.margin_left).to_equal(15.0)  # oracle: second token is the horizontal pair
    expect(b.style.margin_right).to_equal(15.0)  # oracle: second token is the horizontal pair

else:
    assert_true(false)  # oracle: the fixture element must exist
```

</details>

#### reads width, style and colour out of the border shorthand

- reads width, style and colour out of the border shorthand
- Declare a border shorthand in width/style/colour order
   - Expected: a.style.border_width equals `2.0`
   - Expected: a.style.border_style equals `solid`
   - Expected: a.style.border_color equals `blue`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reads width, style and colour out of the border shorthand")
step("Declare a border shorthand in width/style/colour order")
val root = styled(page("#a { border: 2px solid blue; }", "<div id='a'>a</div>"))
val maybe_a = find_by_id(root, "a")
if val a = maybe_a:
    expect(a.style.border_width).to_equal(2.0)  # oracle: 2px is the width component
    expect(a.style.border_style).to_equal("solid")  # oracle: solid is the style component
    expect(a.style.border_color).to_equal("blue")  # oracle: blue is the colour component

else:
    assert_true(false)  # oracle: the fixture element must exist
```

</details>

#### passes inherited properties down to a child that declares none

- passes inherited properties down to a child that declares none
- Style only the parent
- The child computes the parent's inherited values
   - Expected: child.style.color equals `teal`
   - Expected: child.style.font_size equals `24.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("passes inherited properties down to a child that declares none")
"""A child of a styled parent should compute the parent's colour and
font-size. Before the inheritance pass it computed the bare defaults."""
step("Style only the parent")
val root = styled(page(
    "#parent { color: teal; font-size: 24px; }",
    "<div id='parent'><span id='child'>x</span></div>"))
val maybe_child = find_by_id(root, "child")
if val child = maybe_child:
    step("The child computes the parent's inherited values")
    expect(child.style.color).to_equal("teal")  # oracle: color is an inherited property
    expect(child.style.font_size).to_equal(24.0)  # oracle: font-size is an inherited property

else:
    assert_true(false)  # oracle: the fixture element must exist
```

</details>

#### lets a child's own declaration win over the inherited value

- lets a child's own declaration win over the inherited value
- Style parent and child with conflicting colours
   - Expected: child.style.color equals `red`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("lets a child's own declaration win over the inherited value")
"""Inheritance runs after the cascade, so it must never overwrite a
value the child declared for itself."""
step("Style parent and child with conflicting colours")
val root = styled(page(
    "#parent { color: teal; } #child { color: red; }",
    "<div id='parent'><span id='child'>x</span></div>"))
val maybe_child = find_by_id(root, "child")
if val child = maybe_child:
    expect(child.style.color).to_equal("red")  # oracle: own declaration beats inheritance

else:
    assert_true(false)  # oracle: the fixture element must exist
```

</details>

#### does not inherit the non-inherited box properties

- does not inherit the non-inherited box properties
- Give the parent a margin and a border width the child never declares
   - Expected: child.style.margin_top equals `0.0`
   - Expected: child.style.border_width equals `0.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("does not inherit the non-inherited box properties")
"""Only the CSS inherited set propagates. A parent's margin must not
appear on its child, or every nested box would gain phantom spacing."""
step("Give the parent a margin and a border width the child never declares")
val root = styled(page(
    "#parent { margin: 30px; border: 4px solid red; }",
    "<div id='parent'><span id='child'>x</span></div>"))
val maybe_child = find_by_id(root, "child")
if val child = maybe_child:
    expect(child.style.margin_top).to_equal(0.0)  # oracle: margin is NOT inherited in CSS
    expect(child.style.border_width).to_equal(0.0)  # oracle: border-width is NOT inherited in CSS

else:
    assert_true(false)  # oracle: the fixture element must exist
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `08cc9001c7435a85e11a65b94d662d0678da19c218148df8932c5beb269c6a96`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `08cc9001c7435a85e11a65b94d662d0678da19c218148df8932c5beb269c6a96`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `08cc9001c7435a85e11a65b94d662d0678da19c218148df8932c5beb269c6a96`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/gc_async_mut/gpu/browser_engine/style_longhand_cascade_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/style_longhand_cascade_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/style_longhand_cascade_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/style_longhand_cascade_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/style_longhand_cascade_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps a font-size declaration instead of discarding it' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/style_longhand_cascade_spec.spl:68:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'computes the nine originally-supported properties alongside the new ones' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/style_longhand_cascade_spec.spl:89:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'expands the one-value and four-value box shorthands' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
