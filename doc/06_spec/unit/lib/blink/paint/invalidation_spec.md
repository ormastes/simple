# Blink Paint Invalidation Specification

> When a page restyles, I do not want to be told "everything changed". I want to know which boxes actually changed and what area they cover, so a repaint can be scoped to that area.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Blink Paint Invalidation Specification

When a page restyles, I do not want to be told "everything changed". I want to know which boxes actually changed and what area they cover, so a repaint can be scoped to that area.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Browser / Blink |
| Status | Active |
| Source | `test/unit/lib/blink/paint/invalidation_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

When a page restyles, I do not want to be told "everything changed". I want to
know which boxes actually changed and what area they cover, so a repaint can be
scoped to that area.

These examples build the same document twice with two stylesheets, diff the two
resulting styled layouts, and assert on the exact set of changed node ids and
the damage rects that cover them.

**What is NOT claimed here.** The cascade is still total: every element is
re-resolved against the whole stylesheet on both frames, and nothing in this
module makes that incremental. The property under test is CORRECTNESS of the
reported damage — an identical frame reports nothing, a recoloured box reports
itself alone, a box that moved reports the union of where it was and where it
now is, and a document whose box set changed reports an honest full
invalidation rather than a diff it cannot compute. No timing is measured and no
speed-up is asserted.

That exactness matters: a "recompute everything" invalidation would satisfy
safety but fail every example below that pins a one-element changed set.

@manual_section Browser Rendering

## Scenarios

### diff_styled_layouts

#### reports no damage at all when the two frames are identical

- reports no damage at all when the two frames are identical
- build the same document twice from the same stylesheet
- diff them
- nothing changed, so nothing repaints and no area is damaged
   - Expected: inv.structural is false
   - Expected: inv.changed_node_ids.len() equals `0`
   - Expected: inv.damage.len() equals `0`
   - Expected: inv.is_empty() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports no damage at all when the two frames are identical")
step("build the same document twice from the same stylesheet")
val a = _layout(BASE_CSS)
val b = _layout(BASE_CSS)

step("diff them")
val inv = diff_styled_layouts(a, b)

step("nothing changed, so nothing repaints and no area is damaged")
expect(inv.structural).to_equal(false)
expect(inv.changed_node_ids.len()).to_equal(0)
expect(inv.damage.len()).to_equal(0)
expect(inv.is_empty()).to_equal(true)
```

</details>

#### reports only the recoloured box when one rule changes colour

- reports only the recoloured box when one rule changes colour
- change `.b`'s background from blue to green, touching nothing else
- diff the two frames
- exactly ONE box changed — a total invalidation would report three
   - Expected: inv.structural is false
   - Expected: inv.changed_node_ids.len() equals `1`
- and it is the second div, node id 3 (body=1, first div=2, second div=3)
   - Expected: inv.changed_node_ids[0 as i32] equals `3`
- its damage is its own box: 100 wide and 50 tall, as the stylesheet says
   - Expected: inv.damage.len() equals `1`
   - Expected: inv.damage[0 as i32].width() equals `100.0`
   - Expected: inv.damage[0 as i32].height() equals `50.0`
- and it sits below the first div, whose 50px height pushes it to y=50
   - Expected: inv.damage[0 as i32].top equals `50.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports only the recoloured box when one rule changes colour")
step("change `.b`'s background from blue to green, touching nothing else")
val before = _layout(BASE_CSS)
val after = _layout("div { display: block; width: 100px; height: 50px; } .a { background-color: red; } .b { background-color: green; }")

step("diff the two frames")
val inv = diff_styled_layouts(before, after)

step("exactly ONE box changed — a total invalidation would report three")
expect(inv.structural).to_equal(false)
expect(inv.changed_node_ids.len()).to_equal(1)

step("and it is the second div, node id 3 (body=1, first div=2, second div=3)")
expect(inv.changed_node_ids[0 as i32]).to_equal(3)

step("its damage is its own box: 100 wide and 50 tall, as the stylesheet says")
expect(inv.damage.len()).to_equal(1)
expect(inv.damage[0 as i32].width()).to_equal(100.0)
expect(inv.damage[0 as i32].height()).to_equal(50.0)

step("and it sits below the first div, whose 50px height pushes it to y=50")
expect(inv.damage[0 as i32].top).to_equal(50.0)
```

</details>

#### reports a box that only MOVED, even though its own style is unchanged

- reports a box that only MOVED, even though its own style is unchanged
- grow the first div from 50 to 80 tall, which pushes the second one down
- diff the two frames
- three boxes are dirty: the restyled div, the div it shifted, and the body they grew
   - Expected: inv.changed_node_ids.len() equals `3`
   - Expected: inv.changed_node_ids[0 as i32] equals `1`
   - Expected: inv.changed_node_ids[1 as i32] equals `2`
   - Expected: inv.changed_node_ids[2 as i32] equals `3`
- the second div's ComputedStyle is byte-for-byte identical across the frames
   - Expected: styles_equal(s_before, s_after) is true
   - Expected: 1 equals `0`
   - Expected: 1 equals `0`
- so a style-only diff would have MISSED it and left a stale box on screen
- its damage spans both positions: from its old top 50 to its new bottom 80+50 = 130
   - Expected: moved.top equals `50.0`
   - Expected: moved.bottom equals `130.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports a box that only MOVED, even though its own style is unchanged")
step("grow the first div from 50 to 80 tall, which pushes the second one down")
val before = _layout(BASE_CSS)
val after = _layout("div { display: block; width: 100px; height: 50px; } .a { background-color: red; height: 80px; } .b { background-color: blue; }")

step("diff the two frames")
val inv = diff_styled_layouts(before, after)

step("three boxes are dirty: the restyled div, the div it shifted, and the body they grew")
# body=1 (its content box grew from 100 to 130 tall), div .a=2 (restyled),
# div .b=3 (unchanged style, shifted down).
expect(inv.changed_node_ids.len()).to_equal(3)
expect(inv.changed_node_ids[0 as i32]).to_equal(1)
expect(inv.changed_node_ids[1 as i32]).to_equal(2)
expect(inv.changed_node_ids[2 as i32]).to_equal(3)

step("the second div's ComputedStyle is byte-for-byte identical across the frames")
match before.style_for(3):
    Some(s_before):
        match after.style_for(3):
            Some(s_after):
                expect(styles_equal(s_before, s_after)).to_equal(true)
            None:
                expect(1).to_equal(0)
    None:
        expect(1).to_equal(0)

step("so a style-only diff would have MISSED it and left a stale box on screen")
step("its damage spans both positions: from its old top 50 to its new bottom 80+50 = 130")
val moved = inv.damage[2 as i32]
expect(moved.top).to_equal(50.0)
expect(moved.bottom).to_equal(130.0)
```

</details>

#### declares a full invalidation when the document's box set changes

- declares a full invalidation when the document's box set changes
- compare a two-div document against a three-div one
- diff the two frames
- the per-node diff is meaningless across different box sets, so it says so
   - Expected: inv.structural is true
- and it does NOT dress that up as a precise list of changed nodes
   - Expected: inv.changed_node_ids.len() equals `0`
   - Expected: inv.is_empty() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("declares a full invalidation when the document's box set changes")
step("compare a two-div document against a three-div one")
val before = _layout(BASE_CSS)
var tokens: [HtmlToken] = [
    _start("body"),
    _start_class("div", "a"), _end("div"),
    _start_class("div", "b"), _end("div"),
    _start_class("div", "b"), _end("div"),
    _end("body")
]
val after = build_styled_layout(build_html_tree(tokens),
                                parse_css(tokenize_css(BASE_CSS)), 800.0, 600.0)

step("diff the two frames")
val inv = diff_styled_layouts(before, after)

step("the per-node diff is meaningless across different box sets, so it says so")
expect(inv.structural).to_equal(true)

step("and it does NOT dress that up as a precise list of changed nodes")
expect(inv.changed_node_ids.len()).to_equal(0)
expect(inv.is_empty()).to_equal(false)
```

</details>

### PaintInvalidation.bounding_damage

#### merges every damage rect into the one rect a whole-surface blit needs

- merges every damage rect into the one rect a whole-surface blit needs
- a change that dirties both divs, stacked at y 0..80 and 80..130
- the bounding damage spans from the topmost top to the bottommost bottom
   - Expected: b.top equals `0.0`
   - Expected: b.bottom equals `130.0`
   - Expected: b.left equals `0.0`
   - Expected: b.width() equals `100.0`
   - Expected: 1 equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("merges every damage rect into the one rect a whole-surface blit needs")
step("a change that dirties both divs, stacked at y 0..80 and 80..130")
val before = _layout(BASE_CSS)
val after = _layout("div { display: block; width: 100px; height: 50px; } .a { background-color: red; height: 80px; } .b { background-color: blue; }")
val inv = diff_styled_layouts(before, after)

step("the bounding damage spans from the topmost top to the bottommost bottom")
match inv.bounding_damage():
    Some(b):
        expect(b.top).to_equal(0.0)
        expect(b.bottom).to_equal(130.0)
        expect(b.left).to_equal(0.0)
        expect(b.width()).to_equal(100.0)
    None:
        expect(1).to_equal(0)
```

</details>

#### has no bounding damage when nothing changed

- has no bounding damage when nothing changed
- diff two identical frames
- no rects to merge means nil, not a zero-sized rect at the origin


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has no bounding damage when nothing changed")
step("diff two identical frames")
val inv = diff_styled_layouts(_layout(BASE_CSS), _layout(BASE_CSS))

step("no rects to merge means nil, not a zero-sized rect at the origin")
expect(inv.bounding_damage()).to_be_nil()
```

</details>

### DamageRect.union

#### returns the smallest rect containing both inputs

- returns the smallest rect containing both inputs
- union two disjoint rects
- each edge takes the outermost of the two: left 0, top 0, right 30, bottom 40
   - Expected: u.left equals `0.0`
   - Expected: u.top equals `0.0`
   - Expected: u.right equals `30.0`
   - Expected: u.bottom equals `40.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns the smallest rect containing both inputs")
step("union two disjoint rects")
val a = DamageRect(left: 0.0, top: 0.0, right: 10.0, bottom: 10.0)
val b = DamageRect(left: 20.0, top: 5.0, right: 30.0, bottom: 40.0)
val u = a.union(b)

step("each edge takes the outermost of the two: left 0, top 0, right 30, bottom 40")
expect(u.left).to_equal(0.0)
expect(u.top).to_equal(0.0)
expect(u.right).to_equal(30.0)
expect(u.bottom).to_equal(40.0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-BLINK-PAINT-INVALIDATION-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b76c967ddda752406931902f26199ec336a8d839bcc538b216cc3fe3f0556c7f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b76c967ddda752406931902f26199ec336a8d839bcc538b216cc3fe3f0556c7f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b76c967ddda752406931902f26199ec336a8d839bcc538b216cc3fe3f0556c7f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **80/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/unit/lib/blink/paint/invalidation_spec.spl
mirror: doc/06_spec/unit/lib/blink/paint/invalidation_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=80; blocker cap makes effective=49
doc/06_spec/unit/lib/blink/paint/invalidation_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/blink/paint/invalidation_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/blink/paint/invalidation_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 26 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/lib/blink/paint/invalidation_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/unit/lib/blink/paint/invalidation_spec.spl:81:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports no damage at all when the two frames are identical' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/blink/paint/invalidation_spec.spl:97:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports only the recoloured box when one rule changes colour' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/blink/paint/invalidation_spec.spl:122:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports a box that only MOVED, even though its own style is unchanged' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
