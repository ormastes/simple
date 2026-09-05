# CSS Margin Collapsing

> Two vertically adjacent block boxes in CSS do not stack their margins — a 20px

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 26 | 26 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# CSS Margin Collapsing

Two vertically adjacent block boxes in CSS do not stack their margins — a 20px

## At a Glance

| Field | Value |
|-------|-------|
| Category | Stdlib / Layout |
| Status | Implemented |
| Plan | doc/03_plan/ui/rendering/blink_wiring_plan.md (blocker 7) |
| Source | `test/unit/lib/common/layout/margin_collapse_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and Audience

Two vertically adjacent block boxes in CSS do not stack their margins — a 20px
bottom margin next to a 10px top margin leaves a 20px gap, not 30px. This is
margin collapsing, and getting it wrong shifts every box below it on the page.
This module is the arithmetic, shared by the blink render lane and the live
browser lane so the two cannot drift apart.

The audience is whoever is laying out block boxes: `blink/layout/block_flow.spl`
today, and the live lane if it is ever re-pointed here.

## Scope and Preconditions

Pure arithmetic over `f64` CSS pixels. There is no DOM, no style record and no
tree — the caller has already decided which two margins are adjoining and asks
what they collapse to, or asks whether they may collapse at all.

## Primary Workflow

`collapse_margins(a, b)` answers the collapsed value. The
`*_collapses_with_parent` and `siblings_margins_collapse` predicates answer
whether collapsing is permitted; `establishes_bfc` answers whether a box fences
collapsing at its boundary.

## Key Concepts

| Concept | Description |
|---------|-------------|
| Collapsed margin | max of the positive margins plus min of the negative ones (CSS 2.1 §8.3.1) |
| Adjoining | Nothing — border, padding, line box, float, clearance — separates the two margins |
| BFC root | A box whose margins never collapse with its children's |
| Clearance | A box moved down by `clear`; it may no longer collapse its top margin |

## Compatibility and Limitations

Self-collapsing (empty) boxes are NOT detected here — the caller must recognise
that case and ask for the collapse itself. Floats, absolutely positioned boxes
and flex/grid items never collapse and must not be routed through this module.

## Scenarios

### collapse_margins

#### two positive margins collapse to the larger, not their sum

- two positive margins collapse to the larger, not their sum
- Collapse a 20px bottom margin against a 10px top margin
   - Expected: collapse_margins(20.0, 10.0) equals `20.0`
- Order must not matter — collapsing is commutative
   - Expected: collapse_margins(10.0, 20.0) equals `20.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("two positive margins collapse to the larger, not their sum")
step("Collapse a 20px bottom margin against a 10px top margin")
# This is the whole point of collapsing: 20 and 10 leave a 20px gap.
# A layout that summed them would put every following box 10px too low.
expect(collapse_margins(20.0, 10.0)).to_equal(20.0)
step("Order must not matter — collapsing is commutative")
expect(collapse_margins(10.0, 20.0)).to_equal(20.0)
```

</details>

#### a positive and a negative margin add together

- a positive and a negative margin add together
- Collapse +20px against -10px
   - Expected: collapse_margins(20.0, -10.0) equals `10.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a positive and a negative margin add together")
step("Collapse +20px against -10px")
# CSS 2.1 §8.3.1: max of the positives (20) plus min of the negatives
# (-10) = 10. A box pulled up by a negative margin really does close
# part of the gap. The live lane's expression yields max(20, -10) = 20
# here, which is the divergence recorded in the module header.
expect(collapse_margins(20.0, -10.0)).to_equal(10.0)
```

</details>

#### two negative margins collapse to the most negative

- two negative margins collapse to the most negative
- Collapse -20px against -10px
   - Expected: collapse_margins(-20.0, -10.0) equals `-20.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("two negative margins collapse to the most negative")
step("Collapse -20px against -10px")
# No positive margin, so the result is 0 + min(-20, -10) = -20: the
# boxes overlap by the larger of the two pulls, not by their sum.
expect(collapse_margins(-20.0, -10.0)).to_equal(-20.0)
```

</details>

#### zero margins collapse to zero

- zero margins collapse to zero
- Collapse 0 against 0
   - Expected: collapse_margins(0.0, 0.0) equals `0.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("zero margins collapse to zero")
step("Collapse 0 against 0")
expect(collapse_margins(0.0, 0.0)).to_equal(0.0)
```

</details>

#### collapsing against zero leaves the other margin untouched

- collapsing against zero leaves the other margin untouched
- Collapse 15px against 0
   - Expected: collapse_margins(15.0, 0.0) equals `15.0`
- And the same for a negative margin against 0
   - Expected: collapse_margins(-15.0, 0.0) equals `-15.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("collapsing against zero leaves the other margin untouched")
step("Collapse 15px against 0")
# max(15, 0) + min(15, 0) = 15 + 0. A zero margin is inert, which is
# what lets a layout driver seed its running margin at 0.
expect(collapse_margins(15.0, 0.0)).to_equal(15.0)
step("And the same for a negative margin against 0")
expect(collapse_margins(-15.0, 0.0)).to_equal(-15.0)
```

</details>

### collapse_margin_list

#### an empty adjoining set collapses to zero

- an empty adjoining set collapses to zero
- Collapse an empty list
   - Expected: collapse_margin_list(empty) equals `0.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("an empty adjoining set collapses to zero")
step("Collapse an empty list")
var empty: [f64] = []
expect(collapse_margin_list(empty)).to_equal(0.0)
```

</details>

#### a whole adjoining chain collapses in one step

- a whole adjoining chain collapses in one step
- Collapse the set 10, 30, -5, 20
   - Expected: collapse_margin_list(ms) equals `25.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a whole adjoining chain collapses in one step")
step("Collapse the set 10, 30, -5, 20")
# Three boxes' margins meeting at one point: the largest positive is
# 30 and the only negative is -5, so the used margin is 30 + (-5) = 25.
var ms: [f64] = []
ms.push(10.0)
ms.push(30.0)
ms.push(-5.0)
ms.push(20.0)
expect(collapse_margin_list(ms)).to_equal(25.0)
```

</details>

### collapsed_gap

#### names the sibling gap as the collapse of the two facing margins

- names the sibling gap as the collapse of the two facing margins
- A 5px margin-bottom faces an 8px margin-top
   - Expected: collapsed_gap(5.0, 8.0) equals `8.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("names the sibling gap as the collapse of the two facing margins")
step("A 5px margin-bottom faces an 8px margin-top")
# 8, not 13. This is the exact number blink's block_flow spec asserts
# for two stacked children.
expect(collapsed_gap(5.0, 8.0)).to_equal(8.0)
```

</details>

### top_margin_collapses_with_parent

#### collapses through a parent with no border, padding or BFC

- collapses through a parent with no border, padding or BFC
- Ask with all four blockers absent


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("collapses through a parent with no border, padding or BFC")
step("Ask with all four blockers absent")
assert_true(top_margin_collapses_with_parent(0.0, 0.0, false, false))
```

</details>

#### is blocked by a top border on the parent

- is blocked by a top border on the parent
- Give the parent a 1px top border


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is blocked by a top border on the parent")
step("Give the parent a 1px top border")
# Even one pixel of border sits between the two margins, so they are no
# longer adjoining and both apply in full.
assert_false(top_margin_collapses_with_parent(1.0, 0.0, false, false))
```

</details>

#### is blocked by top padding on the parent

- is blocked by top padding on the parent
- Give the parent 1px of top padding


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is blocked by top padding on the parent")
step("Give the parent 1px of top padding")
assert_false(top_margin_collapses_with_parent(0.0, 1.0, false, false))
```

</details>

#### is blocked by the parent establishing a block formatting context

- is blocked by the parent establishing a block formatting context
- Mark the parent a BFC root


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is blocked by the parent establishing a block formatting context")
step("Mark the parent a BFC root")
# CSS 2.1 §8.3.1: a BFC root's margins never collapse with its
# in-flow children's. This is the rule that makes `overflow: hidden`
# the classic fix for a child's margin escaping its parent.
assert_false(top_margin_collapses_with_parent(0.0, 0.0, true, false))
```

</details>

#### is blocked by the child having clearance

- is blocked by the child having clearance
- Mark the child as having been moved down by clear


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is blocked by the child having clearance")
step("Mark the child as having been moved down by clear")
assert_false(top_margin_collapses_with_parent(0.0, 0.0, false, true))
```

</details>

### bottom_margin_collapses_with_parent

#### collapses through an auto-height parent with no bottom edge

- collapses through an auto-height parent with no bottom edge
- Ask with no border, no padding, auto height, no min-height


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("collapses through an auto-height parent with no bottom edge")
step("Ask with no border, no padding, auto height, no min-height")
assert_true(bottom_margin_collapses_with_parent(0.0, 0.0, true, 0.0, false))
```

</details>

#### is blocked by a declared height on the parent

- is blocked by a declared height on the parent
- Give the parent a declared (non-auto) height


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is blocked by a declared height on the parent")
step("Give the parent a declared (non-auto) height")
# A declared height pins the parent's bottom content edge, so the last
# child's margin cannot reach past it. This is the extra blocker the
# bottom case has and the top case does not.
assert_false(bottom_margin_collapses_with_parent(0.0, 0.0, false, 0.0, false))
```

</details>

#### is blocked by a non-zero min-height on the parent

- is blocked by a non-zero min-height on the parent
- Give the parent a 10px min-height


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is blocked by a non-zero min-height on the parent")
step("Give the parent a 10px min-height")
assert_false(bottom_margin_collapses_with_parent(0.0, 0.0, true, 10.0, false))
```

</details>

#### is blocked by bottom border or bottom padding

- is blocked by bottom border or bottom padding
- Give the parent a 2px bottom border
- And separately, 2px of bottom padding


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is blocked by bottom border or bottom padding")
step("Give the parent a 2px bottom border")
assert_false(bottom_margin_collapses_with_parent(2.0, 0.0, true, 0.0, false))
step("And separately, 2px of bottom padding")
assert_false(bottom_margin_collapses_with_parent(0.0, 2.0, true, 0.0, false))
```

</details>

### siblings_margins_collapse

#### two ordinary in-flow siblings collapse

- two ordinary in-flow siblings collapse
- Neither has clearance and nothing separates them


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("two ordinary in-flow siblings collapse")
step("Neither has clearance and nothing separates them")
assert_true(siblings_margins_collapse(false, false, false, false))
```

</details>

#### two sibling BFC roots still collapse with EACH OTHER

- two sibling BFC roots still collapse with EACH OTHER
- Mark both siblings as BFC roots


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("two sibling BFC roots still collapse with EACH OTHER")
step("Mark both siblings as BFC roots")
# A BFC root fences its own CHILDREN's margins in; it does not stop it
# collapsing with a sibling. Asserting this explicitly because the
# opposite is the intuitive-but-wrong reading of the rule.
assert_true(siblings_margins_collapse(true, true, false, false))
```

</details>

#### is blocked when the second sibling has clearance

- is blocked when the second sibling has clearance
- Mark the second sibling as cleared


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is blocked when the second sibling has clearance")
step("Mark the second sibling as cleared")
assert_false(siblings_margins_collapse(false, false, true, false))
```

</details>

#### is blocked by a float or line box between them

- is blocked by a float or line box between them
- Report something in between the two margins


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is blocked by a float or line box between them")
step("Report something in between the two margins")
assert_false(siblings_margins_collapse(false, false, false, true))
```

</details>

### establishes_bfc

#### an ordinary visible-overflow block is not a BFC root

- an ordinary visible-overflow block is not a BFC root
- Ask about a plain in-flow block


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("an ordinary visible-overflow block is not a BFC root")
step("Ask about a plain in-flow block")
assert_false(establishes_bfc(false, false, false, true, false, false, false))
```

</details>

#### a float is always a BFC root

- a float is always a BFC root
- Ask about a floated box


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a float is always a BFC root")
step("Ask about a floated box")
assert_true(establishes_bfc(true, false, false, true, false, false, false))
```

</details>

#### non-visible overflow makes a BFC root

- non-visible overflow makes a BFC root
- Ask about a box with overflow other than visible


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("non-visible overflow makes a BFC root")
step("Ask about a box with overflow other than visible")
# This is why `overflow: hidden` contains floats and stops margin
# escape — the single most-used BFC trigger on the web.
assert_true(establishes_bfc(false, false, false, false, false, false, false))
```

</details>

#### absolute positioning, inline-block, table cells and flex items are BFC roots

- absolute positioning, inline-block, table cells and flex items are BFC roots
- Ask about each trigger in turn


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("absolute positioning, inline-block, table cells and flex items are BFC roots")
step("Ask about each trigger in turn")
assert_true(establishes_bfc(false, true, false, true, false, false, false))
assert_true(establishes_bfc(false, false, true, true, false, false, false))
assert_true(establishes_bfc(false, false, false, true, true, false, false))
assert_true(establishes_bfc(false, false, false, true, false, true, false))
```

</details>

#### the root element is a BFC root

- the root element is a BFC root
- Ask about the document root


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("the root element is a BFC root")
step("Ask about the document root")
assert_true(establishes_bfc(false, false, false, true, false, false, true))
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 26 |
| Active scenarios | 26 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** `doc/03_plan/ui/rendering/blink_wiring_plan.md (blocker 7)`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-BLINK-LAYOUT-MARGIN-COLLAPSE-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `d76f0b0955739a70d49196aa2ad5b1d883dfe367d3e9b0149a0188689af1d551`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d76f0b0955739a70d49196aa2ad5b1d883dfe367d3e9b0149a0188689af1d551`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d76f0b0955739a70d49196aa2ad5b1d883dfe367d3e9b0149a0188689af1d551`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **80/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/unit/lib/common/layout/margin_collapse_spec.spl
mirror: doc/06_spec/unit/lib/common/layout/margin_collapse_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=80; blocker cap makes effective=49
doc/06_spec/unit/lib/common/layout/margin_collapse_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/common/layout/margin_collapse_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: evidence, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/common/layout/margin_collapse_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 10 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/lib/common/layout/margin_collapse_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/unit/lib/common/layout/margin_collapse_spec.spl:68:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'two positive margins collapse to the larger, not their sum' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/layout/margin_collapse_spec.spl:78:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'a positive and a negative margin add together' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/layout/margin_collapse_spec.spl:88:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'two negative margins collapse to the most negative' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
