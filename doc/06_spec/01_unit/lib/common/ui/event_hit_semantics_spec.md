# Widget Hit-Test Semantics Spec

> `widget_hit_test` (and its shared helper `_hit_test_rects`) picks the widget under a pointer point from the list of rects `compute_layout` produces. This spec pins down the exact matching convention a caller can rely on:

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Widget Hit-Test Semantics Spec

`widget_hit_test` (and its shared helper `_hit_test_rects`) picks the widget under a pointer point from the list of rects `compute_layout` produces. This spec pins down the exact matching convention a caller can rely on:

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Requirements | N/A |
| Plan | N/A |
| Design | doc/04_architecture/ui/simple_gui_stack.md |
| Research | N/A |
| Source | `test/01_unit/lib/common/ui/event_hit_semantics_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

`widget_hit_test` (and its shared helper `_hit_test_rects`) picks the widget
under a pointer point from the list of rects `compute_layout` produces. This
spec pins down the exact matching convention a caller can rely on:

- **overlap** — when two sibling rects both cover a point, the LAST rect in
  draw order (the later sibling) wins, mirroring window_scene's top-of-stack
  pick.
- **half-open edges** — `_contains` uses `[x, x+w) x [y, y+h)`: a point on the
  left/top edge of a rect is inside it; a point exactly on the right/bottom
  edge (`x == rect.x + rect.w` or `y == rect.y + rect.h`) is outside it.
- **clear miss** — a point outside every rect (including the root container's
  own bounds) returns `found: false, id: ""`.
- **single rect** — a childless leaf node lays out to exactly one rect (its
  own bounds); an interior point hits it directly.
- **zero-size** — a rect with width or height 0 never contains any point,
  even its own origin.

`_hit_test_rects` itself has no `pub` modifier, so per the language's default
file-only visibility it cannot be called directly from this spec (or from
any other module) with a literal empty array. `compute_layout` always
contributes at least one rect (the container's own bounds), so a truly empty
rect list is not reachable through the public surface at all — the "zero-size
rect never hits" scenario below is the closest externally observable stand-in
for that internal branch: it exercises the same "no candidate satisfies
`_contains`" path as an empty list would.

## Requirements

**Requirements:** N/A

## Plan

**Plan:** N/A

## Design

**Design:** doc/04_architecture/ui/simple_gui_stack.md

## Research

**Research:** N/A

## Examples

The "the last sibling in draw order wins" scenario stacks two same-sized
buttons at the same origin under a fixed-layout root and confirms the later
sibling is returned as the hit, matching window_scene's top-of-stack pick.

## Scenarios

### widget_hit_test — hit-test semantics

#### the last sibling in draw order wins when two rects overlap

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- the last sibling in draw order wins when two rects overlap
- Build two same-sized siblings stacked at the same origin under a fixed-layout root
- Hit-test a point both siblings cover
   - Expected: hit.id equals `overlap_front`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("the last sibling in draw order wins when two rects overlap")
step("Build two same-sized siblings stacked at the same origin under a fixed-layout root")
val root = overlap_tree("overlap")

step("Hit-test a point both siblings cover")
val hit = widget_hit_test(root, 100, 100, 10, 10)

assert_true(hit.found)
expect(hit.id).to_equal("overlap_front")
```

</details>

#### half-open rect edges: left/top edge hits, right/bottom edge misses

- half-open rect edges: left/top edge hits, right/bottom edge misses
- Build a single 40x40 button filling a 40x40 root
- Left edge (x == rect.x) is inside
   - Expected: left.id equals `edge_btn`
- Top edge (y == rect.y) is inside
   - Expected: top.id equals `edge_btn`
- Interior point is inside
   - Expected: interior.id equals `edge_btn`
- Right edge (x == rect.x + rect.w) is outside
   - Expected: right.id equals ``
- Bottom edge (y == rect.y + rect.h) is outside
   - Expected: bottom.id equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("half-open rect edges: left/top edge hits, right/bottom edge misses")
step("Build a single 40x40 button filling a 40x40 root")
val root = edge_tree("edge")

step("Left edge (x == rect.x) is inside")
val left = widget_hit_test(root, 40, 40, 0, 20)
assert_true(left.found)
expect(left.id).to_equal("edge_btn")

step("Top edge (y == rect.y) is inside")
val top = widget_hit_test(root, 40, 40, 20, 0)
assert_true(top.found)
expect(top.id).to_equal("edge_btn")

step("Interior point is inside")
val interior = widget_hit_test(root, 40, 40, 20, 20)
assert_true(interior.found)
expect(interior.id).to_equal("edge_btn")

step("Right edge (x == rect.x + rect.w) is outside")
val right = widget_hit_test(root, 40, 40, 40, 20)
assert_false(right.found)
expect(right.id).to_equal("")

step("Bottom edge (y == rect.y + rect.h) is outside")
val bottom = widget_hit_test(root, 40, 40, 20, 40)
assert_false(bottom.found)
expect(bottom.id).to_equal("")
```

</details>

#### a point outside every rect (including the root container) is a clear miss

- a point outside every rect (including the root container) is a clear miss
- Build the same 40x40 tree and query a point far outside its bounds
   - Expected: hit.id equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("a point outside every rect (including the root container) is a clear miss")
step("Build the same 40x40 tree and query a point far outside its bounds")
val root = edge_tree("miss")
val hit = widget_hit_test(root, 40, 40, 1000, 1000)

assert_false(hit.found)
expect(hit.id).to_equal("")
```

</details>

#### a childless leaf node lays out to exactly one rect and hits it directly

- a childless leaf node lays out to exactly one rect and hits it directly
- Build a single leaf widget with no children
- An interior point hits the leaf's own bounds
   - Expected: hit.id equals `single_leaf`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("a childless leaf node lays out to exactly one rect and hits it directly")
step("Build a single leaf widget with no children")
val leaf = text_widget("single_leaf", "hello")

step("An interior point hits the leaf's own bounds")
val hit = widget_hit_test(leaf, 50, 50, 25, 25)

assert_true(hit.found)
expect(hit.id).to_equal("single_leaf")
```

</details>

#### a zero-size rect never registers a hit, even at its own origin

- a zero-size rect never registers a hit, even at its own origin
- Build a tree but hit-test it against a 0x0 canvas
- The root's own rect collapses to 0x0 and lays out no children
   - Expected: hit.id equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("a zero-size rect never registers a hit, even at its own origin")
step("Build a tree but hit-test it against a 0x0 canvas")
val root = edge_tree("zero")

step("The root's own rect collapses to 0x0 and lays out no children")
val hit = widget_hit_test(root, 0, 0, 0, 0)

assert_false(hit.found)
expect(hit.id).to_equal("")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Design:** `doc/04_architecture/ui/simple_gui_stack.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `39ecc12737503d281ec615413fd5c85ec318d62812e3b1c2ee17048020ffb499`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `39ecc12737503d281ec615413fd5c85ec318d62812e3b1c2ee17048020ffb499`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `39ecc12737503d281ec615413fd5c85ec318d62812e3b1c2ee17048020ffb499`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/ui/event_hit_semantics_spec.spl
mirror: doc/06_spec/01_unit/lib/common/ui/event_hit_semantics_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/ui/event_hit_semantics_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/ui/event_hit_semantics_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/ui/event_hit_semantics_spec.spl:91:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'the last sibling in draw order wins when two rects overlap' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/ui/event_hit_semantics_spec.spl:103:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'half-open rect edges: left/top edge hits, right/bottom edge misses' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/ui/event_hit_semantics_spec.spl:134:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'a point outside every rect (including the root container) is a clear miss' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
