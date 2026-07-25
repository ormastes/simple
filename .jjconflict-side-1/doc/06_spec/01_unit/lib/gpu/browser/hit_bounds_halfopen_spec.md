# Browser Hit-Test Half-Open Bounds Spec

> `_box_contains` (src/lib/gc_async_mut/gpu/browser_engine/layout.spl), the point-in-box test backing `hit_test`/`hit_test_anchor`, used to be inclusive on the right/bottom edge (`x <= box.x + box.width`). That let a point exactly on a shared border between two adjacent boxes match BOTH boxes, contradicting the GUI reference convention pinned down in test/01_unit/lib/common/ui/event_hit_semantics_spec.spl (`common.ui.widget_hit._contains`, half-open `[x, x+w) x [y, y+h)`).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Browser Hit-Test Half-Open Bounds Spec

`_box_contains` (src/lib/gc_async_mut/gpu/browser_engine/layout.spl), the point-in-box test backing `hit_test`/`hit_test_anchor`, used to be inclusive on the right/bottom edge (`x <= box.x + box.width`). That let a point exactly on a shared border between two adjacent boxes match BOTH boxes, contradicting the GUI reference convention pinned down in test/01_unit/lib/common/ui/event_hit_semantics_spec.spl (`common.ui.widget_hit._contains`, half-open `[x, x+w) x [y, y+h)`).

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Requirements | N/A — conformance evidence for doc/03_plan/ui/unified_2d_engine/unified_2d_interaction_2026-07-20.md (Phase 0, BOUNDS-P0). |
| Plan | doc/03_plan/ui/unified_2d_engine/unified_2d_interaction_2026-07-20.md |
| Design | N/A |
| Research | N/A |
| Source | `test/01_unit/lib/gpu/browser/hit_bounds_halfopen_spec.spl` |
| Updated | 2026-07-20 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

`_box_contains` (src/lib/gc_async_mut/gpu/browser_engine/layout.spl), the
point-in-box test backing `hit_test`/`hit_test_anchor`, used to be inclusive
on the right/bottom edge (`x <= box.x + box.width`). That let a point exactly
on a shared border between two adjacent boxes match BOTH boxes, contradicting
the GUI reference convention pinned down in
test/01_unit/lib/common/ui/event_hit_semantics_spec.spl
(`common.ui.widget_hit._contains`, half-open `[x, x+w) x [y, y+h)`).

This spec locks the fixed convention down for the browser engine: a point on
a shared border hits exactly the box whose half-open interval contains it,
never the box whose edge it sits on.

## Requirements

**Requirements:** N/A — conformance evidence for doc/03_plan/ui/unified_2d_engine/unified_2d_interaction_2026-07-20.md (Phase 0, BOUNDS-P0).

## Plan

**Plan:** doc/03_plan/ui/unified_2d_engine/unified_2d_interaction_2026-07-20.md

## Design

**Design:** N/A

## Research

**Research:** N/A

## Examples

Fixture: a 30x20 root containing two adjacent 10x10 children sharing the
vertical edge at x=10 — `left` spans x:[0,10) and `right` spans x:[10,20).
The root is wider/taller than the children so a point that misses both
children still lands inside the root (falls through to the `Some(node)` root
fallback in `hit_test`) instead of a total miss, letting each edge case name
exactly which node absorbed the point.

## Scenarios

### Browser hit-test half-open bounds

#### an interior point hits the left box

- Build the two-adjacent-boxes fixture (left [0,10), right [10,20))
- Hit-test a point well inside the left box
   - Expected: _tag_at(fx, 5.0, 5.0) equals `left`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Build the two-adjacent-boxes fixture (left [0,10), right [10,20))")
val fx = _fixture()

step("Hit-test a point well inside the left box")
expect(_tag_at(fx, 5.0, 5.0)).to_equal("left")
```

</details>

#### an interior point hits the right box

- Build the two-adjacent-boxes fixture
- Hit-test a point well inside the right box
   - Expected: _tag_at(fx, 15.0, 5.0) equals `right`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Build the two-adjacent-boxes fixture")
val fx = _fixture()

step("Hit-test a point well inside the right box")
expect(_tag_at(fx, 15.0, 5.0)).to_equal("right")
```

</details>

#### a point on the shared vertical border hits exactly the right box, never the left one

- Build the two-adjacent-boxes fixture sharing the x=10 edge
- Hit-test x=10 (left box's right edge, right box's left edge)
   - Expected: tag equals `right`
- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Build the two-adjacent-boxes fixture sharing the x=10 edge")
val fx = _fixture()

step("Hit-test x=10 (left box's right edge, right box's left edge)")
val tag = _tag_at(fx, 10.0, 5.0)

expect(tag).to_equal("right")
assert_true(tag != "left")
```

</details>

#### a point on a box's own right edge misses that box (falls through to its parent)

- Build the fixture; the right box's right edge sits at x=20
- Hit-test x=20, still inside the wider root but outside both children
   - Expected: tag equals `root`
- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Build the fixture; the right box's right edge sits at x=20")
val fx = _fixture()

step("Hit-test x=20, still inside the wider root but outside both children")
val tag = _tag_at(fx, 20.0, 5.0)

expect(tag).to_equal("root")
assert_true(tag != "right")
```

</details>

#### a point on a box's own bottom edge misses that box (falls through to its parent)

- Build the fixture; both children's bottom edge sits at y=10
- Hit-test y=10 over the left box's x-range, still inside the taller root
   - Expected: tag equals `root`
- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Build the fixture; both children's bottom edge sits at y=10")
val fx = _fixture()

step("Hit-test y=10 over the left box's x-range, still inside the taller root")
val tag = _tag_at(fx, 5.0, 10.0)

expect(tag).to_equal("root")
assert_true(tag != "left")
```

</details>

#### a point outside the root entirely is a clear miss

- Build the fixture and hit-test a point far outside the 30x20 root
- Hit-test (1000, 1000)
   - Expected: _tag_at(fx, 1000.0, 1000.0) equals `MISS`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Build the fixture and hit-test a point far outside the 30x20 root")
val fx = _fixture()

step("Hit-test (1000, 1000)")
expect(_tag_at(fx, 1000.0, 1000.0)).to_equal("MISS")
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

- **Requirements:** `N/A — conformance evidence for doc/03_plan/ui/unified_2d_engine/unified_2d_interaction_2026-07-20.md (Phase 0, BOUNDS-P0).`
- **Plan:** `doc/03_plan/ui/unified_2d_engine/unified_2d_interaction_2026-07-20.md`


</details>
