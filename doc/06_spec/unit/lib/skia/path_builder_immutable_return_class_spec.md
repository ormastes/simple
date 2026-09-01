# SkPath builders are immutable — discarded-return defect class

> Similar-problem detection spec generalizing the defect fixed in `doc/08_tracking/bug/skia_path_op_boolean_algorithm_2026-07-20.md`.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SkPath builders are immutable — discarded-return defect class

Similar-problem detection spec generalizing the defect fixed in `doc/08_tracking/bug/skia_path_op_boolean_algorithm_2026-07-20.md`.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SKI-PATHOP |
| Category | Stdlib |
| Difficulty | 2/5 |
| Status | Implemented |
| Source | `test/unit/lib/skia/path_builder_immutable_return_class_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Similar-problem detection spec generalizing the defect fixed in
`doc/08_tracking/bug/skia_path_op_boolean_algorithm_2026-07-20.md`.

The root cause there was not geometry: it was calling an IMMUTABLE builder
(`_emit_rect` -> `SkPath.move_to/line_to/close`) as a bare expression
statement and discarding the returned path. Any such call site silently
does nothing.

This spec pins the two properties that make that class of bug detectable:

1. `SkPath` builder methods are PURE — the receiver is unchanged after the
   call, so a discarded return value loses the work. If a future change ever
   made them mutate in place, these examples go RED and the "always assign
   the result" rule can be relaxed deliberately rather than by accident.
2. Multi-contour `path_op` results are STRUCTURALLY complete — a result
   built from two rectangles carries both rectangles' verbs, so an emit
   whose return value is dropped shows up as a verb-count shortfall, not
   merely as a membership surprise at one probe point.

## Scenarios

### SkPath builder immutability

#### move_to returns a new path and leaves the receiver empty

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- move_to returns a new path and leaves the receiver empty
   - Expected: empty.count_verbs() equals `before`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("move_to returns a new path and leaves the receiver empty")
val empty = sk_path_new()
val before = empty.count_verbs()
val moved = empty.move_to(1.0, 2.0)
# The receiver must be untouched: this is why a bare statement call
# discards all the work.
expect(empty.count_verbs()).to_equal(before)
expect(moved.count_verbs()).to_be_greater_than(before)
```

</details>

#### line_to returns a new path and leaves the receiver unchanged

- line_to returns a new path and leaves the receiver unchanged
   - Expected: base.count_verbs() equals `before`
   - Expected: lined.count_verbs() equals `before + 1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("line_to returns a new path and leaves the receiver unchanged")
val base = sk_path_new().move_to(0.0, 0.0)
val before = base.count_verbs()
val lined = base.line_to(5.0, 0.0)
expect(base.count_verbs()).to_equal(before)
expect(lined.count_verbs()).to_equal(before + 1)
```

</details>

#### close returns a new path and leaves the receiver unchanged

- close returns a new path and leaves the receiver unchanged
   - Expected: open_path.count_verbs() equals `before`
   - Expected: closed.count_verbs() equals `before + 1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("close returns a new path and leaves the receiver unchanged")
val open_path = sk_path_new().move_to(0.0, 0.0).line_to(4.0, 0.0)
val before = open_path.count_verbs()
val closed = open_path.close()
expect(open_path.count_verbs()).to_equal(before)
expect(closed.count_verbs()).to_equal(before + 1)
```

</details>

#### a chain that discards an intermediate result loses that segment

- a chain that discards an intermediate result loses that segment
   - Expected: base.count_verbs() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a chain that discards an intermediate result loses that segment")
# Direct demonstration of the defect shape: `base.line_to(...)` used
# as a statement contributes nothing to `base`.
val base = sk_path_new().move_to(0.0, 0.0)
base.line_to(9.0, 9.0)
expect(base.count_verbs()).to_equal(1)
```

</details>

### path_op results are structurally complete

#### disjoint union carries the verbs of BOTH rectangles

- disjoint union carries the verbs of BOTH rectangles


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("disjoint union carries the verbs of BOTH rectangles")
val a = _rect(0.0, 0.0, 4.0, 4.0)
val b = _rect(10.0, 10.0, 14.0, 14.0)
val one_rect = a.count_verbs()
val u = path_op(a, b, PathOp.Union)
# Dropping either emit leaves at most one rect's worth of verbs.
expect(u.count_verbs()).to_be_greater_than(one_rect)
```

</details>

#### overlapping union carries more verbs than a single rectangle

- overlapping union carries more verbs than a single rectangle


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("overlapping union carries more verbs than a single rectangle")
val a = _rect(0.0, 0.0, 10.0, 10.0)
val b = _rect(5.0, 5.0, 15.0, 15.0)
val one_rect = a.count_verbs()
val u = path_op(a, b, PathOp.Union)
expect(u.count_verbs()).to_be_greater_than(one_rect)
```

</details>

#### union bbox is never smaller than either operand bbox

- union bbox is never smaller than either operand bbox
   - Expected: covers_a is true
   - Expected: covers_b is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("union bbox is never smaller than either operand bbox")
val a = _rect(0.0, 0.0, 10.0, 10.0)
val b = _rect(5.0, 5.0, 15.0, 15.0)
val u = path_op(a, b, PathOp.Union)
val ba = a.bounds()
val bb = b.bounds()
val bu = u.bounds()
val covers_a = bu.left <= ba.left and bu.top <= ba.top and bu.right >= ba.right and bu.bottom >= ba.bottom
val covers_b = bu.left <= bb.left and bu.top <= bb.top and bu.right >= bb.right and bu.bottom >= bb.bottom
expect(covers_a).to_equal(true)
expect(covers_b).to_equal(true)
```

</details>

#### union is symmetric in its operands' bboxes

- union is symmetric in its operands' bboxes
   - Expected: ab.left equals `ba.left`
   - Expected: ab.top equals `ba.top`
   - Expected: ab.right equals `ba.right`
   - Expected: ab.bottom equals `ba.bottom`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("union is symmetric in its operands' bboxes")
val a = _rect(0.0, 0.0, 10.0, 10.0)
val b = _rect(5.0, 5.0, 15.0, 15.0)
val ab = path_op(a, b, PathOp.Union).bounds()
val ba = path_op(b, a, PathOp.Union).bounds()
# An emit dropped on only one side breaks this symmetry.
expect(ab.left).to_equal(ba.left)
expect(ab.top).to_equal(ba.top)
expect(ab.right).to_equal(ba.right)
expect(ab.bottom).to_equal(ba.bottom)
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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `d4a8c5d305eb4f0959fe54fef5c06865d200903e52e0d1158f4735f47d7374b5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d4a8c5d305eb4f0959fe54fef5c06865d200903e52e0d1158f4735f47d7374b5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d4a8c5d305eb4f0959fe54fef5c06865d200903e52e0d1158f4735f47d7374b5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/unit/lib/skia/path_builder_immutable_return_class_spec.spl
mirror: doc/06_spec/unit/lib/skia/path_builder_immutable_return_class_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/skia/path_builder_immutable_return_class_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/skia/path_builder_immutable_return_class_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/skia/path_builder_immutable_return_class_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/lib/skia/path_builder_immutable_return_class_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'move_to returns a new path and leaves the receiver empty' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/skia/path_builder_immutable_return_class_spec.spl:63:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'line_to returns a new path and leaves the receiver unchanged' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/skia/path_builder_immutable_return_class_spec.spl:72:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'close returns a new path and leaves the receiver unchanged' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
