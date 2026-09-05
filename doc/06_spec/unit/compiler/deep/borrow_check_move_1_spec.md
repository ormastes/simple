# borrow_check_move_1_spec

> Borrow-checker move dataflow — forward propagation across program points

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# borrow_check_move_1_spec

Borrow-checker move dataflow — forward propagation across program points

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/deep/borrow_check_move_1_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Borrow-checker move dataflow — forward propagation across program points
and place-projection granularity (lane SF1, 2026-07-28).

Companion to test/01_unit/compiler/borrow/borrow_check_spec.spl, which
covers the top-level same-point/later-point/reassign contract. This file
drills into BorrowGraph.moved_now specifically at the PlaceElem.Field
projection granularity: place_conflicts_with treats a place and any of
its projections as conflicting (x conflicts with x.field), so a move of
the whole local must be visible through a later field read, and a move of
one field must be visible through a later whole-local read.

Places are built via the `Place(base:, projections:)` struct literal
rather than a chained `.field(idx)` call: the field-projection helper in
borrow_graph.spl is a free function (`place_field(self: Place, idx: i64)`,
not an `impl Place` method), so it is not reachable through method-call
syntax and is not re-exported from the borrow_check package besides.

## Scenarios

### BorrowGraph move dataflow — forward propagation

#### detects use-after-move at the same program point

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- detects use-after-move at the same program point


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects use-after-move at the same program point")
var graph = BorrowGraph.create()
val p = Place.local(0)
graph.record_move(3, p)
graph.record_use(3, p)
assert_true(graph.has_errors())
```

</details>

#### detects use-after-move at a LATER program point

- detects use-after-move at a LATER program point


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects use-after-move at a LATER program point")
# Core dataflow fix: moved_places used to be keyed and read only at
# the SAME point, so a move at pt3 + use at pt7 was invisible.
# moved_now is the running forward union that closes this gap.
var graph = BorrowGraph.create()
val p = Place.local(0)
graph.record_move(3, p)
graph.record_use(7, p)
assert_true(graph.has_errors())
```

</details>

#### detects use-after-move many points later

- detects use-after-move many points later


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects use-after-move many points later")
var graph = BorrowGraph.create()
val p = Place.local(0)
graph.record_move(1, p)
graph.record_use(50, p)
assert_true(graph.has_errors())
```

</details>

### BorrowGraph move dataflow — place-projection granularity

#### a whole-local move is visible through a later FIELD read

- a whole-local move is visible through a later FIELD read


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a whole-local move is visible through a later FIELD read")
# x moved at pt3; x.f0 read at pt7 -> conflict (x is a prefix of
# x.f0), even though the exact Place values differ.
var graph = BorrowGraph.create()
val whole: Place = Place.local(0)
val field0: Place = field_of(whole, 0)
graph.record_move(3, whole)
graph.record_use(7, field0)
assert_true(graph.has_errors())
```

</details>

#### a FIELD move is visible through a later whole-local read

- a FIELD move is visible through a later whole-local read


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a FIELD move is visible through a later whole-local read")
var graph = BorrowGraph.create()
val whole: Place = Place.local(0)
val field0: Place = field_of(whole, 0)
graph.record_move(3, field0)
graph.record_use(7, whole)
assert_true(graph.has_errors())
```

</details>

#### moving one field does not flag a read of a DIFFERENT field

- moving one field does not flag a read of a DIFFERENT field


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("moving one field does not flag a read of a DIFFERENT field")
var graph = BorrowGraph.create()
val base: Place = Place.local(0)
val field0: Place = field_of(base, 0)
val field1: Place = field_of(base, 1)
graph.record_move(3, field0)
graph.record_use(7, field1)
assert_false(graph.has_errors())
```

</details>

#### different dynamic index locals still conflict conservatively

- different dynamic index locals still conflict conservatively


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("different dynamic index locals still conflict conservatively")
# Local IDs identify the expressions that compute an index, not the
# runtime values. They can both evaluate to the same element.
var graph = BorrowGraph.create()
val base: Place = Place.local(0)
val left: Place = index_of(base, 1)
val right: Place = index_of(base, 2)
graph.record_move(3, left)
graph.record_use(7, right)
assert_true(graph.has_errors())
```

</details>

#### borrow-of-moved is also forward-propagated across projections

- borrow-of-moved is also forward-propagated across projections


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("borrow-of-moved is also forward-propagated across projections")
var graph = BorrowGraph.create()
val whole: Place = Place.local(0)
val field0: Place = field_of(whole, 0)
graph.record_move(3, whole)
val b = graph.record_borrow(7, field0, BorrowKind.Shared)
assert_false(b.?)
assert_true(graph.has_errors())
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

- Canonical SPipe generation for source `38bf0fbbc71077549298f5b74a2acd1c93dd1ead578c1a163d6e897456897847`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `38bf0fbbc71077549298f5b74a2acd1c93dd1ead578c1a163d6e897456897847`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `38bf0fbbc71077549298f5b74a2acd1c93dd1ead578c1a163d6e897456897847`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/compiler/deep/borrow_check_move_1_spec.spl
mirror: doc/06_spec/unit/compiler/deep/borrow_check_move_1_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/deep/borrow_check_move_1_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/deep/borrow_check_move_1_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/deep/borrow_check_move_1_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'detects use-after-move at the same program point' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/deep/borrow_check_move_1_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'detects use-after-move at a LATER program point' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/deep/borrow_check_move_1_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'detects use-after-move many points later' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
