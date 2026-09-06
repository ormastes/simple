# Indexed Augmented Assignment Specification

> Tests covering interpreter indexed augmented assignment.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Indexed Augmented Assignment Specification

## Scenarios

### interpreter indexed augmented assignment

#### applies every augmented operator to an array element

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- applies every augmented operator to an array element
   - Expected: xs[0] equals `15`
   - Expected: xs[1] equals `15`
   - Expected: xs[2] equals `60`
   - Expected: xs[3] equals `10`
   - Expected: xs[4] equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("applies every augmented operator to an array element")
var xs = [10, 20, 30, 40, 50]
xs[0] += 5
xs[1] -= 5
xs[2] *= 2
xs[3] /= 4
xs[4] %= 7
expect(xs[0]).to_equal(15)
expect(xs[1]).to_equal(15)
expect(xs[2]).to_equal(60)
expect(xs[3]).to_equal(10)
expect(xs[4]).to_equal(1)
```

</details>

#### applies an augmented operator to a dict entry

- applies an augmented operator to a dict entry
   - Expected: counts["a"] equals `11`
   - Expected: counts["b"] equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("applies an augmented operator to a dict entry")
var counts = {"a": 1, "b": 2}
counts["a"] += 10
counts["b"] *= 3
expect(counts["a"]).to_equal(11)
expect(counts["b"]).to_equal(6)
```

</details>

#### applies an augmented operator through a field-access receiver

- applies an augmented operator through a field-access receiver
   - Expected: box.slots[1] equals `42`
   - Expected: box.slots[0] equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("applies an augmented operator through a field-access receiver")
var box = CounterBox(slots: [1, 2, 3])
box.slots[1] += 40
expect(box.slots[1]).to_equal(42)
expect(box.slots[0]).to_equal(1)
```

</details>

#### evaluates a side-effecting subscript exactly once

- evaluates a side-effecting subscript exactly once
   - Expected: xs[2] equals `8`
   - Expected: subscript_evaluations_ equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("evaluates a side-effecting subscript exactly once")
var xs = [7, 7, 7]
subscript_evaluations_ = 0
xs[counting_index(2)] += 1
expect(xs[2]).to_equal(8)
expect(subscript_evaluations_).to_equal(1)
```

</details>

#### leaves no temporary bindings visible after the assignment

- leaves no temporary bindings visible after the assignment
   - Expected: xs[0] equals `2`
   - Expected: after equals `9`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("leaves no temporary bindings visible after the assignment")
var xs = [1, 2]
xs[0] += 1
# The desugaring binds `__aug_idx_temp__`/`__aug_rhs_temp__` internally
# and must restore the environment; the surrounding names stay intact.
val after = 9
expect(xs[0]).to_equal(2)
expect(after).to_equal(9)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/interpreter/indexed_augmented_assignment_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering interpreter indexed augmented assignment.
- interpreter indexed augmented assignment

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `def6464b36d7945be84cdec20699487b0c845aebaf0a287e48fffa6ba447eef4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `def6464b36d7945be84cdec20699487b0c845aebaf0a287e48fffa6ba447eef4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `def6464b36d7945be84cdec20699487b0c845aebaf0a287e48fffa6ba447eef4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/interpreter/indexed_augmented_assignment_spec.spl
mirror: doc/06_spec/01_unit/compiler/interpreter/indexed_augmented_assignment_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/interpreter/indexed_augmented_assignment_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/interpreter/indexed_augmented_assignment_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/interpreter/indexed_augmented_assignment_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 13 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/interpreter/indexed_augmented_assignment_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'applies every augmented operator to an array element' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/interpreter/indexed_augmented_assignment_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'applies an augmented operator to a dict entry' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/interpreter/indexed_augmented_assignment_spec.spl:59:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'applies an augmented operator through a field-access receiver' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
