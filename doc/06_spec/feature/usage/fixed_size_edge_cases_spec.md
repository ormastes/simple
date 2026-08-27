# Fixed-Size Array Edge Cases and Boundary Conditions

> This spec exercises the boundary conditions and edge cases of fixed-size arrays that go beyond typical usage. It tests zero-length arrays, single-element arrays, negative indexing on various sizes, and fixed-size arrays of non-numeric types (text, bool). It also verifies that functional operations like `map`, `filter`, and `reduce` behave correctly when applied to fixed-size arrays, including cases where `filter` produces a result smaller than the original size.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Fixed-Size Array Edge Cases and Boundary Conditions

This spec exercises the boundary conditions and edge cases of fixed-size arrays that go beyond typical usage. It tests zero-length arrays, single-element arrays, negative indexing on various sizes, and fixed-size arrays of non-numeric types (text, bool). It also verifies that functional operations like `map`, `filter`, and `reduce` behave correctly when applied to fixed-size arrays, including cases where `filter` produces a result smaller than the original size.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #LANG-008b |
| Category | Language |
| Status | Active |
| Source | `test/feature/usage/fixed_size_edge_cases_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This spec exercises the boundary conditions and edge cases of fixed-size arrays that go
beyond typical usage. It tests zero-length arrays, single-element arrays, negative indexing
on various sizes, and fixed-size arrays of non-numeric types (text, bool). It also verifies
that functional operations like `map`, `filter`, and `reduce` behave correctly when applied
to fixed-size arrays, including cases where `filter` produces a result smaller than the
original size.

## Syntax

```simple
use std.spec.step

val empty: [i64; 0] = []
val single: [i64; 1] = [42]
val names: [text; 3] = ["alice", "bob", "charlie"]
val flags: [bool; 2] = [true, false]
val big = arr.filter(_1 > 3)
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| Zero-Size Array | `[T; 0]` is a valid empty fixed-size array that supports iteration |
| Boundary Indexing | Single and two-element arrays test the smallest non-trivial sizes |
| Multi-Type Support | Fixed-size arrays work with `i64`, `f64`, `text`, and `bool` element types |
| Size-Changing Ops | `filter` on a fixed-size array returns a dynamic array that may be smaller |

## Scenarios

### Fixed-Size Array Edge Cases

#### Size Zero

#### allows size-zero arrays

- allows size-zero arrays


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("allows size-zero arrays")
val empty: [i64; 0] = []
expect empty.len() == 0
```

</details>

#### iterates over size-zero arrays

- iterates over size-zero arrays


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("iterates over size-zero arrays")
val empty: [i64; 0] = []
var count = 0
for _ in empty:
    count = count + 1
expect count == 0
```

</details>

#### Negative Indexing

#### supports negative indices

- supports negative indices


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("supports negative indices")
val arr: [i64; 5] = [1, 2, 3, 4, 5]
expect arr[-1] == 5
expect arr[-2] == 4
expect arr[-3] == 3
```

</details>

#### Boundary Conditions

#### handles single element arrays

- handles single element arrays


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("handles single element arrays")
val single: [i64; 1] = [42]
expect single[0] == 42
expect single.len() == 1
```

</details>

#### handles two element arrays

- handles two element arrays


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("handles two element arrays")
val pair: [i64; 2] = [10, 20]
expect pair[0] == 10
expect pair[1] == 20
expect pair.len() == 2
```

</details>

#### Mixed Types

#### works with string arrays

- works with string arrays


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("works with string arrays")
val names: [text; 3] = ["alice", "bob", "charlie"]
expect names[0] == "alice"
expect names.len() == 3
```

</details>

#### works with boolean arrays

- works with boolean arrays


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("works with boolean arrays")
val flags: [bool; 2] = [true, false]
expect flags[0] == true
expect flags[1] == false
```

</details>

#### Functional Operations on Fixed

#### map preserves values

- map preserves values


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("map preserves values")
val arr: [i64; 4] = [1, 2, 3, 4]
val doubled = arr.map(_1 * 2)
expect doubled[0] == 2
expect doubled.len() == 4
expect doubled[3] == 8
```

</details>

#### filter may reduce size

- filter may reduce size


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("filter may reduce size")
val arr: [i64; 5] = [1, 2, 3, 4, 5]
val big = arr.filter(_1 > 3)
expect big[0] == 4
expect big.len() == 2
expect big[1] == 5
```

</details>

#### reduce works on fixed arrays

- reduce works on fixed arrays


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("reduce works on fixed arrays")
val arr: [i64; 3] = [10, 20, 30]
val total = arr.reduce(0, \acc, x: acc + x)
expect total == 60
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-FEATURE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `9fec30fc376f741cf6ca62c05e2465c0e98d16713e7d419bf9465546ba0b7e00`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9fec30fc376f741cf6ca62c05e2465c0e98d16713e7d419bf9465546ba0b7e00`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9fec30fc376f741cf6ca62c05e2465c0e98d16713e7d419bf9465546ba0b7e00`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/feature/usage/fixed_size_edge_cases_spec.spl
mirror: doc/06_spec/feature/usage/fixed_size_edge_cases_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/usage/fixed_size_edge_cases_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/usage/fixed_size_edge_cases_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/usage/fixed_size_edge_cases_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'allows size-zero arrays' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/fixed_size_edge_cases_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'iterates over size-zero arrays' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/fixed_size_edge_cases_spec.spl:63:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'supports negative indices' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
